#define _GNU_SOURCE
#define SYSCALL_NO_TLS 1
#include <stdlib.h>
#include <stdarg.h>
#include <stddef.h>
#include <string.h>
#include <unistd.h>
#include <stdint.h>
#include <elf.h>
#include <sys/stat.h>
#include <sys/mman.h>
#include <limits.h>
#include <fcntl.h>
#include <errno.h>
#include <link.h>
#include <setjmp.h>
#include <ctype.h>
#include <dlfcn.h>
#include <semaphore.h>
#include "dynlink.h"

#include <unistd.h>
#include <stdio.h>

// #include "musl-1.2.5/arch/x86_64/reloc.h"
#include "reloc.h"

#include "syscall.h"

static size_t ldso_page_size = 0x1000;
#ifndef PAGE_SIZE
#define PAGE_SIZE ldso_page_size
#endif

// #define malloc __libc_malloc
// #define calloc __libc_calloc
// #define realloc __libc_realloc
// #define free __libc_free

#define MAXP2(a,b) (-(-(a)&-(b)))
#define ALIGN(x,y) ((x)+(y)-1 & -(y))

#define container_of(p,t,m) ((t*)((char *)(p)-offsetof(t,m)))
#define countof(a) ((sizeof (a))/(sizeof (a)[0]))

struct td_index {
	size_t args[2];
	struct td_index *next;
};

struct dso {
	unsigned char *base;
	char *name;
	size_t *dynv;
	struct dso *next, *prev;

	Phdr *phdr;
	int phnum;
	size_t phentsize;
	Sym *syms;
	Elf_Symndx *hashtab;
	uint32_t *ghashtab;
	int16_t *versym;
	char *strings;
	struct dso *syms_next, *lazy_next;
	size_t *lazy, lazy_cnt;
	unsigned char *map;
	size_t map_len;
	dev_t dev;
	ino_t ino;
	char relocated;
	char constructed;
	char kernel_mapped;
	char mark;
	char bfs_built;
	char runtime_loaded;
	struct dso **deps, *needed_by;
	size_t ndeps_direct;
	size_t next_dep;
	char *rpath_orig, *rpath;
	size_t tls_id;
	size_t relro_start, relro_end;
	uintptr_t *new_dtv;
	unsigned char *new_tls;
	struct td_index *td_index;
	struct dso *fini_next;
	char *shortname;
#if DL_FDPIC
	unsigned char *base;
#else
	struct fdpic_loadmap *loadmap;
#endif
	struct funcdesc {
		void *addr;
		size_t *got;
	} *funcdescs;
	size_t *got;
	char buf[];
};

struct symdef {
	Sym *sym;
	struct dso *dso;
};

typedef void (*stage3_func)(size_t *, size_t *);
#define MIN_TLS_ALIGN offsetof(struct builtin_tls, pt)

#define ADDEND_LIMIT 4096
static size_t *saved_addends, *apply_addends_to;

static struct dso ldso;
static struct dso *head, *tail, *fini_head, *syms_tail, *lazy_head;
static char *env_path, *sys_path;
static unsigned long long gencnt;
static int runtime;
static int ldd_mode;
static int ldso_fail;
static int noload;
static int shutting_down;
static jmp_buf *rtld_fail;
static size_t static_tls_cnt;
static struct dso *builtin_deps[2];
static struct dso *const no_deps[1];
static struct dso *builtin_ctor_queue[4];
static struct dso **main_ctor_queue;
static struct fdpic_loadmap *app_loadmap;
static struct fdpic_dummy_loadmap app_dummy_loadmap;

extern weak hidden char __ehdr_start[];

extern hidden int __malloc_replaced;

hidden void (*const __init_array_start)(void)=0, (*const __fini_array_start)(void)=0;

extern hidden void (*const __init_array_end)(void), (*const __fini_array_end)(void);

weak_alias(__init_array_start, __init_array_end);
weak_alias(__fini_array_start, __fini_array_end);

static int dl_strcmp(const char *l, const char *r)
{
	for (; *l==*r && *l; l++, r++);
	return *(unsigned char *)l - *(unsigned char *)r;
}
#define strcmp(l,r) dl_strcmp(l,r)

#define laddr(p, v) (void *)((p)->base + (v))
#define laddr_pg(p, v) laddr(p, v)
#define fpaddr(p, v) ((void (*)())laddr(p, v))

static void decode_vec(size_t *v, size_t *a, size_t cnt)
{
	size_t i;
	for (i=0; i<cnt; i++) a[i] = 0;
	for (; v[0]; v+=2) if (v[0]-1<cnt-1) {
		if (v[0] < 8*sizeof(long))
			a[0] |= 1UL<<v[0];
		a[v[0]] = v[1];
	}
}

static int search_vec(size_t *v, size_t *r, size_t key)
{
	for (; v[0]!=key; v+=2)
		if (!v[0]) return 0;
	*r = v[1];
	return 1;
}

static uint32_t sysv_hash(const char *s0)
{
	const unsigned char *s = (void *)s0;
	uint_fast32_t h = 0;
	while (*s) {
		h = 16*h + *s++;
		h ^= h>>24 & 0xf0;
	}
	return h & 0xfffffff;
}

static uint32_t gnu_hash(const char *s0)
{
	const unsigned char *s = (void *)s0;
	uint_fast32_t h = 5381;
	for (; *s; s++)
		h += h*32 + *s;
	return h;
}

static Sym *sysv_lookup(const char *s, uint32_t h, struct dso *dso)
{
	size_t i;
	Sym *syms = dso->syms;
	Elf_Symndx *hashtab = dso->hashtab;
	char *strings = dso->strings;
	for (i=hashtab[2+h%hashtab[0]]; i; i=hashtab[2+hashtab[0]+i]) {
		if ((!dso->versym || dso->versym[i] >= 0)
		    && (!strcmp(s, strings+syms[i].st_name)))
			return syms+i;
	}
	return 0;
}

static Sym *gnu_lookup(uint32_t h1, uint32_t *hashtab, struct dso *dso, const char *s)
{
	uint32_t nbuckets = hashtab[0];
	uint32_t *buckets = hashtab + 4 + hashtab[2]*(sizeof(size_t)/4);
	uint32_t i = buckets[h1 % nbuckets];

	if (!i) return 0;

	uint32_t *hashval = buckets + nbuckets + (i - hashtab[1]);

	for (h1 |= 1; ; i++) {
		uint32_t h2 = *hashval++;
		if ((h1 == (h2|1)) && (!dso->versym || dso->versym[i] >= 0)
		    && !strcmp(s, dso->strings + dso->syms[i].st_name))
			return dso->syms+i;
		if (h2 & 1) break;
	}

	return 0;
}

static Sym *gnu_lookup_filtered(uint32_t h1, uint32_t *hashtab, struct dso *dso, const char *s, uint32_t fofs, size_t fmask)
{
	const size_t *bloomwords = (const void *)(hashtab+4);
	size_t f = bloomwords[fofs & (hashtab[2]-1)];
	if (!(f & fmask)) return 0;

	f >>= (h1 >> hashtab[3]) % (8 * sizeof f);
	if (!(f & 1)) return 0;

	return gnu_lookup(h1, hashtab, dso, s);
}

#define OK_TYPES (1<<STT_NOTYPE | 1<<STT_OBJECT | 1<<STT_FUNC | 1<<STT_COMMON | 1<<STT_TLS)
#define OK_BINDS (1<<STB_GLOBAL | 1<<STB_WEAK | 1<<STB_GNU_UNIQUE)

#ifndef ARCH_SYM_REJECT_UND
#define ARCH_SYM_REJECT_UND(s) 0
#endif

#if defined(__GNUC__)
__attribute__((always_inline))
#endif
static inline struct symdef find_sym2(struct dso *dso, const char *s, int need_def, int use_deps)
{
	uint32_t h = 0, gh = gnu_hash(s), gho = gh / (8*sizeof(size_t)), *ght;
	size_t ghm = 1ul << gh % (8*sizeof(size_t));
	struct symdef def = {0};
	struct dso **deps = use_deps ? dso->deps : 0;
	for (; dso; dso=use_deps ? *deps++ : dso->syms_next) {
		Sym *sym;
		if ((ght = dso->ghashtab)) {
			sym = gnu_lookup_filtered(gh, ght, dso, s, gho, ghm);
		} else {
			if (!h) h = sysv_hash(s);
			sym = sysv_lookup(s, h, dso);
		}
		if (!sym) continue;
		if (!sym->st_shndx)
			if (need_def || (sym->st_info&0xf) == STT_TLS
			    || ARCH_SYM_REJECT_UND(sym))
				continue;
		if (!sym->st_value)
			if ((sym->st_info&0xf) != STT_TLS)
				continue;
		if (!(1<<(sym->st_info&0xf) & OK_TYPES)) continue;
		if (!(1<<(sym->st_info>>4) & OK_BINDS)) continue;
		def.sym = sym;
		def.dso = dso;
		break;
	}
	return def;
}

static struct symdef find_sym(struct dso *dso, const char *s, int need_def)
{
	return find_sym2(dso, s, need_def, 0);
}

static struct symdef get_lfs64(const char *name)
{
	const char *p;
	static const char lfs64_list[] =
		"aio_cancel\0aio_error\0aio_fsync\0aio_read\0aio_return\0"
		"aio_suspend\0aio_write\0alphasort\0creat\0fallocate\0"
		"fgetpos\0fopen\0freopen\0fseeko\0fsetpos\0fstat\0"
		"fstatat\0fstatfs\0fstatvfs\0ftello\0ftruncate\0ftw\0"
		"getdents\0getrlimit\0glob\0globfree\0lio_listio\0"
		"lockf\0lseek\0lstat\0mkostemp\0mkostemps\0mkstemp\0"
		"mkstemps\0mmap\0nftw\0open\0openat\0posix_fadvise\0"
		"posix_fallocate\0pread\0preadv\0prlimit\0pwrite\0"
		"pwritev\0readdir\0scandir\0sendfile\0setrlimit\0"
		"stat\0statfs\0statvfs\0tmpfile\0truncate\0versionsort\0"
		"__fxstat\0__fxstatat\0__lxstat\0__xstat\0";
	size_t l;
	char buf[16];
	for (l=0; name[l]; l++) {
		if (l >= sizeof buf) goto nomatch;
		buf[l] = name[l];
	}
	if (!strcmp(name, "readdir64_r"))
		return find_sym(&ldso, "readdir_r", 1);
	if (l<2 || name[l-2]!='6' || name[l-1]!='4')
		goto nomatch;
	buf[l-=2] = 0;
	for (p=lfs64_list; *p; p++) {
		if (!strcmp(buf, p)) return find_sym(&ldso, buf, 1);
		while (*p) p++;
	}
nomatch:
	return (struct symdef){ 0 };
}

static void do_relocs(struct dso *dso, size_t *rel, size_t rel_size, size_t stride)
{
	unsigned char *base = dso->base;
	Sym *syms = dso->syms;
	char *strings = dso->strings;
	Sym *sym;
	const char *name;
	void *ctx;
	int type;
	int sym_index;
	struct symdef def;
	size_t *reloc_addr;
	size_t sym_val;
	size_t tls_val;
	size_t addend;
	int skip_relative = 0, reuse_addends = 0, save_slot = 0;

	if (dso == &ldso) {
		/* Only ldso's REL table needs addend saving/reuse. */
		if (rel == apply_addends_to)
			reuse_addends = 1;
		skip_relative = 1;
	}

	for (; rel_size; rel+=stride, rel_size-=stride*sizeof(size_t)) {
		if (skip_relative && IS_RELATIVE(rel[1], dso->syms)) continue;
		type = R_TYPE(rel[1]);
		if (type == REL_NONE) continue;
		reloc_addr = laddr(dso, rel[0]);

		if (stride > 2) {
			addend = rel[2];
		} else if (type==REL_GOT || type==REL_PLT|| type==REL_COPY) {
			addend = 0;
		} else if (reuse_addends) {
			/* Save original addend in stage 2 where the dso
			 * chain consists of just ldso; otherwise read back
			 * saved addend since the inline one was clobbered. */
			if (head==&ldso)
				saved_addends[save_slot] = *reloc_addr;
			addend = saved_addends[save_slot++];
		} else {
			addend = *reloc_addr;
		}

		sym_index = R_SYM(rel[1]);
		if (sym_index) {
			sym = syms + sym_index;
			name = strings + sym->st_name;
			ctx = type==REL_COPY ? head->syms_next : head;
			def = (sym->st_info>>4) == STB_LOCAL
				? (struct symdef){ .dso = dso, .sym = sym }
				: find_sym(ctx, name, type==REL_PLT);
			if (!def.sym) def = get_lfs64(name);
			if (!def.sym && (sym->st_shndx != SHN_UNDEF
			    || sym->st_info>>4 != STB_WEAK)) {
				if (dso->lazy && (type==REL_PLT || type==REL_GOT)) {
					dso->lazy[3*dso->lazy_cnt+0] = rel[0];
					dso->lazy[3*dso->lazy_cnt+1] = rel[1];
					dso->lazy[3*dso->lazy_cnt+2] = addend;
					dso->lazy_cnt++;
					continue;
				}
				dprintf(2, "Error relocating %s: %s: symbol not found",
					dso->name, name);
				if (runtime) longjmp(*rtld_fail, 1);
				continue;
			}
		} else {
			sym = 0;
			def.sym = 0;
			def.dso = dso;
		}

		sym_val = def.sym ? (size_t)laddr(def.dso, def.sym->st_value) : 0;
		tls_val = def.sym ? def.sym->st_value : 0;

		switch(type) {
		case REL_OFFSET:
			addend -= (size_t)reloc_addr;
		case REL_SYMBOLIC:
		case REL_GOT:
		case REL_PLT:
			*reloc_addr = sym_val + addend;
			break;
		case REL_USYMBOLIC:
			memcpy(reloc_addr, &(size_t){sym_val + addend}, sizeof(size_t));
			break;
		case REL_RELATIVE:
			*reloc_addr = (size_t)base + addend;
			break;
		case REL_SYM_OR_REL:
			if (sym) *reloc_addr = sym_val + addend;
			else *reloc_addr = (size_t)base + addend;
			break;
		case REL_COPY:
			memcpy(reloc_addr, (void *)sym_val, sym->st_size);
			break;
		case REL_OFFSET32:
			*(uint32_t *)reloc_addr = sym_val + addend
				- (size_t)reloc_addr;
			break;
		case REL_FUNCDESC:
			*reloc_addr = def.sym ? (size_t)(def.dso->funcdescs
				+ (def.sym - def.dso->syms)) : 0;
			break;
		case REL_FUNCDESC_VAL:
			if ((sym->st_info&0xf) == STT_SECTION) *reloc_addr += sym_val;
			else *reloc_addr = sym_val;
			reloc_addr[1] = def.sym ? (size_t)def.dso->got : 0;
			break;
		default:
			dprintf(2, "Error relocating %s: unsupported relocation type %d",
				dso->name, type);
			if (runtime) longjmp(*rtld_fail, 1);
			continue;
		}
	}
}

static void do_relr_relocs(struct dso *dso, size_t *relr, size_t relr_size)
{
	if (dso == &ldso) return; /* self-relocation was done in _dlstart */
	unsigned char *base = dso->base;
	size_t *reloc_addr;
	for (; relr_size; relr++, relr_size-=sizeof(size_t))
		if ((relr[0]&1) == 0) {
			reloc_addr = laddr(dso, relr[0]);
			*reloc_addr++ += (size_t)base;
		} else {
			int i = 0;
			for (size_t bitmap=relr[0]; (bitmap>>=1); i++)
				if (bitmap&1)
					reloc_addr[i] += (size_t)base;
			reloc_addr += 8*sizeof(size_t)-1;
		}
}

static void *mmap_fixed(void *p, size_t n, int prot, int flags, int fd, off_t off)
{
	static int no_map_fixed;
	char *q;
	if (!n) return p;
	if (!no_map_fixed) {
		q = mmap(p, n, prot, flags|MAP_FIXED, fd, off);
		if (!DL_NOMMU_SUPPORT || q != MAP_FAILED || errno != EINVAL)
			return q;
		no_map_fixed = 1;
	}
	/* Fallbacks for MAP_FIXED failure on NOMMU kernels. */
	if (flags & MAP_ANONYMOUS) {
		memset(p, 0, n);
		return p;
	}
	ssize_t r;
	if (lseek(fd, off, SEEK_SET) < 0) return MAP_FAILED;
	for (q=p; n; q+=r, off+=r, n-=r) {
		r = read(fd, q, n);
		if (r < 0 && errno != EINTR) return MAP_FAILED;
		if (!r) {
			memset(q, 0, n);
			break;
		}
	}
	return p;
}

static void *map_library(int fd, struct dso *dso)
{
	Ehdr buf[(896+sizeof(Ehdr))/sizeof(Ehdr)];
	void *allocated_buf=0;
	size_t phsize;
	size_t addr_min=SIZE_MAX, addr_max=0, map_len;
	size_t this_min, this_max;
	size_t nsegs = 0;
	off_t off_start;
	Ehdr *eh;
	Phdr *ph, *ph0;
	unsigned prot;
	unsigned char *map=MAP_FAILED, *base;
	size_t dyn=0;
	size_t tls_image=0;
	size_t i;

	ssize_t l = read(fd, buf, sizeof buf);
	eh = buf;
	if (l<0) return 0;
	if (l<sizeof *eh || (eh->e_type != ET_DYN && eh->e_type != ET_EXEC))
		goto noexec;
	phsize = eh->e_phentsize * eh->e_phnum;
	if (phsize > sizeof buf - sizeof *eh) {
		allocated_buf = malloc(phsize);
		if (!allocated_buf) return 0;
		l = pread(fd, allocated_buf, phsize, eh->e_phoff);
		if (l < 0) goto error;
		if (l != phsize) goto noexec;
		ph = ph0 = allocated_buf;
	} else if (eh->e_phoff + phsize > l) {
		l = pread(fd, buf+1, phsize, eh->e_phoff);
		if (l < 0) goto error;
		if (l != phsize) goto noexec;
		ph = ph0 = (void *)(buf + 1);
	} else {
		ph = ph0 = (void *)((char *)buf + eh->e_phoff);
	}
	for (i=eh->e_phnum; i; i--, ph=(void *)((char *)ph+eh->e_phentsize)) {
		if (ph->p_type == PT_DYNAMIC) {
			dyn = ph->p_vaddr;
		} else if (ph->p_type == PT_GNU_RELRO) {
			dso->relro_start = ph->p_vaddr & -PAGE_SIZE;
			dso->relro_end = (ph->p_vaddr + ph->p_memsz) & -PAGE_SIZE;
		}
		if (ph->p_type != PT_LOAD) continue;
		nsegs++;
		if (ph->p_vaddr < addr_min) {
			addr_min = ph->p_vaddr;
			off_start = ph->p_offset;
			prot = (((ph->p_flags&PF_R) ? PROT_READ : 0) |
				((ph->p_flags&PF_W) ? PROT_WRITE: 0) |
				((ph->p_flags&PF_X) ? PROT_EXEC : 0));
		}
		if (ph->p_vaddr+ph->p_memsz > addr_max) {
			addr_max = ph->p_vaddr+ph->p_memsz;
		}
	}
	if (!dyn) goto noexec;

	addr_max += PAGE_SIZE-1;
	addr_max &= -PAGE_SIZE;
	addr_min &= -PAGE_SIZE;
	off_start &= -PAGE_SIZE;
	map_len = addr_max - addr_min + off_start;
	/* The first time, we map too much, possibly even more than
	 * the length of the file. This is okay because we will not
	 * use the invalid part; we just need to reserve the right
	 * amount of virtual address space to map over later. */
	map = DL_NOMMU_SUPPORT
		? mmap((void *)addr_min, map_len, PROT_READ|PROT_WRITE|PROT_EXEC,
			MAP_PRIVATE|MAP_ANONYMOUS, -1, 0)
		: mmap((void *)addr_min, map_len, prot,
			MAP_PRIVATE, fd, off_start);
	if (map==MAP_FAILED) goto error;
	dso->map = map;
	dso->map_len = map_len;
	/* If the loaded file is not relocatable and the requested address is
	 * not available, then the load operation must fail. */
	if (eh->e_type != ET_DYN && addr_min && map!=(void *)addr_min) {
		errno = EBUSY;
		goto error;
	}
	base = map - addr_min;
	dso->phdr = 0;
	dso->phnum = 0;
	for (ph=ph0, i=eh->e_phnum; i; i--, ph=(void *)((char *)ph+eh->e_phentsize)) {
		if (ph->p_type != PT_LOAD) continue;
		/* Check if the programs headers are in this load segment, and
		 * if so, record the address for use by dl_iterate_phdr. */
		if (!dso->phdr && eh->e_phoff >= ph->p_offset
		    && eh->e_phoff+phsize <= ph->p_offset+ph->p_filesz) {
			dso->phdr = (void *)(base + ph->p_vaddr
				+ (eh->e_phoff-ph->p_offset));
			dso->phnum = eh->e_phnum;
			dso->phentsize = eh->e_phentsize;
		}
		this_min = ph->p_vaddr & -PAGE_SIZE;
		this_max = ph->p_vaddr+ph->p_memsz+PAGE_SIZE-1 & -PAGE_SIZE;
		off_start = ph->p_offset & -PAGE_SIZE;
		prot = (((ph->p_flags&PF_R) ? PROT_READ : 0) |
			((ph->p_flags&PF_W) ? PROT_WRITE: 0) |
			((ph->p_flags&PF_X) ? PROT_EXEC : 0));
		/* Reuse the existing mapping for the lowest-address LOAD */
		if ((ph->p_vaddr & -PAGE_SIZE) != addr_min || DL_NOMMU_SUPPORT)
			if (mmap_fixed(base+this_min, this_max-this_min, prot, MAP_PRIVATE|MAP_FIXED, fd, off_start) == MAP_FAILED)
				goto error;
		if (ph->p_memsz > ph->p_filesz && (ph->p_flags&PF_W)) {
			size_t brk = (size_t)base+ph->p_vaddr+ph->p_filesz;
			size_t pgbrk = brk+PAGE_SIZE-1 & -PAGE_SIZE;
			memset((void *)brk, 0, pgbrk-brk & PAGE_SIZE-1);
			if (pgbrk-(size_t)base < this_max && mmap_fixed((void *)pgbrk, (size_t)base+this_max-pgbrk, prot, MAP_PRIVATE|MAP_FIXED|MAP_ANONYMOUS, -1, 0) == MAP_FAILED)
				goto error;
		}
	}
	for (i=0; ((size_t *)(base+dyn))[i]; i+=2)
		if (((size_t *)(base+dyn))[i]==DT_TEXTREL) {
			if (mprotect(map, map_len, PROT_READ|PROT_WRITE|PROT_EXEC)
			    && errno != ENOSYS)
				goto error;
			break;
		}
done_mapping:
	dso->base = base;
	dso->dynv = laddr(dso, dyn);
	free(allocated_buf);
	return map;
noexec:
	errno = ENOEXEC;
error:
	free(allocated_buf);
	return 0;
}

static void decode_dyn(struct dso *p)
{
	size_t dyn[DYN_CNT];
	decode_vec(p->dynv, dyn, DYN_CNT);
	p->syms = laddr(p, dyn[DT_SYMTAB]);
	p->strings = laddr(p, dyn[DT_STRTAB]);
	if (dyn[0]&(1<<DT_HASH))
		p->hashtab = laddr(p, dyn[DT_HASH]);
	if (dyn[0]&(1<<DT_RPATH))
		p->rpath_orig = p->strings + dyn[DT_RPATH];
	if (dyn[0]&(1<<DT_RUNPATH))
		p->rpath_orig = p->strings + dyn[DT_RUNPATH];
	if (dyn[0]&(1<<DT_PLTGOT))
		p->got = laddr(p, dyn[DT_PLTGOT]);
	if (search_vec(p->dynv, dyn, DT_GNU_HASH))
		p->ghashtab = laddr(p, *dyn);
	if (search_vec(p->dynv, dyn, DT_VERSYM))
		p->versym = laddr(p, *dyn);
}

static void reloc_all(struct dso *p)
{
	size_t dyn[DYN_CNT];
	for (; p; p=p->next) {
		if (p->relocated) continue;
		decode_vec(p->dynv, dyn, DYN_CNT);
		do_relocs(p, laddr(p, dyn[DT_JMPREL]), dyn[DT_PLTRELSZ],
			2+(dyn[DT_PLTREL]==DT_RELA));
		do_relocs(p, laddr(p, dyn[DT_REL]), dyn[DT_RELSZ], 2);
		do_relocs(p, laddr(p, dyn[DT_RELA]), dyn[DT_RELASZ], 3);
		if (!DL_FDPIC)
			do_relr_relocs(p, laddr(p, dyn[DT_RELR]), dyn[DT_RELRSZ]);

		if (head != &ldso && p->relro_start != p->relro_end) {
			long ret = __syscall(SYS_mprotect, laddr(p, p->relro_start),
				p->relro_end-p->relro_start, PROT_READ);
			if (ret != 0 && ret != -ENOSYS) {
				dprintf(2, "Error relocating %s: RELRO protection failed: %m",
					p->name);
				if (runtime) longjmp(*rtld_fail, 1);
			}
		}

		p->relocated = 1;
	}
}

/* Stage 3 of the dynamic linker is called with the dynamic linker/libc
 * fully functional. Its job is to load (if not already loaded) and
 * process dependencies and relocations for the main application and
 * transfer control to its entry point. */

void __dls3(int argc, char **argv)
{
	static struct dso app, vdso;
	size_t aux[AUX_CNT];
	size_t i;
	char *env_preload=0;
	char *replace_argv0=0;
	size_t vdso_base;
	char **argv_orig = argv;

	{
		int fd;
		char *ldname = argv[0];
		size_t l = strlen(ldname);
		argv++;

		argv[-1] = (void *)(argc - (argv-argv_orig));

		fd = open(argv[0], O_RDONLY);
		if (fd < 0) {
			dprintf(2, "%s: cannot load %s: %s\n", ldname, argv[0], strerror(errno));
			_exit(1);
		}
		Ehdr *ehdr = map_library(fd, &app);
		if (!ehdr) {
			dprintf(2, "%s: %s: Not a valid dynamic program\n", ldname, argv[0]);
			_exit(1);
		}
		close(fd);
		ldso.name = ldname;
		app.name = argv[0];
		aux[AT_ENTRY] = (size_t)laddr(&app, ehdr->e_entry);
		/* Find the name that would have been used for the dynamic
		 * linker had ldd not taken its place. */
		if (ldd_mode) {
			for (i=0; i<app.phnum; i++) {
				if (app.phdr[i].p_type == PT_INTERP)
					ldso.name = laddr(&app, app.phdr[i].p_vaddr);
			}
			dprintf(1, "\t%s (%p)\n", ldso.name, ldso.base);
		}
	}
	decode_dyn(&app);

	/* Initial dso chain consists only of the app. */
	head = tail = syms_tail = &app;

	/* The main program must be relocated LAST since it may contain
	 * copy relocations which depend on libraries' relocations. */
	reloc_all(app.next);
	reloc_all(&app);

	if (ldso_fail) _exit(127);
	if (ldd_mode) _exit(0);

	/* Switch to runtime mode: any further failures in the dynamic
	 * linker are a reportable failure rather than a fatal startup
	 * error. */
	runtime = 1;

	if (replace_argv0) argv[0] = replace_argv0;

	errno = 0;
	CRTJMP((void *)aux[AT_ENTRY], argv-1);
	for(;;);
}

int main(int argc, char **argv) {
	__dls3(argc, argv);
	return 0;
}
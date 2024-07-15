CC = ./musl-arm/bin/musl-gcc

ARCH = arm

CFLAGS = -static -fpie -Wl,-pie -g -I src/arch/$(ARCH) -I src

all: prog dynlink

prog: src/prog.c
	$(CC) $^ -o $@ $(CFLAGS)

dynlink: src/dynlink.c
	$(CC) $^ -o $@ $(CFLAGS)

clean:
	@rm prog || true
	@rm dynlink || true

run: prog dynlink
	./dynlink $< 2
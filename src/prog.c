#include <stdio.h>
#include <stdlib.h>

int glob_uninit;
int glob_init = 0x42;

int foo() {
    static int stat = 0x43;
    return glob_uninit + glob_init + stat;
}

int main(int argc, char *argv[]) {
    int xd[64];
    glob_uninit += 1;
    int var = foo();
    printf("0x%02x %d %d\n", var, atoi(argv[1]) + 1, xd[1]);
    return 0;
}
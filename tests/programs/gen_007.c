#include <stdio.h>
#include <stdint.h>
int64_t A[32];
int64_t B[32];
int main() {
    int64_t v0 = 0, v1 = 0, v2 = 0, v3 = 0, v4 = 0, v5 = 0;
    int64_t b0 = 0, b1 = 0;
    v0 = 42;
    v3 = -5;
    v1 = 100;
    A[0] = 42;
    A[1] = -1;
    A[2] = 100;
    B[0] = 100;
    B[1] = 42;
    B[2] = 2;
    B[3] = 42;
    A[((int64_t)((uint64_t)(int64_t)((uint64_t)42 * (uint64_t)5) - (uint64_t)(int64_t)((uint64_t)v2 + (uint64_t)100)) % 32)] = v3;
    if (((b1 && ((10 != 10) ? 1 : 0)) ? 1 : 0)) {
        while (v4 < 7) {
            B[(v3 % 32)] = 100;
            v4 = v4 + 1;
        }
    } else {
        B[(v0 % 32)] = v5;
    }
    if ((((int64_t)((uint64_t)-1 + (uint64_t)10) <= 10) ? 1 : 0)) {
        v3 = v2;
    } else {
        b0 = ((v2 == v0) ? 1 : 0);
    }
    v4 = 7;
    printf("%s = %ld\n", "v0", v0);
    printf("%s = %ld\n", "v1", v1);
    printf("%s = %ld\n", "v2", v2);
    printf("%s = %ld\n", "v3", v3);
    printf("%s = %ld\n", "v4", v4);
    printf("%s = %ld\n", "v5", v5);
    printf("%s = %ld\n", "b0", b0);
    printf("%s = %ld\n", "b1", b1);
    return 0;
}

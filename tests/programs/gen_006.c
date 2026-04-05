#include <stdio.h>
#include <stdint.h>
int64_t A[32];
int64_t B[32];
int main() {
    int64_t v0 = 0, v1 = 0, v2 = 0, v3 = 0, v4 = 0, v5 = 0;
    int64_t b0 = 0, b1 = 0;
    v3 = 2;
    v1 = 1;
    v2 = 10;
    A[0] = 42;
    B[0] = 3;
    B[1] = 42;
    b0 = ((7 >= v0) ? 1 : 0);
    while (v2 < 6) {
        if (((7 > v1) ? 1 : 0)) {
            v4 = v2;
        } else {
            A[(10 % 32)] = v0;
        }
        v2 = v2 + 1;
    }
    v4 = (int64_t)((uint64_t)(int64_t)((uint64_t)7 + (uint64_t)v2) * (uint64_t)(int64_t)((uint64_t)v4 + (uint64_t)v3));
    B[(A[(v3 % 32)] % 32)] = (int64_t)((uint64_t)(int64_t)((uint64_t)10 - (uint64_t)5) + (uint64_t)B[(v3 % 32)]);
    if ((!((((v5 <= 1) ? 1 : 0) && ((v4 == -5) ? 1 : 0)) ? 1 : 0))) {
        if (((-5 <= 3) ? 1 : 0)) {
            v3 = v0;
        } else {
            A[(v3 % 32)] = 3;
        }
    } else {
        while (v0 < 7) {
            v5 = 100;
            v0 = v0 + 1;
        }
    }
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

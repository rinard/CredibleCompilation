#include <stdio.h>
#include <stdint.h>
int64_t A[32];
int64_t B[32];
int main() {
    int64_t v0 = 0, v1 = 0, v2 = 0, v3 = 0, v4 = 0, v5 = 0;
    int64_t b0 = 0, b1 = 0;
    v1 = -1;
    v5 = 2;
    v4 = 42;
    A[0] = 10;
    B[0] = -5;
    B[1] = 3;
    B[2] = 42;
    if (((((((v4 <= 3) ? 1 : 0) && ((v3 == 3) ? 1 : 0)) ? 1 : 0) && ((v3 > v4) ? 1 : 0)) ? 1 : 0)) {
        while (v1 < 10) {
            v2 = v5;
            v1 = v1 + 1;
        }
    } else {
        while (v4 < 2) {
            if (((v2 < 1) ? 1 : 0)) {
                v1 = 5;
            } else {
                v3 = v1;
            }
            v4 = v4 + 1;
        }
    }
    while (v0 < 7) {
        v4 = v3;
        v0 = v0 + 1;
    }
    while (v2 < 4) {
        v0 = (int64_t)((uint64_t)7 * (uint64_t)v2);
        v2 = v2 + 1;
    }
    if (((v4 >= 1) ? 1 : 0)) {
        v1 = (int64_t)((uint64_t)v4 * (uint64_t)1);
    } else {
        b0 = ((-1 >= 1) ? 1 : 0);
    }
    if ((!((((v3 == 0) ? 1 : 0) && ((v1 == -1) ? 1 : 0)) ? 1 : 0))) {
        A[(B[(1 % 32)] % 32)] = v3;
    } else {
        v3 = (int64_t)((uint64_t)0 - (uint64_t)7);
    }
    while (v5 < 6) {
        v2 = (v3 / 10);
        v5 = v5 + 1;
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

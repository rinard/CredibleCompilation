#include <stdio.h>
#include <stdint.h>
int64_t A[32];
int64_t B[32];
int main() {
    int64_t v0 = 0, v1 = 0, v2 = 0, v3 = 0, v4 = 0, v5 = 0;
    int64_t b0 = 0, b1 = 0;
    v1 = 1;
    v2 = 100;
    v0 = 2;
    A[0] = 5;
    A[1] = -1;
    A[2] = 3;
    B[0] = 3;
    B[1] = -5;
    B[2] = -5;
    while (v4 < 8) {
        v0 = 10;
        v4 = v4 + 1;
    }
    while (v0 < 1) {
        b0 = (!((v1 == 42) ? 1 : 0));
        v0 = v0 + 1;
    }
    if (((2 < B[(-1 % 32)]) ? 1 : 0)) {
        A[(v0 % 32)] = (int64_t)((uint64_t)-5 + (uint64_t)v4);
    } else {
        while (v5 < 3) {
            while (v1 < 3) {
                v1 = 10;
                v1 = v1 + 1;
            }
            v5 = v5 + 1;
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

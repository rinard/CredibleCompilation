#include <stdio.h>
#include <stdint.h>
int64_t A[32];
int64_t B[32];
int main() {
    int64_t v0 = 0, v1 = 0, v2 = 0, v3 = 0, v4 = 0, v5 = 0;
    int64_t b0 = 0, b1 = 0;
    v0 = -1;
    v4 = 3;
    v2 = -5;
    A[0] = -5;
    B[0] = 5;
    B[1] = -5;
    B[2] = 10;
    B[3] = 1;
    v0 = v3;
    v1 = (int64_t)((uint64_t)v2 + (uint64_t)(int64_t)((uint64_t)100 * (uint64_t)10));
    while (v4 < 7) {
        while (v2 < 1) {
            if (((v3 <= 42) ? 1 : 0)) {
                v1 = v0;
            } else {
                v4 = -5;
            }
            v2 = v2 + 1;
        }
        v4 = v4 + 1;
    }
    b0 = ((((((v0 != -5) ? 1 : 0) || ((v5 <= -5) ? 1 : 0)) ? 1 : 0) || (!((v0 < 7) ? 1 : 0))) ? 1 : 0);
    v1 = (int64_t)((uint64_t)100 + (uint64_t)v1);
    while (v1 < 6) {
        while (v5 < 1) {
            v1 = v4;
            v5 = v5 + 1;
        }
        v1 = v1 + 1;
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

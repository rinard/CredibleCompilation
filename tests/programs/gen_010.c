#include <stdio.h>
#include <stdint.h>
int64_t A[32];
int64_t B[32];
int main() {
    int64_t v0 = 0, v1 = 0, v2 = 0, v3 = 0, v4 = 0, v5 = 0;
    int64_t b0 = 0, b1 = 0;
    v0 = 1;
    v3 = -1;
    v4 = -5;
    A[0] = 2;
    B[0] = -1;
    B[1] = 5;
    v1 = 10;
    if (((((v3 > v4) ? 1 : 0) && ((0 > 3) ? 1 : 0)) ? 1 : 0)) {
        v0 = v1;
    } else {
        if (((v5 != 5) ? 1 : 0)) {
            v2 = 42;
        } else {
            while (v5 < 10) {
                v5 = 3;
                v5 = v5 + 1;
            }
        }
    }
    A[((int64_t)((uint64_t)2 + (uint64_t)(int64_t)((uint64_t)v2 * (uint64_t)v3)) % 32)] = (int64_t)((uint64_t)(42 % 5) - (uint64_t)(int64_t)((uint64_t)5 * (uint64_t)3));
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

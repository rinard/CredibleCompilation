#include <stdio.h>
#include <stdint.h>
int64_t A[32];
int64_t B[32];
int main() {
    int64_t v0 = 0, v1 = 0, v2 = 0, v3 = 0, v4 = 0, v5 = 0;
    int64_t b0 = 0, b1 = 0;
    v4 = 42;
    v0 = 100;
    v1 = -5;
    A[0] = 5;
    A[1] = 2;
    A[2] = -1;
    A[3] = 10;
    B[0] = 1;
    B[1] = 42;
    B[2] = 7;
    B[3] = 10;
    b0 = ((((v2 >= v0) ? 1 : 0) || b1) ? 1 : 0);
    b1 = ((((((v5 < 100) ? 1 : 0) || ((v3 != 0) ? 1 : 0)) ? 1 : 0) || ((v3 == v1) ? 1 : 0)) ? 1 : 0);
    B[(v5 % 32)] = A[((int64_t)((uint64_t)3 * (uint64_t)5) % 32)];
    if (b0) {
        A[(A[(v5 % 32)] % 32)] = (v3 % 2);
    } else {
        A[(v4 % 32)] = (v2 / 3);
    }
    while (v4 < 5) {
        while (v2 < 5) {
            while (v5 < 3) {
                v3 = v3;
                v5 = v5 + 1;
            }
            v2 = v2 + 1;
        }
        v4 = v4 + 1;
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

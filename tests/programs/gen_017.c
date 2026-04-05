#include <stdio.h>
#include <stdint.h>
int64_t A[32];
int64_t B[32];
int main() {
    int64_t v0 = 0, v1 = 0, v2 = 0, v3 = 0, v4 = 0, v5 = 0;
    int64_t b0 = 0, b1 = 0;
    v0 = -1;
    v2 = 10;
    v3 = -5;
    A[0] = 5;
    A[1] = 1;
    A[2] = 10;
    A[3] = 0;
    B[0] = 2;
    B[1] = -1;
    B[2] = 42;
    while (v2 < 2) {
        A[(v4 % 32)] = A[(v2 % 32)];
        v2 = v2 + 1;
    }
    v1 = -5;
    v4 = v2;
    b0 = ((v1 <= A[(v5 % 32)]) ? 1 : 0);
    B[((int64_t)((uint64_t)B[(-5 % 32)] * (uint64_t)v3) % 32)] = B[((int64_t)((uint64_t)0 * (uint64_t)v3) % 32)];
    v2 = (int64_t)((uint64_t)(int64_t)((uint64_t)v4 + (uint64_t)42) + (uint64_t)A[(v4 % 32)]);
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

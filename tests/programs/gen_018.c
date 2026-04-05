#include <stdio.h>
#include <stdint.h>
int64_t A[32];
int64_t B[32];
int main() {
    int64_t v0 = 0, v1 = 0, v2 = 0, v3 = 0, v4 = 0, v5 = 0;
    int64_t b0 = 0, b1 = 0;
    v0 = 7;
    v3 = 1;
    v5 = 100;
    A[0] = 0;
    A[1] = 3;
    B[0] = 42;
    B[1] = 100;
    B[2] = 100;
    B[3] = -1;
    v2 = (int64_t)((uint64_t)B[(-5 % 32)] - (uint64_t)(int64_t)((uint64_t)v0 * (uint64_t)v4));
    v5 = (int64_t)((uint64_t)(int64_t)((uint64_t)1 - (uint64_t)v2) * (uint64_t)1);
    b1 = (!((-5 <= v5) ? 1 : 0));
    A[(v1 % 32)] = (int64_t)((uint64_t)(int64_t)((uint64_t)3 - (uint64_t)v0) - (uint64_t)(int64_t)((uint64_t)100 + (uint64_t)-5));
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

#include <stdio.h>
#include <stdint.h>
int64_t A[32];
int64_t B[32];
int main() {
    int64_t v0 = 0, v1 = 0, v2 = 0, v3 = 0, v4 = 0, v5 = 0;
    int64_t b0 = 0, b1 = 0;
    v5 = 3;
    v4 = 42;
    v3 = 10;
    A[0] = 1;
    A[1] = 1;
    B[0] = 7;
    B[1] = 10;
    B[2] = 10;
    B[3] = 42;
    while (v0 < 2) {
        v5 = v0;
        v0 = v0 + 1;
    }
    v1 = (B[(42 % 32)] / 5);
    while (v4 < 2) {
        v4 = (int64_t)((uint64_t)v1 + (uint64_t)42);
        v4 = v4 + 1;
    }
    while (v0 < 3) {
        b1 = ((v3 != v1) ? 1 : 0);
        v0 = v0 + 1;
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

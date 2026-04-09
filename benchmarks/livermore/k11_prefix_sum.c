#include <stdio.h>
#include <time.h>
#include <stdint.h>

#define N     1024
#define NREPS 10000

int main(void) {
    int64_t x[N];

    for (int i = 0; i < N; i++) {
        x[i] = i;
    }

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (int rep = 0; rep < NREPS; rep++) {
        for (int i = 1; i < N; i++) {
            x[i] = x[i] + x[i - 1];
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("x[N-1] = %lld\n", (long long)x[N - 1]);
    return 0;
}

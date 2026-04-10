#include <stdio.h>
#include <time.h>
#include <stdint.h>
#include <stdlib.h>

#define N     1024
#define NREPS 10000

int main(void) {
    double vx[N];
    int64_t ix1[N];
    int64_t seed = 12345;

    for (int i = 0; i < N; i++) {
        seed = seed * 6364136223846793005LL + 1442695040888963407LL;
        vx[i] = (seed % 1000) * 0.001;
    }

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (int rep = 0; rep < NREPS; rep++) {
        int ng = 0;
        for (int i = 0; i < N; i++) {
            seed = seed * 6364136223846793005LL + 1442695040888963407LL;
            int64_t idx = seed % 512;
            if (idx < 0) idx = -idx;
            ix1[ng] = idx;
            ng++;
        }
        for (int i = 0; i < ng; i++) {
            int64_t idx = ix1[i];
            vx[idx] = vx[idx] + 1.0;
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("vx[0] = %f\n", vx[0]);
    return 0;
}

#include <stdio.h>
#include <time.h>

#define NW    64
#define NREPS 1000

int main(void) {
    double w[NW], b[NW * NW];

    for (int i = 0; i < NW * NW; i++) {
        b[i] = i * 0.0001;
    }

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (int rep = 0; rep < NREPS; rep++) {
        for (int i = 0; i < NW; i++) w[i] = 0.0;
        for (int i = 1; i < NW; i++) {
            w[i] = 0.01;
            for (int k = 0; k < i; k++) {
                w[i] = w[i] + b[k * NW + i] * w[i - k - 1];
            }
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("w[NW-1] = %f\n", w[NW - 1]);
    return 0;
}

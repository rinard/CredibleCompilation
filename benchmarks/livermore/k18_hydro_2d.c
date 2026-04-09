#include <stdio.h>
#include <time.h>

#define DIM   32
#define N     (DIM * DIM)
#define NREPS 10000

int main(void) {
    double za[N], zp[N], zr[N];

    for (int i = 0; i < N; i++) {
        zp[i] = i * 0.01;
        zr[i] = i * 0.005 + 0.5;
        za[i] = 0.0;
    }

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (int rep = 0; rep < NREPS; rep++) {
        for (int j = 1; j < DIM - 1; j++) {
            for (int k = 1; k < DIM - 1; k++) {
                int idx = j * DIM + k;
                za[idx] = (zp[idx + 1] - zp[idx - 1]) * zr[idx]
                        + (zp[idx + DIM] - zp[idx - DIM]) * zr[idx];
            }
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("za[DIM+1] = %f\n", za[DIM + 1]);
    return 0;
}

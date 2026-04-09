#include <stdio.h>
#include <time.h>

#define DIM   32
#define NREPS 1000

int main(void) {
    double a[DIM * DIM], b[DIM * DIM], c[DIM * DIM];

    for (int i = 0; i < DIM; i++) {
        for (int j = 0; j < DIM; j++) {
            a[i * DIM + j] = (i + j) * 0.01;
            b[i * DIM + j] = (i - j + DIM) * 0.01;
        }
    }

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (int rep = 0; rep < NREPS; rep++) {
        for (int i = 0; i < DIM; i++) {
            for (int j = 0; j < DIM; j++) {
                double s = 0.0;
                for (int k = 0; k < DIM; k++) {
                    s += a[i * DIM + k] * b[k * DIM + j];
                }
                c[i * DIM + j] = s;
            }
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("c[0] = %f\n", c[0]);
    return 0;
}

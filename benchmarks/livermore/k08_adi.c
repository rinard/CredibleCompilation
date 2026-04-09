#include <stdio.h>
#include <time.h>

#define DIM   32
#define N     (DIM * DIM)
#define NREPS 10000

int main(void) {
    double u[N], z[N];
    double r = 0.25;

    for (int i = 0; i < N; i++) {
        u[i] = i * 0.01;
        z[i] = i * 0.005 + 0.5;
    }

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (int rep = 0; rep < NREPS; rep++) {
        for (int j = 1; j < DIM - 1; j++) {
            for (int i = 1; i < DIM - 1; i++) {
                int idx = j * DIM + i;
                u[idx] = u[idx] + r * (z[idx + 1] + z[idx - 1] +
                         z[idx + DIM] + z[idx - DIM] - 4.0 * z[idx]);
            }
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("u[DIM+1] = %f\n", u[DIM + 1]);
    return 0;
}

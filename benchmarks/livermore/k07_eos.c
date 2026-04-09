#include <stdio.h>
#include <time.h>

#define N     1024
#define NREPS 10000

int main(void) {
    double x[N], y[N], z[N], u[N];
    double r = 0.5;

    for (int i = 0; i < N; i++) {
        y[i] = i * 0.01;
        z[i] = i * 0.02 + 1.0;
        u[i] = i * 0.003 + 0.5;
    }

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (int rep = 0; rep < NREPS; rep++) {
        for (int k = 0; k < N; k++) {
            x[k] = u[k] + r * (z[k] + r * y[k]);
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("x[0] = %f\n", x[0]);
    return 0;
}

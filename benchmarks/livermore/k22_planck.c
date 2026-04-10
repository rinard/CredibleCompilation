#include <stdio.h>
#include <math.h>
#include <time.h>

#define N     1024
#define NREPS 10000

int main(void) {
    double x[N], y[N];

    for (int i = 0; i < N; i++) {
        x[i] = i * 0.01 + 0.01;
    }

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (int rep = 0; rep < NREPS; rep++) {
        for (int k = 0; k < N; k++) {
            double expx = exp(x[k]);
            y[k] = x[k] / (expx - 1.0);
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("y[0] = %f\n", y[0]);
    return 0;
}

#include <stdio.h>
#include <time.h>

#define N     1001
#define NREPS 10000

int main(void) {
    double x[N], y[N];

    for (int i = 0; i < N; i++) {
        x[i] = i * 0.01 + 1.0;
        y[i] = i * 0.001;
    }

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (int rep = 0; rep < NREPS; rep++) {
        for (int k = 5; k < N; k += 5) {
            double xk = x[k];
            x[k - 4] = x[k - 4] - xk * y[k - 4];
            x[k - 3] = x[k - 3] - xk * y[k - 3];
            x[k - 2] = x[k - 2] - xk * y[k - 2];
            x[k - 1] = x[k - 1] - xk * y[k - 1];
            x[k]     = x[k]     - xk * y[k];
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("x[0] = %f\n", x[0]);
    return 0;
}

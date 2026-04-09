#include <stdio.h>
#include <time.h>

#define N     1024
#define NREPS 10000

int main(void) {
    double x[N], v[N], w[N];

    for (int i = 0; i < N; i++) {
        x[i] = i * 0.01;
        v[i] = i * 0.001 + 0.1;
        w[i] = i * 0.002 + 0.05;
    }

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (int rep = 0; rep < NREPS; rep++) {
        for (int k = 2; k < N; k++) {
            x[k] = x[k] - v[k] * x[k - 1] - w[k] * x[k - 2];
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("x[N-1] = %f\n", x[N - 1]);
    return 0;
}

#include <stdio.h>
#include <time.h>

#define N     1001
#define NREPS 10000

int main(void) {
    double x[N], y[N], z[N];

    for (int i = 0; i < N; i++) {
        x[i] = i * 0.01;
        y[i] = i * 0.02 + 1.0;
        z[i] = i * 0.003;
    }

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (int rep = 0; rep < NREPS; rep++) {
        for (int i = 1; i < N; i++) {
            x[i] = z[i] * (y[i] - x[i - 1]);
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("x[N-1] = %f\n", x[N - 1]);
    return 0;
}

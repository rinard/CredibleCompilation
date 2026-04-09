#include <stdio.h>
#include <time.h>

#define N     1024
#define NREPS 10000

int main(void) {
    double vy[N];
    double dt = 0.01;

    for (int i = 0; i < N; i++) {
        vy[i] = (i - 512) * 0.01;
    }

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (int rep = 0; rep < NREPS; rep++) {
        for (int k = 1; k < N; k++) {
            if (vy[k] < 0.0) {
                vy[k] = vy[k] - dt * vy[k - 1];
            }
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("vy[N-1] = %f\n", vy[N - 1]);
    return 0;
}

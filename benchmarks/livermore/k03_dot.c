#include <stdio.h>
#include <time.h>

#define N     1001
#define NREPS 10000

int main(void) {
    double x[N], z[N];

    for (int i = 0; i < N; i++) {
        x[i] = i * 0.001;
        z[i] = i * 0.002;
    }

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    double q = 0.0;
    for (int rep = 0; rep < NREPS; rep++) {
        q = 0.0;
        for (int i = 0; i < N; i++) {
            q += x[i] * z[i];
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("q = %f\n", q);
    return 0;
}

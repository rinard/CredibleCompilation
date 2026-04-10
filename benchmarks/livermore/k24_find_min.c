#include <stdio.h>
#include <time.h>
#include "signel.h"

#define N     1001
#define NREPS 10000

int main(void) {
    double x[N];

    signel(x, N);

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    int m = 0;
    double xm, xk;
    for (int rep = 0; rep < NREPS; rep++) {
        x[N/2] = -1.0e+10;
        m = 0;
        xm = x[0];
        for (int k = 1; k < N; k++) {
            xk = x[k];
            if (xk < xm) {
                m = k;
                xm = xk;
            }
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("m = %d\n", m);
    return 0;
}

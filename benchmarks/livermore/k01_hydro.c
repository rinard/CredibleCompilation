#include <stdio.h>
#include <time.h>
#include "signel.h"

#define N    1001
#define KMAX 1001
#define NREPS 10000

int main(void) {
    double x[1012], y[1012], z[1012];
    double spacer[39]; signel(spacer, 39);
    double q = spacer[27], r = spacer[29], t = spacer[35];

    signel(y, 1012);
    signel(z, 1012);

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (int rep = 0; rep < NREPS; rep++) {
        for (int k = 0; k < KMAX; k++) {
            x[k] = q + y[k] * (r * z[k + 10] + t * z[k + 11]);
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("x[0] = %f\n", x[0]);
    return 0;
}

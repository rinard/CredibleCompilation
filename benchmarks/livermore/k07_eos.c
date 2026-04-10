#include <stdio.h>
#include <time.h>
#include "signel.h"

/* K7 — Equation of state fragment
   Original Fortran: n=995, 3-level Horner with R, T, Q */

#define N     995
#define NREPS 10000

int main(void) {
    double x[1001], y[1001], z[1001], u[1001];
    double spacer[39]; signel(spacer, 39);
    double r = spacer[29], t = spacer[35], q = spacer[27];

    signel(y, 1001);
    signel(z, 1001);
    signel(u, 1001);

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (int rep = 0; rep < NREPS; rep++) {
        for (int k = 0; k < N; k++) {
            x[k] = u[k] + r*(z[k] + r*y[k]) +
                   t*(u[k+3] + r*(u[k+2] + r*u[k+1]) +
                      t*(u[k+6] + q*(u[k+5] + q*u[k+4])));
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("x[0] = %f\n", x[0]);
    return 0;
}

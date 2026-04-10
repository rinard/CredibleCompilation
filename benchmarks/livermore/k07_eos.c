#include <stdio.h>
#include <time.h>

/* K7 — Equation of state fragment
   Original Fortran: n=995, 3-level Horner with R, T, Q */

#define N     995
#define NREPS 10000

int main(void) {
    double x[1001], y[1001], z[1001], u[1001];
    double r = 0.5, t = 0.3, q = 0.2;

    for (int i = 0; i < 1001; i++) {
        y[i] = i * 0.01;
        z[i] = i * 0.02 + 1.0;
        u[i] = i * 0.003 + 0.5;
    }

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
    double elapsed = (t0.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("x[0] = %f\n", x[0]);
    return 0;
}

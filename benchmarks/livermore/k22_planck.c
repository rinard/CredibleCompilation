/* K22 — Planck (Exponential) Function
   Original Livermore Loop kernel 22.
   n=101, 5 arrays u,v,x,y,w. y[k]=u[k]/v[k], w[k]=x[k]/(exp(y[k])-1). */
#include <stdio.h>
#include <math.h>
#include <time.h>
#include "signel.h"

#define N     101
#define NREPS 10000

int main(void) {
    double u[N], v[N], x[N], y[N], w[N];

    signel(u, N);
    signel(v, N);
    signel(x, N);
    /* Ensure v[k] > 0 and u[k]/v[k] is moderate so exp doesn't overflow */
    for (int i = 0; i < N; i++) {
        if (v[i] <= 0.0) v[i] = 0.01;
        if (u[i] <= 0.0) u[i] = 0.01;
    }

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    double expmax = 20.0;
    for (int rep = 0; rep < NREPS; rep++) {
        u[N-1] = 0.99 * expmax * v[N-1];
        for (int k = 0; k < N; k++) {
            y[k] = u[k] / v[k];
            w[k] = x[k] / (exp(y[k]) - 1.0);
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("w[0] = %f\n", w[0]);
    return 0;
}

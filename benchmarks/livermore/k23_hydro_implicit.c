#include <stdio.h>
#include <time.h>
#include "signel.h"

/* Original K23: 2-D implicit hydrodynamics
   za[j][k] += 0.175*(qa - za[j][k])
   qa = za[j+1][k]*zr[j][k] + za[j-1][k]*zb[j][k]
      + za[j][k+1]*zu[j][k] + za[j][k-1]*zv[j][k] + zz[j][k]
   Arrays are [7][101], j=1..5, k=1..n-1 (n=101) */

#define NJ    7
#define NK    101
#define NTOT  (NJ * NK)
#define NREPS 100000

/* Flatten [j][k] as [j + k*NJ] (column-major matching Fortran) */
#define IDX(j,k) ((j) + (k) * NJ)

int main(void) {
    double za[NTOT], zr[NTOT], zb[NTOT], zu[NTOT], zv[NTOT], zz[NTOT];

    signel(za, NTOT);
    signel(zr, NTOT);
    signel(zb, NTOT);
    signel(zu, NTOT);
    signel(zv, NTOT);
    signel(zz, NTOT);
    /* Scale coefficients for stable relaxation: 0.175 * 4 * coeff < 1 */
    for (int i = 0; i < NTOT; i++) {
        zr[i] *= 0.1; zb[i] *= 0.1; zu[i] *= 0.1; zv[i] *= 0.1;
    }

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (int rep = 0; rep < NREPS; rep++) {
        for (int j = 1; j < 6; j++) {
            for (int k = 1; k < NK - 1; k++) {
                double qa = za[IDX(j+1,k)]*zr[IDX(j,k)] + za[IDX(j-1,k)]*zb[IDX(j,k)]
                          + za[IDX(j,k+1)]*zu[IDX(j,k)] + za[IDX(j,k-1)]*zv[IDX(j,k)] + zz[IDX(j,k)];
                za[IDX(j,k)] += 0.175 * (qa - za[IDX(j,k)]);
            }
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("za[0] = %f\n", za[IDX(1,1)]);
    return 0;
}

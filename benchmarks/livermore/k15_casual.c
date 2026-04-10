/* K15 -- Casual Fortran (Development version)
   Original Livermore Loop kernel 15.
   2D arrays: vy[25][101], vh,vf,vg,vs[7][101].
   ng=7, nz=101. Scalars: ar=0.053, br=0.073, r, s, t.
   Uses sqrt() as in original Fortran. */
#include <stdio.h>
#include <math.h>
#include <time.h>
#include "signel.h"

#define NZ    101
#define NG    7
#define VYROWS 25
#define NREPS 10000

int main(void) {
    double vy[VYROWS][NZ], vh[NG][NZ], vf[NG][NZ], vg[NG][NZ], vs[NG][NZ];

    /* Initialise arrays with signel */
    signel((double *)vh, NG * NZ);
    signel((double *)vf, NG * NZ);
    signel((double *)vg, NG * NZ);
    /* Ensure vf is positive (used as divisor) */
    for (int j = 0; j < NG; j++)
        for (int k = 0; k < NZ; k++)
            if (vf[j][k] <= 0.0) vf[j][k] = 0.001;
    for (int j = 0; j < NG; j++)
        for (int k = 0; k < NZ; k++)
            vs[j][k] = 0.0;
    /* Initialise vy with signel (not zeros) */
    signel((double *)vy, VYROWS * NZ);

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    double ar, br, r, s, t;
    for (int l = 0; l < NREPS; l++) {
        ar = 0.053; br = 0.073;
        for (int j = 1; j < NG; j++) {
            for (int k = 1; k < NZ; k++) {
                if ((j + 1) >= NG) {
                    vy[j][k] = 0.0;
                    continue;
                }
                if (vh[j+1][k] > vh[j][k]) t = ar; else t = br;
                if (vf[j][k] < vf[j][k-1]) {
                    if (vh[j][k-1] > vh[j+1][k-1]) r = vh[j][k-1]; else r = vh[j+1][k-1];
                    s = vf[j][k-1];
                } else {
                    if (vh[j][k] > vh[j+1][k]) r = vh[j][k]; else r = vh[j+1][k];
                    s = vf[j][k];
                }
                vy[j][k] = sqrt(vg[j][k]*vg[j][k] + r*r) * t / s;

                if ((k + 1) >= NZ) {
                    vs[j][k] = 0.0;
                    continue;
                }
                if (vf[j][k] < vf[j-1][k]) {
                    if (vg[j-1][k] > vg[j-1][k+1]) r = vg[j-1][k]; else r = vg[j-1][k+1];
                    s = vf[j-1][k]; t = br;
                } else {
                    if (vg[j][k] > vg[j][k+1]) r = vg[j][k]; else r = vg[j][k+1];
                    s = vf[j][k]; t = ar;
                }
                vs[j][k] = sqrt(vh[j][k]*vh[j][k] + r*r) * t / s;
            }
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("vy[3][50] = %f\n", vy[3][50]);
    return 0;
}

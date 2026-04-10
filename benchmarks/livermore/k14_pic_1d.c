#include <stdio.h>
#include <time.h>
#include "signel.h"

#define N     1001
#define NREPS 10000

int main(void) {
    double grd[1001], dex_arr[1001], xi[1001];
    double ex_arr[1001], ex1[1001], dex1[1001];
    double vx[1001], xx[1001], rx[1001];
    double rh[2049];
    long ix[1001], ir[1001];
    double spacer[39]; signel(spacer, 39);
    double flx = spacer[26];

    signel(grd, 1001);
    /* Scale grd to be valid grid indices (1..512) */
    for (int i = 0; i < 1001; i++) grd[i] = (i % 512) + 1.5;
    signel(ex_arr, 1001);
    signel(dex_arr, 1001);
    for (int i = 0; i < 2049; i++) rh[i] = 0.0;

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (int rep = 0; rep < NREPS; rep++) {
        for (int k = 0; k < N; k++) {
            vx[k] = 0.0;
            xx[k] = 0.0;
            ix[k] = (long)grd[k];
            xi[k] = (double)ix[k];
            ex1[k] = ex_arr[ix[k] - 1];
            dex1[k] = dex_arr[ix[k] - 1];
        }
        for (int k = 0; k < N; k++) {
            vx[k] = vx[k] + ex1[k] + (xx[k] - xi[k]) * dex1[k];
            xx[k] = xx[k] + vx[k] + flx;
            ir[k] = xx[k];
            rx[k] = xx[k] - ir[k];
            ir[k] = (ir[k] & (2048-1)) + 1;
            xx[k] = rx[k] + ir[k];
        }
        for (int k = 0; k < N; k++) {
            rh[ir[k]-1] += 1.0 - rx[k];
            rh[ir[k]] += rx[k];
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("rh[0] = %f\n", rh[0]);
    return 0;
}

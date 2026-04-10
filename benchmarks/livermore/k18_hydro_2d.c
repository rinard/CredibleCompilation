/* K18 — 2-D Explicit Hydrodynamics Fragment
   Original Livermore Loop kernel 18.
   Arrays: za,zp,zq,zr,zm,zb,zu,zv,zz are all [7][101].
   kn=6, jn=100. Scalars: t=0.0037, s=0.0041. */
#include <stdio.h>
#include <time.h>
#include "signel.h"

#define JN  100
#define KN  6
#define KD  7
#define JD  101
#define NREPS 10000

int main(void) {
    double za[KD][JD], zb[KD][JD], zp[KD][JD], zq[KD][JD];
    double zr[KD][JD], zm[KD][JD], zu[KD][JD], zv[KD][JD], zz[KD][JD];

    /* Initialise arrays with signel */
    signel((double *)zp, KD * JD);
    signel((double *)zq, KD * JD);
    signel((double *)zr, KD * JD);
    signel((double *)zm, KD * JD);
    /* Ensure zm is large enough to damp division */
    for (int k = 0; k < KD; k++)
        for (int j = 0; j < JD; j++)
            zm[k][j] += 10.0;
    signel((double *)zz, KD * JD);
    for (int k = 0; k < KD; k++)
        for (int j = 0; j < JD; j++) {
            zu[k][j] = 0.0;
            zv[k][j] = 0.0;
            za[k][j] = 0.0;
            zb[k][j] = 0.0;
        }

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    double t, s;
    for (int l = 0; l < NREPS; l++) {
        t = 0.0037; s = 0.0041;

        /* Phase 1: compute za, zb */
        for (int k = 1; k < KN; k++)
            for (int j = 1; j < JN; j++) {
                za[k][j] = (zp[k+1][j-1] + zq[k+1][j-1] - zp[k][j-1] - zq[k][j-1])
                          * (zr[k][j] + zr[k][j-1])
                          / (zm[k][j-1] + zm[k+1][j-1]);
                zb[k][j] = (zp[k][j-1] + zq[k][j-1] - zp[k][j] - zq[k][j])
                          * (zr[k][j] + zr[k-1][j])
                          / (zm[k][j] + zm[k][j-1]);
            }

        /* Phase 2: update zu, zv */
        for (int k = 1; k < KN; k++)
            for (int j = 1; j < JN; j++) {
                zu[k][j] += s * (za[k][j]   * (zz[k][j] - zz[k][j+1])
                               - za[k][j-1] * (zz[k][j] - zz[k][j-1])
                               - zb[k][j]   * (zz[k][j] - zz[k-1][j])
                               + zb[k+1][j] * (zz[k][j] - zz[k+1][j]));
                zv[k][j] += s * (za[k][j]   * (zr[k][j] - zr[k][j+1])
                               - za[k][j-1] * (zr[k][j] - zr[k][j-1])
                               - zb[k][j]   * (zr[k][j] - zr[k-1][j])
                               + zb[k+1][j] * (zr[k][j] - zr[k+1][j]));
            }

        /* Phase 3: update zr, zz */
        for (int k = 1; k < KN; k++)
            for (int j = 1; j < JN; j++) {
                zr[k][j] += t * zu[k][j];
                zz[k][j] += t * zv[k][j];
            }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("zr[3][50] = %f\n", zr[3][50]);
    return 0;
}

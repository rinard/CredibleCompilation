/* K18 — 2-D Explicit Hydrodynamics Fragment
   Original Livermore Loop kernel 18.
   Arrays: za,zp,zq,zr,zm,zb,zu,zv,zz are all [7][101].
   kn=6, jn=101. Scalars: t=0.0037, s=0.0041. */
#include <stdio.h>
#include <time.h>

#define JN  101
#define KN  6
#define KD  7
#define NREPS 10000

int main(void) {
    double za[KD][JN], zb[KD][JN], zp[KD][JN], zq[KD][JN];
    double zr[KD][JN], zm[KD][JN], zu[KD][JN], zv[KD][JN], zz[KD][JN];

    /* Initialise arrays with deterministic values */
    for (int k = 0; k < KD; k++)
        for (int j = 0; j < JN; j++) {
            zp[k][j] = (k + 1) * 0.01 + j * 0.001;
            zq[k][j] = (k + 1) * 0.005 + j * 0.0005;
            zr[k][j] = (k + 1) * 0.02 + j * 0.002 + 0.5;
            zm[k][j] = (k + 1) * 0.03 + j * 0.003 + 1.0;
            zz[k][j] = (k + 1) * 0.015 + j * 0.0015;
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
                zu[k][j] += s * (za[k][j]   * (zz[k][j] - zz[k][j+1 < JN ? j+1 : j])
                               - za[k][j-1] * (zz[k][j] - zz[k][j-1])
                               - zb[k][j]   * (zz[k][j] - zz[k-1][j])
                               + zb[k+1 < KD ? k+1 : k][j] * (zz[k][j] - zz[k+1 < KD ? k+1 : k][j]));
                zv[k][j] += s * (za[k][j]   * (zr[k][j] - zr[k][j+1 < JN ? j+1 : j])
                               - za[k][j-1] * (zr[k][j] - zr[k][j-1])
                               - zb[k][j]   * (zr[k][j] - zr[k-1][j])
                               + zb[k+1 < KD ? k+1 : k][j] * (zr[k][j] - zr[k+1 < KD ? k+1 : k][j]));
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

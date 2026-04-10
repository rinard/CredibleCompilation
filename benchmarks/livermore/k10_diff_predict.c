/* K10 — Difference Predictors
   Original Livermore Loop kernel 10.
   px[101][25], cx[101][25]. n=101. */
#include <stdio.h>
#include <time.h>
#include "signel.h"

#define N     101
#define NCOL  25
#define NREPS 10000

int main(void) {
    double px[N][NCOL], cx[N][NCOL];

    /* Initialise */
    signel((double *)px, N * NCOL);
    signel((double *)cx, N * NCOL);

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (int l = 0; l < NREPS; l++) {
        for (int i = 0; i < N; i++) {
            double ar, br, cr;
            ar       =      cx[i][4];
            br       = ar - px[i][4];
            px[i][4] = ar;
            cr       = br - px[i][5];
            px[i][5] = br;
            ar       = cr - px[i][6];
            px[i][6] = cr;
            br       = ar - px[i][7];
            px[i][7] = ar;
            cr       = br - px[i][8];
            px[i][8] = br;
            ar       = cr - px[i][9];
            px[i][9] = cr;
            br       = ar - px[i][10];
            px[i][10] = ar;
            cr       = br - px[i][11];
            px[i][11] = br;
            px[i][13] = cr - px[i][12];
            px[i][12] = cr;
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("px[50][4] = %f\n", px[50][4]);
    return 0;
}

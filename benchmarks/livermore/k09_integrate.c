/* K9 — Integrate Predictors
   Original Livermore Loop kernel 9.
   px is [101][25]. Scalars: dm22..dm28, c0. n=101. */
#include <stdio.h>
#include <time.h>

#define N     101
#define NCOL  25
#define NREPS 10000

int main(void) {
    double px[N][NCOL];
    double dm28 = 0.01, dm27 = 0.02, dm26 = 0.03, dm25 = 0.04;
    double dm24 = 0.05, dm23 = 0.06, dm22 = 0.07, c0 = 0.5;

    /* Initialise */
    for (int i = 0; i < N; i++)
        for (int j = 0; j < NCOL; j++)
            px[i][j] = (i + 1) * 0.01 + j * 0.001;

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (int l = 0; l < NREPS; l++) {
        for (int i = 0; i < N; i++) {
            px[i][0] = dm28*px[i][12] + dm27*px[i][11] + dm26*px[i][10]
                     + dm25*px[i][9]  + dm24*px[i][8]  + dm23*px[i][7]
                     + dm22*px[i][6]  + c0*(px[i][4] + px[i][5]) + px[i][2];
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("px[50][0] = %f\n", px[50][0]);
    return 0;
}

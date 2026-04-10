/* K8 — ADI Integration (Alternating Direction Implicit)
   Original Livermore Loop kernel 8.
   u1,u2,u3 are [2][101][5], du1,du2,du3 are [101].
   ky range 1..n-1 (1..100), kx range 1..2. */
#include <stdio.h>
#include <time.h>
#include "signel.h"

#define NDIM  101
#define N     100
#define KXD   5
#define NREPS 10000

int main(void) {
    double u1[2][NDIM][KXD], u2[2][NDIM][KXD], u3[2][NDIM][KXD];
    double du1[NDIM], du2[NDIM], du3[NDIM];
    double spacer[39]; signel(spacer, 39);
    double a11 = spacer[0], a12 = spacer[1], a13 = spacer[2];
    double a21 = spacer[3], a22 = spacer[4], a23 = spacer[5];
    double a31 = spacer[6], a32 = spacer[7], a33 = spacer[8];
    double sig = spacer[33];
    int nl1, nl2;

    /* Initialise */
    signel((double *)u1, 2 * NDIM * KXD);
    signel((double *)u2, 2 * NDIM * KXD);
    signel((double *)u3, 2 * NDIM * KXD);
    signel(du1, NDIM);
    signel(du2, NDIM);
    signel(du3, NDIM);

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (int l = 0; l < NREPS; l++) {
        nl1 = 0; nl2 = 1;
        for (int kx = 1; kx < 3; kx++) {
            for (int ky = 1; ky < N - 1; ky++) {
                du1[ky] = u1[nl1][ky+1][kx] - u1[nl1][ky-1][kx];
                du2[ky] = u2[nl1][ky+1][kx] - u2[nl1][ky-1][kx];
                du3[ky] = u3[nl1][ky+1][kx] - u3[nl1][ky-1][kx];
                u1[nl2][ky][kx] = u1[nl1][ky][kx]
                    + a11*du1[ky] + a12*du2[ky] + a13*du3[ky]
                    + sig*(u1[nl1][ky][kx+1] - 2.0*u1[nl1][ky][kx] + u1[nl1][ky][kx-1]);
                u2[nl2][ky][kx] = u2[nl1][ky][kx]
                    + a21*du1[ky] + a22*du2[ky] + a23*du3[ky]
                    + sig*(u2[nl1][ky][kx+1] - 2.0*u2[nl1][ky][kx] + u2[nl1][ky][kx-1]);
                u3[nl2][ky][kx] = u3[nl1][ky][kx]
                    + a31*du1[ky] + a32*du2[ky] + a33*du3[ky]
                    + sig*(u3[nl1][ky][kx+1] - 2.0*u3[nl1][ky][kx] + u3[nl1][ky][kx-1]);
            }
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("u1[1][50][1] = %f\n", u1[1][50][1]);
    return 0;
}

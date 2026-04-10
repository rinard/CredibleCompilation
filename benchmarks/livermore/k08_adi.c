/* K8 — ADI Integration (Alternating Direction Implicit)
   Original Livermore Loop kernel 8.
   u1,u2,u3 are [2][101][5], du1,du2,du3 are [101].
   ky range 1..n-1 (1..100), kx range 1..2. */
#include <stdio.h>
#include <time.h>

#define N     101
#define KXD   5
#define NREPS 10000

int main(void) {
    double u1[2][N][KXD], u2[2][N][KXD], u3[2][N][KXD];
    double du1[N], du2[N], du3[N];
    double a11 = 0.1, a12 = 0.2, a13 = 0.3;
    double a21 = 0.05, a22 = 0.15, a23 = 0.25;
    double a31 = 0.02, a32 = 0.12, a33 = 0.22;
    double sig = 0.5;
    int nl1, nl2;

    /* Initialise */
    for (int nl = 0; nl < 2; nl++)
        for (int ky = 0; ky < N; ky++)
            for (int kx = 0; kx < KXD; kx++) {
                u1[nl][ky][kx] = (nl + 1) * 0.01 * ky + 0.001 * kx;
                u2[nl][ky][kx] = (nl + 1) * 0.02 * ky + 0.002 * kx;
                u3[nl][ky][kx] = (nl + 1) * 0.03 * ky + 0.003 * kx;
            }
    for (int ky = 0; ky < N; ky++) {
        du1[ky] = 0.0;
        du2[ky] = 0.0;
        du3[ky] = 0.0;
    }

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (int l = 0; l < NREPS; l++) {
        nl1 = 0; nl2 = 1;
        for (int kx = 1; kx < 3; kx++) {
            for (int ky = 1; ky < N; ky++) {
                du1[ky] = u1[nl1][ky+1 < N ? ky+1 : ky][kx] - u1[nl1][ky-1][kx];
                du2[ky] = u2[nl1][ky+1 < N ? ky+1 : ky][kx] - u2[nl1][ky-1][kx];
                du3[ky] = u3[nl1][ky+1 < N ? ky+1 : ky][kx] - u3[nl1][ky-1][kx];
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

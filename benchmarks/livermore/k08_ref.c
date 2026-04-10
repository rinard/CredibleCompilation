/* K8 — ADI integration (Livermore Loop 8) — netlib reference */
#include <stdio.h>
#include <time.h>

static double u1[2][101][5], u2[2][101][5], u3[2][101][5];
static double du1[101], du2[101], du3[101];

int main(void) {
    int kx, ky, nl1, nl2, n = 100, rep;
    double a11 = 0.1, a12 = 0.2, a13 = 0.3;
    double a21 = 0.1, a22 = 0.2, a23 = 0.3;
    double a31 = 0.1, a32 = 0.2, a33 = 0.3;
    double sig = 0.05;

    for (int p = 0; p < 2; p++)
        for (int i = 0; i < 101; i++)
            for (int j = 0; j < 5; j++) {
                u1[p][i][j] = (p * 101 * 5 + i * 5 + j) * 0.001;
                u2[p][i][j] = (p * 101 * 5 + i * 5 + j) * 0.001 + 0.1;
                u3[p][i][j] = (p * 101 * 5 + i * 5 + j) * 0.001 + 0.2;
            }

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (rep = 0; rep < 10000; rep++) {
        nl1 = 0; nl2 = 1;
        for (kx = 1; kx < 3; kx++) {
            for (ky = 1; ky < n - 1; ky++) {
                du1[ky] = u1[nl1][ky + 1][kx] - u1[nl1][ky - 1][kx];
                du2[ky] = u2[nl1][ky + 1][kx] - u2[nl1][ky - 1][kx];
                du3[ky] = u3[nl1][ky + 1][kx] - u3[nl1][ky - 1][kx];
                u1[nl2][ky][kx] = u1[nl1][ky][kx] + a11 * du1[ky] + a12 * du2[ky] + a13 * du3[ky]
                    + sig * (u1[nl1][ky][kx + 1] - 2.0 * u1[nl1][ky][kx] + u1[nl1][ky][kx - 1]);
                u2[nl2][ky][kx] = u2[nl1][ky][kx] + a21 * du1[ky] + a22 * du2[ky] + a23 * du3[ky]
                    + sig * (u2[nl1][ky][kx + 1] - 2.0 * u2[nl1][ky][kx] + u2[nl1][ky][kx - 1]);
                u3[nl2][ky][kx] = u3[nl1][ky][kx] + a31 * du1[ky] + a32 * du2[ky] + a33 * du3[ky]
                    + sig * (u3[nl1][ky][kx + 1] - 2.0 * u3[nl1][ky][kx] + u3[nl1][ky][kx - 1]);
            }
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("K8 ADI: u1[1][50][1] = %.15e\n", u1[1][50][1]);
    printf("Time: %.6f s\n", elapsed);
    return 0;
}

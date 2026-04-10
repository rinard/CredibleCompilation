/* K16 — Monte Carlo Search
   Original Livermore Loop kernel 16.
   Simplified translation of the goto/break/continue zone traversal.
   Arrays: d[300], plan[300], zone[300] (integer).
   n=100, ii=n/3, lb=ii+ii. Scalars: r,s,t,tmp. */
#include <stdio.h>
#include <time.h>
#include <stdint.h>
#include "signel.h"

#define N     100
#define NREPS 100

int main(void) {
    double d[300], plan[300];
    int zone[300];
    int ii = N / 3;
    int lb = ii + ii;
    double spacer[39]; signel(spacer, 39);
    double r = spacer[29], s = spacer[31], t = spacer[35];

    /* Initialise arrays */
    signel(d, 300);
    signel(plan, 300);
    for (int i = 0; i < 300; i++)
        zone[i] = i % (N + 1);
    zone[0] = 5;  /* max m value */

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    int k2, k3, m, i1, j2, j4, j5;
    double tmp;
    for (int l = 0; l < NREPS; l++) {
        i1 = 1; m = 1; k2 = 0; k3 = 0;
        int done = 0;
        while (!done) {
            j2 = (N + N) * (m - 1) + 1;
            int brk = 0;
            for (int k = 1; k <= N && !brk; k++) {
                k2++;
                j4 = j2 + k + k;
                /* Clamp j4 indices to array bounds */
                int j4m1 = (j4 - 1) % 300; if (j4m1 < 0) j4m1 += 300;
                int j4m2 = (j4 - 2) % 300; if (j4m2 < 0) j4m2 += 300;
                j5 = zone[j4m1];
                if (j5 < 0) j5 = -j5;
                if (j5 >= 300) j5 = j5 % 300;

                if (j5 < N) {
                    if (j5 + lb < N)      tmp = plan[j5] - t;
                    else if (j5 + ii < N) tmp = plan[j5] - s;
                    else                   tmp = plan[j5] - r;
                } else if (j5 == N) {
                    brk = 1;
                    continue;
                } else {
                    k3++;
                    int j5m2 = (j5 - 2) % 300; if (j5m2 < 0) j5m2 += 300;
                    int j5m3 = (j5 - 3) % 300; if (j5m3 < 0) j5m3 += 300;
                    int j5m4 = (j5 - 4) % 300; if (j5m4 < 0) j5m4 += 300;
                    int j5m5 = (j5 - 5) % 300; if (j5m5 < 0) j5m5 += 300;
                    int j5m1 = (j5 - 1) % 300; if (j5m1 < 0) j5m1 += 300;
                    tmp = d[j5m1] - (d[j5m2] * (t - d[j5m3]) * (t - d[j5m3])
                          + (s - d[j5m4]) * (s - d[j5m4])
                          + (r - d[j5m5]) * (r - d[j5m5]));
                }

                int zval = zone[j4m2];
                if (tmp < 0.0) {
                    if (zval < 0) { /* continue */ }
                    else if (zval == 0) { brk = 1; continue; }
                    else { /* fall through to m update */ }
                } else if (tmp > 0.0) {
                    if (zval > 0) { /* continue */ }
                    else if (zval == 0) { brk = 1; continue; }
                    else { /* fall through to m update */ }
                } else {
                    brk = 1; continue;
                }

                /* Only reach here when we need to update m and restart */
                if (tmp < 0.0 && zval < 0) continue;
                if (tmp > 0.0 && zval > 0) continue;

                m++;
                if (m > zone[0]) m = 1;
                if (i1 != m) {
                    brk = 1;  /* restart outer while */
                } else {
                    brk = 1;
                }
            }
            if (!brk || i1 == m) done = 1;
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("k2 = %d, k3 = %d\n", k2, k3);
    return 0;
}

/* K16 -- Monte Carlo Search
   Original Livermore Loop kernel 16.
   Arrays: d[300], plan[300], zone[300] (integer).
   n=75, NREPS=10000. Uses direct array indices with bounds-check breaks. */
#include <stdio.h>
#include <time.h>
#include <stdint.h>
#include "signel.h"

#define N     75
#define NREPS 10000

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
    for (int rep = 0; rep < NREPS; rep++) {
        ii = N / 3; lb = ii + ii; k2 = 0; k3 = 0;
        i1 = m = 1;
label410:
        j2 = (N + N) * (m - 1) + 1;
        for (int k = 1; k <= N; k++) {
            k2++;
            j4 = j2 + k + k;
            if (j4-1 < 0 || j4-1 >= 300) break;
            j5 = zone[j4-1];
            if (j5 < N) {
                if (j5 < 1) break;
                if (j5+lb < N) tmp = plan[j5-1] - t;
                else if (j5+ii < N) tmp = plan[j5-1] - s;
                else tmp = plan[j5-1] - r;
            } else if (j5 == N) {
                break;
            } else {
                if (j5-1 < 0 || j5-1 >= 300 || j5-5 < 0) break;
                k3++;
                tmp = d[j5-1] - (d[j5-2]*(t-d[j5-3])*(t-d[j5-3])
                      + (s-d[j5-4])*(s-d[j5-4])
                      + (r-d[j5-5])*(r-d[j5-5]));
            }
            if (tmp < 0.0) {
                if (j4-2 < 0 || j4-2 >= 300) break;
                if (zone[j4-2] < 0) continue;
                else if (!zone[j4-2]) break;
            } else if (tmp > 0.0) {
                if (j4-2 < 0 || j4-2 >= 300) break;
                if (zone[j4-2] > 0) continue;
                else if (!zone[j4-2]) break;
            } else {
                break;
            }
            m++;
            if (m > zone[0]) m = 1;
            if (i1 != m) goto label410;
            else break;
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("k2 = %d, k3 = %d\n", k2, k3);
    return 0;
}

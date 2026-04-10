#include <stdio.h>
#include <time.h>
#include "signel.h"

/* K2 — ICCG excerpt (Incomplete Cholesky - Conjugate Gradient)
   Original Fortran: n=101, halving do-while with stride-2 inner loop */

#define N     101
#define NREPS 10000

int main(void) {
    double x[1001], v[1001];

    signel(x, 1001);
    signel(v, 1001);

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (int rep = 0; rep < NREPS; rep++) {
        int ii = N;
        int ipntp = 0;
        do {
            int ipnt = ipntp;
            ipntp += ii;
            ii /= 2;
            int i = ipntp;
            for (int k = ipnt + 1; k < ipntp; k += 2) {
                i++;
                x[i] = x[k] - v[k] * x[k-1] - v[k+1] * x[k+1];
            }
        } while (ii > 1);
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("x[0] = %f\n", x[0]);
    return 0;
}

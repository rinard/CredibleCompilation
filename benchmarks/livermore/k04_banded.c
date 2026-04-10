#include <stdio.h>
#include <time.h>
#include "signel.h"

#define N     1001
#define NREPS 10000

int main(void) {
    double x[N], y[N];

    signel(x, N);
    signel(y, N);

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (int rep = 0; rep < NREPS; rep++) {
        signel(x, N);
        int m = (N - 7) / 2;
        for (int k = 6; k < N; k = k + m) {
            int lw = k - 6;
            double temp = x[k - 1];
            for (int j = 4; j < N; j = j + 5) {
                temp -= x[lw] * y[j];
                lw++;
            }
            x[k - 1] = y[4] * temp;
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("x[0] = %f\n", x[0]);
    return 0;
}

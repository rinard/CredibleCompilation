#include <stdio.h>
#include <time.h>
#include "signel.h"

#define N     1001
#define NREPS 10000

int main(void) {
    double sa[N], b[N];
    double spacer[39]; signel(spacer, 39);
    double stb5 = spacer[34];

    signel(sa, N);

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (int rep = 0; rep < NREPS; rep++) {
        b[0] = sa[0];
        for (int k = 1; k < N; k++) {
            b[k] = sa[k] + stb5 * b[k - 1];
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("b[N-1] = %f\n", b[N - 1]);
    return 0;
}

/* K19 — General Linear Recurrence Equations
   Original Livermore Loop kernel 19.
   n=101, arrays b5[101], sa[101], sb[101].
   Forward pass k=0..n-1, then backward pass k=n-1..0. */
#include <stdio.h>
#include <time.h>
#include "signel.h"

#define N     101
#define NREPS 10000

int main(void) {
    double b5[N], sa[N], sb[N];

    signel(sa, N);
    signel(sb, N);

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    int kb5i = 0;
    for (int rep = 0; rep < NREPS; rep++) {
        double stb5 = 0.5;
        kb5i = 0;
        for (int k = 0; k < N; k++) {
            b5[k + kb5i] = sa[k] + stb5 * sb[k];
            stb5 = b5[k + kb5i] - stb5;
        }
        for (int i = 1; i <= N; i++) {
            int k = N - i;
            b5[k + kb5i] = sa[k] + stb5 * sb[k];
            stb5 = b5[k + kb5i] - stb5;
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("b5[N-1] = %f\n", b5[N - 1]);
    return 0;
}

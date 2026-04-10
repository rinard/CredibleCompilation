/* K1 — Hydro fragment (Livermore Loop 1) — netlib reference */
#include <stdio.h>
#include <time.h>

static double x[1001], y[1001], z[1012];

int main(void) {
    int k, n = 1001, rep;
    double q = 0.5, r = 0.1, t = 0.2;

    for (int i = 0; i < 1012; i++) {
        if (i < 1001) { y[i] = i * 0.001 + 0.5; x[i] = 0.0; }
        z[i] = i * 0.001 + 0.3;
    }

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (rep = 0; rep < 10000; rep++) {
        for (k = 0; k < n; k++) {
            x[k] = q + y[k] * (r * z[k + 10] + t * z[k + 11]);
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("K1 hydro: x[0] = %.15e\n", x[0]);
    printf("Time: %.6f s\n", elapsed);
    return 0;
}

/* K5 — Tri-diagonal elimination (Livermore Loop 5) — netlib reference */
#include <stdio.h>
#include <time.h>

static double x[1001], y[1001], z[1001];

int main(void) {
    int i, n = 1001, rep;

    for (int j = 0; j < 1001; j++) {
        x[j] = j * 0.001 + 0.5;
        y[j] = j * 0.001 + 0.3;
        z[j] = j * 0.001 + 0.1;
    }

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (rep = 0; rep < 10000; rep++) {
        /* reset x each rep */
        for (int j = 0; j < 1001; j++)
            x[j] = j * 0.001 + 0.5;

        for (i = 1; i < n; i++) {
            x[i] = z[i] * (y[i] - x[i - 1]);
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("K5 tridiag: x[500] = %.15e\n", x[500]);
    printf("Time: %.6f s\n", elapsed);
    return 0;
}

/* K20 — Discrete ordinates transport (Livermore Loop 20) — netlib reference */
#include <stdio.h>
#include <time.h>

static double x[1001], y[1001], z[1001], w[1001], v[1001];
static double u[1001], g[1001], xx[1001], vx[1001];

int main(void) {
    int k, n = 1000, rep;
    double di, dk, dn, s, t;

    for (int i = 0; i < 1001; i++) {
        x[i]  = i * 0.001 + 0.5;
        y[i]  = i * 0.001 + 0.5;
        z[i]  = i * 0.001 + 0.5;
        w[i]  = i * 0.001 + 0.5;
        v[i]  = i * 0.001 + 0.5;
        u[i]  = i * 0.001 + 0.5;
        g[i]  = i * 0.001 + 0.1;  /* keep g small so di is well-behaved */
        xx[i] = i * 0.001 + 1.0;  /* ensure xx[k]+dk nonzero */
        vx[i] = i * 0.001 + 2.0;  /* ensure vx[k]+v[k]*dn nonzero */
    }
    dk = 1.5; s = 0.001; t = 100.0;

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (rep = 0; rep < 10000; rep++) {
        /* re-init xx to avoid drift */
        for (int i = 0; i < 1001; i++)
            xx[i] = i * 0.001 + 1.0;

        for (k = 0; k < n; k++) {
            di = y[k] - g[k]/(xx[k] + dk);
            dn = 0.2;
            if (di) {
                dn = z[k]/di;
                if (t < dn) dn = t;
                if (s > dn) dn = s;
            }
            x[k] = ((w[k] + v[k]*dn)*xx[k] + u[k])/(vx[k] + v[k]*dn);
            xx[k+1] = (x[k] - xx[k])*dn + xx[k];
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("K20 discrete ord: x[0] = %.15e\n", x[0]);
    printf("Time: %.6f s\n", elapsed);
    return 0;
}

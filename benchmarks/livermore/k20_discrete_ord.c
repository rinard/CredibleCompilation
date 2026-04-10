/* K20 — Discrete Ordinates Transport
   Original Livermore Loop kernel 20.
   n=1000, arrays of size 1001. Re-initialises xx each rep.
   Uses if(di) nonzero check, updates xx[k+1]. */
#include <stdio.h>
#include <time.h>
#include "signel.h"

#define N     1000
#define NREPS 10000

int main(void) {
    double y[N], g[N], xx[N+1], z[N];
    double w[N], v[N], u[N], vx[N], x[N];
    double spacer[39]; signel(spacer, 39);
    double dk = spacer[14], s = spacer[31], t = spacer[35];

    signel(y, N);
    signel(g, N);
    signel(z, N);
    signel(w, N);
    signel(v, N);
    signel(u, N);
    signel(vx, N);
    /* Ensure vx[k]+v[k]*dn is nonzero */
    for (int i = 0; i < N; i++)
        vx[i] += 2.0;

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (int rep = 0; rep < NREPS; rep++) {
        /* Re-initialise xx each rep */
        signel(xx, N+1);
        for (int i = 0; i < N+1; i++) xx[i] += 1.0;

        for (int k = 0; k < N; k++) {
            double di = y[k] - g[k] / (xx[k] + dk);
            double dn = 0.2;
            if (di) {
                dn = z[k] / di;
                if (t < dn) dn = t;
                if (s > dn) dn = s;
            }
            x[k] = ((w[k] + v[k] * dn) * xx[k] + u[k]) / (vx[k] + v[k] * dn);
            xx[k+1] = (x[k] - xx[k]) * dn + xx[k];
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("x[0] = %f\n", x[0]);
    return 0;
}

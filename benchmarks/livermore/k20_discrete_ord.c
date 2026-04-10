#include <stdio.h>
#include <time.h>
#include "signel.h"

#define N     1001
#define NREPS 10000

int main(void) {
    double y[N], g[N], xx[N], z[N];
    double w[N], v[N], u[N], vv[N], x[N];
    double spacer[39]; signel(spacer, 39);
    double dk = spacer[14], s = spacer[31], t = spacer[35];

    signel(y, N);
    signel(g, N);
    signel(xx, N);
    signel(z, N);
    signel(w, N);
    signel(v, N);
    signel(u, N);
    signel(vv, N);
    /* Ensure xx[k]+dk and vv[k]+v[k]*dn are nonzero */
    for (int i = 0; i < N; i++) {
        xx[i] += 1.0;
        vv[i] += 2.0;
    }

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (int rep = 0; rep < NREPS; rep++) {
        for (int k = 0; k < N - 1; k++) {
            double di = y[k] - g[k] / (xx[k] + dk);
            double dn = 0.0;
            if (di < -0.0001 || di > 0.0001) {
                dn = z[k] / di;
                if (dn > t) dn = t;
                if (dn < s) dn = s;
            }
            x[k] = ((w[k] + v[k] * dn) * xx[k] + u[k]) / (vv[k] + v[k] * dn);
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("x[0] = %f\n", x[0]);
    return 0;
}

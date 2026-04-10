#include <stdio.h>
#include <time.h>

#define N     1001
#define NREPS 10000

int main(void) {
    double y[N], g[N], xx[N], z[N];
    double w[N], v[N], u[N], vv[N], x[N];
    double dk = 1.5, s = 0.001, t = 100.0;

    for (int i = 0; i < N; i++) {
        y[i]  = i * 0.01 + 1.0;
        g[i]  = i * 0.005;
        xx[i] = i * 0.02 + 0.5;
        z[i]  = i * 0.003;
        w[i]  = i * 0.001 + 0.1;
        v[i]  = i * 0.004;
        u[i]  = i * 0.002 + 0.3;
        vv[i] = i * 0.006 + 1.0;
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

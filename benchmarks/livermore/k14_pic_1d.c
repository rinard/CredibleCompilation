#include <stdio.h>
#include <time.h>

#define N     1024
#define NREPS 10000

int main(void) {
    double rx[N], vx[N], ex[N], dex[N];
    double flx = 0.001;

    for (int i = 0; i < N; i++) {
        rx[i]  = i * 0.5 + 0.5;
        vx[i]  = 0.0;
        ex[i]  = i * 0.001;
        dex[i] = i * 0.0005;
    }

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (int rep = 0; rep < NREPS; rep++) {
        for (int k = 0; k < 512; k++) {
            int ix = (int)rx[k];
            double xi = (double)ix;
            vx[k] = vx[k] + ex[ix] + (rx[k] - xi) * dex[ix];
            rx[k] = rx[k] + vx[k] + flx;
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("vx[0] = %f\n", vx[0]);
    return 0;
}

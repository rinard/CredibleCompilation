#include <stdio.h>
#include <time.h>

#define NPART 512
#define NGRID 1024   /* 32 x 32 flattened */
#define NREPS 10000

int main(void) {
    double px[NPART], py[NPART], vx[NPART], vy[NPART];
    double E[NGRID];
    double dt = 0.01;

    for (int i = 0; i < NPART; i++) {
        px[i] = (i % 32) + 0.5;
        py[i] = (i / 32) + 0.5;
        vx[i] = 0.001;
        vy[i] = 0.001;
    }

    for (int i = 0; i < NGRID; i++) {
        E[i] = i * 0.0001;
    }

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (int rep = 0; rep < NREPS; rep++) {
        for (int k = 0; k < NPART; k++) {
            int ix = (int)px[k];
            int iy = (int)py[k];
            int idx = ix * 32 + iy;
            double ex_val = E[idx];
            vx[k] = vx[k] + ex_val * dt;
            vy[k] = vy[k] + ex_val * dt;
            px[k] = px[k] + vx[k] * dt;
            py[k] = py[k] + vy[k] * dt;
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("vx[0] = %f\n", vx[0]);
    return 0;
}

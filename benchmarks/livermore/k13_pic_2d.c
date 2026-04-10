#include <stdio.h>
#include <time.h>

#define NPART 512
#define NGRID 64
#define NREPS 10000

int main(void) {
    double p_x[NPART], p_y[NPART], p_vx[NPART], p_vy[NPART];
    double b[NGRID*NGRID], c[NGRID*NGRID], h[NGRID*NGRID];
    double y[1001], z[1001];
    long e[96], f[96];

    for (int i = 0; i < NPART; i++) {
        p_x[i] = (i % NGRID) + 0.5;
        p_y[i] = (i / NGRID) + 0.5;
        p_vx[i] = 0.001;
        p_vy[i] = 0.001;
    }
    for (int i = 0; i < NGRID*NGRID; i++) {
        b[i] = i * 0.0001;
        c[i] = i * 0.00005;
        h[i] = 0.0;
    }
    for (int i = 0; i < 1001; i++) { y[i] = 0.001; z[i] = 0.001; }
    for (int i = 0; i < 96; i++) { e[i] = i % NGRID; f[i] = i % NGRID; }

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (int rep = 0; rep < NREPS; rep++) {
        for (int ip = 0; ip < NPART; ip++) {
            int i1 = (int)p_x[ip] & (NGRID-1);
            int j1 = (int)p_y[ip] & (NGRID-1);
            p_vx[ip] += b[j1*NGRID + i1];
            p_vy[ip] += c[j1*NGRID + i1];
            p_x[ip] += p_vx[ip];
            p_y[ip] += p_vy[ip];
            int i2 = ((int)p_x[ip] & (NGRID-1)) - 1;
            int j2 = ((int)p_y[ip] & (NGRID-1)) - 1;
            p_x[ip] += y[i2+32];
            p_y[ip] += z[j2+32];
            i2 += e[i2+32];
            j2 += f[j2+32];
            h[j2*NGRID + i2] += 1.0;
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("p_vx[0] = %f\n", p_vx[0]);
    return 0;
}

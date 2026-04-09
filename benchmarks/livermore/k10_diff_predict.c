#include <stdio.h>
#include <time.h>

#define N     1024
#define NREPS 10000

int main(void) {
    double cx0[N], cx1[N], cx2[N], cx3[N], cx4[N];
    double t = 0.037;

    for (int i = 0; i < N; i++) {
        cx0[i] = i * 0.01;
        cx1[i] = i * 0.005;
        cx2[i] = i * 0.003;
        cx3[i] = i * 0.002;
        cx4[i] = i * 0.001;
    }

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (int rep = 0; rep < NREPS; rep++) {
        for (int i = 0; i < N; i++) {
            double ar = cx4[i];
            double cr = t * ar + cx3[i];
            ar = t * cr + cx2[i];
            cr = t * ar + cx1[i];
            ar = t * cr + cx0[i];
            cx0[i] = ar;
            cx1[i] = cr;
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("cx0[0] = %f\n", cx0[0]);
    return 0;
}

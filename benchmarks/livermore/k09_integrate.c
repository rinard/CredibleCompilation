#include <stdio.h>
#include <time.h>

#define N     1024
#define NREPS 10000

int main(void) {
    double px[N], cx1[N], cx2[N], cx3[N];
    double c0 = 0.5, c1 = 0.25, c2 = 0.125, c3 = 0.0625;

    for (int i = 0; i < N; i++) {
        px[i]  = i * 0.01;
        cx1[i] = i * 0.005;
        cx2[i] = i * 0.003;
        cx3[i] = i * 0.001;
    }

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (int rep = 0; rep < NREPS; rep++) {
        for (int i = 0; i < N; i++) {
            px[i] = c0 * px[i] + c1 * cx1[i] + c2 * cx2[i] + c3 * cx3[i];
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("px[0] = %f\n", px[0]);
    return 0;
}

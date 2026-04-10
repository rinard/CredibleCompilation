#include <stdio.h>
#include <time.h>

/* Original K21: px[j][i] += vy[k][i] * cx[j][k]
   px[101][25], vy[25][101], cx[101][25]
   Loop order: k=0..24, i=0..24, j=0..n-1 (n=101) */

#define NJ    101
#define NK    25
#define NREPS 1000

int main(void) {
    double px[NJ * NK], vy[NK * NJ], cx[NJ * NK];

    for (int i = 0; i < NJ; i++) {
        for (int j = 0; j < NK; j++) {
            px[i * NK + j] = (i + j) * 0.01;
            cx[i * NK + j] = (i - j + NK) * 0.01;
        }
    }
    for (int i = 0; i < NK; i++) {
        for (int j = 0; j < NJ; j++) {
            vy[i * NJ + j] = (i * j % 50) * 0.002;
        }
    }

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (int rep = 0; rep < NREPS; rep++) {
        for (int k = 0; k < NK; k++) {
            for (int i = 0; i < NK; i++) {
                for (int j = 0; j < NJ; j++) {
                    px[j * NK + i] += vy[k * NJ + i] * cx[j * NK + k];
                }
            }
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("px[0] = %f\n", px[0]);
    return 0;
}

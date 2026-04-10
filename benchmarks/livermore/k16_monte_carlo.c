#include <stdio.h>
#include <time.h>
#include <stdint.h>
#include <stdlib.h>

#define N     1024
#define NTALLY 64
#define NREPS 10000

int main(void) {
    double d[N], weight[N], tally[NTALLY];
    int64_t seed = 67890;

    for (int i = 0; i < N; i++) {
        seed = seed * 6364136223846793005LL + 1442695040888963407LL;
        d[i] = (seed % 500 + 250) * 0.001;
        seed = seed * 6364136223846793005LL + 1442695040888963407LL;
        weight[i] = (seed % 100 + 1) * 0.01;
    }

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    for (int rep = 0; rep < NREPS; rep++) {
        for (int i = 0; i < NTALLY; i++) tally[i] = 0.0;
        int hits = 0;
        for (int i = 0; i < N; i++) {
            seed = seed * 6364136223846793005LL + 1442695040888963407LL;
            int64_t zone = seed % 64;
            if (zone < 0) zone = -zone;
            seed = seed * 6364136223846793005LL + 1442695040888963407LL;
            int64_t plan = seed % 3;
            if (plan < 0) plan = -plan;
            if (plan == 0) {
                tally[zone] = tally[zone] + weight[i] * d[i];
                hits++;
            } else if (plan == 1) {
                tally[zone] = tally[zone] - weight[i] * d[i];
                hits++;
            }
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("tally[0] = %f\n", tally[0]);
    return 0;
}

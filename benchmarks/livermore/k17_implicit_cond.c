/* K17 — Implicit Conditional Computation
   Original Livermore Loop kernel 17.
   7 arrays of size 101, goto-based forward/backward loop.
   n=101, i starts at n-2 (=99), ink=-1, j=0. */
#include <stdio.h>
#include <time.h>
#include "signel.h"

#define N     101
#define NREPS 10000

int main(void) {
    static double vsp[N], vstp[N], vxne[N], vxnd[N], ve3[N], vlr[N], vlin[N];

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    int i, j, ink;
    double scale, xnm, e6, e3, xnei, xnc;

    for (int rep = 0; rep < NREPS; rep++) {
        signel(vsp, N); signel(vstp, N); signel(vxne, N); signel(vxnd, N);
        signel(ve3, N); signel(vlr, N); signel(vlin, N);

        i = N - 2; j = 0; ink = -1;
        scale = 5.0 / 3.0; xnm = 1.0 / 3.0; e6 = 1.03 / 3.07;
        goto l61;
    l60:
        e6 = xnm * vsp[i] + vstp[i];
        vxne[i] = e6;
        xnm = e6;
        ve3[i] = e6;
        i += ink;
        if (i == j) goto l62;
    l61:
        e3 = xnm * vlr[i] + vlin[i];
        xnei = vxne[i];
        vxnd[i] = e6;
        xnc = scale * e3;
        if (xnm > xnc) goto l60;
        if (xnei > xnc) goto l60;
        ve3[i] = e3;
        e6 = e3 + e3 - xnm;
        vxne[i] = e3 + e3 - xnei;
        xnm = e6;
        i += ink;
        if (i != j) goto l61;
    l62: ;
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) * 1e-9;
    printf("elapsed: %.6f s\n", elapsed);
    printf("ve3[0] = %f\n", ve3[0]);
    return 0;
}

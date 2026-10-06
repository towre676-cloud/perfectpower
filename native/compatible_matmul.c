/* Comparable C99 kernels with exact bounded uint32 input / uint64 output.
   The Python adapter limits n<=512 and each input<=65535, so every sum fits.
   Tiled dimensions satisfy row_block^2=column_block^3 for its exact family. */
#include <stdint.h>
#include <stddef.h>
#include <string.h>

void pp_naive(size_t n,const uint32_t *a,const uint32_t *b,uint64_t *out) {
    for(size_t i=0;i<n;i++) for(size_t j=0;j<n;j++) {
        uint64_t value=0;
        for(size_t k=0;k<n;k++) value+=(uint64_t)a[i*n+k]*b[k*n+j];
        out[i*n+j]=value;
    }
}

void pp_untiled(size_t n,const uint32_t *a,const uint32_t *b,uint64_t *out) {
    memset(out,0,n*n*sizeof(uint64_t));
    for(size_t i=0;i<n;i++) for(size_t k=0;k<n;k++) {
        uint64_t value=a[i*n+k];
        for(size_t j=0;j<n;j++) out[i*n+j]+=value*b[k*n+j];
    }
}

void pp_tiled(size_t n,const uint32_t *a,const uint32_t *b,uint64_t *out,size_t rows,size_t columns) {
    memset(out,0,n*n*sizeof(uint64_t));
    for(size_t r=0;r<n;r+=rows) for(size_t c=0;c<n;c+=columns) {
        size_t re=r+rows<n?r+rows:n,ce=c+columns<n?c+columns:n;
        for(size_t i=r;i<re;i++) for(size_t k=0;k<n;k++) {
            uint64_t value=a[i*n+k];
            for(size_t j=c;j<ce;j++) out[i*n+j]+=value*b[k*n+j];
        }
    }
}

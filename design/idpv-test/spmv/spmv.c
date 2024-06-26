#include "spmv.h"
#include <assert.h>

void spmv(TYPE val[NNZ], int32_t cols[NNZ], int32_t rowDelimiters[N+1], TYPE vec[N], TYPE out[N]){
    int i, j;
    TYPE sum, Si;

    spmv_1 : for(i = 0; i < N; i++){
        sum = 0; Si = 0;
        int tmp_begin = rowDelimiters[i];
        int tmp_end = rowDelimiters[i+1];
        spmv_2 : for (j = tmp_begin; j < tmp_end; j++){
            Si = val[j] * vec[cols[j]];
            sum = sum + Si;
        }
        out[i] = sum;
    }
}

int main(){
    TYPE val[NNZ];
    int32_t cols[NNZ];
    int32_t rowDelimiters[N+1];
    TYPE vec[N];
    TYPE out[N];
    spmv(val, cols, rowDelimiters, vec, out);

    assert(out[N] == 0);

    return 0;
}

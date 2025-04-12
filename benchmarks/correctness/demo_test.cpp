#include <stdio.h>
#include <stdlib.h>
#include <time.h>

#define ITER 100  // Number of iterations for longer branches

// Function to execute the branch based on the secret value and return a result
int benchmarkBranch(int branch __attribute((annotate("secret"))), int result) {
    int A[10] = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9};
    int i = 3;
    int k = A[branch];
    switch(k) {
        // case 0:
        //     for (int i = 0; i < ITER; i++) {
        //         result += (i % 3) * 7;
        //         result ^= i;
        //     }
        //     break;
        // case 1:
        //     for (int i = 0; i < ITER; i++) {
        //         result += (i % 4) * 8;
        //         result ^= (i >> 2);
        //     }
        //     break;
        // case 2:
        //     for (int i = 0; i < ITER; i++) {
        //         result += (i % 5) * 9;
        //         result ^= (i >> 1);
        //     }
        //     break;
        // case 3:
        //     for (int i = 0; i < ITER; i++) {
        //         result += (i % 2) * 3;
        //         result ^= (i << 1);
        //     }
        //     break;
        // case 4:
        //     for (int i = 0; i < ITER; i++) {
        //         result += (i % 6) * 10;
        //         result ^= (i >> 3);
        //     }
        //     break;
        case 5:
            // This branch is significantly shorter
            result = (42 * 2) - (7 / 3);
            break;
        case 6:
            for (int i = 0; i < ITER; i++) {
                result += (i % 7) * 11;
                result ^= (i << 2);
            }
            break;
        // case 7:
        //     for (int i = 0; i < ITER; i++) {
        //         result += (i % 8) * 12;
        //         result ^= (i >> 4);
        //     }
        //     break;
        // case 8:
        //     for (int i = 0; i < ITER; i++) {
        //         result += (i % 9) * 13;
        //         result ^= (i >> 1);
        //     }
        //     break;
        // case 9:
        //     for (int i = 0; i < ITER; i++) {
        //         result += (i % 10) * 14;
        //         result ^= (i << 3);
        //     }
        //     break;
        default:
            // Return a default value for any unexpected branch value
            result = -1;
            break;
    }
    return result;
}

int main(void) {
    // Seed the random number generator
    srand((unsigned int)time(NULL));

    // Randomly choose a branch between 0 and 9
    int secretBranch = rand() % 2 + 5;

    // Execute the branch function with the secret value
    int result = benchmarkBranch(secretBranch, 0);

    printf("Branch %d executed, result = %d\n", secretBranch, result);

    return 0;
}

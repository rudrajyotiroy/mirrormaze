#include <stdio.h>
#include <stdlib.h>
#include <time.h>

#define ITER 1000000 // Number of iterations for longer branches

// Function to execute the branch based on the secret value and return a result
int targetBranch(int branch __attribute((annotate("secret"))), int i) {
    int A[10] = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9};
    int k = A[branch];
    int result = 0;
    switch(k) {
        case 0:
            result /= 3;
            result ^= (i % 14) * 243;
            result += A[i%10];
            break;
        case 1:
            result += (i % 5) * 9;
            result ^= (i >> 3);
            result *= 2;
            i *= 2;
            result ^= (i % 14) * 243;
            i = result / 3;
            result += (i % 5) * 9;
            result ^= (i >> 1);
            break;
        case 2:
            result += (i % 7) * 91;
            result ^= (i >> 2);
            result -= A[i%5];
            result /= 3;
            break;
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
    int secretBranch = rand() % 3;

    // Execute the branch function with the secret value
    for (int i = 0; i < ITER; i++){
        int result = targetBranch(secretBranch, i);
    }

    return 0;
}

#include <stdio.h>
#include <stdlib.h>
#define ITER 50000
/*
 * modexp() computes (base^exp) mod mod using the “square and multiply”
 * algorithm. This implementation uses a branch inside the loop (the if
 * statement) that processes bits of the exponent, which leaks timing information.
 * For real cryptographic purposes, you would use a constant‑time algorithm.
 */
unsigned long long modexp(unsigned long long base, unsigned long long exp __attribute((annotate("secret"))), unsigned long long mod) {
    unsigned long long result = 1;
    base %= mod;
    
    while(exp > 0) {
        // Branch based on the LSB of the exponent
        if(exp & 1) {
            result = (result * base) % mod;
        }
        exp >>= 1;
        base = (base * base) % mod;
    }
    
    return result;
}

int main() {
    /*
     * RSA key parameters (from a common textbook example):
     * p = 61, q = 53  => n = 61 * 53 = 3233
     * phi = (p - 1) * (q - 1) = 3120
     * Public exponent: e = 17
     * Private exponent: d = 2753 (since (e * d) mod phi = 1)
     */
    unsigned long long p = 61, q = 53;
    unsigned long long n = p * q;
    unsigned long long phi = (p - 1) * (q - 1);
    unsigned long long e = 17;
    unsigned long long d = 2753;  // Private key

    // Plaintext to encrypt (it should be less than n)
    unsigned long long plaintext = 65; // For example, the ASCII code for 'A'
    
    // RSA encryption: ciphertext = plaintext^e mod n
    for (int i = 0; i < ITER; i++){
        unsigned long long ciphertext = modexp(plaintext, e, n);
    
        // RSA decryption: decrypted text = ciphertext^d mod n
        unsigned long long decrypted = modexp(ciphertext, d, n);
    }

    printf("RSA Branch Unsafe Example\n");
    // printf("Plaintext : %llu\n", plaintext);
    // printf("Ciphertext: %llu\n", ciphertext);
    // printf("Decrypted : %llu\n", decrypted);

    // if(plaintext == decrypted) {
    //     printf("Success: Decrypted text matches plaintext.\n");
    // } else {
    //     printf("Error: Decryption failed.\n");
    // }
    
    return 0;
}

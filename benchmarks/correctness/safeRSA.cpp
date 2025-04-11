#include <stdio.h>
#include <stdlib.h>

/*
 * montgomery_ladder_modexp() computes (base^exp) mod mod using the Montgomery ladder algorithm.
 * This implementation uses an explicit if‑else to decide which operations to perform based on the
 * current bit of the exponent. As a result, it is branch unsafe (i.e. its execution time depends 
 * on the secret exponent's bit pattern), and it should not be used in production or security‑sensitive applications.
 */
unsigned long long montgomery_ladder_modexp(unsigned long long base, unsigned long long exp __attribute((annotate("secret"))), unsigned long long mod) {
    // Initialize the two registers for the Montgomery ladder.
    unsigned long long R0 = 1;
    unsigned long long R1 = base % mod;
    
    // Iterate over each bit of the exponent from the most-significant bit to the least.
    int total_bits = sizeof(exp) * 8;
    for (int i = total_bits - 1; i >= 0; i--) {
        // Check the current bit of the exponent.
        unsigned long long iBit = (exp >> i) & 1ULL;
        if (iBit) {
            // When the current bit is 1:
            //    - Update R0 = R0 * R1 mod mod.
            //    - Update R1 = R1^2 mod mod.
            R0 = (R0 * R1) % mod;
            R1 = (R1 * R1) % mod;
        } else {
            // When the current bit is 0:
            //    - Update R1 = R0 * R1 mod mod.
            //    - Update R0 = R0^2 mod mod.
            R1 = (R0 * R1) % mod;
            R0 = (R0 * R0) % mod;
        }
    }
    
    // At the end of the loop, R0 holds (base^exp) mod mod.
    return R0;
}

int main() {
    /*
     * RSA parameters using small, textbook primes:
     * p = 61, q = 53  => n = 61 * 53 = 3233
     * Public exponent: e = 17
     * Private exponent: d = 2753  (such that (e * d) mod ((p - 1) * (q - 1)) = 1)
     */
    unsigned long long p = 61, q = 53;
    unsigned long long n = p * q;
    unsigned long long e = 17;
    unsigned long long d = 2753;  // Private key exponent

    // Example plaintext value (must be less than n).
    unsigned long long plaintext = 65; // For example, ASCII for 'A'
    
    // RSA encryption: ciphertext = plaintext^e mod n.
    unsigned long long ciphertext = montgomery_ladder_modexp(plaintext, e, n);
    
    // RSA decryption: decrypted = ciphertext^d mod n.
    unsigned long long decrypted = montgomery_ladder_modexp(ciphertext, d, n);

    printf("RSA Example using Montgomery Ladder (if-else version)\n");
    printf("Plaintext : %llu\n", plaintext);
    printf("Ciphertext: %llu\n", ciphertext);
    printf("Decrypted : %llu\n", decrypted);

    if (plaintext == decrypted) {
        printf("Success: Decrypted plaintext matches the original.\n");
    } else {
        printf("Error: Decryption failed.\n");
    }
    
    return 0;
}

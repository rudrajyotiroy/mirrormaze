#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAX_ACCOUNTS 100
#define PENALTY 10.00  // Fixed penalty when funds are insufficient

typedef struct {
    char accountNumber[32];
    char customerName[64];
    double balance;
} BankAccount;

BankAccount* accounts[MAX_ACCOUNTS];
int accountCount = 0;

// Create a new account and store it in the global array.
void createAccount(const char *accNum, const char *customer, double initialDeposit) {
    if (accountCount >= MAX_ACCOUNTS) {
        printf("Error: Maximum accounts reached.\n");
        return;
    }

    BankAccount* acc = (BankAccount*)malloc(sizeof(BankAccount));
    if (!acc) {
        printf("Error: Memory allocation failed.\n");
        exit(1);
    }
    strncpy(acc->accountNumber, accNum, sizeof(acc->accountNumber)-1);
    acc->accountNumber[sizeof(acc->accountNumber)-1] = '\0';
    strncpy(acc->customerName, customer, sizeof(acc->customerName)-1);
    acc->customerName[sizeof(acc->customerName)-1] = '\0';
    acc->balance = initialDeposit;

    accounts[accountCount++] = acc;
    printf("Created account %s for %s with initial deposit $%.2f\n", 
           acc->accountNumber, acc->customerName, initialDeposit);
}

// Search for an account by account number.
BankAccount* getAccountByNumber(const char *accNum) {
    int i;
    for (i = 0; i < accountCount; i++) {
        if (strcmp(accounts[i]->accountNumber, accNum) == 0) {
            return accounts[i];
        }
    }
    return NULL;
}

// Deposit money into an account.
// Fee is computed inline using the conversion logic from before (comparing amount with 128 remains).
void deposit(BankAccount *account __attribute((annotate("secret"))), double amount) {
    if (amount <= 0) {
        printf("Deposit amount must be positive.\n");
        return;
    }
    unsigned int amt = (unsigned int) amount;
    int adjust = 0;
    double fee = adjust * 0.01;
    account->balance += amount - fee;
    printf("Deposited $%.2f (fee: $%.2f) into account %s\n", amount, fee, account->accountNumber);
}

// Withdraw money from an account.
// Instead of comparing with 128, the fee is calculated uniformly as: fee = (amount's integer part * 3) * 0.01.
// Then the account's balance is checked. If sufficient, the withdrawal and fee are deducted;
// otherwise, a fixed penalty is applied and the transaction is aborted.
void withdraw(BankAccount *account __attribute((annotate("secret"))), double amount) {
    if (amount <= 0) {
        printf("Withdrawal amount must be positive.\n");
        return;
    }
    double fee = 0.01;
    unsigned int amt = (unsigned int) amount;
    if (account->balance >= amount) {
        account->balance -= amount*(1 + fee);
        // printf("Withdrew $%.2f (fee: $%.2f) from account %s\n", amount, fee, account->accountNumber);
    } else {
        account->balance -= PENALTY;
        // printf("Insufficient funds for withdrawal from account %s. Penalty of $%.2f charged.\n", 
        //        account->accountNumber, PENALTY);
    }
}

// Transfer funds from source to destination account.
// Fee is calculated uniformly as: fee = (amount's integer part * 4) * 0.01.
// If the source account has sufficient funds (balance >= amount + fee),
// the amount plus fee is deducted from source and the amount is added to destination.
// Otherwise, a fixed penalty is deducted from the source and the transfer does not occur.
void transferFunds(BankAccount *source __attribute((annotate("secret"))), BankAccount *destination __attribute((annotate("secret"))), double amount) {
    if (amount <= 0) {
        printf("Transfer amount must be positive.\n");
        return;
    }
    unsigned int amt = (unsigned int) amount;
    double fee = 0.01;
    if (source->balance >= amount) {
        source->balance -= amount*(1 + fee);
        destination->balance += amount;
        // printf("Transferred $%.2f (fee: $%.2f) from account %s to account %s\n", 
        //        amount, fee, source->accountNumber, destination->accountNumber);
    } else {
        source->balance -= PENALTY;
        // printf("Insufficient funds for transfer from account %s. Penalty of $%.2f charged.\n", 
        //        source->accountNumber, PENALTY);
    }
}

// Apply interest to an account.
void applyInterest(BankAccount *account __attribute((annotate("secret"))), double interestRate, double time) {
    if(time < 1) return;
    if(time - (int)time >= 0.5){
        interestRate = interestRate/2;
        time = time*2;
    }
    if(time - (int)time >= 0.5){
        interestRate = interestRate/2;
        time = time*2;
    }
    if (account->balance >= 10000) {
         for(int i = 0; i < time; i++){
            double interest = account->balance * interestRate;
            account->balance += interest;
         }
    } else if (account->balance >= 5000) {
         for(int i = 0; i < time; i++){
            double interest = account->balance * interestRate * 0.85;
            account->balance += interest;
         }
    } else {
         double interest = account->balance * interestRate * time * 0.75;
         account->balance += interest;
    }
}



// Print a summary of all accounts.
void printAccounts() {
    int i;
    printf("\n----- Account Summary -----\n");
    for (i = 0; i < accountCount; i++) {
        printf("Account: %s | Customer: %s | Balance: $%.2f\n", 
               accounts[i]->accountNumber, accounts[i]->customerName, accounts[i]->balance);
    }
    printf("---------------------------\n\n");
}

int main(void) {
    int i;
    // Preload three accounts.
    createAccount("ACC1001", "Alice Johnson", 1000.00);
    createAccount("ACC1002", "Bob Smith", 1500.00);
    createAccount("ACC1003", "Carol Davis", 2000.00);

    // --- Demo run: Execute about 100 operations ---
    printf("\nStarting demo run with 100 operations...\n\n");
    for (i = 0; i < 100; i++) {
        // Cycle through different operations based on the loop index.
        if (i % 4 == 0) {
            // Deposit into account ACC1001.
            BankAccount *acc = getAccountByNumber("ACC1001");
            if (acc) {
                double amount = 50 + (i % 20);  // varying deposit amount
                deposit(acc, amount);
            }
        } else if (i % 4 == 1) {
            // Withdraw from account ACC1002.
            BankAccount *acc = getAccountByNumber("ACC1002");
            if (acc) {
                double amount = 20 + (i % 10);  // varying withdrawal amount
                withdraw(acc, amount);
            }
        } else if (i % 4 == 2) {
            // Transfer from ACC1003 to ACC1001.
            BankAccount *source = getAccountByNumber("ACC1003");
            BankAccount *dest = getAccountByNumber("ACC1001");
            if (source && dest) {
                double amount = 5 + (i % 15);  // varying transfer amount
                transferFunds(source, dest, amount);
            }
        } else if (i % 4 == 3) {
            // Apply interest to all accounts with a varying rate.
            double rate = 0.01 + ((i % 5) * 0.001);
            int j;
            for (j = 0; j < accountCount; j++) {
                applyInterest(accounts[j], rate, i/10);
            }
        }

        // Every 10 operations, print a summary.
        if ((i % 10) == 9) {
            printAccounts();
        }
    }
    
    // Final account summary.
    printAccounts();
    printf("Demo run complete. Shutting down server.\n");

    // Clean up allocated memory.
    for (i = 0; i < accountCount; i++) {
        free(accounts[i]);
    }
    
    return 0;
}

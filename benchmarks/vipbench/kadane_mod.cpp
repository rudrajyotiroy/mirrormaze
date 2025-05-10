
#include <iostream>
using namespace std;
//#include "../config.h"
 
// Function to find the maximum sum of a contiguous subarray
// in a given integer array
int kadane(int arr[] __attribute__((annotate("secret"))), int n, int &ends_at)
{
  // stores the maximum sum subarray found so far
  int max_so_far = 0;
  ends_at = -1;
 
  // stores the maximum sum of subarray ending at the current position
  int max_ending_here = 0;
 
  // traverse the given array
  for (int i = 0; i < n; i++)
  {
    // update the maximum sum of subarray "ending" at index `i` (by adding the
    // current element to maximum sum ending at previous index `i-1`)
    max_ending_here = max_ending_here + arr[i];

  }
  return max_so_far;
}
 
int main()
{
  int arr[] = { 8155, -14406, 20973, -26471, 25508, -24548, -2094, 29777, 20197, -28944 };
  int n = sizeof(arr)/sizeof(arr[0]);
  int max_sum, ends_at;
 
  fprintf(stdout, "Array size= %d\n", n);
  {
    max_sum = kadane(arr, n, ends_at);
  }
  fprintf(stdout, "The maximum sum of a contiguous subarray is %d (ending at index %d)\n", max_sum, ends_at);
  return 0;
}

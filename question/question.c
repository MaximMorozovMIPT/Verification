
/*@
logic integer IntGreater(integer a_i, integer x) =
    (a_i > x) ? 1 : 0;

logic integer NumsGreaterInterval(int *a, integer low, integer high, integer x) =
    (low > high) ? 0 : IntGreater(a[low], x) + NumsGreaterInterval(a, low + 1, high, x);
*/

/*@

logic integer NumsInterval(int *a, integer low, integer high) =
    (low > high) ? 0 : 1 + NumsInterval(a, low + 1, high);
*/


/*@  requires   \valid(arr + (0 .. n−1));
  @  requires   1000 >= n > 0;
  */
void cycle_rl(int *arr, int n) {
    int lo = n - 1;
    int x = arr[lo];
    int idx = lo;
    int i = lo - 1;

    //@ assert idx == lo;

    /*@
        loop invariant  -1 <= i <= lo-1;
        loop invariant  idx <= lo;
        loop invariant  idx == lo - NumsGreaterInterval(arr, i + 1, lo - 1, x);
        loop invariant  x == arr[lo];
        loop invariant  lo == n - 1;
        loop assigns    idx;
        loop variant    i;
    */
    for (i = lo - 1; i >= 0; --i) {
        //@ assert idx == lo - NumsGreaterInterval(arr, i + 1, lo - 1, x);
        if (arr[i] > x) {
            --idx;
            //@ assert i >= 0;
        }
        //@ assert idx == lo - NumsGreaterInterval(arr, i, lo - 1, x);
    }
    //@ assert idx == lo - NumsGreaterInterval(arr, 0, lo - 1, x);

    //@ assert NumsGreaterInterval(arr, 0, lo - 1, x) >= 0;
    //@ assert NumsGreaterInterval(arr, 0, lo - 1, x) <= lo;
    //@ assert NumsInterval(arr, 0, lo - 1) == lo;
}
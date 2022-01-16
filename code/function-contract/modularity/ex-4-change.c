/* run.config
   DONTRUN:
*/

enum note { N500, N200, N100, N50, N20, N10, N5, N2, N1 };
int const values[] = { 500, 200, 100, 50, 20, 10, 5, 2, 1 };

int remove_max_notes(enum note n, int* rest){
  // ...
}

int make_change(int amount, int received, int change[9]){
  // ...

  int rest ;

  change[N500] = remove_max_notes(N500, &rest);
  // ...

  return 0;
}

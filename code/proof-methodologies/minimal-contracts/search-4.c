/* run.config
   DONTRUN:
*/

/* Generated by Frama-C */
#include <stddef.h>
/*@ requires \valid_read(array + (0 .. length - 1)); */
int *search(int *array, size_t length, int element)
{
  int *__retres;
  {
    size_t i = (unsigned int)0;
    /*@ loop invariant 0 ≤ i ≤ length;
        loop assigns i;
        loop variant length - i;
    */
    while (i < length) {
      /*@ assert rte: mem_access: \valid_read(array + i); */
      if (*(array + i) == element) {
        __retres = array + i;
        goto return_label;
      }
      i += (size_t)1;
    }
  }
  __retres = (int *)0;
  return_label: return __retres;
}

void foo(int *array, size_t length)
{
  int *p = search(array,length,0);
  if (p)
    /*@ assert rte: mem_access: \valid(p); */
    /*@ assert rte: mem_access: \valid_read(p); */
    /*@ assert rte: signed_overflow: *p + 1 ≤ 2147483647; */
    (*p) ++;
  return;
}

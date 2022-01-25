/* run.config
   DONTRUN:
*/

#include <stddef.h>

/*@ ghost
  void occ_bounds(int v, int* arr, size_t len){
    // ...
  }

  void not_in_occ_0(int v, int* arr, size_t len){
    // ...
  }

  void occ_monotonic(int v, int* arr, size_t pos, size_t more){
    // ...
  }

  void occ_0_not_in(int v, int* arr, size_t len){
    // ...
    // needs occ_monotonic
  }

  size_t occ_pos_find(int v, int* arr, size_t len){
    // ...
    // needs occ_monotonic
  }

  void occ_pos_exists(int v, int* arr, size_t len){
    // ...
    // should use occ_pos_find
  }
*/

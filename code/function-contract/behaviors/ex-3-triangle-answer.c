#include <limits.h>

enum Sides { SCALENE, ISOSCELE, EQUILATERAL };
enum Angles { RIGHT, ACUTE, OBTUSE };

/*@
  requires 0 <= a && 0 <= b && 0 <= c;
  requires a >= b && a >= c; // Note that this condition is not
                             // necessary for the function but
                             // added for this exercise

  assigns \nothing;

  behavior equilateral:
    assumes a == b == c ;
    ensures \result == EQUILATERAL;

  behavior isocele:
    assumes a == b || a == c || b == c ;
    assumes a != b || a != c || b != c ;
    ensures \result == ISOSCELE;

  behavior scalene:
    assumes a != b && a != c && b != c ;
    ensures \result == SCALENE;

  disjoint behaviors;
  complete behaviors;
*/
enum Sides sides_kind(int a, int b, int c) {
  if (a == b && b == c) {
    return EQUILATERAL ;
  } else if (a == b || b == c || a == c) {
    return ISOSCELE ;
  } else {
    return SCALENE ;
  }
}

/*@
  requires a <= b+c && a >= b && a >= c ;
  requires 0 <= a && a*a <= INT_MAX;
  requires 0 <= b && b*b <= INT_MAX;
  requires 0 <= c && c*c <= INT_MAX;

  assigns \nothing;

  behavior obtuse:
    assumes a*a > b*b + c*c;
    ensures \result == OBTUSE;

  behavior acute:
    assumes a*a < b*b + c*c;
    ensures \result == ACUTE;

  behavior right:
    assumes a*a == b*b + c*c;
    ensures \result == RIGHT;

  disjoint behaviors;
  complete behaviors;
*/
enum Angles angles_kind(int a, int b, int c) {
  if (a * a - b * b > c * c) {
    return OBTUSE;
  } else if (a * a - b * b < c * c) {
    return ACUTE;
  } else {
    return RIGHT;
  }
}


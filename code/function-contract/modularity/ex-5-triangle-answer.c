#include <limits.h>

enum Sides { SCALENE, ISOSCELE, EQUILATERAL };
enum Angles { RIGHT, ACUTE, OBTUSE };

struct TriangleInfo {
  enum Sides sides;
  enum Angles angles;
};

/*@
  requires 0 <= a && 0 <= b && 0 <= c;
  requires a <= b+c;

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
enum Sides sides_kind(int a, int b, int c){
  if(a == b && b == c){
    return EQUILATERAL ;
  } else if(a == b || b == c || a == c){
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
enum Angles angles_kind(int a, int b, int c){
  if(a*a - b*b > c*c){
    return OBTUSE;
  } else if(a*a - b*b < c*c){
    return ACUTE;
  } else {
    return RIGHT;
  }
}

/*@
  requires \valid(info);
  requires a <= b+c && a >= b && a >= c ;
  requires 0 <= a && a*a <= INT_MAX;
  requires 0 <= b && b*b <= INT_MAX;
  requires 0 <= c && c*c <= INT_MAX;

  assigns *info;
  
  behavior not_a_triangle:
    assumes a > b+c ;
    ensures \result == -1;

  behavior triangle:
    assumes a <= b+c ;
    ensures \result == 0;

  behavior equilateral:
    assumes a <= b+c && a == b == c ;
    ensures info->sides == EQUILATERAL;

  behavior isocele:
    assumes a <= b+c ;
    assumes a == b || a == c || b == c ;
    assumes a != b || a != c || b != c ;
    ensures info->sides == ISOSCELE;

  behavior scalene:
    assumes a <= b+c && a != b && a != c && b != c ;
    ensures info->sides == SCALENE;

  behavior obtuse:
    assumes a <= b+c && a*a > b*b + c*c ;
    ensures info->angles == OBTUSE;

  behavior acute:
    assumes a <= b+c && a*a < b*b + c*c ;
    ensures info->angles == ACUTE;

  behavior right:
    assumes a <= b+c && a*a == b*b + c*c ;
    ensures info->angles == RIGHT;

  disjoint behaviors triangle, not_a_triangle;
  complete behaviors triangle, not_a_triangle;

  disjoint behaviors equilateral, isocele, scalene;
  complete behaviors equilateral, isocele, scalene, not_a_triangle;

  disjoint behaviors obtuse, acute, right;
  complete behaviors obtuse, acute, right, not_a_triangle;
*/
int classify(int a, int b, int c, struct TriangleInfo* info){
  if(a > b+c) return -1;

  info->sides  = sides_kind(a, b, c);
  info->angles = angles_kind(a, b, c);

  return 0;
}

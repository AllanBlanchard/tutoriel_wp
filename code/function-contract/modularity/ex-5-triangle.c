/* run.config
   OPT:
*/

#include <limits.h>

enum Sides { SCALENE, ISOSCELE, EQUILATERAL };
enum Angles { RIGHT, ACUTE, OBTUSE };

struct TriangleInfo {
  enum Sides sides;
  enum Angles angles;
};

enum Sides sides_kind(int a, int b, int c){
  // ...
}

enum Angles angles_kind(int a, int b, int c){
  // ...
}

int classify(int a, int b, int c, struct TriangleInfo* info){
  // ...
}

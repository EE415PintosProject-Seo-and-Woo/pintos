/* This file implements the fixed-point arithmetic through 17.14 fixed-point
 number representation. 17.14 format numbers express real numbers. Every
comment that says "real number" means 17.14 format number.*/
#include<stdint.h>

#define F_CONST (1<<14)
/* Changes an integer n to a real number.*/
int i_to_f(int n){
  return n*F_CONST;
}
/* Changes a real number f to an integer */
int f_to_i(int f){
  if(f>>31 == 0)
    return (f+F_CONST/2)/F_CONST;
  return (f-F_CONST/2)/F_CONST;
}
/* Adds a real number y to a real number y and return the result */
int add_f_f(int x, int y){
  return x+y;
}
/* Subtracts a real number y from a real number x and return the result */
int sub_f_f(int x, int y){
  return x-y;
}
/* Adds an integer n to a real number x and return the result */
int add_f_i(int x, int n){
  return x+n*F_CONST;
}
/* Subtracts an integer n from a real number x and return the result */
int sub_f_i(int x, int n){
  return x-n*F_CONST;
}
/* Multiplies a real number x by a real number y and return the result */
int mul_f_f(int x, int y){
  return (int)(((int64_t)x)*y/F_CONST);
}
/* Multiplies a real number x by an integer n and return the result */
int mul_f_i(int x, int n){
  return x*n;
}
/* Divides a real number x by a real number y and return the result */
int div_f_f(int x, int y){
  return (int)(((int64_t)x)*F_CONST/y);
}
/* Divides a real number x by an integer n and return the result */
int div_f_i(int x, int n){
  return x/n;
}

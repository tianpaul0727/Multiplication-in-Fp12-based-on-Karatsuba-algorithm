
#include "finitefield.h"

/* the package about multiplication */



void fastMul(const bigInteger *a, const bigInteger *b, bigInteger *c)
{

   int digs = a->occupied + b->occupied + 1;
   bool neg = (a->sign != b->sign);

   bigIntSchoolMul(a, b, c, digs);

   c->sign = ((c->occupied > 0) && neg) ? NEGATIVE : POSITIVE;

}


// 

/* input : bigInteger a and b, the multiplication result is bigInteger c */
bigIntCatch generMul(const bigInteger *a, const bigInteger *b, bigInteger *c)
{
   bigIntCatch err;
   int digs = a->occupied + b->occupied + 1;
   bool neg = (a->sign != b->sign); 

   err = bigIntSchoolMul(a, b, c, digs);

   c->sign = ((c->occupied > 0) && neg) ? NEGATIVE : POSITIVE;// determine the sign of result c
   return err;

}




bigIntCatch bigIntCombaMul(const bigInteger *a, const bigInteger *b, bigInteger *c, int digs)
{
   int      oldoccupied, pa, ix;
   bigIntCatch   err;
   bigIntDigit W[MP_WARRAY];
   uSignInt  _W;

   /* grow the destination as required */
   if ((err = bigIntIncrease(c, digs)) != runSuccess) {
      return err;
   }

   /* number of output digits to produce */
   pa = mathMIN(digs, a->occupied + b->occupied);

   /* clear the carry */
   _W = 0;
   for (ix = 0; ix < pa; ix++) {
      int tx, ty, iy, iz;

      /* get offsets into the two bignums */
      ty = mathMIN(b->occupied-1, ix);
      tx = ix - ty;

      /* this is the number of times the loop will iterrate, essentially
         while (tx++ < a->occupied && ty-- >= 0) { ... }
       */
      iy = mathMIN(a->occupied-tx, ty+1);

      /* execute loop */
      for (iz = 0; iz < iy; ++iz) {
         _W += (uSignInt)a->adp[tx + iz] * (uSignInt)b->adp[ty - iz];
      }

      /* store term */
      W[ix] = (bigIntDigit)_W & ANDR_1;

      /* make next carry */
      _W = _W >> (uSignInt)DefaultBitOfDigit;
   }

   /* setup dest */
   oldoccupied  = c->occupied;
   c->occupied = pa;

   for (ix = 0; ix < pa; ix++) {
      /* now extract the previous digit [below the carry] */
      c->adp[ix] = W[ix];
   }

   /* clear unoccupied digits [that existed in the old copy of c] */
   bigIntZeroDigits(c->adp + c->occupied, oldoccupied - c->occupied);

   bigIntAdjust(c);
   return runSuccess;
}

/* Karatsuba algorithm refers to libtommath */
bigIntCatch bigIntKaratsubaMul(const bigInteger *a, const bigInteger *b, bigInteger *c)
{
   bigInteger  x0, x1, y0, y1, t1, x0y0, x1y1;
   int  B;
   bigIntCatch  err;

   /* get the min value of digit of two bigInteger */
   B = mathMIN(a->occupied, b->occupied);

   /* B = B/2 */
   B = B >> 1;

   /* init copy all the temps */
   if ((err = bigIntInitialGiv(&x0, B)) != runSuccess) {
      goto ERROR_CLEAR;
   }
   if ((err = bigIntInitialGiv(&x1, a->occupied - B)) != runSuccess) {
      goto X0;
   }
   if ((err = bigIntInitialGiv(&y0, B)) != runSuccess) {
      goto X1;
   }
   if ((err = bigIntInitialGiv(&y1, b->occupied - B)) != runSuccess) {
      goto Y0;
   }

   /* init temps */
   if ((err = bigIntInitialGiv(&t1, B * 2)) != runSuccess) {
      goto Y1;
   }
   if ((err = bigIntInitialGiv(&x0y0, B * 2)) != runSuccess) {
      goto T1;
   }
   if ((err = bigIntInitialGiv(&x1y1, B * 2)) != runSuccess) {
      goto X0Y0;
   }

   /* now shift the digits */
   x0.occupied = y0.occupied = B;
   x1.occupied = a->occupied - B;
   y1.occupied = b->occupied - B;

   /* we copy the digits directly instead of using higher level functions
    * since we also need to shift the digits
    */
   bigIntCopyDigits(x0.adp, a->adp, x0.occupied);
   bigIntCopyDigits(y0.adp, b->adp, y0.occupied);
   bigIntCopyDigits(x1.adp, a->adp + B, x1.occupied);
   bigIntCopyDigits(y1.adp, b->adp + B, y1.occupied);

   /* only need to clamp the lower words since by definition the
    * upper words x1/y1 must have a known number of digits
    */
   bigIntAdjust(&x0);
   bigIntAdjust(&y0);

   /* now compute x0y0 and x1y1 */
   if ((err = generMul(&x0, &y0, &x0y0)) != runSuccess) {
      goto X1Y1;          /* x0y0 = x0*y0 */
   }
   if ((err = generMul(&x1, &y1, &x1y1)) != runSuccess) {
      goto X1Y1;          /* x1y1 = x1*y1 */
   }

    /* we compute (x1 + x0) * (y1 + y0) */
   if ((err = bigIntUnAddition(&x1, &x0, &t1)) != runSuccess) {
      goto X1Y1;          /* t1 = x1 + x0 */
   }
   if ((err = bigIntUnAddition(&y1, &y0, &x0)) != runSuccess) {
      goto X1Y1;          /* t2 = y1 + y0 */
   }
   if ((err = generMul(&t1, &x0, &t1)) != runSuccess) {
      goto X1Y1;          /* t1 = (x1 + x0) * (y1 + y0) */
   }

   /* add x0y0 */
   if ((err = bigIntAddition(&x0y0, &x1y1, &x0)) != runSuccess) {
      goto X1Y1;          /* t2 = x0y0 + x1y1 */
   }
   if ((err = bigIntUnSubtraction(&t1, &x0, &t1)) != runSuccess) {
      goto X1Y1;          /* t1 = (x1+x0)*(y1+y0) - (x1y1 + x0y0) */
   }

   /* shift by B */
   if ((err = bigIntLeftShift(&t1, B)) != runSuccess) {
      goto X1Y1;          /* t1 = (x0y0 + x1y1 - (x1-x0)*(y1-y0))<<B */
   }
   if ((err = bigIntLeftShift(&x1y1, B * 2)) != runSuccess) {
      goto X1Y1;          /* x1y1 = x1y1 << 2*B */
   }

   if ((err = bigIntAddition(&x0y0, &t1, &t1)) != runSuccess) {
      goto X1Y1;          /* t1 = x0y0 + t1 */
   }
   if ((err = bigIntAddition(&t1, &x1y1, c)) != runSuccess) {
      goto X1Y1;          /* t1 = x0y0 + t1 + x1y1 */
   }

X1Y1:
   bigIntClear(&x1y1);
X0Y0:
   bigIntClear(&x0y0);
T1:
   bigIntClear(&t1);
Y1:
   bigIntClear(&y1);
Y0:
   bigIntClear(&y0);
X1:
   bigIntClear(&x1);
X0:
   bigIntClear(&x0);
ERROR_CLEAR:
   return err;
}


bigIntCatch bigIntSchoolMul(const bigInteger *a, const bigInteger *b, bigInteger *c, int digs)
{
   bigInteger  t;
   bigIntCatch  err;
   int     pa, ix;

   if ((err = bigIntInitialGiv(&t, digs)) != runSuccess) {
      return err;
   }
   t.occupied = digs;

   /* compute the digits of the product directly */
   pa = a->occupied;
   for (ix = 0; ix < pa; ix++) {
      int iy, schbb;
      bigIntDigit u = 0;

      /* limit ourselves to making digs digits of output */
      schbb = mathMIN(b->occupied, digs - ix);

      /* compute the columns of the output and propagate the carry */
      for (iy = 0; iy < schbb; iy++) {
         /* compute the column as a uSignInt */
         uSignInt r = (uSignInt)t.adp[ix + iy] +
                     ((uSignInt)a->adp[ix] * (uSignInt)b->adp[iy]) +
                     (uSignInt)u;

         /* the new column is the lower part of the result */
         t.adp[ix + iy] = (bigIntDigit)(r & (uSignInt)ANDR_1);

         /* get the carry word from the result */
         u       = (bigIntDigit)(r >> (uSignInt)DefaultBitOfDigit);
      }
      /* set carry if it is placed below digs */
      if ((ix + iy) < digs) {
         t.adp[ix + schbb] = u;
      }
   }
   bigIntAdjust(&t);
   bigIntExchange(&t, c);

   bigIntClear(&t);
   return runSuccess;
}









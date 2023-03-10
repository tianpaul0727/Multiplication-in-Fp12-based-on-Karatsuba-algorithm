
#include "finitefield.h"


/*  readme!
this pack is the code is is use for testing for mod
it not have connection with our implementation, becuase we do not invlove in division */


bigIntCatch bigIntGenMod(const bigInteger *a, const bigInteger *b, bigInteger *c)
{
	bigIntCatch err;
	if ((err = mp_div(a, b, NULL, c)) != runSuccess) {
		return err;
	}
	return isZero(c) || (c->sign == b->sign) ? runSuccess : bigIntAddition(b, c, c);
}




bigIntCatch mp_div(const bigInteger *a, const bigInteger *b, bigInteger *c, bigInteger *d)
{
	bigIntCatch err;

	/* is divisor zero ? */
	if (isZero(b)) {
		return runInvalid;
	}

	/* if a < b then quotient = 0, remainder = a */
	if (bigIntUnCom(a, b) == LESS) {
		if (d != NULL) {
			if ((err = bigIntCopy(a, d)) != runSuccess) {
				return err;
			}
		}
		if (c != NULL) {
			bigIntZero(c);
		}
		return runSuccess;
	}




 /*  DELETE, the code may be unsafe
	if ((b->occupied > (2 * MUL_KARATSUBA_CUTOFF))
		&& (b->occupied <= ((a->occupied/3)*2))) {
			err = s_mp_div_recursive(a, b, c, d);
	} else  {
		err = bigInt_school_div(a, b, c, d);
	}
 */

   err = bigInt_school_div(a, b, c, d);
	

	return err;
}





bigIntCatch bigIntDiv2k(const bigInteger *a, int b, bigInteger *c, bigInteger *d)
{
	bigIntCatch err;

	if (b < 0) {
		return runInvalid;
	}

	if ((err = bigIntCopy(a, c)) != runSuccess) {
		return err;
	}

	/* 'a' should not be occupied after here - it might be the same as d */

	/* get the remainder */
	if (d != NULL) {
		if ((err = bigIntMod2k(a, b, d)) != runSuccess) {
			return err;
		}
	}

	/* shift by as many digits in the bit count */
	if (b >= DefaultBitOfDigit) {
		bigIntRightShift(c, b / DefaultBitOfDigit);
	}

	/* shift any bit count < DefaultBitOfDigit */
	b %= DefaultBitOfDigit;
	if (b != 0u) {
		int x;
		bigIntDigit r, mask, shift;

		/* mask */
		mask = ((bigIntDigit)1 << b) - 1uL;

		/* shift for lsb */
		shift = (bigIntDigit)(DefaultBitOfDigit - b);

		/* carry */
		r = 0;
		for (x = c->occupied; x --> 0;) {
			/* get the lower  bits of this word in a temp */
			bigIntDigit rr = c->adp[x] & mask;

			/* shift the current word and mix in the carry bits from the previous word */
			c->adp[x] = (c->adp[x] >> b) | (r << shift);

			/* set the carry to the carry bits of the current word found above */
			r = rr;
		}
	}
	bigIntAdjust(c);
	return runSuccess;
}


bigIntCatch bigInt_school_div(const bigInteger *a, const bigInteger *b, bigInteger *c, bigInteger *d)
{
   bigInteger q, x, y, t1, t2;
   int n, t, i, norm;
   bool neg;
   bigIntCatch err;

   if ((err = bigIntInitialGiv(&q, a->occupied + 2)) != runSuccess) {
      return err;
   }
   q.occupied = a->occupied + 2;

   if ((err = bigIntInitial(&t1)) != runSuccess)                           goto LBL_Q;
   if ((err = bigIntInitial(&t2)) != runSuccess)                           goto LBL_T1;
   if ((err = bigIntInitial_copy(&x, a)) != runSuccess)                    goto LBL_T2;
   if ((err = bigIntInitial_copy(&y, b)) != runSuccess)                    goto LBL_X;

   /* fix the sign */
   neg = (a->sign != b->sign);
   x.sign = y.sign = POSITIVE;

   /* normalize both x and y, ensure that y >= b/2, [b == 2**DefaultBitOfDigit] */
   norm = bigIntCountBits(&y) % DefaultBitOfDigit;
   if (norm < (DefaultBitOfDigit - 1)) {
      norm = (DefaultBitOfDigit - 1) - norm;
      if ((err = bigIntMul2k(&x, norm, &x)) != runSuccess)             goto LBL_Y;
      if ((err = bigIntMul2k(&y, norm, &y)) != runSuccess)             goto LBL_Y;
   } else {
      norm = 0;
   }

   /* note hac does 0 based, so if occupied==5 then its 0,1,2,3,4, e.g. use 4 */
   n = x.occupied - 1;
   t = y.occupied - 1;

   /* while (x >= y*b**n-t) do { q[n-t] += 1; x -= y*b**{n-t} } */
   /* y = y*b**{n-t} */
   if ((err = bigIntLeftShift(&y, n - t)) != runSuccess)                     goto LBL_Y;

   while (bigIntSignCom(&x, &y) != LESS) {
      ++(q.adp[n - t]);
      if ((err = bigIntSubtraction(&x, &y, &x)) != runSuccess)                  goto LBL_Y;
   }

   /* reset y by shifting it back down */
   bigIntRightShift(&y, n - t);

   /* step 3. for i from n down to (t + 1) */
   for (i = n; i >= (t + 1); i--) {
      if (i > x.occupied) {
         continue;
      }

      /* step 3.1 if xi == yt then set q{i-t-1} to b-1,
       * otherwise set q{i-t-1} to (xi*b + x{i-1})/yt */
      if (x.adp[i] == y.adp[t]) {
         q.adp[(i - t) - 1] = ((bigIntDigit)1 << (bigIntDigit)DefaultBitOfDigit) - (bigIntDigit)1;
      } else {
         uSignInt tmp;
         tmp = (uSignInt)x.adp[i] << (uSignInt)DefaultBitOfDigit;
         tmp |= (uSignInt)x.adp[i - 1];
         tmp /= (uSignInt)y.adp[t];
         if (tmp > (uSignInt)ANDR_1) {
            tmp = ANDR_1;
         }
         q.adp[(i - t) - 1] = (bigIntDigit)(tmp & (uSignInt)ANDR_1);
      }

      /* while (q{i-t-1} * (yt * b + y{t-1})) >
               xi * b**2 + xi-1 * b + xi-2

         do q{i-t-1} -= 1;
      */
      q.adp[(i - t) - 1] = (q.adp[(i - t) - 1] + 1uL) & (bigIntDigit)ANDR_1;
      do {
         q.adp[(i - t) - 1] = (q.adp[(i - t) - 1] - 1uL) & (bigIntDigit)ANDR_1;

         /* find left hand */
         bigIntZero(&t1);
         t1.adp[0] = ((t - 1) < 0) ? 0u : y.adp[t - 1];
         t1.adp[1] = y.adp[t];
         t1.occupied = 2;
         if ((err = bigIntMul_d(&t1, q.adp[(i - t) - 1], &t1)) != runSuccess)   goto LBL_Y;

         /* find right hand */
         t2.adp[0] = ((i - 2) < 0) ? 0u : x.adp[i - 2];
         t2.adp[1] = x.adp[i - 1]; /* i >= 1 always holds */
         t2.adp[2] = x.adp[i];
         t2.occupied = 3;
      } while (bigIntUnCom(&t1, &t2) == GREATER);

      /* step 3.3 x = x - q{i-t-1} * y * b**{i-t-1} */
      if ((err = bigIntMul_d(&y, q.adp[(i - t) - 1], &t1)) != runSuccess)       goto LBL_Y;
      if ((err = bigIntLeftShift(&t1, (i - t) - 1)) != runSuccess)                  goto LBL_Y;
      if ((err = bigIntSubtraction(&x, &t1, &x)) != runSuccess)                        goto LBL_Y;

      /* if x < 0 then { x = x + y*b**{i-t-1}; q{i-t-1} -= 1; } */
      if (isNegative(&x)) {
         if ((err = bigIntCopy(&y, &t1)) != runSuccess)                        goto LBL_Y;
         if ((err = bigIntLeftShift(&t1, (i - t) - 1)) != runSuccess)               goto LBL_Y;
         if ((err = bigIntAddition(&x, &t1, &x)) != runSuccess)                     goto LBL_Y;

         q.adp[(i - t) - 1] = (q.adp[(i - t) - 1] - 1uL) & ANDR_1;
      }
   }

   /* now q is the quotient and x is the remainder
    * [which we have to normalize]
    */

   /* get sign before writing to c */
   x.sign = isZero(&x) ? POSITIVE : a->sign;

   if (c != NULL) {
      bigIntAdjust(&q);
      bigIntExchange(&q, c);
      c->sign = (neg ? NEGATIVE : POSITIVE);
   }

   if (d != NULL) {
      if ((err = bigIntDiv2k(&x, norm, &x, NULL)) != runSuccess)       goto LBL_Y;
      bigIntExchange(&x, d);
   }

LBL_Y:
   bigIntClear(&y);
LBL_X:
   bigIntClear(&x);
LBL_T2:
   bigIntClear(&t2);
LBL_T1:
   bigIntClear(&t1);
LBL_Q:
   bigIntClear(&q);
   return err;
}


comRes bigIntSignCom_d(const bigInteger *a, bigIntDigit b)
{
	/* compare based on sign */
	if (isNegative(a)) {
		return LESS;
	}

	/* compare based on magnitude */
	if (a->occupied > 1) {
		return GREATER;
	}

	/* compare the only digit of a to b */
	if (a->adp[0] != b) {
		return a->adp[0] > b ? GREATER : LESS;
	}

	return EQUAL;
}





















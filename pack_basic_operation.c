
#include "finitefield.h"


#include <stdarg.h>

/* pack_basic_operation, include mod 2^k or div 2^knor multiple 2^k , left logic shigt, right logic shift */

bigIntCatch bigIntMul2k(const bigInteger *a, int b, bigInteger *c)
{
	bigIntCatch err;

	if (b < 0) {
		return runInvalid;
	}

	if ((err = bigIntCopy(a, c)) != runSuccess) {
		return err;
	}

	if ((err = bigIntIncrease(c, c->occupied + (b / DefaultBitOfDigit) + 1)) != runSuccess) {
		return err;
	}

	/* shift by as many digits in the bit count */
	if (b >= DefaultBitOfDigit) {
		if ((err = bigIntLeftShift(c, b / DefaultBitOfDigit)) != runSuccess) {
			return err;
		}
	}

	/* shift any bit count < DefaultBitOfDigit */
	b %= DefaultBitOfDigit;
	if (b != 0u) {
		bigIntDigit shift, mask, r;
		int x;

		/* bitmask for carries */
		mask = ((bigIntDigit)1 << b) - (bigIntDigit)1;

		/* shift for msbs */
		shift = (bigIntDigit)(DefaultBitOfDigit - b);

		/* carry */
		r    = 0;
		for (x = 0; x < c->occupied; x++) {
			/* get the higher bits of the current word */
			bigIntDigit rr = (c->adp[x] >> shift) & mask;

			/* shift the current word and OR in the carry */
			c->adp[x] = ((c->adp[x] << b) | r) & ANDR_1;

			/* set the carry to the carry bits of the current word */
			r = rr;
		}

		/* set final carry */
		if (r != 0u) {
			c->adp[(c->occupied)++] = r;
		}
	}
	bigIntAdjust(c);
	return runSuccess;
}


bigIntCatch bigIntMod2k(const bigInteger *a, int b, bigInteger *c)
{
	int x;
	bigIntCatch err;

	if (b < 0) {
		return runInvalid;
	}

	if (b == 0) {
		bigIntZero(c);
		return runSuccess;
	}

	/* if the modulus is larger than the value than return */
	if (b >= (a->occupied * DefaultBitOfDigit)) {
		return bigIntCopy(a, c);
	}

	if ((err = bigIntCopy(a, c)) != runSuccess) {
		return err;
	}

	/* zero digits above the last digit of the modulus */
	x = (b / DefaultBitOfDigit) + (((b % DefaultBitOfDigit) == 0) ? 0 : 1);
	bigIntZeroDigits(c->adp + x, c->occupied - x);

	/* clear the digit that is not completely outside/inside the modulus */
	c->adp[b / DefaultBitOfDigit] &=
		((bigIntDigit)1 << (bigIntDigit)(b % DefaultBitOfDigit)) - (bigIntDigit)1;
	bigIntAdjust(c);
	return runSuccess;
}


bigIntCatch bigIntLeftShift(bigInteger *a, int b)
{
   bigIntCatch err;
   int x;

   /* if its less than zero return */
   if (b <= 0) {
      return runSuccess;
   }
   /* no need to shift 0 around */
   if (isZero(a)) {
      return runSuccess;
   }

   /* Increase to fit the new digits */
   if ((err = bigIntIncrease(a, a->occupied + b)) != runSuccess) {
      return err;
   }

   /* increment the occupied by the shift amount then copy upwards */
   a->occupied += b;

   for (x = a->occupied; x --> b;) {
      a->adp[x] = a->adp[x - b];
   }

   /* zero the lower digits */
   bigIntZeroDigits(a->adp, b);

   return runSuccess;
}




void bigIntRightShift(bigInteger *a, int b)
{
   int x;

   /* if b <= 0 then ignore it */
   if (b <= 0) {
      return;
   }

   /* if b > occupied then simply zero it and return */
   if (a->occupied <= b) {
      bigIntZero(a);
      return;
   }

   for (x = 0; x < (a->occupied - b); x++) {
      a->adp[x] = a->adp[x + b];
   }

   /* zero the top digits */
   bigIntZeroDigits(a->adp + a->occupied - b, b);

   /* remove excess digits */
   a->occupied -= b;
}



/* single digit addition */
bigIntCatch bigIntAddition_d(const bigInteger *a, bigIntDigit b, bigInteger *c)
{
	bigIntCatch err;
	int oldoccupied;

	/* fast path for a == c */
	if (a == c) {
		if (!isNegative(c) &&
			!isZero(c) &&
			((c->adp[0] + b) < MP_DIGIT_MAX)) {
				c->adp[0] += b;
				return runSuccess;
		}
		if (isNegative(c) &&
			(c->adp[0] > b)) {
				c->adp[0] -= b;
				return runSuccess;
		}
	}

	/* grow c as required */
	if ((err = bigIntIncrease(c, a->occupied + 1)) != runSuccess) {
		return err;
	}

	/* if a is negative and |a| >= b, call c = |a| - b */
	if (isNegative(a) && ((a->occupied > 1) || (a->adp[0] >= b))) {
		bigInteger a_ = *a;
		/* temporarily fix sign of a */
		a_.sign = POSITIVE;

		/* c = |a| - b */
		err = bigIntSubtraction_d(&a_, b, c);

		/* fix sign  */
		c->sign = NEGATIVE;

		/* clamp */
		bigIntAdjust(c);

		return err;
	}

	/* old number of occupied digits in c */
	oldoccupied = c->occupied;

	/* if a is positive */
	if (!isNegative(a)) {
		/* add digits, mu is carry */
		int i;
		bigIntDigit mu = b;
		for (i = 0; i < a->occupied; i++) {
			c->adp[i] = a->adp[i] + mu;
			mu = c->adp[i] >> DefaultBitOfDigit;
			c->adp[i] &= ANDR_1;
		}
		/* set final carry */
		c->adp[i] = mu;

		/* setup size */
		c->occupied = a->occupied + 1;
	} else {
		/* a was negative and |a| < b */
		c->occupied = 1;

		/* the result is a single digit */
		c->adp[0] = (a->occupied == 1) ? b - a->adp[0] : b;
	}

	/* sign always positive */
	c->sign = POSITIVE;

	/* now zero to oldoccupied */
	bigIntZeroDigits(c->adp + c->occupied, oldoccupied - c->occupied);
	bigIntAdjust(c);

	return runSuccess;
}

bigIntCatch bigIntSubtraction_d(const bigInteger *a, bigIntDigit b, bigInteger *c)
{
   bigIntCatch err;
   int oldoccupied;

   /* fast path for a == c */
   if (a == c) {
      if ((c->sign == NEGATIVE) &&
          ((c->adp[0] + b) < MP_DIGIT_MAX)) {
         c->adp[0] += b;
         return runSuccess;
      }
      if ((c->sign == POSITIVE) &&
          (c->adp[0] > b)) {
         c->adp[0] -= b;
         return runSuccess;
      }
   }

   /* grow c as required */
   if ((err = bigIntIncrease(c, a->occupied + 1)) != runSuccess) {
      return err;
   }

   /* if a is negative just do an unsigned
    * addition [with fudged signs]
    */
   if (a->sign == NEGATIVE) {
      bigInteger a_ = *a;
      a_.sign = POSITIVE;
      err     = bigIntAddition_d(&a_, b, c);
      c->sign = NEGATIVE;

      /* clamp */
      bigIntAdjust(c);

      return err;
   }

   oldoccupied = c->occupied;

   /* if a <= b simply fix the single digit */
   if (((a->occupied == 1) && (a->adp[0] <= b)) || isZero(a)) {
      c->adp[0] = (a->occupied == 1) ? b - a->adp[0] : b;

      /* negative/1digit */
      c->sign = NEGATIVE;
      c->occupied = 1;
   } else {
      int i;
      bigIntDigit mu = b;

      /* positive/size */
      c->sign = POSITIVE;
      c->occupied = a->occupied;

      /* subtract digits, mu is carry */
      for (i = 0; i < a->occupied; i++) {
         c->adp[i] = a->adp[i] - mu;
         mu = c->adp[i] >> (SIZE_OF_BITS(bigIntDigit) - 1u);
         c->adp[i] &= ANDR_1;
      }
   }

   /* zero excess digits */
   bigIntZeroDigits(c->adp + c->occupied, oldoccupied - c->occupied);

   bigIntAdjust(c);
   return runSuccess;
}



/* multiply by a digit */
bigIntCatch bigIntMul_d(const bigInteger *x, bigIntDigit b, bigInteger *y)
{
	bigIntDigit carry;
	bigIntCatch   err;
	int   i, oldoccu;

	if (b == 1u) {
		return bigIntCopy(x, y);
	}



	/* make sure c is big enough to hold a*b */
	if ((err = bigIntIncrease(y, x->occupied + 1)) != runSuccess) {
		return err;
	}

	/* get the original destinations occupied count */
	oldoccu = y->occupied;

	/* set the sign */
	y->sign = x->sign;

	/* zero carry */
	carry = 0;

	// compute every digit
	for (i = 0; i < x->occupied; i++) {

		/* compute product and carry sum for this term */
		uSignInt r = (uSignInt)carry + ((uSignInt)x->adp[i] * (uSignInt)b);

		/* do mod operartion, the store y[i] = x[i]*b % R */
		y->adp[i] = (bigIntDigit)(r & (uSignInt)ANDR_1);

		/* PASS UP the carry value, it equal to (x[i]*b+ carry) >> 15 bit */
		carry = (bigIntDigit)(r >> (uSignInt)DefaultBitOfDigit);
	}

	y->adp[i] = carry; //store the (possible) most significant digit in the y[occupied]

	/* set occupied count */
	y->occupied = x->occupied + 1;

	/* now zero digits above the top */
	bigIntZeroDigits(y->adp + y->occupied, oldoccu - y->occupied);

	bigIntAdjust(y);

	return runSuccess;
}




bigIntCatch mp_div_d(const bigInteger *a, bigIntDigit b, bigInteger *c, bigIntDigit *d)
{
	bigInteger  q;
	uSignInt w;
	bigIntCatch err;
	int ix;

	/* cannot divide by zero */
	if (b == 0u) {
		return runInvalid;
	}

	/* quick outs */
	if ((b == 1u) || isZero(a)) {
		if (d != NULL) {
			*d = 0;
		}
		if (c != NULL) {
			return bigIntCopy(a, c);
		}
		return runSuccess;
	}


	/* no easy answer [c'est la vie].  Just division */
	if ((err = bigIntInitialGiv(&q, a->occupied)) != runSuccess) {
		return err;
	}

	q.occupied = a->occupied;
	q.sign = a->sign;
	w = 0;
	for (ix = a->occupied; ix --> 0;) {
		bigIntDigit t = 0;
		w = (w << (uSignInt)DefaultBitOfDigit) | (uSignInt)a->adp[ix];
		if (w >= b) {
			t = (bigIntDigit)(w / b);
			w -= (uSignInt)t * (uSignInt)b;
		}
		q.adp[ix] = t;
	}

	if (d != NULL) {
		*d = (bigIntDigit)w;
	}

	if (c != NULL) {
		bigIntAdjust(&q);
		bigIntExchange(&q, c);
	}
	bigIntClear(&q);

	return runSuccess;
}




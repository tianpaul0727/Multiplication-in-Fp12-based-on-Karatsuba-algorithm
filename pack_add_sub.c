
#include "finitefield.h"



// the idea of addiiton and subtraction is inspired from libtommath, but we do some modification on it

bigIntCatch bigIntUnAddition(const bigInteger *x, const bigInteger *y, bigInteger *z)
{
   int oldoccupied, min, max, i;
   bigIntDigit carry;
   bigIntCatch err;

   /* find sizes
    */
   if (x->occupied < y->occupied) {
      mathExchange(const bigInteger *, x, y);
   }

   min = y->occupied;
   max = x->occupied;

   /* init result */
   if ((err = bigIntIncrease(z, max + 1)) != runSuccess) {
      return err;
   }

   /* get old occupied digit count and set new one */
   oldoccupied = z->occupied;
   z->occupied = max + 1;

   /* set the carry is 0 */
   carry = 0;
   for (i = 0; i < min; i++) {
      /* Compute each digit of z: z[i] = x[i] + y[i] + carry */
      z->adp[i] = x->adp[i] + y->adp[i] + carry;

      /* the value of carry of z[i] */
      carry = z->adp[i] >> (bigIntDigit)DefaultBitOfDigit; // right shift 15 bit

      /* take away the carry , the rest of it */
      z->adp[i] &= ANDR_1; // AND R-1 is faster
   }

   /* TRANSFER THE CARRY IF THE DIGIT IS DIFFERENT
    */
   if (min != max) {
      for (; i < max; i++) {
         /* T[i] = A[i] + carry */
         z->adp[i] = x->adp[i] + carry;

         /* carry = carry bit of T[i] */
         carry = z->adp[i] >> (bigIntDigit)DefaultBitOfDigit;

         /* take away carry bit from T[i] */
         z->adp[i] &= ANDR_1;
      }
   }

   /* add carry */
   z->adp[i] = carry;

   /* clear and zero  */
   bigIntZeroDigits(z->adp + z->occupied, oldoccupied - z->occupied);


   /* delete all unness zero */

   bigIntAdjust(z);
   return runSuccess;
}

/* high level addition (signs) */
bigIntCatch bigIntAddition(const bigInteger *a, const bigInteger *b, bigInteger *c)
{
	/* handle two cases, not four */
	if (a->sign == b->sign) {
		/* both positive or both negative */
		/* add their magnitudes, copy the sign */
		c->sign = a->sign;
		return bigIntUnAddition(a, b, c);
	}

	/* one positive, the other negative. The result gets the sign of the one with the greater magnitude. */
	if (bigIntUnCom(a, b) == LESS) {
		mathExchange(const bigInteger *, a, b);
	}

	c->sign = a->sign;
	return bigIntUnSubtraction(a, b, c);
}

/* Unsigned Integer subtraction (assumes |a| > |b|) */
bigIntCatch bigIntUnSubtraction(const bigInteger *a, const bigInteger *b, bigInteger *c)
{
   int oldoccupied = c->occupied, min = b->occupied, max = a->occupied, i;
   bigIntDigit borrow;
   bigIntCatch err;

   /* init result */
   if ((err = bigIntIncrease(c, max)) != runSuccess) {
      return err;
   }

   c->occupied = max;

   /* set carry to zero */
   borrow = 0;
   for (i = 0; i < min; i++) {
      /* T[i] = A[i] - B[i] - borrow */
      c->adp[i] = (a->adp[i] - b->adp[i]) - borrow;

      /* borrow = carry bit of T[i]
       * an AND operation is mod R
       */
      borrow = c->adp[i] >> (SIZE_OF_BITS(bigIntDigit) - 1u);

      /* Clear carry from T[i] */
      c->adp[i] &= ANDR_1;
   }

   /* now copy higher words if any  */
   for (; i < max; i++) {
      /* T[i] = A[i] - U */
      c->adp[i] = a->adp[i] - borrow;

      /* borrow = carry bit of T[i] */
      borrow = c->adp[i] >> (SIZE_OF_BITS(bigIntDigit) - 1u);

      /* Clear carry from T[i] */
      c->adp[i] &= ANDR_1;
   }

   /* clear digits above occupied (since we may not have grown result above) */
   bigIntZeroDigits(c->adp + c->occupied, oldoccupied - c->occupied);

   bigIntAdjust(c);
   return runSuccess;
}


bigIntCatch bigIntSubtraction(const bigInteger *a, const bigInteger *b, bigInteger *c)
{
	if (a->sign != b->sign) {
		
		return bigIntUnAddition(a, b, c);
	}

	if (bigIntUnCom(a, b) == LESS) {

		c->sign = (!isNegative(a) ? NEGATIVE : POSITIVE);
		mathExchange(const bigInteger *, a, b);
	} else {
		/* The first has a larger or equal magnitude */
		/* Copy the sign from the first */
		c->sign = a->sign;
	}
	return bigIntUnSubtraction(a, b, c);
}



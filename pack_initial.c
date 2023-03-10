
#include "finitefield.h"
#include <stdarg.h>



extern const char radixMap[] ;

extern const uint8_t radixMap_reverse[];


bigIntCatch bigIntInitial(bigInteger *a)
{
   /* Default precison is 64 */
   a->adp = (bigIntDigit *) CALLOC((size_t)DEFAULT_PRECII, sizeof(bigIntDigit));
   if (a->adp == NULL) {
      return runOutMem;
   }

   /* set the occupied to zero, allocated digits to the default precision,sign to positive */
   a->occupied  = 0;
   a->alloc = DEFAULT_PRECII;
   a->sign  = POSITIVE;

   return runSuccess;
}

bigIntCatch bigIntInitial_multi(bigInteger *mp, ...)
{
   bigIntCatch err = runSuccess;
   int n = 0;                 /* Number of ok inits */
   bigInteger *cur_arg = mp;
   va_list args;

   va_start(args, mp);        /* init args to next argument from caller */
   while (cur_arg != NULL) {
      err = bigIntInitial(cur_arg);
      if (err != runSuccess) {
         /* Oops - error! Back-track and bigIntClear what we already
            succeeded in init-ing, then return error.
         */
         va_list clean_args;

         /* now start cleaning up */
         cur_arg = mp;
         va_start(clean_args, mp);
         while (n-- != 0) {
            bigIntClear(cur_arg);
            cur_arg = va_arg(clean_args, bigInteger *);
         }
         va_end(clean_args);
         break;
      }
      n++;
      cur_arg = va_arg(args, bigInteger *);
   }
   va_end(args);
   return err;
}

void bigIntClear_multi(bigInteger *mp, ...)
{
	va_list args;
	va_start(args, mp);
	while (mp != NULL) {
		bigIntClear(mp);
		mp = va_arg(args, bigInteger *);
	}
	va_end(args);
}

void bigIntZeroBuff(void *mem, size_t size)
{

	memset(mem, 0, size);

}

/* init an bigIntInitial for a given size */
bigIntCatch bigIntInitialGiv(bigInteger *a, int size)
{
	size = mathMax(mathMIN_DIGIT_COUNT, size);

	if (size > mathMax_DIGIT_COUNT) {
		return runIntOF;
	}

	/* alloc mem */
	a->adp = (bigIntDigit *) CALLOC((size_t)size, sizeof(bigIntDigit));
	if (a->adp == NULL) {
		return runOutMem;
	}

	/* set the members */
	a->occupied  = 0;
	a->alloc = size;
	a->sign  = POSITIVE;

	return runSuccess;
}


bigIntCatch bigIntCopy(const bigInteger *a, bigInteger *b)
{
	bigIntCatch err;

	/* if a == b, nothing to do*/
	if (a == b) {
		return runSuccess;
	}

	/* Increase */
	if ((err = bigIntIncrease(b, a->occupied)) != runSuccess) {
		return err;
	}

	/* copy everything over and zero high digits */
	bigIntCopyDigits(b->adp, a->adp, a->occupied);
	bigIntZeroDigits(b->adp + a->occupied, b->occupied - a->occupied);
	b->occupied = a->occupied;
	b->sign = a->sign;

	return runSuccess;
}

/* clear one (frees)  */
void bigIntClear(bigInteger *a)
{
	/* if has been clear, hen we have nothing to do */
	if (a->adp != NULL) {
		/* free every digits  */
		doFree_DIGS(a->adp, a->alloc);

		/* reset all parameter */
		a->adp    = NULL;
		a->alloc = a->occupied = 0;
		a->sign  = POSITIVE;
	}
}

void bigIntZero(bigInteger *a)
{
	a->sign = POSITIVE;
	bigIntZeroDigits(a->adp, a->occupied);
	a->occupied = 0;
}

bigIntCatch bigIntIncrease(bigInteger *a, int size)
{
   /* if the alloc size is smaller, alloc more */
   if (a->alloc < size) {
      bigIntDigit *adp;

      if (size > mathMax_DIGIT_COUNT) {
         return runIntOF;
      }

      /* reallocate the array a->adp   */
      adp = (bigIntDigit *) REALLOC(a->adp,
                                   (size_t)a->alloc * sizeof(bigIntDigit),
                                   (size_t)size * sizeof(bigIntDigit));
      if (adp == NULL) {
         /* reallocation failed but "a" is still valid */
         return runOutMem;
      }

      /* reallocation succeeded so set a->adp */
      a->adp = adp;

      /* zero excess digits */
      bigIntZeroDigits(a->adp + a->alloc, size - a->alloc);
      a->alloc = size;
   }
   return runSuccess;
}




void bigIntZeroDigits(bigIntDigit *d, int digits)
{

	if (digits > 0) {
		memset(d, 0, (size_t)digits * sizeof(bigIntDigit));
	}

}



void bigIntCopyDigits(bigIntDigit *d, const bigIntDigit *s, int digits)
{
	if (digits > 0) {
		memcpy(d, s, (size_t)digits * sizeof(bigIntDigit));
	}

}


bigIntCatch bigIntInitial_copy(bigInteger *a, const bigInteger *b)
{
	bigIntCatch     err;

	if ((err = bigIntInitialGiv(a, b->occupied)) != runSuccess) {
		return err;
	}

	if ((err = bigIntCopy(b, a)) != runSuccess) {
		bigIntClear(a);
	}

	return err;
}

void bigIntAdjust(bigInteger *a)
{
   /* decrease occupied while the most significant digit is zero  */
   while ((a->occupied > 0) && (a->adp[a->occupied - 1] == 0u)) {
      --(a->occupied);
   }

   /* reset the sign flag if zero */
   if (isZero(a)) {
      a->sign = POSITIVE;
   }
}









#include "finitefield.h"
 
 // some fuction to help me compare bigInt or read the radix

const uint8_t radixMap_reverse[] = {
	0x3e, 0xff, 0xff, 0xff, 0x3f, 0x00, 0x01, 0x02, 0x03, 0x04, /* +,-./01234 */
	0x05, 0x06, 0x07, 0x08, 0x09, 0xff, 0xff, 0xff, 0xff, 0xff, /* 56789:;<=> */
	0xff, 0xff, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11, /* ?@ABCDEFGH */
	0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b, /* IJKLMNOPQR */
	0x1c, 0x1d, 0x1e, 0x1f, 0x20, 0x21, 0x22, 0x23, 0xff, 0xff, /* STUVWXYZ[\ */
	0xff, 0xff, 0xff, 0xff, 0x24, 0x25, 0x26, 0x27, 0x28, 0x29, /* ]^_`abcdef */
	0x2a, 0x2b, 0x2c, 0x2d, 0x2e, 0x2f, 0x30, 0x31, 0x32, 0x33, /* ghijklmnop */
	0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x3a, 0x3b, 0x3c, 0x3d  /* qrstuvwxyz */
};

// The code coms from libtommth
bigIntCatch bigIntReadRadix(bigInteger *a, const char *str, int radix)
{
   bigIntCatch   err;
   bigIntSign  sign = POSITIVE;

   /* make sure the radix is ok */
   if ((radix < 2) || (radix > 64)) {
      return runInvalid;
   }

   /* if the leading digit is a
    * minus set the sign to negative.
    */
   if (*str == '-') {
      ++str;
      sign = NEGATIVE;
   }

   /* set the integer to the default of zero */
   bigIntZero(a);

   /* process each digit of the string */
   while (*str != '\0') {
      /* if the radix <= 36 the conversion is case insensitive  this allows
       numbers like 1AB and 1ab to represent the same  value  */
      uint8_t y;
      char ch = (radix <= 36) ? (char)MP_TOUPPER((int)*str) : *str;
      unsigned pos = (unsigned)(ch - '+');
      if (MP_RADIX_MAP_REVERSE_SIZE <= pos) {
         break;
      }
      y = radixMap_reverse[pos];

	 

      /* if the char was found in the map
       * and is less than the given radix add it
       * to the number, otherwise exit the loop.
       */
      if (y >= radix) {
         break;
      }
      if ((err = bigIntMul_d(a, (bigIntDigit)radix, a)) != runSuccess) {
         return err;
      }
      if ((err = bigIntAddition_d(a, y, a)) != runSuccess) {
         return err;
      }
      ++str;
   }

   /* if an illegal character was found, fail. */
   if ((*str != '\0') && (*str != '\r') && (*str != '\n')) {
      return runInvalid;
   }

   /* the zero's sign is positive */
   if (!isZero(a)) {
      a->sign = sign;
   }
   return runSuccess;
}






int bigIntCountBits(const bigInteger *a)
{
	int     count;
	bigIntDigit q;

	/* shortcut */
	if (isZero(a)) {
		return 0;
	}

	/* get number of digits and add that */
	count = (a->occupied - 1) * DefaultBitOfDigit;

	/* take the last digit and count the bits in it */
	q = a->adp[a->occupied - 1];
	while (q > 0u) {
		++count;
		q >>= 1u;
	}
	return count;
}





void bigIntExchange(bigInteger *a, bigInteger *b)
{
	mathExchange(bigInteger, *a, *b);
}


const char *bigIntCatchor_to_string(bigIntCatch code)
{
	switch (code) {
	case runSuccess:
		return "Successful";
	case runError:
		return "Unknown error";
	case runOutMem:
		return "Out of heap";
	case runInvalid:
		return "Value out of range";
	case runMaxIteration:
		return "Max. iterations reached";
	case runBufOF:
		return "Buffer overflow";
	case runIntOF:
		return "Integer overflow";
	default:
		return "Invalid error code";
	}
}



const char radixMap[] = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz+/";

void nbigIntPrint(const bigInteger *a, const char *name)
{
	char buf[4096];

	//printf("%s: ", name);
	CHECK_OK(mp_to_radix(a, buf, sizeof(buf), NULL, 10));
	printf("%s\n", buf);
}

void bigIntPrint(const bigInteger *a)
{
	nbigIntPrint(a, "");
}


/* reverse an array, occupied for radix code */
void s_reverse(char *s, size_t len)
{
   size_t ix = 0, iy = len - 1u;
   while (ix < iy) {
      mathExchange(char, s[ix], s[iy]);
      ++ix;
      --iy;
   }
}

/* It come from libtommath
 */
bigIntCatch mp_to_radix(const bigInteger *a, char *str, size_t maxlen, size_t *written, int radix)
{
   size_t  digs;
   bigIntCatch  err;
   bigInteger  t;
   bigIntDigit d;
   char   *_s = str;

   /* check range of radix and size*/
   if (maxlen < 2u) {
      return runBufOF;
   }
   if ((radix < 2) || (radix > 64)) {
      return runInvalid;
   }

   /* quick out if its zero */
   if (isZero(a)) {
      *str++ = '0';
      *str = '\0';
      if (written != NULL) {
         *written = 2u;
      }
      return runSuccess;
   }

   if ((err = bigIntInitial_copy(&t, a)) != runSuccess) {
      return err;
   }

   /* if it is negative output a - */
   if (isNegative(&t)) {
      /* we have to reverse our digits later... but not the - sign!! */
      ++_s;

      /* store the flag and mark the number as positive */
      *str++ = '-';
      t.sign = POSITIVE;

      /* subtract a char */
      --maxlen;
   }
   digs = 0u;
   while (!isZero(&t)) {
      if (--maxlen < 1u) {
         /* no more room */
         err = runBufOF;
         goto ERROR_CLEAR;
      }
      if ((err = mp_div_d(&t, (bigIntDigit)radix, &t, &d)) != runSuccess) {
         goto ERROR_CLEAR;
      }


      *str++ = radixMap[d];
      ++digs;
   }
   /* reverse the digits of the string.  In this case _s points
    * to the first digit [excluding the sign] of the number
    */
   s_reverse(_s, digs);

   /* append a NULL so the string is properly terminated */
   *str = '\0';
   digs++;

   if (written != NULL) {
      *written = isNegative(a) ? (digs + 1u): digs;
   }

ERROR_CLEAR:
   bigIntClear(&t);
   return err;
}





/* compare two ints (unsigned) */
comRes bigIntUnCom(const bigInteger *a, const bigInteger *b)
{
	int n;

	/* compare the occupied */
	if (a->occupied != b->occupied) {
		return a->occupied > b->occupied ? GREATER : LESS;
	}

	/* if the occupie is equal, we compare every digit from the most significant digit */
	for (n = a->occupied; n --> 0;) {
		if (a->adp[n] != b->adp[n]) {
			return a->adp[n] > b->adp[n] ? GREATER : LESS;
		}
	}

	return EQUAL;
}


comRes bigIntSignCom(const bigInteger *a, const bigInteger *b)
{
	/* sign compare is  based on sign , positive integer is bigger than negative one*/
	if (a->sign != b->sign) {
		return isNegative(a) ? LESS : GREATER;
	}

	/* if negative compare opposite direction */
	if (isNegative(a)) {
		mathExchange(const bigInteger *, a, b);
	}

	return bigIntUnCom(a, b);
}





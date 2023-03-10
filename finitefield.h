#ifndef finitefield_h
#define finitefield_h

#include <stdlib.h>
#include<stdio.h>
#include<string.h>
#include <stdint.h>
#include <limits.h>
#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>
#include <stdarg.h>
#include <ctype.h>


typedef unsigned int       uSignInt;  
#define DEFAULT_PRECII 32

/* the default radix is 2^15*/
#define DefaultBitOfDigit 15 // radix 2^15

typedef uint32_t             bigIntDigit; 


#define isZero(a) ((a)->occupied == 0)
#define isNegative(a)  ((a)->sign == NEGATIVE)
#define isEven(a) (((a)->occupied == 0) || (((a)->adp[0] & 1u) == 0u))
#define isOdd(a)  (!isEven(a))


#define doFree(mem, size)                free(mem)
#define REALLOC(mem, oldsize, newsize) realloc((mem), (newsize))
#define doFree_DIGS(mem, digits) doFree((mem), sizeof (bigIntDigit) * (size_t)(digits))

#define mathMIN(x, y) (((x) < (y)) ? (x) : (y))
#define mathMax(x, y) (((x) > (y)) ? (x) : (y))

#define SIZE_OF_BITS(type)    ((size_t)CHAR_BIT * sizeof(type))
#define mathMIN_DIGIT_COUNT mathMax(3, (((int)SIZE_OF_BITS(uint64_t) + DefaultBitOfDigit) - 1) / DefaultBitOfDigit)

/* ANDR_1 is mod R, and it is equal to & R-1 , AND with R-1*/
#define ANDR_1          ((((bigIntDigit)1)<<((bigIntDigit)DefaultBitOfDigit))-((bigIntDigit)1))

#define mathExchange(t, a, b) do { t _c = a; a = b; b = _c; } while (0)

#define mathMax_DIGIT_COUNT ((INT_MAX - 2) / DefaultBitOfDigit)

#define CHECK_OK(x) do { bigIntCatch err; if ((err = (x)) != runSuccess) { fprintf(stderr, "%d: CHECK_OK(%s) failed: %s\n", __LINE__, #x, bigIntCatchor_to_string(err)); exit(EXIT_FAILURE); } }while(0)


#define CALLOC(nmemb, size)            calloc((nmemb), (size))




#define MP_DIGIT_MAX       USHRT_MAX

#define RADIX              (MP_DIGIT_MAX+1)




/* Macros for accessing the bigInteger internals           */
#define  SIGN(MP)     ((MP)->sign)
#define  USED(MP)     ((MP)->occupied)
#define  ALLOC(MP)    ((MP)->alloc)
#define  DIGITS(MP)   ((MP)->adp)
#define  DIGIT(MP,N)  (MP)->adp[(N)]

#define  CARRYOUT(W)  ((W)>>DIGIT_BIT)
#define  ACCUM(W)     ((W)&MP_DIGIT_MAX)
#define DIGIT_BIT         DefaultBitOfDigit
#define DIGIT_MAX         MP_DIGIT_MAX

#define  ARGCHK(X,Y)  {if(!(X)){return (Y);}}
#define MAX_RADIX         64
#define MP_DEFPREC    64 /* default precision, in digits        */

static unsigned int s_mp_defprec = MP_DEFPREC;



#define runOutMemSET 0
#define runOutMemCPY 0

#if runOutMemSET == 0
#define  s_mp_setz(adp, count) \
{int ix;for(ix=0;ix<(count);ix++)(adp)[ix]=0;}
#else
#define  s_mp_setz(adp, count) memset(adp, 0, (count) * sizeof(bigIntDigit))
#endif /* runOutMemSET */

#if runOutMemCPY == 0
#define  s_bigIntCopy(sp, adp, count) \
{int ix;for(ix=0;ix<(count);ix++)(adp)[ix]=(sp)[ix];}
#else
#define  s_bigIntCopy(sp, adp, count) memcpy(adp, sp, (count) * sizeof(bigIntDigit))
#endif /* runOutMemCPY */

#define  s_mp_alloc(nb, ni)  calloc(nb, ni)
#define  s_mp_free(ptr) {if(ptr) free(ptr);}
#define MP_TOUPPER(c) ((((c) >= 'a') && ((c) <= 'z')) ? (((c) + 'A') - 'a') : (c))
#define MP_RADIX_MAP_REVERSE_SIZE 80u

#define bigIntSquareS(a, b) generMul((a), (a), (b))

#define mathMax_COMBA            (int)(1uL << (SIZE_OF_BITS(uSignInt) - (2u * (size_t)DefaultBitOfDigit)))
#define MP_WARRAY               (int)(1uL << ((SIZE_OF_BITS(uSignInt) - (2u * (size_t)DefaultBitOfDigit)) + 1u))


#  define MUL_KARATSUBA_CUTOFF 8
#  define SQR_KARATSUBA_CUTOFF 12


#define mp_decr(a) bigIntSubtraction_d((a), 1u, (a))







typedef enum {
	POSITIVE = 0,   /* positive */
	NEGATIVE = 1     /* negative */
} bigIntSign;

/* construct multi precision integer structure */
typedef struct  {
	int occupied, alloc;
	bigIntSign sign;
	bigIntDigit *adp;
} bigInteger;

typedef enum {
	LESS = -1,    
	EQUAL = 0,     
	GREATER = 1      
} comRes; /* comapre result, return less, equal or greater */

typedef enum {
	runSuccess  = 0,   
	runError   = -1,  /* unknown error */
	runOutMem   = -2,  
	runInvalid   = -3,  /* invalid input */
	runMaxIteration  = -4,  
	runBufOF   = -5,  /* buffer overflow, supplied buffer too small */
	runIntOF   = -6   /* bigInteger overflow, too many digits */
} bigIntCatch;




//----------------
bigIntCatch bigIntInitial(bigInteger *a);

//--------------------
void nbigIntPrint(const bigInteger *a, const char *name);
void bigIntPrint(const bigInteger *a);
void s_reverse(char *s, size_t len);
bigIntCatch mp_to_radix(const bigInteger *a, char *str, size_t maxlen, size_t *written, int radix);
bigIntCatch bigIntInitial_copy(bigInteger *a, const bigInteger *b);
bigIntCatch bigIntInitialGiv(bigInteger *a, int size);
bigIntCatch bigIntCopy(const bigInteger *a, bigInteger *b);
void bigIntClear(bigInteger *a);
bigIntCatch bigIntIncrease(bigInteger *a, int size);
void bigIntZeroDigits(bigIntDigit *d, int digits);
void bigIntCopyDigits(bigIntDigit *d, const bigIntDigit *s, int digits);
bigIntCatch mp_div_d(const bigInteger *a, bigIntDigit b, bigInteger *c, bigIntDigit *d);
void bigIntAdjust(bigInteger *a);
void bigIntExchange(bigInteger *a, bigInteger *b);
const char *bigIntCatchor_to_string(bigIntCatch code);
//-------------


bigIntCatch bigIntReadRadix(bigInteger *a, const char *str, int radix);
void bigIntZero(bigInteger *a);
bigIntCatch bigIntMul_d(const bigInteger *a, bigIntDigit b, bigInteger *c);
bigIntCatch bigIntAddition_d(const bigInteger *a, bigIntDigit b, bigInteger *c);
bigIntCatch bigIntSubtraction_d(const bigInteger *a, bigIntDigit b, bigInteger *c);

//--------------------------

bigIntCatch bigIntKaratsubaMul(const bigInteger *a, const bigInteger *b, bigInteger *c);
bigIntCatch bigIntUnAddition(const bigInteger *a, const bigInteger *b, bigInteger *c);
bigIntCatch bigIntAddition(const bigInteger *a, const bigInteger *b, bigInteger *c);
bigIntCatch bigIntUnSubtraction(const bigInteger *a, const bigInteger *b, bigInteger *c);
bigIntCatch bigIntLeftShift(bigInteger *a, int b);
comRes bigIntUnCom(const bigInteger *a, const bigInteger *b);

//---------------

bigIntCatch generMul(const bigInteger *a, const bigInteger *b, bigInteger *c);

bigIntCatch bigIntSchoolMul(const bigInteger *a, const bigInteger *b, bigInteger *c, int digs);



//----------------
bigIntCatch bigIntCombaMul(const bigInteger *a, const bigInteger *b, bigInteger *c, int digs);


//------------------

bigIntCatch bigIntGenMod(const bigInteger *a, const bigInteger *b, bigInteger *c);
bigIntCatch bigIntSubtraction(const bigInteger *a, const bigInteger *b, bigInteger *c);
comRes bigIntSignCom(const bigInteger *a, const bigInteger *b);
bigIntCatch bigIntMod2k(const bigInteger *a, int b, bigInteger *c);


//-------------
bigIntCatch mp_div(const bigInteger *a, const bigInteger *b, bigInteger *c, bigInteger *d);

bigIntCatch bigIntDiv2k(const bigInteger *a, int b, bigInteger *c, bigInteger *d);
bigIntCatch bigInt_school_div(const bigInteger *a, const bigInteger *b, bigInteger *c, bigInteger *d);
comRes bigIntSignCom_d(const bigInteger *a, bigIntDigit b);
int bigIntCountBits(const bigInteger *a);


//----------------

bigIntCatch bigIntInitial_multi(bigInteger *mp, ...);
bigIntCatch bigIntMul2k(const bigInteger *a, int b, bigInteger *c);
void bigIntClear_multi(bigInteger *mp, ...);
void bigIntRightShift(bigInteger *a, int b);







//--------------------


void bigIntZeroBuff(void *mem, size_t size);







//----------------


int correctnessNew(bigInteger* data,bigInteger* p);
void testFp2();
void testFp3();
bigIntCatch testCorrect_Method2();
void setRandBigInt(bigInteger *x);
void Fp2correctness();
void Fp3correctness();

void fastMul(const bigInteger *a, const bigInteger *b, bigInteger *c);
void testFp4_2();
void Fp4correctness();
void testFp6_3over2();
void Fp6_3over2correctness();
void testFp6_2over3();
void Fp6_2over3correctness();
void testFp12_2over2over3();
void Fp12_2over2over3correctness();
void testFp12_2over3over2();
void Fp12_2over3over2correctness();
void testFp12_3over2over2();
void Fp12_3over2over2correctness();

void testFp4_direct();
void Fp4_directcorrectness();
void testFp12_3overDirect4();
void Fp12_3overDirect4correctness();
void Fp2_Cycles();
void Fp3_Cycles();
void Fp4_2over2Cycles();
void Fp4_DirectCycles();
void Fp6_3over2Cycles();
void Fp6_2over3Cycles();
void Fp12_3over4Cycles();
void Fp12_3over2over2Cycles();
void Fp12_2over3over2Cycles();
void Fp12_2over2over3Cycles();

#endif
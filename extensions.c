

#include "extensions.h"

#include <stdlib.h>
#include<stdio.h>
#include<string.h>
#include <time.h>
#include "finitefield.h"


#include <stdio.h>
#include <time.h>
#include <unistd.h>
#include <sys/time.h>
#include "x86estimate.h"




#ifdef IOWNANATHLON
#include <unistd.h>
#define SLEEP sleep(4)
#else
#define SLEEP
#endif

#ifdef LTM_TIMING_REAL_RAND
#define LTM_TIMING_RAND_SEED  time(NULL)
#else
#define LTM_TIMING_RAND_SEED  23
#endif

#ifndef MP_VERSION
#define MP_TIMING_VERSION
#else
#define MP_TIMING_VERSION "-" MP_VERSION
#endif

#define CHECK_OK(x) do { bigIntCatch err; if ((err = (x)) != runSuccess) { fprintf(stderr, "%d: CHECK_OK(%s) failed: %s\n", __LINE__, #x, bigIntCatchor_to_string(err)); exit(EXIT_FAILURE); } }while(0)




#define DO2(x) do { bigIntCatch err = x; err = x; (void)err; }while(0)
#define DO4(x) DO2(x); DO2(x)
#define DO8(x) DO4(x); DO4(x)

#if 1
#define DO(x) DO2(x)
#else
#define DO(x) DO8(x); DO8(x)
#endif

#ifdef TIMING_NO_LOGS
#define FOPEN(a, b)        NULL
#define FPRINTF(a,b,c,d)
#define FFLUSH(a)
#define FCLOSE(a)          (void)(a)
#define PRINTLN(fm,b,n,m)  printf(fm "\n", b, n, m)
#else
#define FOPEN(a,b)         fopen(a,b)
#define FPRINTF(a,b,c,d)   fprintf(a,b,c,d)
#define FFLUSH(a)          fflush(a)
#define FCLOSE(a)          fclose(a)
#define PRINTLN(fm,b,n,m)  do { printf("\r" fm, b, n, m); fflush(stdout); }while(0)
#endif






#define NFp 2




extern bigInteger p;
extern bigInteger b;

void passModPrime(){

  bigIntInitial(&p);
  bigIntReadRadix(&p,  "218297830370226601612193514776502382704221475011035725792624279635059316315225569375126760584265176077347911285544462735949991646330887",  10);
  bigIntInitial(&b);
  bigIntReadRadix(&b,  "69483102369481741238779539457487162259686267605807805821845161466786040355659291428116315259606973237527239712986696166788515112157093",  10);

}





/* element in Fp2 always have two coefficients,
   element in Fp3 always have three coefficients
   len is the number of the coefficients
*/
void bigIntIniCoefficient(bigInteger coef[],int len){

	for (int i=0;i<len;i++)
	{
		bigIntInitial(&coef[i]);
		bigIntReadRadix(&coef[i],  "0",  10);
	}

}



void setRand_bigInt_array(bigInteger x[]){

	char s[150];

	bigIntIniCoefficient(x,NFp);

	int len;

	for (int i=0;i<NFp;i++)
	{
		len= rand() % 134;     // the length of each coefficient is not larger than 10^100

		for (int j=0;j<len;j++)
		{
			s[j]='0'+(rand() % 10);
		}
		s[len]='\0';

		if (len>0)
		{
			bigIntReadRadix(&x[i],  s,  10);
		}
	}
}


void  Fp2mul(bigInteger ele1[],bigInteger ele2[],bigInteger res[]){

    /* Request memory space to store intermediate values generated during computation
	*/
	bigInteger v[2];  
	bigIntIniCoefficient(v,2);	
	bigInteger r[2];
	bigIntIniCoefficient(r,2);
	passModPrime(); // pass in the value of prime number

    /* The arrays ele1 and ele2 store the coefficients of two polynomials, respectively
	  eg: ele1[0] + ele1[1]*x,  ele2[0] + ele2[1]*x,
	  The coefficients of the resulting polynomial are stored in the array res.
	 */	
    generMul(&ele1[0],&ele2[0],&v[0]); // v0 = a0*b0
	bigIntGenMod(&res[0], &p,&res[0]);
    generMul(&ele1[1],&ele2[1],&v[1]); // v1 = a1*b1	
    bigIntGenMod(&res[0], &p,&res[0]);

	/* result res0 = v0- v1 */
	bigIntSubtraction(&v[0],&v[1],&res[0]);
	bigIntGenMod(&res[0], &p,&res[0]); 
	
    /* res1 = (a0+a1)*(b0+b1) - v0 -v1 */
	bigIntAddition(&ele1[0],&ele1[1],&r[0]); //r0 = a0 + a1
	bigIntAddition(&ele2[0],&ele2[1],&r[1]); //r1 = b0 + b1
	generMul(&r[0], &r[1], &res[1]); // 
	bigIntSubtraction(&res[1],&v[0],&res[1]);  
	bigIntSubtraction(&res[1],&v[1],&res[1]);
    bigIntGenMod(&res[1], &p,&res[1]);
     
    return ;
}



void Fp3mul(bigInteger ele1[],bigInteger ele2[],bigInteger res[]){

	 /* Request memory space to store intermediate values generated during computation
	  */
	passModPrime();
	bigIntDigit beta = 2u ;
	bigInteger v[3];
	bigIntIniCoefficient(v,3);
	bigInteger r[3];
	bigIntIniCoefficient(r,3);
	

	/* if the irreducible polynomial is change, use the parameter of beta, if not, is -2.
	   x^3 + 2 is the most simple irreducible polynomial
	*/

    // v0 = a0*b0, v1 = a1*b1, v2 = a2*b2
	for (int i=0;i<3;i++)
	{
		generMul(&ele1[i],&ele2[i],&v[i]);
		bigIntGenMod(&v[i], &p, &v[i]);
	}

	/*---------------compute res0 ----------------*/
	bigIntAddition(&ele1[1],&ele1[2],&r[0]); // r0 = a1 + a2
	bigIntAddition(&ele2[1],&ele2[2],&r[1]); // r1 = b1 + b2
	generMul(&r[0],&r[1],&r[2]);
	bigIntGenMod(&r[2],&p,&r[2]);  // r[2] = (a1+a2)*(b1+b2) mod p
    bigIntSubtraction(&r[2],&v[1],&r[2]);
	bigIntSubtraction(&r[2],&v[2],&r[2]);
	bigIntMul_d(&r[2],beta,&r[2]);
	bigIntSubtraction(&v[0],&r[2],&res[0]);//res0 = v0 - beta[(a1+a2)*(b1+b2) - v1 - v2]
	bigIntGenMod(&res[0],&p,&res[0]); // res0

	/*---------------compute res1 ----------------*/
	bigIntAddition(&ele1[0],&ele1[1],&r[0]); // r0 = a0 + a1
	bigIntAddition(&ele2[0],&ele2[1],&r[1]); // r1 = b0 + b1
	generMul(&r[0],&r[1],&r[2]);   // r[2] = (a0+a1)*(b0+b1)
	bigIntSubtraction(&r[2],&v[0],&r[2]);// res1 = (a0+a1)*(b0+b1) - v0 -v1 -beta*v2
	bigIntSubtraction(&r[2],&v[1],&r[2]);
	bigIntMul_d(&v[2],beta,&r[0]);
	bigIntSubtraction(&r[2],&r[0],&res[1]);
	bigIntGenMod(&res[1],&p,&res[1]); // res1

    /*---------------compute res2 ----------------*/
    bigIntAddition(&ele1[0],&ele1[2],&r[0]); // r0 = a0 + a2
	bigIntAddition(&ele2[0],&ele2[2],&r[1]); // r1 = b0 + b2
    generMul(&r[0],&r[1],&r[2]);   // r2 = (a0+a2)*(b0+b2)
	bigIntSubtraction(&r[2],&v[0],&r[2]);
	bigIntAddition(&r[2],&v[1],&r[2]);
	bigIntSubtraction(&r[2],&v[2],&res[2]); // res2 = (a0+a2)*(b0+b2) - v0 + v1 -v2
	bigIntGenMod(&res[2],&p,&res[2]);

	return ;

}



/*quartic is quadratic over quadratic , you should set the define  nfp  = 2
  the form of an element in the fp^2 over fp^2 is like:   (a + bx) + (c + dx) y
  the result is C0 and C1, C0[0] = a, C0[1] = b, C1[0] = c, C1[1] = d
*/


void Fp4_2input(bigInteger A0[], bigInteger A1[], bigInteger B0[], bigInteger B1[], bigInteger res[]){
    

     /* Request memory space to store intermediate values generated during computation
	  */
	passModPrime();
	bigIntDigit two = 2u;
	bigInteger v0[2];
    bigInteger v1[2];
    bigInteger temp0[2];
    bigInteger temp1[2];
	bigInteger temp2[2];
	bigIntIniCoefficient(v0,2);
	bigIntIniCoefficient(v1,2);
	bigIntIniCoefficient(temp0,2); 
	bigIntIniCoefficient(temp1,2); 
	bigIntIniCoefficient(temp2,2); 
     
    /* v0 = a0*b0, v1 = a1*b1  
	the result of multiplication in Fp2 store in v0 and v1 respectively
    */
	Fp2mul(A0,B0,v0); 
	Fp2mul(A1,B1,v1); 
	
	//the result is C0 + C1*Y, firstly, we compute C0 =  C0[0] + C0[1]*x, that is the res[0], res[1]

    bigIntMul_d(&v1[1], two, &temp0[0]);// t0[0] = 2V1[1]
    bigIntAddition(&v0[0],&temp0[0],&temp0[0]); //t0[0] = VO[0]+2V1[1]
    bigIntSubtraction(&temp0[0], &v1[0],&res[0]); // res[0] = V0[0] - V1[0] + 2V1[1]
	bigIntGenMod(&res[0],&p,&res[0]);

	bigIntMul_d(&v1[0],two, &temp0[1]); //t0[1] = 2V1[0]
    bigIntSubtraction(&v0[1], &temp0[1],&res[1]); //
	bigIntSubtraction(&res[1], &v1[1],&res[1]); // the coefficient of x
	bigIntGenMod(&res[1],&p,&res[1]);

    //secondly, we compute C1 = C1[0] + c1[1]*x, that is the res[2], res[3]
	bigIntAddition(&A0[0],&A1[0],&temp1[0]); // A0+A1
	bigIntAddition(&A0[1],&A1[1],&temp1[1]);
	bigIntAddition(&B0[0],&B1[0],&temp2[0]); // B0+B1
	bigIntAddition(&B0[1],&B1[1],&temp2[1]);
	Fp2mul(temp1,temp2,temp0); // (A0+A1)*(B0+B1)
	bigIntSubtraction(&temp0[0],&v0[0],&res[2]); // (A0+A1)(B0+B1) - V0 -V1
	bigIntSubtraction(&temp0[1],&v0[1],&res[3]);
	bigIntSubtraction(&res[2],&v1[0],&res[2]);
	bigIntSubtraction(&res[3],&v1[1],&res[3]);
	bigIntGenMod(&res[2],&p,&res[2]);
	bigIntGenMod(&res[3],&p,&res[3]);

	return ;



}




void Fp6_3over2input(bigInteger A0[],bigInteger A1[],bigInteger A2[],bigInteger B0[],bigInteger B1[],bigInteger B2[],bigInteger res[]){
    
	passModPrime(); // initial and set the prime p
    bigInteger temp0[2];
    bigInteger temp1[2];
	bigInteger temp2[2];
	bigIntIniCoefficient(temp0,2); // Store some data for subsequent computing
	bigIntIniCoefficient(temp1,2);
	bigIntIniCoefficient(temp2,2);
	bigIntDigit two = 2u;

    // intinial the VO, V1 ,V2 , THEN V0 = A0*B0, V1 = A1*B1, V2 = A2*B2
    bigInteger v0[2];
    bigInteger v1[2];
	bigInteger v2[2];
	bigIntIniCoefficient(v0,2); 
	bigIntIniCoefficient(v1,2);
	bigIntIniCoefficient(v2,2);

	Fp2mul(A0,B0,v0);
    Fp2mul(A1,B1,v1);
    Fp2mul(A2,B2,v2);

	/*
	-------------------the following part is compute the C0----------------------------------------------------
	*/
    // temp2 = (A1+A2)*(B1+B2)
	bigIntAddition(&A1[0],&A2[0],&temp0[0]);
	bigIntAddition(&A1[1],&A2[1],&temp0[1]); // temp0 = A1+A2
    bigIntAddition(&B1[0],&B2[0],&temp1[0]); 
	bigIntAddition(&B1[1],&B2[1],&temp1[1]); // temp1 = B1+B2
	Fp2mul(temp0,temp1,temp2);

	// temp2 = (temp2 - v1 - v2)*2
	bigIntSubtraction(&temp2[0],&v1[0],&temp2[0]);
    bigIntSubtraction(&temp2[1],&v1[1],&temp2[1]);
    bigIntSubtraction(&temp2[0],&v2[0],&temp2[0]);
    bigIntSubtraction(&temp2[1],&v2[1],&temp2[1]);
	bigIntMul_d(&temp2[0],two, &temp2[0]);
	bigIntMul_d(&temp2[1],two, &temp2[1]);

    // (the constant term) C0 =  V0 - t2 = V0 − 2*((A1+A2)(B1+B2)−V1−V2)
    bigIntSubtraction(&v0[0],&temp2[0],&res[0]);
	bigIntGenMod(&res[0],&p,&res[0]);
	bigIntSubtraction(&v0[1],&temp2[1],&res[1]);
	bigIntGenMod(&res[1],&p,&res[0]);

	/*
	-------------------the following part is compute the C1----------------------------------------------------
	*/
    // temp2 = (A0+A1)*(B0+B1)
	bigIntAddition(&A0[0],&A1[0],&temp0[0]);
	bigIntAddition(&A0[1],&A1[1],&temp0[1]); // temp0 = A0+A1
    bigIntAddition(&B0[0],&B1[0],&temp1[0]); 
	bigIntAddition(&B0[1],&B1[1],&temp1[1]); // temp1 = B0+B1
    Fp2mul(temp0,temp1,temp2);

    // temp2 = temp2 - v0 - v1
	bigIntSubtraction(&temp2[0],&v0[0],&temp2[0]);
    bigIntSubtraction(&temp2[1],&v0[1],&temp2[1]);
    bigIntSubtraction(&temp2[0],&v1[0],&temp2[0]);
    bigIntSubtraction(&temp2[1],&v1[1],&temp2[1]);

    // temp2 = temp2 - 2V2 so: C1 = (A0 +A1)(B0 +B1)− V0 − V1 − 2V2
	bigIntMul_d(&v2[0],two,&temp0[0]); //temp0 = 2V2, and C1 = t2-t1, THEN DO mod and print the result
    bigIntMul_d(&v2[1],two,&temp0[1]);
	bigIntSubtraction(&temp2[0],&temp0[0],&res[2]);
	bigIntGenMod(&res[2],&p,&res[2]);
    bigIntSubtraction(&temp2[1],&temp0[1],&res[3]);
	bigIntGenMod(&res[3],&p,&res[3]);

    /*
	-------------------the following part is compute the C2----------------------------------------------------
	*/

    // temp2 = (A0+A2)*(B0+B2)
	bigIntAddition(&A0[0],&A2[0],&temp0[0]);
	bigIntAddition(&A0[1],&A2[1],&temp0[1]); // temp0 = A0+A2
    bigIntAddition(&B0[0],&B2[0],&temp1[0]); 
	bigIntAddition(&B0[1],&B2[1],&temp1[1]); // temp1 = B0+B2
    Fp2mul(temp0,temp1,temp2);

	// temp2 - V0 + V1 - V2 and then DO mod
    bigIntSubtraction(&temp2[0],&v0[0],&temp2[0]);
    bigIntSubtraction(&temp2[1],&v0[1],&temp2[1]);
    bigIntAddition(&temp2[0],&A1[0],&temp2[0]);
	bigIntAddition(&temp2[1],&A1[1],&temp2[1]);
	bigIntSubtraction(&temp2[0],&v2[0],&res[4]);
	bigIntGenMod(&res[4],&p,&res[4]);
    bigIntSubtraction(&temp2[1],&v2[1],&res[5]);
	bigIntGenMod(&res[5],&p,&res[5]);

	return ;

}




void Fp6_2over3input(bigInteger A0[], bigInteger A1[], bigInteger B0[], bigInteger B1[], bigInteger res[]){
    

    passModPrime(); // initial and set the prime p

	/* the input is Fp6 elements, which is A0 + A1*y and B0 + B1*y, 
	 res is the form of (a + b*x + c*x^2) + (d + e*x + f*x^2)*y
     hence, the length of res are 6, res[0] = a, ..., res[5] = f
	*/

    /*request memory space to store intermediate values generated during computation
	  */
	bigInteger v0[3];
	bigInteger v1[3];
	bigIntIniCoefficient(v0,3);
	bigIntIniCoefficient(v1,3);
	bigInteger temp0[3];
	bigInteger temp1[3];
	bigInteger temp2[3];
	bigIntIniCoefficient(temp0,3);
	bigIntIniCoefficient(temp1,3);
	bigIntIniCoefficient(temp2,3);

	/*compute the V0 AND V1  */
    Fp3mul(A0,B0,v0);
	Fp3mul(A1,B1,v1);
	
    // the constant term C0
	for(int i = 0; i< 3; i++){
      bigIntSubtraction(&v0[i],&v1[i],&res[i]);
	  bigIntGenMod(&res[i],&p,&res[i]);
	}

    // the y's coefficient C1
    for(int i = 0; i< 3; i++){
      bigIntAddition(&A0[i],&A1[i],&temp0[i]); // (A0 + A1)
	  bigIntAddition(&B0[i],&B1[i],&temp1[i]); // (B0 + B1) 
	}
	Fp3mul(temp0,temp1,temp2); // (A0 + A1)*(B0 + B1)
	for(int i = 0; i< 3; i++){
      bigIntSubtraction(&temp2[i],&v0[i],&res[i+3]); // (A0 + A1)*(B0 + B1) - VO - V1
      bigIntSubtraction(&temp2[i],&v1[i],&res[i+3]);
	  bigIntGenMod(&res[i+3],&p,&res[i+3]); //do mod, check
	}

	return ;

}

void   Fp12_2over2over3(bigInteger A00[],bigInteger A01[],bigInteger A10[],bigInteger A11[], bigInteger B00[],bigInteger B01[],bigInteger B10[], bigInteger B11[], bigInteger res[]){
 
 /* 
    two elements are A0 + A1*z AND b0+b1*z, A0 = A00 + A00*y, A1 = A10 + A11*y,
    B0 = B00 + B01*y, B1 = B10 + B11*y
	A00,... B11 are the elements in Fp3(cubic)
 */
 /* 
    request memory space to store intermediate values generated during computation
  */
    bigInteger temp0[3];
	bigInteger temp1[3];
	bigInteger temp2[3];
	bigInteger temp3[3];
    bigIntIniCoefficient(temp0,3);
	bigIntIniCoefficient(temp1,3);
	bigIntIniCoefficient(temp2,3);
	bigIntIniCoefficient(temp3,3);
	passModPrime();
	bigInteger V00[6];
	bigIntIniCoefficient(V00, 6);
	bigInteger V11[6];
	bigIntIniCoefficient(V11, 6);
	bigInteger CZ[6];
	bigIntIniCoefficient(CZ, 6);

	Fp6_2over3input(A00,A01,B00,B01,V00); // compute A0*B0
    Fp6_2over3input(A10,A11,B10,B11,V11); // compute A1*B1
    
    // compute C0 = A0*B0 - A1*B1, we store C0 from res[0] to res[5]
	for(int i = 0; i < 6; i++){
		bigIntSubtraction(&V00[i],&V11[i],&res[i]);
		bigIntGenMod(&res[i],&p,&res[i]);
	}
	//  C1 = (A0 + A1)*(B0 + B1) - V0 - V1

	for(int i=0; i<3;i++){
        bigIntAddition(&A00[i],&A10[i],&temp0[i]); // A00+A10     A0+A1 is temp0 + temp1
        bigIntAddition(&A01[i],&A11[i],&temp1[i]); // A01+A11
		bigIntAddition(&B00[i],&B10[i],&temp2[i]); // B00+B10     B0+B1 is temp2 + temp3
        bigIntAddition(&B01[i],&B11[i],&temp3[i]); // B01+B11
	} 

	Fp6_2over3input(temp0,temp1,temp2,temp3,CZ);// (A0+A1)*(B0+B1)

	// (A0+A1)*(B0+B1)-V0-V1, we store C1 from res[6] tO res[11]
    for(int i = 0; i<6; i++){
		bigIntSubtraction(&CZ[i],&V00[i],&res[i+6]);
		bigIntSubtraction(&res[i+6],&V11[i],&res[i+6]);
		bigIntGenMod(&res[i+6],&p,&res[i+6]);
	}
	return ;

}


void Fp12_2over3over2(bigInteger A00[],bigInteger A01[],bigInteger A02[],bigInteger A10[], bigInteger A11[],bigInteger A12[],bigInteger B00[], bigInteger B01[],bigInteger B02[], bigInteger B10[], bigInteger B11[], bigInteger B12[], bigInteger res[]){
 
 /* two elements are a0 + a1*z AND b0+b1*z, a0 = a00 + a01*y+ a02*y^2, a1 = a10 + a11*y + a12*y^2,
    b0 = b00 + b01*y + b02*y^2, b1 = b10 + b11*y + b12*y^2
	a00,... b12 are the elements in fp2
  */
    // NFp = 2
    bigInteger temp0[2];
	bigInteger temp1[2];
	bigInteger temp2[2];
	bigInteger temp3[2];
    bigInteger temp4[2];
	bigInteger temp5[2];

    bigIntIniCoefficient(temp0,2);
	bigIntIniCoefficient(temp1,2);
	bigIntIniCoefficient(temp2,2);
	bigIntIniCoefficient(temp3,2);
    bigIntIniCoefficient(temp4,2);
	bigIntIniCoefficient(temp5,2);
	passModPrime();

    bigInteger V00[6]; //A0*B0
	bigIntIniCoefficient(V00, 6);
	bigInteger V11[6]; //A1*B1
	bigIntIniCoefficient(V11, 6);
	bigInteger CZ[6];
	bigIntIniCoefficient(CZ, 6);

	
	Fp6_3over2input(A00,A01,A02,B00,B01,B02,V00);
    Fp6_3over2input(A10,A11,A12,B10,B11,B12,V11);

	//the result is like C0+C1*z form, (a+b*x)+(c+d*x)*y+(e+f*x)*y^2 + ((g+h*x)+(i+j*x)*y+(k+l*x)*y^2)*z

    // the c0
	for(int i = 0; i < 6; i++){
		bigIntSubtraction(&V00[i],&V11[i],&res[i]);
		bigIntGenMod(&res[i],&p,&res[i]);
	}

	// the c1 (A0 + A1)*(B0 + B1) - V0 - V1
	// A0 + A1 = A00 + A01*y + A02*y^2 + A10 + A11*y + A12*y^2;   B0 + B1 = B00 + B01*y + B02*y^2 + B10 + B11*y + B12*y^2;
	for(int i=0; i<2;i++){
        bigIntAddition(&A00[i],&A10[i],&temp0[i]); // A00+A10
        bigIntAddition(&A01[i],&A11[i],&temp1[i]); // A01+A11
		bigIntAddition(&A02[i],&A12[i],&temp2[i]); // A02+A12
		bigIntAddition(&B00[i],&B10[i],&temp3[i]); // B00+B10
        bigIntAddition(&B01[i],&B11[i],&temp4[i]); // B01+B11
        bigIntAddition(&B02[i],&B12[i],&temp5[i]); // B02+B12
	}
	
	Fp6_3over2input(temp0,temp1,temp2,temp3,temp4,temp5,CZ);// (A0+A1)*(B0+B1)

	// (A0+A1)*(B0+B1)-V0-V1
    for(int i = 0; i<6; i++){
		bigIntSubtraction(&CZ[i],&V00[i],&res[i+6]);
		bigIntSubtraction(&res[i+6],&V11[i],&res[i+6]);
		bigIntGenMod(&res[i+6],&p,&res[i+6]);
	}
	return;

	//printf("the computing in 2over3over2 has completed !!! \n");

}




void Fp12_3over2over2(bigInteger A00[],bigInteger A01[],bigInteger A10[],bigInteger A11[], bigInteger A20[],bigInteger A21[],bigInteger B00[], bigInteger B01[],bigInteger B10[], bigInteger B11[], bigInteger B20[], bigInteger B21[], bigInteger res[]){
 
 /* two elements are a0 + a1*z + a2*z^2 AND b0 + b1*z + b2*z^2 . 
    a0 = a00 + a01*y, a1 = a10 + a11*y, a2 = a20 + a21*y
    b0 = b00 + b01*y, b1 = b10 + b11*y, b2 = b20 + b21*y
	a00,... b21 are the elements in fp2
  */
    // NFp = 2
    bigInteger temp0[2];
	bigInteger temp1[2];
	bigInteger temp2[2];
	bigInteger temp3[2];
    bigIntIniCoefficient(temp0,2);
	bigIntIniCoefficient(temp1,2);
	bigIntIniCoefficient(temp2,2);
	bigIntIniCoefficient(temp3,2);


	bigIntDigit two = 2u; 
	passModPrime();

    //A0*B0
	bigInteger V00[4];
	bigIntIniCoefficient(V00, 4);

    //A1*B1
    bigInteger V11[4];
	bigIntIniCoefficient(V11, 4);

	//A2*B2
    bigInteger V22[4];
	bigIntIniCoefficient(V22, 4);


	bigInteger V12[4];
	bigIntIniCoefficient(V12, 4);


	bigInteger V01[4];
	bigIntIniCoefficient(V01, 4);

	bigInteger V02[4];
	bigIntIniCoefficient(V02,4);

	Fp4_2input(A00,A01,B00,B01,V00);

    Fp4_2input(A10,A11,B10,B11,V11);
  
    Fp4_2input(A20,A21,B20,B21,V22);


    // (A1+A2)*(B1+B2)
	for(int i = 0; i<2; i++){
		bigIntAddition(&A10[i],&A20[i],&temp0[i]); //A1 + A2
        bigIntAddition(&A11[i],&A21[i],&temp1[i]);
		bigIntAddition(&B10[i],&B20[i],&temp2[i]); //B1 + B2
        bigIntAddition(&B21[i],&B21[i],&temp3[i]);
	}
	
	Fp4_2input(temp0,temp1,temp2,temp3,V12);
	
    // CO = V0 - 2((A1+A2)*(B1+B2)-V1-V2)
	for(int i = 0; i<4;i++){
		bigIntSubtraction(&V12[i],&V11[i],&V12[i]);
		bigIntSubtraction(&V12[i],&V22[i],&V12[i]);
		bigIntMul_d(&V12[i],two,&V12[i]);
		bigIntSubtraction(&V00[i],&V12[i],&res[i]);
		bigIntGenMod(&res[i],&p,&res[i]);
	}

/*---------------------------------------------------------------------------------*/
    // (A0+A1)*(B0+B1)


	for(int i = 0; i<2; i++){
		bigIntAddition(&A00[i],&A10[i],&temp0[i]); //A0 + A1
        bigIntAddition(&A01[i],&A11[i],&temp1[i]);
		bigIntAddition(&B00[i],&B10[i],&temp2[i]); //B0 + B1
        bigIntAddition(&B01[i],&B11[i],&temp3[i]);
	}
	
	Fp4_2input(temp0,temp1,temp2,temp3,V01);
    

    // C1 = (A0+A1)*(B0+B1)-V0-V1-2V2
    for(int i = 0; i<4; i++){
		bigIntSubtraction(&V01[i],&V00[i],&V01[i]);
		bigIntSubtraction(&V01[i],&V11[i],&V01[i]);
		bigIntMul_d(&V22[i],two,&res[i+4]);
		bigIntSubtraction(&V01[i],&res[i+4],&res[i+4]);
		bigIntGenMod(&res[i+4],&p,&res[i+4]);
	}
/*-------------------------------------------------------------------------------------*/

    // (A0+A2)*(B0+B2)
	for(int i = 0; i<2; i++){
		bigIntAddition(&A00[i],&A20[i],&temp0[i]); //A0 + A2
        bigIntAddition(&A01[i],&A21[i],&temp1[i]);
		bigIntAddition(&B00[i],&B20[i],&temp2[i]); //B0 + B2
        bigIntAddition(&B01[i],&B21[i],&temp3[i]);
	} 
   

	Fp4_2input(temp0,temp1,temp2,temp3,V02);

    // (A0+A2)*(B0+B2) -V0+V1-V2
	for(int i = 0; i<4; i++){
        bigIntSubtraction(&V02[i],&V00[i],&res[i+8]);
        bigIntAddition(&res[i+8],&V11[i],&res[i+8]);
		bigIntSubtraction(&res[i+8],&V22[i],&res[i+8]);
		bigIntGenMod(&res[i+8],&p,&res[i+8]);
	}


	return ;

	/*

	printf("the result is!!!!\n");
	for(int i =0; i < 12; i++){
		bigIntPrint(&res[i]);
		printf("!\n");
	}
	*/
	

	//printf("the computing in 3over2over2 has completed !!! \n");

}



void Fp4_direct(bigInteger ele1[],bigInteger ele2[],bigInteger res[]){
   
     /* Request memory space to store intermediate values generated during computation
	  */
   bigIntDigit five = 5u;
   passModPrime();
   bigInteger v[4];
   bigIntIniCoefficient(v,4);
   bigInteger temp[4];
   bigIntIniCoefficient(temp,4);

   for(int i = 0; i<4; i++){
	   generMul(&ele1[i],&ele2[i],&v[i]); //A0*B0 = v[0], A1*B1 = v[1], A2*B2 = v[2], A3*B3 = v[3]
	   bigIntGenMod(&v[i],&p,&v[i]);
   }

   /*--------calculate the value of the first coefficient of the result ,store in res[0]------------------*/
   
   /* compute (a1+a3)*(b1+b3)-v1-v3+v2 */
   bigIntAddition(&ele1[1],&ele1[3],&temp[0]);
   bigIntAddition(&ele2[1],&ele2[3],&temp[1]);
   generMul(&temp[0],&temp[1],&temp[2]);
   bigIntSubtraction(&temp[2],&v[1],&temp[2]);
   bigIntSubtraction(&temp[2],&v[3],&temp[2]);
   bigIntAddition(&temp[2],&v[2],&temp[2]);
   bigIntGenMod(&temp[2],&p,&temp[2]);  /* temp[2] = (a1+a3)*(b1+b3)-v1-v3+v2  This result needs to be modulo because it is also used in the process of calculating res[1].*/
   bigIntMul_d(&temp[2],five,&res[0]);  //temp[2] = ((a1+a3)*(b1+b3)-v1-v3+v2)*5
   bigIntSubtraction(&v[0],&res[0],&res[0]); // res[0] = v0- ((a1+a3)*(b1+b3)-v1-v3+v2)*5
   bigIntGenMod(&res[0],&p,&res[0]);

 /*--------calculate the value of the second coefficient of the result ,store in res[1]------------------*/

    //(a0+a1)*(b0+b1)-v0-v1
   bigIntAddition(&ele1[0],&ele1[1],&temp[0]);
   bigIntAddition(&ele2[0],&ele2[1],&temp[1]);
   generMul(&temp[0],&temp[1],&res[1]);
   bigIntSubtraction(&res[1],&v[0],&res[1]);
   bigIntSubtraction(&res[1],&v[1],&res[1]);
 
   // -( (a1+a3)*(b1+b3)-v1-v3+v2 )  +  (a0+a1)*(b0+b1)-v0-v1 ,the result is temporarily stored in res[1]
   bigIntSubtraction(&res[1],&temp[2],&res[1]); 
   //(a2+a3)*(b2+b3)-v2-v3
   bigIntAddition(&ele1[2],&ele1[3],&temp[0]);
   bigIntAddition(&ele2[2],&ele2[3],&temp[1]);
   generMul(&temp[0],&temp[1],&temp[2]);
   bigIntSubtraction(&temp[2],&v[2],&temp[2]);
   bigIntSubtraction(&temp[2],&v[3],&temp[2]);
   bigIntGenMod(&temp[2],&p,&temp[2]);  //temp[2] = (a2+a3)*(b2+b3)-v2-v3, This result needs to be modulo for subsequent use
   bigIntMul_d(&temp[2],five,&temp[3]);  //temp[3] = ((a1+a3)*(b1+b3)-v1-v3+v2)*5
   bigIntSubtraction(&res[1],&temp[3],&res[1]);
   bigIntGenMod(&res[1],&p,&res[1]);
   
/*--------calculate the value of the third coefficient of the result ,store in res[2]------------------*/

   //(a0+a2)*(b0+b2)-v0-v2+v1
   bigIntAddition(&ele1[0],&ele1[2],&temp[0]);
   bigIntAddition(&ele2[0],&ele2[2],&temp[1]);
   generMul(&temp[0],&temp[1],&res[2]);
   bigIntSubtraction(&res[2],&v[0],&res[2]);
   bigIntSubtraction(&res[2],&v[2],&res[2]);
   bigIntAddition(&res[2],&v[1],&res[2]);
   //bigIntGenMod(&res[2],&p,&res[2]);  

   //(a0+a2)*(b0+b2)-v0-v2+v1 -  ((a2+a3)*(b2+b3)-v2-v3) - 5*v3
   bigIntSubtraction(&res[2],&temp[2],&res[2]);
   bigIntMul_d(&v[3],five,&temp[2]);
   bigIntSubtraction(&res[2],&temp[2],&res[2]);  //the result : C2
   bigIntGenMod(&res[2],&p,&res[2]);

/*--------calculate the value of the fourth coefficient of the result ,store in res[3]------------------*/

   //(a0+a3)*(b0+b3)-v0-v3
   bigIntAddition(&ele1[0],&ele1[3],&temp[0]);
   bigIntAddition(&ele2[0],&ele2[3],&temp[1]);
   generMul(&temp[0],&temp[1],&temp[2]);
   bigIntSubtraction(&temp[2],&v[0],&temp[2]);
   bigIntSubtraction(&temp[2],&v[3],&temp[2]);
   //bigIntGenMod(&temp[2],&p,&temp[2]);   //temp[2] = (a0+a3)*(b0+b3)-v0-v3

   //(a1+a2)*(b1+b2)-v1-v2
   bigIntAddition(&ele1[1],&ele1[2],&temp[0]);
   bigIntAddition(&ele2[1],&ele2[2],&temp[1]);
   generMul(&temp[0],&temp[1],&res[3]);
   bigIntSubtraction(&res[3],&v[1],&res[3]);
   bigIntSubtraction(&res[3],&v[2],&res[3]);
   //bigIntGenMod(&res[3],&p,&res[3]);   // (a1+a2)*(b1+b2)-v1-v2
   //c3  =    (a1+a2)*(b1+b2)-v1-v2   +    (a0+a3)*(b0+b3)-v0-v3   - v3
   bigIntAddition(&temp[2],&res[3],&res[3]);
   bigIntSubtraction(&res[3],&v[3],&res[3]);
   bigIntGenMod(&res[3],&p,&res[3]);

   return ;

}


void Fp12_3overDirect4(bigInteger A0[],bigInteger A1[],bigInteger A2[],bigInteger B0[],bigInteger B1[],bigInteger B2[],bigInteger res[]){

     bigInteger V0[4];
	 bigInteger V1[4];
	 bigInteger V2[4];
	 bigInteger temp0[4];
	 bigInteger temp1[4];
	 bigInteger temp2[4];

	 bigIntDigit two = 2u;
	 passModPrime();

	 bigIntIniCoefficient(V0,4);
     bigIntIniCoefficient(V1,4);
     bigIntIniCoefficient(V2,4);
	 bigIntIniCoefficient(temp0,4);
     bigIntIniCoefficient(temp1,4);
     bigIntIniCoefficient(temp2,4);


	 Fp4_direct(A0,B0,V0);
	 Fp4_direct(A1,B1,V1);
	 Fp4_direct(A2,B2,V2);

	 //A1+A2     AND     B1+B2
	 for(int i = 0; i<4; i++){
        bigIntAddition(&A1[i],&A2[i],&temp0[i]);
        bigIntAddition(&B1[i],&B2[i],&temp1[i]);
	 }
	 //  C0 = V0 - 2*((A1+A2)*(B1+B2)-V1-V2)
	 Fp4_direct(temp0,temp1,temp2);

	 for(int i = 0; i<4; i++){
		 bigIntAddition(&temp2[i],&V1[i],&temp2[i]);
		 bigIntAddition(&temp2[i],&V2[i],&temp2[i]);
         bigIntMul_d(&temp2[i],two,&temp2[i]);
		 bigIntSubtraction(&V0[i],&temp2[i],&res[i]);
		 bigIntGenMod(&res[i],&p,&res[i]);    // THE RESULT OF C0
	 }

//------------------------------------------------------------------------------

     //A0+A1     AND     B0+B1
	 for(int i = 0; i<4; i++){
        bigIntAddition(&A0[i],&A1[i],&temp0[i]);
        bigIntAddition(&B0[i],&B1[i],&temp1[i]);
	 }

	 //C1 = (A0+A1)*(B0+B1) - V0 -V1 -2V2
     Fp4_direct(temp0,temp1,temp2);
     for(int i =0; i<4; i++){
         bigIntSubtraction(&temp2[i],&V0[i],&res[i+4]);
		 bigIntSubtraction(&res[i+4],&V1[i],&res[i+4]);
         bigIntMul_d(&V2[i],two,&temp0[i]);
		 bigIntSubtraction(&res[i+4],&temp0[i],&res[i+4]);
		 bigIntGenMod(&res[i+4],&p,&res[i+4]);   // THE RESULT OF C1
	 }

//-----------------------------------------------------------------------------------	 

     // A0+A2    AND    B0+B2
	 for(int i = 0; i<4; i++){
        bigIntAddition(&A0[i],&A2[i],&temp0[i]);
        bigIntAddition(&B0[i],&B2[i],&temp1[i]);
	 }
    //C2 = (A0+A2)*(B0+B2) - V0 + V1 -V2
     Fp4_direct(temp0,temp1,temp2);
	 for(int i = 0; i<4; i++){
		 bigIntAddition(&temp2[i],&V1[i],&res[i+8]);
		 bigIntSubtraction(&res[i+8],&V2[i],&res[i+8]);
		 bigIntSubtraction(&res[i+8],&V0[i],&res[i+8]);
		 bigIntGenMod(&res[i+8],&p,&res[i+8]);
	 }

	 return ;

	 //printf("Fp 12 3over4 is success!!!! \n");




}



void setRandCo(bigInteger x[], int n){

	char s[134];

	bigIntIniCoefficient(x,n);

	int len;

	for (int i=0;i<n;i++)
	{
		len= rand() % 133;     // the length of each coefficient is not larger than 10^100

		for (int j=0;j<len;j++)
		{
			s[j]='0'+(rand() % 10);
		}
		s[len]='\0';

		if (len>0)
		{
			bigIntReadRadix(&x[i],  s,  10);
		}
	}
}



// su = 4681u;(unsigned int_32)


/* Montgomery refers to libtommath*/

void bigIntGenMontReduce(bigInteger *x){

	bigIntDigit su = 4681u;
   passModPrime();
	bigIntMontReduce(x,&p,su);

	generMul(x,&b,x);
  // printf("After Mont, we multi with the b, THE RESULT IS !!! \n");
  // bigIntPrint(x);

   //bigIntVagueReduction(x,&p);
	bigIntGenMod(x,&p,x);

}

/* su is the setup parameter, which is precomputed according to the modulus p
   and x is the product of two elements in Fp,hence, if x > p, p < x <= (p-1)^2
*/
bigIntCatch bigIntMontReduce(bigInteger *x, const bigInteger *p, bigIntDigit su)
{
   bigIntCatch err; // catch the error
   int xi, newoccu;

   newoccu = (p->occupied * 2) + 6;
   
   /* increase the digit of the input, we will add p's multiple on it*/
   if ((err = bigIntIncrease(x, newoccu)) != runSuccess) {
      return err;
   }
   x->occupied = newoccu;

   for (xi = 0; xi < p->occupied; xi++) {
      int yi; // yi use for loop, for compute every iteration of the result of new x  
      /*
      we have computed the  value of -1/p mod R, is su
      every loop we should pre-compute the value of sigma =  -xi/p mod R = xi*su mod R
      */
      bigIntDigit sigma = ((x->adp[xi] * su) & ANDR_1); 

      bigIntDigit carry = 0;
      /* this "for yi loop" is to compute the every "loop of xi": the result of x, 
      x = x + sigma * p * R^i */
      for (yi = 0; yi < p->occupied; yi++) {
         /* 
         because in every xi loop, the value of x would continue update
         we donot need to care about the digit of x less than xi
         hence the accumulation is base on x->adp[xi + yi], yi is start from 0
          */
         bigIntDigit ua = (sigma * p->adp[yi] + carry + x->adp[xi + yi]);// sum of

         /* carry, pass to the next digit*/
         carry = (bigIntDigit)(ua >> DefaultBitOfDigit);

         /*fix the digit of result of x of in every "for xi loop" */
         x->adp[xi + yi] = (ua & ANDR_1);// AND R-1 operation is equal to mod R
      }
      /* pass up carries, if carry is not 0*/
      while (carry != 0u) {
         x->adp[xi + yi] += carry;
         carry = x->adp[xi + yi] >> DefaultBitOfDigit; // pass the carry to next digit
         x->adp[xi + yi++] &= ANDR_1; // fix the digit
      }
   }

   /* now, the digit from 0 to p.occupied of x is 0, we need to right shift p.occupied
   */
   bigIntRightShift(x, p->occupied);
   bigIntAdjust(x);

   return runSuccess;
}








// discard the following code












// the below function is used to check our setup value is 4681u or not

// bigIntDigit setup = 4681u;


/* setups the montgomery reduction stuff */
bigIntCatch mp_montgomery_setup(const bigInteger *n, bigIntDigit *rho)
{
   bigIntDigit x, b;


   /* fast inversion mod 2**k
    *
    * Based on the fact that
    *
    * XA = 1 (mod 2**n)  =>  (X(2-XA)) A = 1 (mod 2**2n)
    *                    =>  2*X*A - X*X*A*A = 1
    *                    =>  2*(1) - (1)     = 1
    */
   b = n->adp[0];

   if ((b & 1u) == 0u) {
      return runInvalid;
   }

   x = (((b + 2u) & 4u) << 1) + b; /* here x*a==1 mod 2**4 */
   x *= 2u - (b * x);              /* here x*a==1 mod 2**8 */
   x *= 2u - (b * x);              /* here x*a==1 mod 2**16 */


   /* rho = -1/m mod b */
   *rho = (bigIntDigit)(((uSignInt)1 << (uSignInt)DefaultBitOfDigit) - x) & ANDR_1;
   

   return runSuccess;
}







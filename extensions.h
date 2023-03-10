#ifndef extensions_h
#define extensions_h


#include "finitefield.h"
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <time.h>
#include "finitefield.h"






void Fp2mul(bigInteger coef1[],bigInteger coef2[],bigInteger res[]);
void Fp3mul(bigInteger coef1[],bigInteger coef2[],bigInteger res[]);

void bigIntIniCoefficient(bigInteger coef[],int len);


void passModPrime();


void Fp4_2input(bigInteger A0[], bigInteger A1[], bigInteger B0[], bigInteger B1[], bigInteger res[]);
void Fp6_3over2input(bigInteger A0[],bigInteger A1[],bigInteger A2[],bigInteger B0[],bigInteger B1[],bigInteger B2[], bigInteger res[]);
void Fp6_2over3input(bigInteger A0[],bigInteger A1[],bigInteger B0[],bigInteger B1[],bigInteger res[]);



void Fp12_2over2over3(bigInteger A00[],bigInteger A01[],bigInteger A10[],bigInteger A11[], bigInteger B00[],bigInteger B01[],bigInteger B10[], bigInteger B11[], bigInteger res[]);

void Fp12_2over3over2(bigInteger A00[],bigInteger A01[],bigInteger A02[],bigInteger A10[], bigInteger A11[],bigInteger A12[],bigInteger B00[], bigInteger B01[], bigInteger B02[], bigInteger B10[], bigInteger B11[], bigInteger B12[], bigInteger res[]);
void Fp12_3over2over2(bigInteger A00[],bigInteger A01[],bigInteger A10[],bigInteger A11[], bigInteger A20[],bigInteger A21[],bigInteger B00[], bigInteger B01[],bigInteger B10[], bigInteger B11[], bigInteger B20[], bigInteger B21[], bigInteger res[]);

void Fp4_direct(bigInteger ele1[],bigInteger ele2[],bigInteger res[]);
void setRandCo(bigInteger x[], int n);

void Fp12_3overDirect4(bigInteger A0[],bigInteger A1[],bigInteger A2[],bigInteger B0[],bigInteger B1[],bigInteger B2[],bigInteger res[]);

void Execute_Fp3();
void Execute_Fp4_2over2();
void Execute_Fp4_direct();
void Execute_Fp6_3over2();
void Execute_Fp6_2over3();

void Execute_Fp12_3over4();
void Execute_Fp12_3over2over2();
void Execute_Fp12_2over2over3();
void Execute_Fp12_2over3over2();


void bigIntGenMontReduce(bigInteger *x);
bigIntCatch bigIntMontReduce(bigInteger *x, const bigInteger *p, bigIntDigit su);
bigIntCatch mp_montgomery_setup(const bigInteger *n, bigIntDigit *rho);












#endif

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "finitefield.h"
#include "extensions.h"
#include <time.h>
#include <unistd.h>
#include <sys/time.h>
#include "x86estimate.h"


// global variable 
bigInteger p; //prime p
bigInteger b;




int main(int argc,char **argv)
{

	char s1[300];
	
  // srand should not be delete
  srand((unsigned)time(NULL));  // Initialization function of random number generator
  



  /*               initialize the parameters*/
  bigInteger k1;
  bigIntInitial(&k1);
  passModPrime();//pass fixed p value


  /* INPUT ANY integer, we would multiply itself p-1 times, and check the result is 1 or not,
     if it is not 1, the multiplication implementation is wrong
  */
  printf("please input your random integer a\n");
  gets(s1);
  bigIntReadRadix(&k1,  s1,  10);
  correctnessNew(&k1,&p);

 

  /*  TEST clock cycles of different extentions of finite field*/
  Fp2_Cycles();
  Fp3_Cycles(); 
  Fp4_2over2Cycles();
  Fp4_DirectCycles();
  Fp6_3over2Cycles();
  Fp6_2over3Cycles();
  Fp12_3over4Cycles(); 
  Fp12_3over2over2Cycles();
  Fp12_2over3over2Cycles(); 
  Fp12_2over2over3Cycles();

//------------------------------------------------------------------------------------------------------

  /*
  The second correctness test is to take the recognized libraries as the standard.
  When our implementation and the library do the same multiplication and modular operation,
  compare whether the results of two are consistent.
  

  bigIntCatch err;
  if ( (err = testCorrect_Method2()) != runSuccess) {
    printf("Occur Error!!!! Occur Error!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! \n");
  }
  else{
    printf("The second method to test multiplication in Fp is correct!!!! \n");
  }
  printf("\n");

  */

//------------------------------------------------------------------------------------------------------




/*test multiplication in Fp2, there are two parts:
  first part: generate randomly two elements and print them
  second part: compare the result with the known libraries or vectors


  //testFp2();   //if you want to see the randomly input and their result, execute this
  printf("let us test Fp2!!!!!!!!!!!!!!!!! \n");
  Fp2correctness();
  printf("\n");

  test multiplication in Fp3, there are two parts:
  first part: generate randomly two elements and print them
  second part: compare the result with the known libraries or vectors
  

  //testFp3();  //if you want to see the randomly input and their result, execute this
 printf("let us test Fp3!!!!!!!!!!!!!!!!! \n");
  Fp3correctness();
  printf("\n");
*/




/*test multiplication in Fp4, there are four parts:
  first part: TEST fp2 over fp2: generate randomly two elements and print them
  seconde part: TEST fp2 over fp2: compare the result with the known libraries or vectors

  third part: TEST direct Fp4: generate randomly two elements and print them
  fourth part: TEST direct Fp4: compare the result with the known libraries or vectors


  printf("let us test Fp4 (Fp2 over Fp2)!!!!!!!!!!!!!!!!! \n");
  //testFp4_2(); // if you want to generate some random inputs and print them and their result
  Fp4correctness();
  printf("\n");

  printf("let us test Fp4 (direct Fp4)!!!!!!!!!!!!!!!!! \n");
  //testFp4_direct(); // if you want to generate some random inputs and print them and their result
  Fp4_directcorrectness();
  printf("\n");


*/








//------------------------------------------------------------------------------------------------------

/*test multiplication in Fp6, we will test Fp3 over Fp2 and Fp2 over Fp3
 
*/
/*
  printf("let us test Fp6 (Fp3 over Fp2)!!!!!!!!!!!!!!!!! \n");
  //testFp6_3over2(); // if you want to generate some random inputs and print them and their result
  Fp6_3over2correctness();
  printf("\n");

  
  printf("let us test Fp6 (Fp2 over Fp3)!!!!!!!!!!!!!!!!! \n");
  //testFp6_2over3(); // if you want to generate some random inputs and print them and their result
  Fp6_2over3correctness();
  printf("\n");

*/

//------------------------------------------------------------------------------------------------------


/*test multiplication in Fp12 
we will test 1)Fp2 over Fp2 over Fp3  2)Fp2 over Fp3 over Fp2
 
*/

/*
  printf("let us test Fp12 (Fp2 over Fp2 over Fp3)!!!!!!!!!!!!!!!!! \n");
  //testFp12_2over2over3();// if you want to generate some random inputs and print them and their result
  Fp12_2over2over3correctness();
  printf("\n");


  printf("let us test Fp12 (Fp2 over Fp3 over Fp2)!!!!!!!!!!!!!!!!! \n"); 
  //testFp12_2over3over2();
  Fp12_2over3over2correctness();
  printf("\n");

  printf("let us test Fp12 (Fp3 over Fp2 over Fp2)!!!!!!!!!!!!!!!!! \n");
  //testFp12_3over2over2(); // if you want to generate some random inputs and print them and their result
  Fp12_3over2over2correctness();


  printf("let us test Fp12 (Fp3 over direct Fp4)!!!!!!!!!!!!!!!!! \n");
  //testFp12_3overDirect4(); // if you want to generate some random inputs and print them and their result
  Fp12_3overDirect4correctness();
*/


  
  

  
 
 


  


	getchar();
  

   return 0;

}












#include "finitefield.h"
#include "extensions.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>
#include <sys/time.h>
#include "x86estimate.h"





// this is the package of tesing about the correctness, security and the efficiency of tesing


typedef long long cycles_t;

extern bigInteger p;
extern bigInteger b;


/* in this function, we use "fermat's little theorem" and "multiply and square", when we input random integer "data", the output is 
   data^p1 mod p, if the result is equal to 1, that means the multiplication and modulo operation is correct.
*/
int correctnessNew(bigInteger* data,bigInteger* p){

    int binaryPrime[500];  // Convert the fixed prime number from decimal to binary and store it in the array "binaryPrime"
    int index = 0;

    bigInteger res;
    bigIntInitial(&res); // result value store in "res"

	bigInteger two;
	bigIntInitial(&two);
	bigIntReadRadix(&two, "2",  10); // we devide p by 2 and convert it into a binary number
	bigIntReadRadix(&res, "1",  10); // Initial value of res is 1

	bigInteger residue;
	bigIntInitial(&residue);

    bigInteger one;
	bigIntInitial(&one);

	
	bigInteger p2;
    bigIntInitial(&p2);
    bigIntSubtraction(p,&res,&p2);
    //printf("print the value of p-1\n");
    //bigIntPrint(&p2);
    printf("-----------------\n");


	//get the binary of the p-1, store in a int array
	while(!isZero(&p2)){

		mp_div(&p2,&two,&p2,&residue); 

		if (residue.adp[0] == 0u)
		{
			binaryPrime[index++]=0;	
           // printf("first : %d\n",index);

		}
		else{
			binaryPrime[index++]=1;
            //printf("second : %d\n",index);//
		}
         
	}
    
    printf("%d\n",index);
    printf("print the array of binary of prime p \n");
    for(int i = 0;i < index; i++){
        printf("%d",binaryPrime[i]);
        //printf("%d",i);
    }

	printf("\nstart the multiple and square!! \n");
    printf("print the original of res!! \n");
    bigIntPrint(&res);



    // we compute the result of data^p-1
	for (int i=index-1;i>-1;i--)
	{
	   if (binaryPrime[i]==1) // 
		{
			generMul(&res,&res,&res);  // square the data
			generMul(&res,data,&res);  // multiply  with original data value
		}
		else{
			generMul(&res,&res,&res);
		}
        bigIntGenMontReduce(&res);
		                                                                                                                  //bigIntGenMod(&res,p,&res);
        
	}

    // Compare the result after multiply and square with 1, if it is equal to 1, the multiplcation and modulo operation
	
	bigIntReadRadix(&one,"1",10);
    // two method to test the result is 1 or not
	if(bigIntSignCom(&res,&one) == EQUAL){
		printf("Using Fermat's little theorem: multiple itself p-1 times, the result is ");
		bigIntPrint(&res);
		printf("\n");
	}
	if ((res.adp[0] == 1u) && (res.occupied = 1)){
		printf("test success!! \n");
	}
    else{
        printf("Error occur!!!!\n");
    }
	return 1;

}






bigIntCatch testCorrect_Method2(){

      bigIntCatch err;
	  bigInteger testarr[4];
	  passModPrime();


	  for(int i = 0; i < 4; i++){
		  bigIntInitial(&testarr[i]);
	  }
	  printf("start second testing to test correctness !!! \n");

	// test 1    Over the single precision multiplication, whether there is data overflow
	  bigIntReadRadix(&testarr[0], "32700",10);
	  bigIntReadRadix(&testarr[1], "23131",10);
	  if((err = generMul(&testarr[0],&testarr[1],&testarr[2])) != runSuccess){
		  return runError;
	  }
	  bigIntReadRadix(&testarr[3], "756383700", 10);
      if( bigIntSignCom(&testarr[2],&testarr[3]) != EQUAL){
		  return runError;
	  }
	  //printf("result: test1!!! \n");
	  //bigIntPrint(&testarr[2]);

	// test2  If the computing result exceeds the maximum storage range of signed int type, is there a possibility of data overflow
      bigIntReadRadix(&testarr[0], "9999999999999",10);
	  bigIntReadRadix(&testarr[1], "8888888888888",10);
	  if((err = generMul(&testarr[0],&testarr[1],&testarr[2])) != runSuccess){
		  return runError;
	  }
	  bigIntReadRadix(&testarr[3], "88888888888871111111111112", 10);
      if( bigIntSignCom(&testarr[2],&testarr[3]) != EQUAL){
		  return runError;
	  }
	  //printf("result: test2!!! \n");
	  //bigIntPrint(&testarr[2]);
	  

      //test3  Multiply two integers of bigInteger type, and then take the module to check whether the result is correct
      bigIntReadRadix(&testarr[0], "98973793541231231431435245245435335635",10);
	  bigIntReadRadix(&testarr[1], "8750956026967927184653173385807580611071113509743794217835509659383833974807299233349991517722081255972774",10);
	  if((err = generMul(&testarr[0],&testarr[1],&testarr[2])) != runSuccess){
		  return runError;
	  }

      bigIntGenMod(&testarr[2],&p,&testarr[2]);
	  bigIntReadRadix(&testarr[3], "129530668781474171478324391930729261226566849111075937771478485728729734628385683724574352616946766257052786569157965446896905441758397", 10);
      if( bigIntSignCom(&testarr[2],&testarr[3]) != EQUAL){
		  return runError;
	  }
	  //printf("result: test3!!! \n");
	  //bigIntPrint(&testarr[2]);
	  
	  
	  //test4  Multiply two integers of bigInteger type, and then take the module to check whether the result is correct
      bigIntReadRadix(&testarr[0], "542714323533040317240657809080777074238723194376488776216936430761889077170320800597073748560547572023470",10);
	  bigIntReadRadix(&testarr[1], "86467788389365701099303128918305098300255839082123572548841203350994268832172808674641370803",10);
	  if((err = generMul(&testarr[0],&testarr[1],&testarr[2])) != runSuccess){
		  return runError;
	  }
	  bigIntGenMod(&testarr[2],&p,&testarr[2]);
	  bigIntReadRadix(&testarr[3], "194407208538274229000824025517805252309272466669420742665439910360119219166367968464304624027452873655938646216600338628088965961362821", 10);
      if( bigIntSignCom(&testarr[2],&testarr[3]) != EQUAL){
		  return runError;
	  }
	  //printf("result: test4!!! \n");
	  //bigIntPrint(&testarr[2]);
	  


	  //test5  Square the maximum value in Fp, the result is the maximum value occurs in our implementation, and then take the module, check the result is correct or not
      bigIntReadRadix(&testarr[0], "218297830370226601612193514776502382704221475011035725792624279635059316315225569375126760584265176077347911285544462735949991646330886",10);
	  bigIntReadRadix(&testarr[1], "218297830370226601612193514776502382704221475011035725792624279635059316315225569375126760584265176077347911285544462735949991646330886",10);
	  if((err = generMul(&testarr[0],&testarr[1],&testarr[2])) != runSuccess){
		  return runError;
	  }
	  bigIntGenMod(&testarr[2],&p,&testarr[2]);
	  bigIntReadRadix(&testarr[3], "1", 10);
      if( bigIntSignCom(&testarr[2],&testarr[3]) != EQUAL){
		  return runError;
	  }
	  //printf("result: test5!!! \n");
	  //bigIntPrint(&testarr[2]);

	  //test6  We may get a negative number after subtraction. Therefore, we want to verify the correctness of negative numbers through modular operation. 
      bigIntReadRadix(&testarr[0], "-779763032873463214",10);
	  bigIntReadRadix(&testarr[1], "161219351477650238270422147501103572579262427963505931631522556937",10);
	  if((err = generMul(&testarr[0],&testarr[1],&testarr[2])) != runSuccess){
		  return runError;
	  }
	  bigIntGenMod(&testarr[2],&p,&testarr[2]);
	  bigIntReadRadix(&testarr[3], "218297830370226601612193514776502382704221475011035600079733813529656386384389626414651567050538971607547233857442938214240711956315369", 10);
      if( bigIntSignCom(&testarr[2],&testarr[3]) != EQUAL){
		  return runError;
	  }
	  //printf("result: test6!!! \n");
	  //bigIntPrint(&testarr[2]);

      //test7 We may get a negative number after subtraction. Therefore, we want to verify the correctness of negative numbers through modular operation. 
      bigIntReadRadix(&testarr[0], "-2382704221475011035725792624279635059316315225569375126760584265176077347898839998009202403235192796545",10);
	  bigIntReadRadix(&testarr[1], "16121935147765023827042214750110357257926242796350593163152215892158921103218304811032183048556937",10);
	  if((err = generMul(&testarr[0],&testarr[1],&testarr[2])) != runSuccess){
		  return runError;
	  }
	  bigIntGenMod(&testarr[2],&p,&testarr[2]);
	  bigIntReadRadix(&testarr[3], "153075134513657313080892290056280067756352405381148867992756014528675390493720364747752756194255740986119998623175131478483620040660249", 10);
      if( bigIntSignCom(&testarr[2],&testarr[3]) != EQUAL){
		  return runError;
	  }
	  //printf("result: test7!!! \n");
	  //bigIntPrint(&testarr[2]);

	 
      //test8 take a mod operation
      bigIntReadRadix(&testarr[0], "9999999984000000011999999994400000001819999999563200000080079999988560000001286999999885600000008007999999563200000018199999999440000000011999999999840000000001",10);
	  bigIntGenMod(&testarr[0],&p,&testarr[0]);
	  bigIntReadRadix(&testarr[3], "59372711149934533533290966163388552603647601581334493063656506341190067180105523206263269022540292933168392259129762486274319143001842", 10);
      if( bigIntSignCom(&testarr[0],&testarr[3]) != EQUAL){
		  return runError;
	  }
	  /*
	  else{
		  printf("result: test8!!! \n");
	      bigIntPrint(&testarr[0]);
		  
	  }
      */

      //test9 continuely spuare a integer and do mod operation
      bigIntReadRadix(&testarr[0], "28735003311021920153",10);
	  if((err = generMul(&testarr[0],&testarr[0],&testarr[0])) != runSuccess){
		  return runError;
	  }
	  if((err = generMul(&testarr[0],&testarr[0],&testarr[0])) != runSuccess){
		  return runError;
	  }
	  if((err = generMul(&testarr[0],&testarr[0],&testarr[0])) != runSuccess){
		  return runError;
	  }
	  bigIntGenMod(&testarr[0],&p,&testarr[0]);
	  bigIntReadRadix(&testarr[3], "82102746432724915705137333981386330887611602608888218564244042894621821537894365543156916154260557048078009611421467252404159269398425", 10);
      if( bigIntSignCom(&testarr[0],&testarr[3]) != EQUAL){
		  return runError;
	  }
	 //printf("result: test9!!! \n");
	 // bigIntPrint(&testarr[2]);


      /*
	  setRandBigInt(&testarr[0]);
	  bigIntPrint(&testarr[0]); 

	  */

	  return runSuccess;

	  }

void testFp2(){

   bigInteger A0[2];
   bigInteger A1[2];
   setRandCo(A0,2);
   setRandCo(A1,2);
   
   printf("the a0 is \n");
   bigIntPrint(&A0[0]);
   printf("the a1 is \n");
   bigIntPrint(&A0[1]);
   printf("the b0 is \n");
   bigIntPrint(&A1[0]);
   printf("the b1 is \n");
   bigIntPrint(&A1[1]);

   bigInteger v0[2];
   bigIntIniCoefficient(v0,2);
   Fp2mul(A0,A1,v0);

}

void Fp2correctness(){

    bigInteger A0[2];
	bigInteger B0[2];
	bigInteger C0[2];
	bigInteger C1[2];
    bigIntIniCoefficient(A0,2);
    bigIntIniCoefficient(B0,2);
    bigIntIniCoefficient(C0,2);
	bigIntIniCoefficient(C1,2);

	bigIntReadRadix(&A0[0], "969264528785624674740859857619041852660676883818503063622535562625352526372362544332262534501498777625",10);
    bigIntReadRadix(&A0[1],"3592839611455157319384995458653747747363526347383892937463662525263626278722333607633362502331806088",10);
	bigIntReadRadix(&B0[0],"671910250071176837172938484736362525363402639083911576056386549716543322329667972099216863",10);
	bigIntReadRadix(&B0[1],"99692813985705752621347362523748484849393837362253647473636209939163823281759269148927825508721001916988275",10);

	Fp2mul(A0,B0,C0);
	bigIntReadRadix(&C1[0], "109626803726792149659679928367401941555291440108904491273762021263297563169408108387706708501764444499826671471902341213511968800376458",10);
    bigIntReadRadix(&C1[1],"212381040026612311730895678879298245432593044350471341726942893728908155905426978865824942795767346313686415834035084695788371483271502",10);

	if( bigIntSignCom(&C0[0],&C1[0]) != EQUAL){
		printf("the result is wrong!!!! \n");
	}
	if( bigIntSignCom(&C0[1],&C1[1]) != EQUAL){
		printf("the result is wrong!!!! \n");
	}
	else{
		printf("the 1st of testing correctness of fp 2 is success!!!!!!!!! \n");
	}

	bigIntReadRadix(&A0[0], "8838185030636225355263473838929374636625252324234223455885325434534635636262787223336076",10);
    bigIntReadRadix(&A0[1],"172938484736362525363402639083913234215760563863365438653754337363533362502331806088",10);
	bigIntReadRadix(&B0[0],"12322345398570575262134736252374848484939383736225364e3345678875442290776555455",10);
	bigIntReadRadix(&B0[1],"9969281374736362099391638232817592691489278255087210019788792982454325930443504713417269428937289081559054269788616988275",10);

	

	Fp2mul(A0,B0,C0);
	bigIntReadRadix(&C1[0], "101999798994749044902981709181529539765128345067498406891363983472204669977806618374226810777301053272966188272885371173036599283616320",10);
    bigIntReadRadix(&C1[1],"77199474700939601536996271100555103714513078986424484357371252110915198162708876885315684783392236568389276967314615046273417267119357",10);

	if( bigIntSignCom(&C0[0],&C1[0]) != EQUAL){
		printf("the result is wrong!!!! \n");
	}
	if( bigIntSignCom(&C0[1],&C1[1]) != EQUAL){
		printf("the result is wrong!!!! \n");
	}
	else{
		printf("the 2nd of testing correctness of fp 2 is success!!!!!!!!! \n");
	}

}

void testFp3(){

   bigInteger A0[3];
   bigInteger A1[3];

   setRandCo(A0,3);
   setRandCo(A1,3);

  
   for (int i =0; i < 3; i++){
     printf("the coefficient of element1 (in Fp3) is \n");
     bigIntPrint(&A0[i]);
     printf("the coefficient of element2 (in Fp3) is \n");
     bigIntPrint(&A1[i]);
     
   }
   bigInteger v0[3];
   bigIntIniCoefficient(v0,3);
   Fp3mul(A0,A1,v0);

   printf("this is the test of fp 3, good evening!!!! SUCCESS!! \n");

}

void Fp3correctness(){

	bigInteger A0[3];
	bigInteger B0[3];
	bigInteger C0[3];
	bigInteger C1[3];

    bigIntIniCoefficient(A0,3);
    bigIntIniCoefficient(B0,3);
    bigIntIniCoefficient(C0,3);
	bigIntIniCoefficient(C1,3);
	
	bigIntReadRadix(&A0[0], "5474419948947708156094636882172934936352515161612727441315263335404590",10);
    bigIntReadRadix(&A0[1],"501971689667752499560624322224322233333333221123348886655444322111245098776548907469595503",10);
	bigIntReadRadix(&A0[2],"7579240264388905955321224983153548293658251895631959150708643359686577072883228475458741492406243027822385",10);
	bigIntReadRadix(&B0[0],"78331435320184982006157691938602893026482564582905835242964771017234343857129",10);
	bigIntReadRadix(&B0[1],"87269476161237839352173455099166002266281651212477533189910994682831664116058791639740963348839331893596206628570",10);
    bigIntReadRadix(&B0[2],"7566537187570380906877905532122492266281651212477533189910831539789249060118456558",10);
	

	Fp3mul(A0,B0,C0);
	bigIntReadRadix(&C1[0], "10218182393298066094345209846475067030301330294608009714413476489899693748877985464643817474407284549508199836698927931796312655855308",10);
    bigIntReadRadix(&C1[1],"185338459549685714364235193665012467296370716402522729117239896573964812113304424187759689853057909898285496577239331611579713270930406",10);
    bigIntReadRadix(&C1[2],"160801102264091053422051404522084725964661365906725865024064424734766204622703646815830446566585769436758986095598253472921684009349857",10);
	if( bigIntSignCom(&C0[0],&C1[0]) != EQUAL){
		printf("the result is wrong!!!! \n");
	}
	if( bigIntSignCom(&C0[1],&C1[1]) != EQUAL){
		printf("the result is wrong!!!! \n");
	}
	if( bigIntSignCom(&C0[2],&C1[2]) != EQUAL){
		printf("the result is wrong!!!! \n");
	}
	else{
		printf("the correctness of fp 3 is success!!!!!!!!! \n");
	}
}

void testFp4_2(){

   bigInteger A0[2];
   bigInteger A1[2];
   bigInteger B0[2];
   bigInteger B1[2];

   setRandCo(A0,2);
   setRandCo(A1,2);
   setRandCo(B0,2);
   setRandCo(B1,2);


   printf("the A0[0] is \n");
   bigIntPrint(&A0[0]);
   printf("the A0[1] is \n");
   bigIntPrint(&A0[1]);
   printf("the A1[0] is \n");
   bigIntPrint(&A1[0]);
   printf("the A1[1] is \n");
   bigIntPrint(&A1[1]);
   printf("the B0[0] is \n");
   bigIntPrint(&B0[0]);
   printf("the B0[1] is \n");
   bigIntPrint(&B0[1]);
   printf("the B1[0] is \n");
   bigIntPrint(&B1[0]);
   printf("the B1[1] is \n");
   bigIntPrint(&B1[1]);

   bigInteger res[4];
   bigIntIniCoefficient(res,4);

   Fp4_2input(A0,A1,B0,B1,res);

   printf("the result of Fp4 (Fp2 over Fp2)is \n");
   for(int i = 0; i<4; i++){
       bigIntPrint(&res[i]);
   }

   printf("running successful!!! Fp2 over Fp2 \n");


}

void Fp4correctness(){
    
	bigInteger A0[2];
    bigInteger A1[2];
    bigInteger B0[2];
    bigInteger B1[2];

    bigIntIniCoefficient(A0,2);
	bigIntIniCoefficient(A1,2);
    bigIntIniCoefficient(B0,2);
    bigIntIniCoefficient(B1,2);

    bigIntReadRadix(&A0[0],"862531906719425278916773330833194221012125072106522706164230148168814560753248549216",10);
    bigIntReadRadix(&A0[1],"716570351483065512153927919087476733911736554393571354874106587211382828353978627003",10);
	bigIntReadRadix(&A1[0],"56505013938232805167684701576613551497097835489282658619641",10);
	bigIntReadRadix(&A1[1],"2563201525011857845701774147778050",10);
	bigIntReadRadix(&B0[0],"393640769462994200152324547587809063730541319343869227779359232780237305",10);
    bigIntReadRadix(&B0[1],"54435631913513852708199466317145622543260650021039546203536480374324",10);
    bigIntReadRadix(&B1[0],"337565442341669515768844942286775113471563361389979583111520474275681432811667713639593021565580690",10);
    bigIntReadRadix(&B1[1],"926928529759708498299985182009865438771577377981216007293699953903677946681020",10);

    bigInteger res[4];
    bigIntIniCoefficient(res,4);
    Fp4_2input(A0,A1,B0,B1,res);

    bigInteger knowresult[4];
    bigIntIniCoefficient(knowresult,4);

    bigIntReadRadix(&knowresult[0],"112410955957214808924207459363267255090953370656822260615062578639438645724317480751963428207216508540334769099396625464352045988040652",10);
    bigIntReadRadix(&knowresult[1],"867414143549851733233907767036835908831965739369745091574888875173444563691349342392941240778931567582537446679324158322896840185867",10);
    bigIntReadRadix(&knowresult[2],"86757119092238234809997009205129341245067214823538849455646748075654782279686324152518353368018485140354659448143676171132354754661813",10);
    bigIntReadRadix(&knowresult[3],"32054929255858820918054584813945941606089482890721927375838536972733226319149287511010178631398558633512181903725239860739916953985185",10);

    if( bigIntSignCom(&res[0],&knowresult[0]) != EQUAL){
		printf("the result is wrong!!!! \n");
	}
	if( bigIntSignCom(&res[1],&knowresult[1]) != EQUAL){
		printf("the result is wrong!!!! \n");
	}
	if( bigIntSignCom(&res[2],&knowresult[2]) != EQUAL){
		printf("the result is wrong!!!! \n");
	}
	if( bigIntSignCom(&res[3],&knowresult[3]) != EQUAL){
		printf("the result is wrong!!!! \n");
	}
	else{
		printf("the correctness of fp 4 (Fp2 over Fp2)is success!!!!!!!!! \n");
	}


}

void testFp4_direct(){

    bigInteger ele1[4];
	bigInteger ele2[4];
    setRandCo(ele1,4);
	setRandCo(ele2,4);

	for(int i =0; i<4; i++){

		printf("the ele 1 and 2 is !!!! \n");
        bigIntPrint(&ele1[i]);
		bigIntPrint(&ele2[i]);
	}

	bigInteger result[4];
	bigIntIniCoefficient(result, 4);

	Fp4_direct(ele1,ele2,result);
	printf("the result is !!!!! \n");
	for(int i = 0; i < 4; i++){
        bigIntPrint(&result[i]);
	}

}

void Fp4_directcorrectness(){
    
	bigInteger ele1[4];
	bigInteger ele2[4];

    bigIntIniCoefficient(ele1,4);
	bigIntIniCoefficient(ele2,4);
	

    bigIntReadRadix(&ele1[0],"9248751784638109447511093940391",10);
    bigIntReadRadix(&ele1[1],"159049478211795954007253563288841047480210409",10);
	bigIntReadRadix(&ele1[2],"821912334850185509926300159896674201353499251482695401032596055908127585136212059403",10);
	bigIntReadRadix(&ele1[3],"257371941064212207724415729464179725686385106011453347907857462021587147830022707322399360910009016",10);
    bigIntReadRadix(&ele2[0],"7362251475813765571269281952983876023744353306631984118123484",10);
	bigIntReadRadix(&ele2[1],"644822437553614849992045860692647939",10);
	bigIntReadRadix(&ele2[2],"316130566323687112745040428306235858279654461698443339328384616920899099873668810046285222",10);
    bigIntReadRadix(&ele2[3],"4006857311226042121",10);



    bigInteger res[4];
	bigIntIniCoefficient(res, 4);
	Fp4_direct(ele1,ele2,res);


    bigInteger knowresult[4];
    bigIntIniCoefficient(knowresult,4);

    bigIntReadRadix(&knowresult[0],"52104031081983899073675342161098631933265574235379480382999857214019753543909654207340217815274205879252579174179716986273955160978922",10);
    bigIntReadRadix(&knowresult[1],"91310913986963641491936812267358460435505504839867242002222228039651164716393502025715865407204368698005639570511727951696817333756466",10);
    bigIntReadRadix(&knowresult[2],"9202045856789175085446544604329419405691684631366876570533542968390039450684744468982430749377269216111645795189894943567717673237817",10);
    bigIntReadRadix(&knowresult[3],"103185318726227352034506038191778828465362322041553639737161674771294550653537383528162332477186527988592998918956294988344441937451596",10);


    if( bigIntSignCom(&res[0],&knowresult[0]) != EQUAL){
		printf("the result is wrong!!!! \n");
	}
	if( bigIntSignCom(&res[1],&knowresult[1]) != EQUAL){
		printf("the result is wrong!!!! \n");
	}
	if( bigIntSignCom(&res[2],&knowresult[2]) != EQUAL){
		printf("the result is wrong!!!! \n");
	}
	if( bigIntSignCom(&res[3],&knowresult[3]) != EQUAL){
		printf("the result is wrong!!!! \n");
	}
	else{
		printf("the correctness of fp4 direct is success!!!!!!!!! \n");
	}
}

void testFp6_3over2(){

   
   bigInteger A0[2];
   bigInteger A1[2];
   bigInteger A2[2];
   bigInteger B0[2];
   bigInteger B1[2];
   bigInteger B2[2];

   setRandCo(A0,2);
   setRandCo(A1,2);
   setRandCo(A2,2);
   setRandCo(B0,2);
   setRandCo(B1,2);
   setRandCo(B2,2);

   printf("the A0[0] is \n");
   bigIntPrint(&A0[0]);
   printf("the A0[1] is \n");
   bigIntPrint(&A0[1]);
   printf("the A1[0] is \n");
   bigIntPrint(&A1[0]);
   printf("the A1[1] is \n");
   bigIntPrint(&A1[1]);
   printf("the A2[0] is \n");
   bigIntPrint(&A2[0]);
   printf("the A2[1] is \n");
   bigIntPrint(&A2[1]);
   printf("the B0[0] is \n");
   bigIntPrint(&B0[0]);
   printf("the B0[1] is \n");
   bigIntPrint(&B0[1]);
   printf("the B1[0] is \n");
   bigIntPrint(&B1[0]);
   printf("the B1[1] is \n");
   bigIntPrint(&B1[1]);
   printf("the B2[0] is \n");
   bigIntPrint(&B2[0]);
   printf("the B2[1] is \n");
   bigIntPrint(&B2[1]);

   bigInteger res[6];
   bigIntIniCoefficient(res,6);

   Fp6_3over2input(A0,A1,A2,B0,B1,B2,res);

   printf("the result is \n");
   for(int i = 0; i<6; i++){
       bigIntPrint(&res[i]);
   }

   printf("running  successful!!! Fp3 over Fp2 \n");

}

void Fp6_3over2correctness(){


    bigInteger A0[2];
    bigInteger A1[2];
    bigInteger A2[2];
    bigInteger B0[2];
    bigInteger B1[2];
    bigInteger B2[2];

    bigIntIniCoefficient(A0,2);
	bigIntIniCoefficient(A1,2);
	bigIntIniCoefficient(A2,2);
    bigIntIniCoefficient(B0,2);
    bigIntIniCoefficient(B1,2);
    bigIntIniCoefficient(B2,2);

    bigIntReadRadix(&A0[0],"4780980462549360001537440270759544",10);
    bigIntReadRadix(&A0[1],"136788663229656498050124454900459064666438095143",10);
	bigIntReadRadix(&A1[0],"7263439886205329312014220354025124468383",10);
	bigIntReadRadix(&A1[1],"36412158838097815285791904561610269050933802353878455607984725",10);
    bigIntReadRadix(&A2[0],"5911162540845786849770848848270875237114763275929070953117600627812097450035732318361747573512777",10);
	bigIntReadRadix(&A2[1],"159686747515130980",10);
	bigIntReadRadix(&B0[0],"250343465177550801847724450444092542727243115861135852263950857253516122174795493676521735470356765",10);
    bigIntReadRadix(&B0[1],"84223575076423805545275673",10);
    bigIntReadRadix(&B1[0],"870915705858294067451463566004417375",10);
    bigIntReadRadix(&B1[1],"487022499827935450189646041613856478932162605875911988097711403759338826267399205734638324743",10);
    bigIntReadRadix(&B2[0],"81294844621782120537648742",10);
    bigIntReadRadix(&B2[1],"3375242620551308539700253453886092219083782303841811120941556271809100066871363",10);

    bigInteger res[6];
    bigIntIniCoefficient(res,6);
    Fp6_3over2input(A0,A1,A2,B0,B1,B2,res);

    bigInteger knowresult[6];
    bigIntIniCoefficient(knowresult,6);

    bigIntReadRadix(&knowresult[0],"85800143282965758360121360077529300973332841985286043579496463466213216600654160587087176468745329918272914225037923986329187923709508",10);
    bigIntReadRadix(&knowresult[1],"184437605597647488914209932374293121213588594290959057086268410457630766113907762099412871148212882894777952801672656608253289431770431",10);
    bigIntReadRadix(&knowresult[2],"35750072860174637548347072203409488331925988053976563250282443593390635651115660462333162189444905245663657716480239103084952851000635",10);
    bigIntReadRadix(&knowresult[3],"141690321958857672055342353530940944303846331144338543940725719167163068266594624935714524232875527411843056721538491107190080907206800",10);
    bigIntReadRadix(&knowresult[4],"10168019765005469561858351169535651442841758777945729755408086856642583116189080767099233217569761060191998369855261442926232717731031",10);
    bigIntReadRadix(&knowresult[5],"218297830369728742330152974862862818564584559906127653131383747967683018632902788510653482714029743138956223290851196384750844018693963",10);


    if( bigIntSignCom(&res[0],&knowresult[0]) != EQUAL){
		printf("the result is wrong!!!! \n");
	}
	if( bigIntSignCom(&res[1],&knowresult[1]) != EQUAL){
		printf("the result is wrong!!!! \n");
	}
	if( bigIntSignCom(&res[2],&knowresult[2]) != EQUAL){
		printf("the result is wrong!!!! \n");
	}
	if( bigIntSignCom(&res[3],&knowresult[3]) != EQUAL){
		printf("the result is wrong!!!! \n");
	}
	if( bigIntSignCom(&res[4],&knowresult[4]) != EQUAL){
		printf("the result is wrong!!!! \n");
	}
	if( bigIntSignCom(&res[5],&knowresult[5]) != EQUAL){
		printf("the result is wrong!!!! \n");
	}
	else{
		printf("the correctness of fp 6 3over2 is success!!!!!!!!! \n");
	}
}

void testFp6_2over3(){

   bigInteger A0[3];
   bigInteger A1[3];
   bigInteger B0[3];
   bigInteger B1[3];

   setRandCo(A0,3);
   setRandCo(A1,3);
   setRandCo(B0,3);
   setRandCo(B1,3);

   printf("the A0[0] is \n");
   bigIntPrint(&A0[0]);
   printf("the A0[1] is \n");
   bigIntPrint(&A0[1]);
   printf("the A0[2] is \n");
   bigIntPrint(&A0[2]);
   printf("the A1[0] is \n");
   bigIntPrint(&A1[0]);
   printf("the A1[1] is \n");
   bigIntPrint(&A1[1]);
   printf("the A1[2] is \n");
   bigIntPrint(&A1[2]);
   printf("the B0[0] is \n");
   bigIntPrint(&B0[0]);
   printf("the B0[1] is \n");
   bigIntPrint(&B0[1]);
   printf("the B0[2] is \n");
   bigIntPrint(&B0[2]);
   printf("the B1[0] is \n");
   bigIntPrint(&B1[0]);
   printf("the B1[1] is \n");
   bigIntPrint(&B1[1]);
   printf("the B1[2] is \n");
   bigIntPrint(&B1[2]);

   bigInteger res[6];
   bigIntIniCoefficient(res,6);

   Fp6_2over3input(A0,A1,B0,B1,res);

   printf("the result is \n");
   for(int i = 0; i<6; i++){
       bigIntPrint(&res[i]);
   }

   printf("running successful!!! Fp2 over Fp3 \n");


}

void Fp6_2over3correctness(){

	bigInteger A0[3];
	bigInteger A1[3];
	bigInteger B0[3];
	bigInteger B1[3];

    bigIntIniCoefficient(A0,3);
	bigIntIniCoefficient(A1,3);
    bigIntIniCoefficient(B0,3);
    bigIntIniCoefficient(B1,3);

    bigIntReadRadix(&A0[0],"7094349252593797145566183686359419542209",10);
    bigIntReadRadix(&A0[1],"33512479879937592205614424347935003724335433829213129804",10);
	bigIntReadRadix(&A0[2],"7150433875238013320845849409114843578378959128416823312745343605061179603701165748460717285",10);
	bigIntReadRadix(&A1[0],"81849025367996890340951304659389588816863538893926624",10);
    bigIntReadRadix(&A1[1],"74090962520494024529602826313369011548168178566260179536840116",10);
	bigIntReadRadix(&A1[2],"83521269",10);
	bigIntReadRadix(&B0[0],"123409039106982003183885795065322780660355809599228057532032862627",10);
    bigIntReadRadix(&B0[1],"27939394034010717781455276535511028542267888558883234743188",10);
    bigIntReadRadix(&B0[2],"5470474290903625836843833643333199394872878887528587507521145343253820619955",10);
    bigIntReadRadix(&B1[0],"741151380691737613614453605892",10);
    bigIntReadRadix(&B1[1],"287928617875800735892744554746521750930610660812619653072163636828156224176772018982",10);
    bigIntReadRadix(&B1[2],"1453029990325085616327",10);

    bigInteger res[6];
    bigIntIniCoefficient(res,6);
    Fp6_2over3input(A0,A1,B0,B1,res);

    bigInteger knowresult[6];
    bigIntIniCoefficient(knowresult,6);

    bigIntReadRadix(&knowresult[0],"62557367506286329092786508967220337224730567615371553132436190235853560058577428707356326603075051066724754004023645536844473262180383",10);
    bigIntReadRadix(&knowresult[1],"83064343340478916671118689223365636522242269386864334259427646981982284416554977633116478216417489469680161963938601126303436437710544",10);
    bigIntReadRadix(&knowresult[2],"53312165251936853160086026796085057757630605149322273894630888934663715232621157656596177671358330637798404678714138922273455952905040",10);
    bigIntReadRadix(&knowresult[3],"37729867322199873793133287945475055460209366376826227140725627785894724413735558669901986855566552491201591995145791859001480472498494",10);
    bigIntReadRadix(&knowresult[4],"73575421190240445461174475092321208574575831277782377578684921913791794499471083860030460941836047208800292722690306494023447529525332",10);
    bigIntReadRadix(&knowresult[5],"132463462776022228445610681694985522919880266335674666931817457117820193578471018781507699820308512482147985565032306370200880620747467",10);


    if( bigIntSignCom(&res[0],&knowresult[0]) != EQUAL){
		printf("the result is wrong!!!! \n");
	}
	if( bigIntSignCom(&res[1],&knowresult[1]) != EQUAL){
		printf("the result is wrong!!!! \n");
	}
	if( bigIntSignCom(&res[2],&knowresult[2]) != EQUAL){
		printf("the result is wrong!!!! \n");
	}
	if( bigIntSignCom(&res[3],&knowresult[3]) != EQUAL){
		printf("the result is wrong!!!! \n");
	}
	if( bigIntSignCom(&res[4],&knowresult[4]) != EQUAL){
		printf("the result is wrong!!!! \n");
	}
	if( bigIntSignCom(&res[5],&knowresult[5]) != EQUAL){
		printf("the result is wrong!!!! \n");
	}
	else{
		printf("the correctness of fp 6 2over3 is success!!!!!!!!!   \n");
	}
}

void testFp12_2over2over3(){

    bigInteger A00[3];
    bigInteger A01[3];
    bigInteger A10[3];
    bigInteger A11[3];
    bigInteger B00[3];
    bigInteger B01[3];
    bigInteger B10[3];
    bigInteger B11[3];

	setRandCo(A00,3);
	setRandCo(A01,3);
	setRandCo(A10,3);
	setRandCo(A11,3);
    setRandCo(B00,3);
	setRandCo(B01,3);
	setRandCo(B10,3);
	setRandCo(B11,3);


   printf("the A00[0] is \n");
   bigIntPrint(&A00[0]);
   printf("the A00[1] is \n");
   bigIntPrint(&A00[1]);
   printf("the A00[2] is \n");
   bigIntPrint(&A00[2]);
   printf("the A01[0] is \n");
   bigIntPrint(&A01[0]);
   printf("the A01[1] is \n");
   bigIntPrint(&A01[1]);
   printf("the A01[2] is \n");
   bigIntPrint(&A01[2]);
   printf("the A10[0] is \n");
   bigIntPrint(&A10[0]);
   printf("the A10[1] is \n");
   bigIntPrint(&A10[1]);
   printf("the A10[2] is \n");
   bigIntPrint(&A10[2]);
   printf("the A11[0] is \n");
   bigIntPrint(&A11[0]);
   printf("the A11[1] is \n");
   bigIntPrint(&A11[1]);
   printf("the A11[2] is \n");
   bigIntPrint(&A11[2]); 
   printf("the B00[0] is \n");
   bigIntPrint(&B00[0]);
   printf("the B00[1] is \n");
   bigIntPrint(&B00[1]);
   printf("the B00[2] is \n");
   bigIntPrint(&B00[2]);
   printf("the B01[0] is \n");
   bigIntPrint(&B01[0]);
   printf("the B01[1] is \n");
   bigIntPrint(&B01[1]);
   printf("the B01[2] is \n");
   bigIntPrint(&B01[2]);
   printf("the B10[0] is \n");
   bigIntPrint(&B10[0]);
   printf("the B10[1] is \n");
   bigIntPrint(&B10[1]);
   printf("the B10[2] is \n");
   bigIntPrint(&B10[2]);
   printf("the B11[0] is \n");
   bigIntPrint(&B11[0]);
   printf("the B11[1] is \n");
   bigIntPrint(&B11[1]);
   printf("the B11[2] is \n");
   bigIntPrint(&B11[2]); 


	bigInteger result[12];
	bigIntIniCoefficient(result, 12);
	Fp12_2over2over3(A00,A01,A10,A11,B00,B01,B10,B11,result);
	for(int i =0; i<12; i++){
		printf("the %d coefficient is \n",i);
		bigIntPrint(&result[i]);
	}

	printf("running Fp2 over Fp2 over Fp3 is successful !! \n");
}

void Fp12_2over2over3correctness(){

	bigInteger A00[3];
    bigInteger A01[3];
    bigInteger A10[3];
    bigInteger A11[3];
    bigInteger B00[3];
    bigInteger B01[3];
    bigInteger B10[3];
    bigInteger B11[3];

    bigIntIniCoefficient(A00,3);
	bigIntIniCoefficient(A01,3);
    bigIntIniCoefficient(A10,3);
    bigIntIniCoefficient(A11,3);
    bigIntIniCoefficient(B00,3);
	bigIntIniCoefficient(B01,3);
    bigIntIniCoefficient(B10,3);
    bigIntIniCoefficient(B11,3);



    bigIntReadRadix(&A00[0],"4516641795365133599901385967614250862080267164176804955503488979736319814929",10);
    bigIntReadRadix(&A00[1],"241436329917884994076003949396809963084152",10);
	bigIntReadRadix(&A00[2],"361830097405266846503641752299447473263997471483081778445634",10);
	bigIntReadRadix(&A01[0],"0",10);
    bigIntReadRadix(&A01[1],"162205322536541709244",10);
	bigIntReadRadix(&A01[2],"1273",10);
	bigIntReadRadix(&A10[0],"36105818033738528652799397964803707510",10);
    bigIntReadRadix(&A10[1],"6354973447057537578824198575032773065361530816241867679370893306746683267362380800078151271664013",10);
    bigIntReadRadix(&A10[2],"64689625587434064385196",10);
    bigIntReadRadix(&A11[0],"803641711475661694827869696470127204850004510208570111844725087388191932654408457036668243985118523",10);
    bigIntReadRadix(&A11[1],"259933624918",10);
    bigIntReadRadix(&A11[2],"2035261409160814877345303259921218709",10);
    bigIntReadRadix(&B00[0],"23",10);
    bigIntReadRadix(&B00[1],"9",10);
	bigIntReadRadix(&B00[2],"815771848300573442628702862389",10);
	bigIntReadRadix(&B01[0],"9",10);
    bigIntReadRadix(&B01[1],"919432023513890775573384580901192404997818594194918860677",10);
	bigIntReadRadix(&B01[2],"153747863120529316116295034413100208241142457750897534361099269732679385767286738656860424",10);
	bigIntReadRadix(&B10[0],"2748483025191283916453959269263744982765475700322702299",10);
    bigIntReadRadix(&B10[1],"7572582981135971814564460951148471152400436019422176890915134826095839884479",10);
    bigIntReadRadix(&B10[2],"4501229449229791181472756754628778031589436675949848842212668712359430",10);
    bigIntReadRadix(&B11[0],"8694528979227",10);
    bigIntReadRadix(&B11[1],"68388",10);
    bigIntReadRadix(&B11[2],"1229943819178428635745010914335508515022516",10);



    bigInteger knowresult[12];
    bigIntIniCoefficient(knowresult,12);

    bigIntReadRadix(&knowresult[0],"186827491459223876493251766288876912657248756820937074582887602503133786925153263582470654578453919694889020702833608325256608919569354",10);
    bigIntReadRadix(&knowresult[1],"57603928826517571234383976712949045850593615300566166388216331340601853920540436576279216128916538327475196991425860657451783001308392",10);
    bigIntReadRadix(&knowresult[2],"180439431462947692834526086863390869345918345661927593589386520098021158527396272180118243353290284726393380352849068392453433715565082",10);
    bigIntReadRadix(&knowresult[3],"4770445378081101629028597005027364329270620884536753965076617842950704097524891187366969469620157667305694536961106080741905381280136",10);
    bigIntReadRadix(&knowresult[4],"2033389958330878197174482380539928930366250789113355661146551026975862797776406521714322962130336917583113382517204903479870118414131",10);
    bigIntReadRadix(&knowresult[5],"214499316028533603825413799445393594501107159980757115654790823927816178022380803603071627674026766842795205955956595101004561476233152",10);
    bigIntReadRadix(&knowresult[6],"195779117822990849846456203863374817874056806899142363023809634122071436856683965087189879100303030794946196298378629918924026104641228",10);
    bigIntReadRadix(&knowresult[7],"116626558083274617962157275893113881126881321263299878446626206258067133662889414507865126640681389708098869414283745030598852686294534",10);
    bigIntReadRadix(&knowresult[8],"94877259324957126478594486573160406685773399675548794770254144867569560143666309136899258745129766411345189513355776490228886371571775",10);
    bigIntReadRadix(&knowresult[9],"210265237974161854565915729862339513397262814447854810858177028135838982832203108178800783794552461561218485234072838787647701155444088",10);
    bigIntReadRadix(&knowresult[10],"171840823095406700393028541094409171590899470399206958668025692261021876393556917168867392158842542681738009786685014453837150493935692",10);
    bigIntReadRadix(&knowresult[11],"199707635077986444118946139045800262105795631177204271806734241301952485950196896843719368600148098089231507417680401361405221846365381",10);

    bigInteger res[12];
	bigIntIniCoefficient(res, 12);
	Fp12_2over2over3(A00,A01,A10,A11,B00,B01,B10,B11,res);


    if( bigIntSignCom(&res[0],&knowresult[0]) != EQUAL){
		printf("the result is wrong!!!! \n");
	}
	if( bigIntSignCom(&res[1],&knowresult[1]) != EQUAL){
		printf("the result is wrong!!!! \n");
	}
	if( bigIntSignCom(&res[2],&knowresult[2]) != EQUAL){
		printf("the result is wrong!!!! \n");
	}
	if( bigIntSignCom(&res[3],&knowresult[3]) != EQUAL){
		printf("the result is wrong!!!! \n");
	}
	if( bigIntSignCom(&res[4],&knowresult[4]) != EQUAL){
		printf("the result is wrong!!!! \n");
	}
	if( bigIntSignCom(&res[5],&knowresult[5]) != EQUAL){
		printf("the result is wrong!!!! \n");
	}
    if( bigIntSignCom(&res[6],&knowresult[6]) != EQUAL){
		printf("the result is wrong!!!! \n");
	}
	if( bigIntSignCom(&res[7],&knowresult[7]) != EQUAL){
		printf("the result is wrong!!!! \n");
	}
	if( bigIntSignCom(&res[8],&knowresult[8]) != EQUAL){
		printf("the result is wrong!!!! \n");
	}
	if( bigIntSignCom(&res[9],&knowresult[9]) != EQUAL){
		printf("the result is wrong!!!! \n");
	}
	if( bigIntSignCom(&res[10],&knowresult[10]) != EQUAL){
		printf("the result is wrong!!!! \n");
	}
	if( bigIntSignCom(&res[11],&knowresult[11]) != EQUAL){
		printf("the result is wrong!!!! \n");
	}


	else{
		printf("the correctness of fp 12 2over2over3 is success!!!!!!!!! \n");
	}

}


void testFp12_2over3over2(){


	bigInteger A00[2];
    bigInteger A01[2];
    bigInteger A02[2];
    bigInteger A10[2];
    bigInteger A11[2];
    bigInteger A12[2];
    bigInteger B00[2];
    bigInteger B01[2];
    bigInteger B02[2];
    bigInteger B10[2];
    bigInteger B11[2];
    bigInteger B12[2];

	setRandCo(A00,2);
	setRandCo(A01,2);
	setRandCo(A02,2);
    setRandCo(A10,2);
	setRandCo(A11,2);
	setRandCo(A12,2);
    setRandCo(B00,2);
	setRandCo(B01,2);
	setRandCo(B02,2);
    setRandCo(B10,2);
	setRandCo(B11,2);
	setRandCo(B12,2);


    printf("the A00[0] is \n");
    bigIntPrint(&A00[0]);
    printf("the A00[1] is \n");
    bigIntPrint(&A00[1]);
    printf("the A01[0] is \n");
    bigIntPrint(&A01[0]);
    printf("the A01[1] is \n");
    bigIntPrint(&A01[1]);
    printf("the A02[0] is \n");
    bigIntPrint(&A02[0]);
    printf("the A02[1] is \n");
    bigIntPrint(&A02[1]);
    printf("the A10[0] is \n");
    bigIntPrint(&A10[0]);
    printf("the A10[1] is \n");
    bigIntPrint(&A10[1]);
    printf("the A11[0] is \n");
    bigIntPrint(&A11[0]);
    printf("the A11[1] is \n");
    bigIntPrint(&A11[1]);
    printf("the A12[0] is \n");
    bigIntPrint(&A12[0]);
    printf("the A12[1] is \n");
    bigIntPrint(&A12[1]); 
    printf("the B00[0] is \n");
    bigIntPrint(&B00[0]);
    printf("the B00[1] is \n");
    bigIntPrint(&B00[1]);
    printf("the B01[0] is \n");
    bigIntPrint(&B01[0]);
    printf("the B01[1] is \n");
    bigIntPrint(&B01[1]);
    printf("the B02[0] is \n");
    bigIntPrint(&B02[0]);
    printf("the B02[1] is \n");
    bigIntPrint(&B02[1]);
    printf("the B10[0] is \n");
    bigIntPrint(&B10[0]);
    printf("the B10[1] is \n");
    bigIntPrint(&B10[1]);
    printf("the B11[0] is \n");
    bigIntPrint(&B11[0]);
    printf("the B11[1] is \n");
    bigIntPrint(&B11[1]);
    printf("the B12[0] is \n");
    bigIntPrint(&B12[0]);
    printf("the B12[1] is \n");
    bigIntPrint(&B12[1]); 


	bigInteger result[12];
	bigIntIniCoefficient(result, 12);
	Fp12_2over3over2(A00,A01,A02,A10,A11,A12,B00,B01,B02,B10,B11,B12, result);
	for(int i =0; i<12; i++){
		printf("the %d coefficient is \n",i);
		bigIntPrint(&result[i]);
	}

	printf("running fp12 (FP2 over Fp3 over Fp2) is successful!! \n");

}

void Fp12_2over3over2correctness(){


	bigInteger A00[2];
    bigInteger A01[2];
    bigInteger A02[2];
    bigInteger A10[2];
    bigInteger A11[2];
    bigInteger A12[2];
    bigInteger B00[2];
    bigInteger B01[2];
    bigInteger B02[2];
    bigInteger B10[2];
    bigInteger B11[2];
    bigInteger B12[2];


    bigIntIniCoefficient(A00,2);
	bigIntIniCoefficient(A01,2);
	bigIntIniCoefficient(A02,2);
    bigIntIniCoefficient(A10,2);
    bigIntIniCoefficient(A11,2);
	bigIntIniCoefficient(A12,2);
    bigIntIniCoefficient(B00,2);
	bigIntIniCoefficient(B01,2);
	bigIntIniCoefficient(B02,2);
    bigIntIniCoefficient(B10,2);
    bigIntIniCoefficient(B11,2);
	bigIntIniCoefficient(B12,2);


    bigIntReadRadix(&A00[0],"905501245681",10);
    bigIntReadRadix(&A00[1],"12730790490876112642096503",10);
	bigIntReadRadix(&A01[0],"4070845690690064952915683750431948149648817849915912216580226994520852934463672814422",10);
	bigIntReadRadix(&A01[1],"8554693571577200662823050288322404526542775235986",10);
    bigIntReadRadix(&A02[0],"8956815150494039535060769187909127262804515510556193161225062762632286086722437728581652",10);
	bigIntReadRadix(&A02[1],"1",10);
	bigIntReadRadix(&A10[0],"56930985525489560989055448830413261559789772531665361290011103239073744306244",10);
    bigIntReadRadix(&A10[1],"91025482613881990196504887847664833461130232081431266146870210341032720799",10);
    bigIntReadRadix(&A11[0],"3058848179377319353",10);
    bigIntReadRadix(&A11[1],"189397549256484652279967823564214937575940797470604044412595200422888191813767259153883038",10);
    bigIntReadRadix(&A12[0],"60575830890362444069285684981359326762222274191",10);
    bigIntReadRadix(&A12[1],"6510816704619617604437574545799224502680404207746554593",10);
    bigIntReadRadix(&B00[0],"430447354104732586077465705729307863295268406632274712322355682130680981978079602884312",10);
    bigIntReadRadix(&B00[1],"11294495805461990452989995484086549605542246517684472855844196121146515893755848413315233372046708",10);
	bigIntReadRadix(&B01[0],"13252140980612214888945229560411258495219677267846974341054186988",10);
	bigIntReadRadix(&B01[1],"345971113495181653906590",10);
    bigIntReadRadix(&B02[0],"7430914765572508009469887425352109399565855947076984188196872894628451215772088906518628612202639",10);
	bigIntReadRadix(&B02[1],"2260633952009275616059100656943515173767086328774367434193830134646245529120958058606207",10);
	bigIntReadRadix(&B10[0],"717919478834114296821949495639374370507767855278732723191189015178178939",10);
    bigIntReadRadix(&B10[1],"7187774535697007829784253591003608880974203090291182815996946431222728973427475484837221",10);
    bigIntReadRadix(&B11[0],"961010091824021095544407877736324589827273554112624793811326886911892764367914549643412260115632",10);
    bigIntReadRadix(&B11[1],"773596171108128562398905088736434184905731500",10);
    bigIntReadRadix(&B12[0],"87537674345659811314008225171362536530086",10);
    bigIntReadRadix(&B12[1],"160734911084767728503961706838983203915223542121575741460145424561716",10);

    bigInteger knowresult[12];
    bigIntIniCoefficient(knowresult,12);

    bigIntReadRadix(&knowresult[0],"135839229175292122525744404566180608121695485979493904324146476819223167254239016452443552837467866510166751444670163176539316698516268",10);
    bigIntReadRadix(&knowresult[1],"98226366164196077227593331544516087879203248728161274200006729330257241817773785825887271481767481690797379331800736779503357354880655",10);
    bigIntReadRadix(&knowresult[2],"151372364852624819474138031712982613882571975628177259303480024654990711987029055156815349199354947901303026897909615225492824103931667",10);
    bigIntReadRadix(&knowresult[3],"208503157683028537534694214271198907169350283872689024933486880655901089126884042253613418074820487132371906521054741986897610548535609",10);
    bigIntReadRadix(&knowresult[4],"105145577958791867575918386359059599232896799243511470029089965203700293254016807611370068922617581618002393042342597413973094034176814",10);
    bigIntReadRadix(&knowresult[5],"184313735811939573602944487601438787347839227328927486271013227030731731366515590370260404646323506323478990745650302862996791854342668",10);
    bigIntReadRadix(&knowresult[6],"23679076850198625930052463016416852725537043105582011600434579297005933261021342899368078326813592645505256505703137274010711580714893",10);
    bigIntReadRadix(&knowresult[7],"131422682423004928714695644618202449689377389823689286955804413076392075796432428044646890640860131606865572143457755166178797360768913",10);
    bigIntReadRadix(&knowresult[8],"169277913374558497611022878944104016984506418398706604665521711880335672275414932764098450150651555111328769067630693167595675193205946",10);
    bigIntReadRadix(&knowresult[9],"155562878659816369939994014240635235661270673616241265983449304788655895924417861943127789298253879759885367448986151481224888909229702",10);
    bigIntReadRadix(&knowresult[10],"965246632065876113177036683192802454965072861870504962895275272111484177929124580051228325866713529766369080490092139257752105295299",10);
    bigIntReadRadix(&knowresult[11],"24208951488220693170163855270002186365838119462772475007040737581557583723937553766854266313200072314944381442796694969257887713006763",10);

    bigInteger res[12];
	bigIntIniCoefficient(res, 12);
	Fp12_2over3over2(A00,A01,A02,A10,A11,A12,B00,B01,B02,B10,B11,B12,res);


    if( bigIntSignCom(&res[0],&knowresult[0]) != EQUAL){
		printf("the result is 1 wrong!!!! \n");
	}
	if( bigIntSignCom(&res[1],&knowresult[1]) != EQUAL){
		printf("the result is 2 wrong!!!! \n");
	}
	if( bigIntSignCom(&res[2],&knowresult[2]) != EQUAL){
		printf("the result is 3 wrong!!!! \n");
	}
	if( bigIntSignCom(&res[3],&knowresult[3]) != EQUAL){
		printf("the result is 4 wrong!!!! \n");
	}
	if( bigIntSignCom(&res[4],&knowresult[4]) != EQUAL){
		printf("the result is 5 wrong!!!! \n");
	}
	if( bigIntSignCom(&res[5],&knowresult[5]) != EQUAL){
		printf("the result is 6 wrong!!!! \n");
	}
    if( bigIntSignCom(&res[6],&knowresult[6]) != EQUAL){
		printf("the result is 7 wrong!!!! \n");
	}
	if( bigIntSignCom(&res[7],&knowresult[7]) != EQUAL){
		printf("the result is 8 wrong!!!! \n");
	}
	if( bigIntSignCom(&res[8],&knowresult[8]) != EQUAL){
		printf("the result is 9 wrong!!!! \n");
	}
	if( bigIntSignCom(&res[9],&knowresult[9]) != EQUAL){
		printf("the result is 10 wrong!!!! \n");
	}
	if( bigIntSignCom(&res[10],&knowresult[10]) != EQUAL){
		printf("the result is 11 wrong!!!! \n");
	}
	if( bigIntSignCom(&res[11],&knowresult[11]) != EQUAL){
		printf("the result is 12 wrong!!!! \n");
	}

	else{
		printf("the correctness of fp 12 2over3over2 is success!!!!!!!!! \n");
	}

}

void testFp12_3over2over2(){

   bigInteger A00[2];
   bigInteger A01[2];
   bigInteger A10[2];
   bigInteger A11[2];
   bigInteger A20[2];
   bigInteger A21[2];
   bigInteger B00[2];
   bigInteger B01[2];
   bigInteger B10[2];
   bigInteger B11[2];
   bigInteger B20[2];
   bigInteger B21[2];

   setRandCo(A00,2);
   setRandCo(A01,2);
   setRandCo(A10,2);
   setRandCo(A11,2);
   setRandCo(A20,2);
   setRandCo(A21,2);
   setRandCo(B00,2);
   setRandCo(B01,2);
   setRandCo(B10,2);
   setRandCo(B11,2);
   setRandCo(B20,2);
   setRandCo(B21,2);


    printf("the A00[0] is \n");
    bigIntPrint(&A00[0]);
    printf("the A00[1] is \n");
    bigIntPrint(&A00[1]);
    printf("the A01[0] is \n");
    bigIntPrint(&A01[0]);
    printf("the A01[1] is \n");
    bigIntPrint(&A01[1]);
    printf("the A10[0] is \n");
    bigIntPrint(&A10[0]);
    printf("the A10[1] is \n");
    bigIntPrint(&A10[1]);
    printf("the A11[0] is \n");
    bigIntPrint(&A11[0]);
    printf("the A11[1] is \n");
    bigIntPrint(&A11[1]);
    printf("the A20[0] is \n");
    bigIntPrint(&A20[0]);
    printf("the A20[1] is \n");
    bigIntPrint(&A20[1]);
    printf("the A21[0] is \n");
    bigIntPrint(&A21[0]);
    printf("the A21[1] is \n");
    bigIntPrint(&A21[1]);

    printf("the B00[0] is \n");
    bigIntPrint(&B00[0]);
    printf("the B00[1] is \n");
    bigIntPrint(&B00[1]);
    printf("the B01[0] is \n");
    bigIntPrint(&B01[0]);
    printf("the B01[1] is \n");
    bigIntPrint(&B01[1]);
    printf("the B10[0] is \n");
    bigIntPrint(&B10[0]);
    printf("the B10[1] is \n");
    bigIntPrint(&B10[1]);
    printf("the B11[0] is \n");
    bigIntPrint(&B11[0]);
    printf("the B11[1] is \n");
    bigIntPrint(&B11[1]);
    printf("the B20[0] is \n");
    bigIntPrint(&B20[0]);
    printf("the B20[1] is \n");
    bigIntPrint(&B20[1]);
    printf("the B21[0] is \n");
    bigIntPrint(&B21[0]);
    printf("the B21[1] is \n");
    bigIntPrint(&B21[1]);


	bigInteger result[12];
	bigIntIniCoefficient(result, 12);
	Fp12_3over2over2(A00,A01,A10,A11,A20,A21,B00,B01,B10,B11,B20,B21, result);
	for(int i =0; i<12; i++){
		printf("the %d coefficient is \n",i);
		bigIntPrint(&result[i]);
	}

	printf("running Fp3 over Fp2 over Fp2 is successful!!! \n");

}

void Fp12_3over2over2correctness(){




    bigInteger A00[2];
    bigInteger A01[2];
    bigInteger A10[2];
    bigInteger A11[2];
    bigInteger A20[2];
    bigInteger A21[2];
    bigInteger B00[2];
    bigInteger B01[2];
    bigInteger B10[2];
    bigInteger B11[2];
    bigInteger B20[2];
    bigInteger B21[2];

    bigIntIniCoefficient(A00,2);
	bigIntIniCoefficient(A01,2);
	bigIntIniCoefficient(A10,2);
    bigIntIniCoefficient(A11,2);
    bigIntIniCoefficient(A20,2);
	bigIntIniCoefficient(A21,2);
    bigIntIniCoefficient(B00,2);
	bigIntIniCoefficient(B01,2);
	bigIntIniCoefficient(B10,2);
    bigIntIniCoefficient(B11,2);
    bigIntIniCoefficient(B20,2);
	bigIntIniCoefficient(B21,2);

    bigIntReadRadix(&A00[0],"22829766658602194877263827514140679991427728",10);
    bigIntReadRadix(&A00[1],"752161398385948493354381478094261988169943138753955599136323242",10);
	bigIntReadRadix(&A01[0],"9286114",10);
	bigIntReadRadix(&A01[1],"64914477277971802279122437546028935845111410349295633",10);
    bigIntReadRadix(&A10[0],"3754042945006253509800598201846320046875278191748844666347298236712980544",10);
	bigIntReadRadix(&A10[1],"173532082084705557816244000705554548311350206334",10);
	bigIntReadRadix(&A11[0],"779898271682629185146560462605333907433011348067",10);
    bigIntReadRadix(&A11[1],"212035621378802655034629367288585763854335824",10);
    bigIntReadRadix(&A20[0],"64430988504547582332437229358122281194445753251163235622809773965956363813596901371242788",10);
    bigIntReadRadix(&A20[1],"5201545088944898475829961289619358020533588335179391027222857602605961704754",10);
    bigIntReadRadix(&A21[0],"4424276131900167821436909770752054",10);
    bigIntReadRadix(&A21[1],"370165756878600246367187470641141946424373530993690195366",10);
    bigIntReadRadix(&B00[0],"4349",10);
    bigIntReadRadix(&B00[1],"5425",10);
	bigIntReadRadix(&B01[0],"8957703665914475075",10);
	bigIntReadRadix(&B01[1],"6863646011146796479671135248729",10);
    bigIntReadRadix(&B10[0],"56592",10);
	bigIntReadRadix(&B10[1],"2752849557147122472409856198514818284137364963189594618384364419560293430573929000382081979453696",10);
	bigIntReadRadix(&B11[0],"684300956702065101609357106558540256347185551419044780324094132439048147",10);
    bigIntReadRadix(&B11[1],"316343169397684368095457907033887591862047685831080451724087474",10);
    bigIntReadRadix(&B20[0],"6604843092679201314376505169102029978197543035381755289236054312458383948724192828",10);
    bigIntReadRadix(&B20[1],"906260028637662997068823047729211380949142387100986614030223539308590992302230802716475105959606642",10);
    bigIntReadRadix(&B21[0],"745331629",10);
    bigIntReadRadix(&B21[1],"89584466720024442",10);


    bigInteger knowresult[12];
    bigIntIniCoefficient(knowresult,12);

    bigIntReadRadix(&knowresult[0],"102052464252118529453944226977793500124123458159186669183083294216378113818622431795870499869856037662945489357770568853530072238734546",10);
    bigIntReadRadix(&knowresult[1],"181459730403793179469429450630449968411490150881710411230293937967831865317103138610911264095226497409382182638526520608589326845088151",10);
    bigIntReadRadix(&knowresult[2],"67310031432015818307004655702201481911912546690191447800606957599643778082862676777299719482405937060690572007360254912558673585711804",10);
    bigIntReadRadix(&knowresult[3],"198206227911876657387871073135403731476018942711047692378632277476773302881366868932735373838189515278679484130152932943371493233181071",10);
    bigIntReadRadix(&knowresult[4],"103174960258326778705935683215342904671442667726070186913423222084946290376473438163767184852101218828110781940185396176190252322559895",10);
    bigIntReadRadix(&knowresult[5],"40931529332142915075726104372830719470067652974172767293237503980295966650268216516113623049702644924459435775091865363532777921768944",10);
    bigIntReadRadix(&knowresult[6],"80256451122438195333649818798308882566676450656714759539573829116053093409450210846532718736461335438047531277038524499400502452340956",10);
    bigIntReadRadix(&knowresult[7],"168005375634520125670783377479335713764475352274127901350930795730631382232121757902070832546684249982361600395051063363674056504941873",10);
    bigIntReadRadix(&knowresult[8],"103677246257715014941147832476245878775010845127922396592166149507784451950504481459099750247202921292768733418199102844827358744370180",10);
    bigIntReadRadix(&knowresult[9],"63264760999311907544282401089646898114621129846612288884852970971755501111588714374564388216780909586107736283490436587054435129113278",10);
    bigIntReadRadix(&knowresult[10],"623874548395338924363112906039289673143706415030712703327298146036388095247149357240820286314253361201781667110237042351612470615694",10);
    bigIntReadRadix(&knowresult[11],"31798157568529429528414241029755672455140311109964461337011444247955514932178567144989892692689937929196728103953090810308819848247308",10);


    bigInteger res[12];
	bigIntIniCoefficient(res, 12);
	Fp12_3over2over2(A00,A01,A10,A11,A20,A21,B00,B01,B10,B11,B20,B21,res);


    if( bigIntSignCom(&res[0],&knowresult[0]) != EQUAL){
		printf("the result is wrong!!!! \n");
	}
	if( bigIntSignCom(&res[1],&knowresult[1]) != EQUAL){
		printf("the result is wrong!!!! \n");
	}
	if( bigIntSignCom(&res[2],&knowresult[2]) != EQUAL){
		printf("the result is wrong!!!! \n");
	}
	if( bigIntSignCom(&res[3],&knowresult[3]) != EQUAL){
		printf("the result is wrong!!!! \n");
	}
	if( bigIntSignCom(&res[4],&knowresult[4]) != EQUAL){
		printf("the result is wrong!!!! \n");
	}
	if( bigIntSignCom(&res[5],&knowresult[5]) != EQUAL){
		printf("the result is wrong!!!! \n");
	}
    if( bigIntSignCom(&res[6],&knowresult[6]) != EQUAL){
		printf("the result is wrong!!!! \n");
	}
	if( bigIntSignCom(&res[7],&knowresult[7]) != EQUAL){
		printf("the result is wrong!!!! \n");
	}
	if( bigIntSignCom(&res[8],&knowresult[8]) != EQUAL){
		printf("the result is wrong!!!! \n");
	}
	if( bigIntSignCom(&res[9],&knowresult[9]) != EQUAL){
		printf("the result is wrong!!!! \n");
	}
	if( bigIntSignCom(&res[10],&knowresult[10]) != EQUAL){
		printf("the result is wrong!!!! \n");
	}
	if( bigIntSignCom(&res[11],&knowresult[11]) != EQUAL){
		printf("the result is wrong!!!! \n");
	}

	else{
		printf("the correctness of fp 12 3over2over2 is success!!!!!!!!!  \n");
	}



}


void testFp12_3overDirect4(){

     bigInteger m0[4];
     bigInteger m1[4];
     bigInteger m2[4];
     bigInteger n0[4];
     bigInteger n1[4];
     bigInteger n2[4];

	 setRandCo(m0,4);
	 setRandCo(m1,4);
	 setRandCo(m2,4);
	 setRandCo(n0,4);
	 setRandCo(n1,4);
	 setRandCo(n2,4);
	 
	 for(int i = 0; i<4; i++){
		 printf("print every elements!!! \n");
		 bigIntPrint(&m0[i]);
		 bigIntPrint(&m1[i]);
		 bigIntPrint(&m2[i]);
		 bigIntPrint(&n0[i]);
		 bigIntPrint(&n1[i]);
		 bigIntPrint(&n2[i]);
	 }

	 bigInteger res[12];
	 bigIntIniCoefficient(res,12);

	 Fp12_3overDirect4(m0,m1,m2,n0,n1,n2,res);
	 for(int i = 0; i<12; i++){
		 printf("the %d coefficient of result is\n ", i);
		 bigIntPrint(&res[i]);
	 }

	 printf("the test is okokokoko!!!  22:08 \n");
	
    

}

void Fp12_3overDirect4correctness(){

     bigInteger m0[4];
     bigInteger m1[4];
     bigInteger m2[4];

     bigInteger n0[4];
     bigInteger n1[4];
     bigInteger n2[4];

	 bigIntIniCoefficient(m0,4);
	 bigIntIniCoefficient(m1,4);
	 bigIntIniCoefficient(m2,4);
	 bigIntIniCoefficient(n0,4);
	 bigIntIniCoefficient(n1,4);
	 bigIntIniCoefficient(n2,4);




	 
    bigIntReadRadix(&m0[0],"963062351501032699198624105100584571676072179",10);
    bigIntReadRadix(&m0[1],"52976376288532814628183535167323370610547135327188771123038052901598686375594291655",10);
	bigIntReadRadix(&m0[2],"314990403356212931992906259365719605248457479866260827922167837905427649249291201",10);
	bigIntReadRadix(&m0[3],"53424769096723950064743360482126141307929422471694",10);
    bigIntReadRadix(&m1[0],"7877672501626020323586497762719083499578060582777493012",10);
	bigIntReadRadix(&m1[1],"5313407546875689074",10);
	bigIntReadRadix(&m1[2],"581153926606845179747721942281751022005738247114801462067263848813828652416685233108073",10);
    bigIntReadRadix(&m1[3],"328916616245356887344837760406841714571124735",10);
    bigIntReadRadix(&m2[0],"85292071319291761457687501568993125878214626885712",10);
    bigIntReadRadix(&m2[1],"10123887233402973624665969233633",10);
    bigIntReadRadix(&m2[2],"4143738632565235196010148181354452244508258338315246468540394316",10);
    bigIntReadRadix(&m2[3],"4378102602458701269168310320827740477471051310549207323570255783908847460",10);
    bigIntReadRadix(&n0[0],"5788196245011157233963790125337440427835895169414063485345370212427307796389731613",10);
    bigIntReadRadix(&n0[1],"427537168173956900685681282970231709",10);
	bigIntReadRadix(&n0[2],"7562687040450052174050920721591826622462636709329407318256290608950523648059112990517586",10);
	bigIntReadRadix(&n0[3],"9332744814757733135739522520923910787472783281384456341446521355892657410187953010",10);
    bigIntReadRadix(&n1[0],"4347116076274689",10);
	bigIntReadRadix(&n1[1],"719984778461438174199344580864596472194378581963347804016007",10);
	bigIntReadRadix(&n1[2],"5312700290894031173437656232047",10);
    bigIntReadRadix(&n1[3],"866074728366043",10);
    bigIntReadRadix(&n2[0],"61977934696413",10);
    bigIntReadRadix(&n2[1],"40039179757530419882916971",10);
    bigIntReadRadix(&n2[2],"745331629",10);
    bigIntReadRadix(&n2[3],"11231363250132400758295274869715702673309203757455431288",10);


    bigInteger knowresult[12];
    bigIntIniCoefficient(knowresult,12);

    bigIntReadRadix(&knowresult[0],"136568478610465133168114380943808342488101150727291769082571231303041964259942926498813863067857560213844417268522482539969463351965436",10);
    bigIntReadRadix(&knowresult[1],"80484006569799870836934053509954248102574223947657791585551899699476376974369959994707791468572199163774117934030938174038460409469977",10);
    bigIntReadRadix(&knowresult[2],"141613191891243527361625293588164410838438011040583483376585686622321761983702646543640032479215915045306474104245469198976355104795007",10);
    bigIntReadRadix(&knowresult[3],"108996565358474743454617390780637063228445909981676750330292162761025048821717028394960369302873375839083161455943065749831796558129254",10);
    bigIntReadRadix(&knowresult[4],"33612371125515442097880937492951694005274858673092156316658038522777647182938865996301061678452138238072041936552640036928421982682252",10);
    bigIntReadRadix(&knowresult[5],"55868826315853383863805142546443076682377877256543765927098242855916586389279743515503698512872971105682080582971379802910194217148070",10);
    bigIntReadRadix(&knowresult[6],"83009202791421343134675620306282704166296527721536582895294129068850459490664686108147419085447460093844742053794475214082130862273499",10);
    bigIntReadRadix(&knowresult[7],"161829540516513329591107890950552747284507834409265038577076942053324565027956935388535442562749543681761784415495589741538776486453551",10);
    bigIntReadRadix(&knowresult[8],"2976820705387128618139126964725468236804101087356753089403308034406575135085041030875175287840743958000198109980875621899276083022607",10);
    bigIntReadRadix(&knowresult[9],"101701515118981262340016056742419499781736318657190106622116121632025540228766061454570411960448422505513945191247273866933612871534350",10);
    bigIntReadRadix(&knowresult[10],"192579976095048207145145570509655618438246992920186104683626079445420997653856821251608843996927063907227880075247287094131339428237206",10);
    bigIntReadRadix(&knowresult[11],"125932490981993919765827519896570970932507743238070541360628470427340359905953396706629666314161339930022679774589319735508744867063455",10);



    
    bigInteger res[12];
	bigIntIniCoefficient(res, 12);
	Fp12_3overDirect4(m0,m1,m2,n0,n1,n2,res);

    if( bigIntSignCom(&res[0],&knowresult[0]) != EQUAL){
		printf("the result is wrong!!!! \n");
	}
	if( bigIntSignCom(&res[1],&knowresult[1]) != EQUAL){
		printf("the result is wrong!!!! \n");
	}
	if( bigIntSignCom(&res[2],&knowresult[2]) != EQUAL){
		printf("the result is wrong!!!! \n");
	}
	if( bigIntSignCom(&res[3],&knowresult[3]) != EQUAL){
		printf("the result is wrong!!!! \n");
	}
	if( bigIntSignCom(&res[4],&knowresult[4]) != EQUAL){
		printf("the result is wrong!!!! \n");
	}
	if( bigIntSignCom(&res[5],&knowresult[5]) != EQUAL){
		printf("the result is wrong!!!! \n");
	}
    if( bigIntSignCom(&res[6],&knowresult[6]) != EQUAL){
		printf("the result is wrong!!!! \n");
	}
	if( bigIntSignCom(&res[7],&knowresult[7]) != EQUAL){
		printf("the result is wrong!!!! \n");
	}
	if( bigIntSignCom(&res[8],&knowresult[8]) != EQUAL){
		printf("the result is wrong!!!! \n");
	}
	if( bigIntSignCom(&res[9],&knowresult[9]) != EQUAL){
		printf("the result is wrong!!!! \n");
	}
	if( bigIntSignCom(&res[10],&knowresult[10]) != EQUAL){
		printf("the result is wrong!!!! \n");
	}
	if( bigIntSignCom(&res[11],&knowresult[11]) != EQUAL){
		printf("the result is wrong!!!! \n");
	}

	else{
		printf("the correctness of fp 12 3over direct 4 is success!!!!!!!!!  \n");
	}


}


void setRandBigInt(bigInteger *x){

	char s[150];

	int len= rand() % 134;

	

	 for (int j=0;j<len;j++)
	{
	  if(j == 0){
        s[j] = '1' + (rand() % 9);
	  }
	  else{
	    s[j]=  '0' + (rand() % 10);
	  }
	}
	  s[len]='\0';

	  if (len>0)
	  {
		bigIntReadRadix(x,  s,  10);
	}


}


/*

    Multiplication in Fp2  (quadratic)

*/

// do one time multiplication in Fp2(quadratic, include allocate memory and compute
void Execute_Fp2(){
  

  bigInteger A0[2];
  bigInteger A1[2];
  setRandCo(A0,2);
  setRandCo(A1,2);
  bigInteger V0[2];
  bigIntIniCoefficient(V0,2);

  Fp2mul(A0,A1,V0);

}

void Fp2_Cycles(){


 cycles_t start = 0, end = 0, cycles = 0, sum = 0;
 
 for(int i =0; i< 1000; i++){


  start = cpucycles();
  Execute_Fp2();
  end = cpucycles();
  cycles = end - start;


  /*preventing clock cycle counting abnormalities caused by clock frequency variation or
hardware errors*/

while(cycles<(long long)0){
  start = cpucycles();
  Execute_Fp2();
  end = cpucycles();
  cycles = end - start;
 }

  //printf("the print the time: %d \n", i);
  //printf("the print the value of cycles: %lld \n", cycles);


  cycles = cycles/(long long)1000;
  sum += cycles;

}
  
 printf("the clock cycles of Fp2 is : %lld \n", sum);

}




/*

    Multiplication in Fp3  (cubic)

*/

// do one time multiplication in Fp3(cubic, include allocate memory and compute
void Execute_Fp3(){

      bigInteger A0[3];
      bigInteger A1[3];
      bigInteger V0[3];
      setRandCo(A0,3);
      setRandCo(A1,3);
 
      bigIntIniCoefficient(V0,3);
      Fp3mul(A0,A1,V0);

}


void Fp3_Cycles(){

  cycles_t start = 0, end = 0, cycles = 0, sum = 0;

  for(int i = 0; i < 1000; i++){

      start = cpucycles();
      Execute_Fp3();
      end = cpucycles();
      cycles = end - start;


/*preventing clock cycle counting abnormalities caused by clock frequency variation or
hardware errors*/

while(cycles<(long long)0){
  start = cpucycles();
  Execute_Fp3();
  end = cpucycles();
  cycles = end - start;
 }

  //printf("the print the time: %d \n", i);
  //printf("the print the value of cycles: %lld \n", cycles);

  cycles = cycles/(long long)1000;
  sum += cycles;

  }
  
printf("the clock cycles of Fp3 is : %lld\n", sum);

}




/*

    Multiplication in Fp4  (quadratic over quadratic)

*/

// do one time multiplication in Fp4(quadratic, include allocate memory and compute)
void Execute_Fp4_2over2(){

   bigInteger M0[2];
   bigInteger M1[2];
   bigInteger N0[2];
   bigInteger N1[2];
   setRandCo(M0,2);
   setRandCo(M1,2);
   setRandCo(N0,2);
   setRandCo(N1,2);
 
   bigInteger results[4];
   bigIntIniCoefficient(results,4);

   Fp4_2input(M0,M1,N0,N1,results);

}


void Fp4_2over2Cycles(){


cycles_t start = 0, end = 0, cycles = 0, sum = 0;

for(int i =0; i< 1000; i++){

   
   start = cpucycles();
   Execute_Fp4_2over2();
   end = cpucycles();
   cycles = end - start;

   
/*preventing clock cycle counting abnormalities caused by clock frequency variation or
hardware errors*/

while(cycles<(long long)0){
  start = cpucycles();
  Execute_Fp4_2over2();
  end = cpucycles();
  cycles = end - start;
 }

  //printf("the print the time: %d \n", i);
  //printf("the print the value of cycles: %lld \n", cycles);


   cycles = cycles/(long long)1000;
   sum += cycles;
  
}

printf("the clock cycles of Fp4(Fp2 over Fp2) is : %lld\n", sum);

}





/*

    Multiplication in Fp4  (direct)

*/

// do one time multiplication in Fp4(quartic, include allocate memory and compute)
void Execute_Fp4_direct(){

  bigInteger M0[4];
  bigInteger M1[4];
  bigInteger result[4];
  setRandCo(M0,4);
  setRandCo(M1,4);
  bigIntIniCoefficient(result,4);

  Fp4_direct(M0,M1,result);

}


void Fp4_DirectCycles(){

cycles_t start = 0, end = 0, cycles = 0, sum = 0;


for(int i =0; i< 1000; i++){

  start = cpucycles();
  Execute_Fp4_direct();
  end = cpucycles();
  cycles = end - start;


/*preventing clock cycle counting abnormalities caused by clock frequency variation or
hardware errors*/

while(cycles<(long long)0){
  start = cpucycles();
  Execute_Fp4_direct();
  end = cpucycles();
  cycles = end - start;
 }

  //printf("the print the time: %d \n", i);
  //printf("the print the value of cycles: %lld \n", cycles);
  cycles = cycles/(long long)1000;
  
  sum = sum + cycles;
  
}

printf("the clock cycles of Fp4(Direct) is : %lld \n", sum);

}










/*

    Multiplication in Fp6  (cubic over quartic)

*/

// do one time multiplication in Fp6(cubic over quartic, include allocate memory and compute)
void Execute_Fp6_3over2(){

   bigInteger A0[2];
   bigInteger A1[2];
   bigInteger A2[2];
   bigInteger B0[2];
   bigInteger B1[2];
   bigInteger B2[2];
   setRandCo(A0,2);
   setRandCo(A1,2);
   setRandCo(A2,2);
   setRandCo(B0,2);
   setRandCo(B1,2);
   setRandCo(B2,2);

   bigInteger res[6];
   bigIntIniCoefficient(res,6);
   Fp6_3over2input(A0,A1,A2,B0,B1,B2,res);
}



void Fp6_3over2Cycles(){

cycles_t start = 0, end = 0, cycles = 0, sum = 0;

for(int i =0; i< 1000; i++){

   start = cpucycles();
   Execute_Fp6_3over2();
   end = cpucycles();
   cycles = end - start;


    /*preventing clock cycle counting abnormalities caused by clock frequency variation or
hardware errors*/

while(cycles<(long long)0){
  start = cpucycles();
  Execute_Fp6_3over2();
  end = cpucycles();
  cycles = end - start;
 }
  
   //printf("the print the time: %d \n", i);
   //printf("the print the value of cycles: %lld \n", cycles);
   cycles = cycles/(long long)1000; 
   sum += cycles;
}

printf("the clock cycles of Fp6(Fp3 over Fp2) : %lld \n", sum);

}





/*

    Multiplication in Fp6  (quartic over cubic)

*/

// do one time multiplication in Fp6(quadratic over cubic, include allocate memory and compute)
void Execute_Fp6_2over3(){
   bigInteger A0[3];
   bigInteger A1[3];
   bigInteger B0[3];
   bigInteger B1[3];
   setRandCo(A0,3);
   setRandCo(A1,3);
   setRandCo(B0,3);
   setRandCo(B1,3);

   bigInteger res[6];
   bigIntIniCoefficient(res,6);

   Fp6_2over3input(A0,A1,B0,B1,res);
}


void Fp6_2over3Cycles(){

 cycles_t start = 0, end = 0, cycles = 0, sum = 0;


for(int i =0; i< 1000; i++){

   start = cpucycles();
   Execute_Fp6_2over3();
   end = cpucycles();
   cycles = end - start;

   /*preventing clock cycle counting abnormalities caused by clock frequency variation or
hardware errors*/

while(cycles<(long long)0){
  start = cpucycles();
  Execute_Fp6_2over3();
  end = cpucycles();
  cycles = end - start;
 }


   //printf("the print the time: %d \n", i);
   //printf("the print the value of cycles: %lld \n", cycles);

   cycles = (long long)cycles/1000;
   sum += cycles;    
}

printf("the clock cycles of Fp6(Fp2 over Fp3) is : %lld \n", sum);

}











/*

    Multiplication in Fp12  (cubic over quartic)

*/

// do one time multiplication in Fp12(cubic over quartic, include allocate memory and compute)
void Execute_Fp12_3over4(){

  bigInteger m0[4];
  bigInteger m1[4];
  bigInteger m2[4];
  bigInteger n0[4];
  bigInteger n1[4];
  bigInteger n2[4];

  setRandCo(m0,4);//Generating random coefficients for polynomials, in the range of 0 to p-1.
  setRandCo(m1,4);
  setRandCo(m2,4);
  setRandCo(n0,4);
  setRandCo(n1,4);
  setRandCo(n2,4);
  bigInteger res[12];
  bigIntIniCoefficient(res,12);
  Fp12_3overDirect4(m0,m1,m2,n0,n1,n2,res);// Performing one multiplication operation within the field extension Fp12.
}


void Fp12_3over4Cycles(){

cycles_t start = 0, end = 0, cycles = 0, sum = 0;//cycles_t is used to receive the clock cycle count
for(int i =0; i< 1000; i++){

  start = cpucycles();
  Execute_Fp12_3over4();  //Execute one time Fp12(3over4) multiplication
  end = cpucycles();
  cycles = end - start;


  
 /*preventing clock cycle counting abnormalities caused by clock frequency variation or
hardware errors*/

while(cycles<(long long)0){
  start = cpucycles();
  Execute_Fp12_3over4();
  end = cpucycles();
  cycles = end - start;
 }

  cycles = (long long)cycles/1000;
  sum = sum + cycles;

}
  
printf("the clock cycles of Fp12(Fp3 over direct Fp4) is : %lld \n", sum);

}










/*

    Multiplication in Fp12  (cubic over quadratic over quadratic)

*/

// do one time multiplication in Fp12(cubic over quadratic over quadratic, include allocate memory and compute)
void Execute_Fp12_3over2over2(){

    bigInteger A00[2];
    bigInteger A01[2];
    bigInteger A10[2];
    bigInteger A11[2];
    bigInteger A20[2];
    bigInteger A21[2];
    bigInteger B00[2];
    bigInteger B01[2];
    bigInteger B10[2];
    bigInteger B11[2];
    bigInteger B20[2];
    bigInteger B21[2];
  
    setRandCo(A00,2);
    setRandCo(A01,2);
    setRandCo(A10,2);
    setRandCo(A11,2);
    setRandCo(A20,2);
    setRandCo(A21,2);
    setRandCo(B00,2);
    setRandCo(B01,2);
    setRandCo(B10,2);
    setRandCo(B11,2);
    setRandCo(B20,2);
    setRandCo(B21,2);

    bigInteger res[12];
    bigIntIniCoefficient(res,12);
    Fp12_3over2over2(A00,A01,A10,A11,A20,A21,B00,B01,B10,B11,B20,B21,res);

}


void Fp12_3over2over2Cycles(){

cycles_t start = 0, end = 0, cycles = 0, sum = 0;

for(int i =0; i< 1000; i++){

   start = cpucycles();
   Execute_Fp12_3over2over2(); //Execute one time Fp12(3over2over2) multiplication
   end = cpucycles();
   cycles = end - start;

 /*preventing clock cycle counting abnormalities caused by clock frequency variation or
hardware errors*/

while(cycles<(long long)0){
  start = cpucycles();
  Execute_Fp12_3over2over2();
  end = cpucycles();
  cycles = end - start;
 }


  //printf("the print the time: %d \n", i);
  //printf("the print the value of cycles: %lld \n", cycles);


  cycles = (long long)cycles/1000;
  sum = sum + cycles;

}

printf("the clock cylces of Fp12(Fp3 over Fp2 over Fp2) is : %lld \n", sum);

}





/*

    Multiplication in Fp12  (quadratic over cubic over quadratic)

*/

// do one time multiplication in Fp12(quadratic over cubic over quadratic, include allocate memory and compute)
void Execute_Fp12_2over3over2(){

 
 bigInteger A00[2];
 bigInteger A01[2];
 bigInteger A02[2];
 bigInteger A10[2];
 bigInteger A11[2];
 bigInteger A12[2];
 bigInteger B00[2];
 bigInteger B01[2];
 bigInteger B02[2];
 bigInteger B10[2];
 bigInteger B11[2];
 bigInteger B12[2];

 setRandCo(A00,2);
 setRandCo(A01,2);
 setRandCo(A02,2);
 setRandCo(A10,2);
 setRandCo(A11,2);
 setRandCo(A12,2);
 setRandCo(B00,2);
 setRandCo(B01,2);
 setRandCo(B02,2);
 setRandCo(B10,2);
 setRandCo(B11,2);
 setRandCo(B12,2);


  bigInteger res[12];
  bigIntIniCoefficient(res,12);

  Fp12_2over3over2(A00,A01,A02,A10,A11,A12,B00,B01,B02,B10,B11,B12,res);

}



void Fp12_2over3over2Cycles(){

cycles_t start = 0, end = 0, cycles = 0, sum = 0;

for(int i =0; i< 1000; i++){

  start = cpucycles();
  Execute_Fp12_2over3over2();  //Execute one time Fp12(2over3over2) multiplication
  end = cpucycles();
  cycles = end - start;

  /*preventing clock cycle counting abnormalities caused by clock frequency variation or
hardware errors*/

while(cycles<(long long)0){
  start = cpucycles();
  Execute_Fp12_2over3over2();
  end = cpucycles();
  cycles = end - start;
 }


  //printf("the print the time: %d \n", i);
  //printf("the print the value of cycles: %lld \n", cycles);

  cycles = (long long) cycles/1000;
  sum += cycles;
  
}

printf("the clock cycles of Fp12(Fp2 over Fp3 over Fp2) : %lld \n", sum);


}




/*

    Multiplication in Fp12  (quadratic over quadratic over cubic)

*/


void Execute_Fp12_2over2over3(){
 
 bigInteger A00[3];
 bigInteger A01[3];
 bigInteger A10[3];
 bigInteger A11[3];
 bigInteger B00[3];
 bigInteger B01[3];
 bigInteger B10[3];
 bigInteger B11[3];

 setRandCo(A00,3);
 setRandCo(A01,3);
 setRandCo(A10,3);
 setRandCo(A11,3);
 setRandCo(B00,3);
 setRandCo(B01,3);
 setRandCo(B10,3);
 setRandCo(B11,3);

 bigInteger res[12];
 bigIntIniCoefficient(res,12);

 Fp12_2over2over3(A00,A01,A10,A11,B00,B01,B10,B11,res);

}


void Fp12_2over2over3Cycles(){

// this is  2 over 2 over 3

cycles_t start = 0, end = 0, cycles = 0, sum = 0;

for(int i =0; i< 1000; i++){

 start = cpucycles();
 Execute_Fp12_2over2over3();//Execute one time Fp12(2over2over3) multiplication
 end = cpucycles();
 cycles = end - start;


/*preventing clock cycle counting abnormalities caused by clock frequency variation or
hardware errors*/

 while(cycles<(long long)0){
 start = cpucycles();
 Execute_Fp12_2over2over3();
 end = cpucycles();
 cycles = end - start;
 }


 //printf("the print the time: %d \n", i);
 //printf("the print the value of cycles: %lld \n", cycles);

 cycles = (long long)cycles/1000;
// printf("print the value of sum: %lld \n", sum);
 sum += cycles;

}
 
printf("the clock cycles of Fp12(Fp2 over Fp2 over Fp3) is : %lld \n", sum);

}




































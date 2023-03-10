
all: k 

k: pack_initial.o pack_assist.o pack_mul.o pack_add_sub.o extensions.o pack_div.o pack_basic_operation.o pack_testing.o x86estimate.o main.o  
	gcc pack_initial.o pack_assist.o pack_mul.o pack_add_sub.o  extensions.o pack_div.o pack_basic_operation.o pack_testing.o x86estimate.o main.o -o k 
	
	
pack_initial.o: pack_initial.c
	gcc pack_initial.c -c 
	
pack_assist.o: pack_assist.c
	gcc pack_assist.c -c 
	
pack_mul.o: pack_mul.c
	gcc pack_mul.c -c 
	
pack_add_sub.o: pack_add_sub.c
	gcc pack_add_sub.c -c 
	
extensions.o: extensions.c
	gcc extensions.c -c 
	
pack_div.o: pack_div.c
	gcc pack_div.c -c 
	
pack_basic_operation.o: pack_basic_operation.c
	gcc pack_basic_operation.c -c 
	
pack_testing.o: pack_testing.c
	gcc pack_testing.c -c 

x86estimate.o: 	x86estimate.c
	gcc x86estimate.c -c
	
main.o: main.c
	gcc main.c -c 

clean:
	rm -f *.o notapp


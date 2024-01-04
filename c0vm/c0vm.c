/**************************************************************************/
/*              COPYRIGHT Carnegie Mellon University 2023                 */
/* Do not post this file or any derivative on a public site or repository */
/**************************************************************************/
#include <assert.h>
#include <stdio.h>
#include <limits.h>
#include <stdlib.h>

#include "lib/xalloc.h"

#include "lib/stack.h"
#include "lib/contracts.h"
#include "lib/c0v_stack.h"
#include "lib/c0vm.h"
#include "lib/c0vm_c0ffi.h"
#include "lib/c0vm_abort.h"

/* call stack frames */
typedef struct frame_info frame;
struct frame_info {
  c0v_stack_t  S;   /* Operand stack of C0 values */
  ubyte       *P;   /* Function body */
  size_t       pc;  /* Program counter */
  c0_value    *V;   /* The local variables */
};

int execute(struct bc0_file *bc0) {
  REQUIRES(bc0 != NULL);

  /* Variables */
  c0v_stack_t S= c0v_stack_new(); /* Operand stack of C0 values */
  ubyte *P= (bc0->function_pool)[0].code;      /* Array of bytes that make up the current function */
  size_t pc=0;     /* Current location within the current byte array P */
  c0_value *V= xcalloc((bc0->function_pool)[0].num_vars, sizeof(c0_value));   /* Local variables (you won't need this till Task 2) */
  (void) V;      // silences compilation errors about V being currently unused

  /* The call stack, a generic stack that should contain pointers to frames */
  /* You won't need this until you implement functions. */
  gstack_t callStack;
  callStack= stack_new(); // silences compilation errors about callStack being currently unused

  while (true) {

#ifdef DEBUG
    /* You can add extra debugging information here */
    fprintf(stderr, "Opcode %x -- Stack size: %zu -- PC: %zu\n",
            P[pc], c0v_stack_size(S), pc);
#endif

    switch (P[pc]) {

    /* Additional stack operation: */

    case POP: {
      pc++;
      c0v_pop(S);
      break;
    }

    case DUP: {
      pc++;
      c0_value v = c0v_pop(S);
      c0v_push(S,v);
      c0v_push(S,v);
      break;
    }

    case SWAP:{
      pc++;
      c0_value v1= c0v_pop(S);
      c0_value v2= c0v_pop(S);
      c0v_push(S, v1);
      c0v_push(S, v2);
      break;
    }


    /* Returning from a function.
     * This currently has a memory leak! You will need to make a slight
     * change for the initial tasks to avoid leaking memory.  You will
     * need to revise it further when you write INVOKESTATIC. */

    case RETURN: {
      int retval = val2int(c0v_pop(S));
      ASSERT(c0v_stack_empty(S));
// Another way to print only in DEBUG mode
      // Free everything before returning from the execute function!
      free(V);
      c0v_stack_free(S);
      if (!stack_empty(callStack)){
        frame* tmp = pop(callStack);
        pc= tmp->pc;
        S= tmp->S;
        P= tmp->P;
        V= tmp->V;
        free(tmp);
        c0v_push(S, int2val(retval));
        break; 
      }
      else{
        stack_free(callStack, &free);
        return retval;

      }
      return retval;
      

    }


    /* Arithmetic and Logical operations */

    case IADD: {
      pc++;
      int32_t a= val2int(c0v_pop(S));
      int32_t b= val2int(c0v_pop(S));
      uint32_t res= (uint32_t)a+(uint32_t)b;
      c0v_push(S, int2val((int32_t)(res)));
      break;
    }

    case ISUB:{
      pc++;
      int32_t a= val2int(c0v_pop(S));
      int32_t b= val2int(c0v_pop(S));
      uint32_t res= (uint32_t)b-(uint32_t)a;
      c0v_push(S, int2val((int32_t)(res)));
      break;

    }
  

    case IMUL:{
      pc++;
      int32_t a= val2int(c0v_pop(S));
      int32_t b= val2int(c0v_pop(S));
      uint32_t res= (uint32_t)a*(uint32_t)b;
      c0v_push(S, int2val((int32_t)(res)));
      break;
    }

    case IDIV:{
      pc++;
      int32_t a= val2int(c0v_pop(S));
      int32_t b= val2int(c0v_pop(S));

      if(a==0){
        c0_arith_error("undefined dividing by zero");

      }
      if(a==-1 && b== INT_MIN){
        c0_arith_error("undefined dividing by negative 1 and INTMIN");
      }
      c0v_push(S, int2val((b/a)));
      break;
    }

    case IREM:{
      pc++;
      int32_t a= val2int(c0v_pop(S));
      int32_t b= val2int(c0v_pop(S));
      if(a==0){
        c0_arith_error("modulo by zero");

      }
      if(a==-1 && b== INT_MIN){
        c0_arith_error("modulo by negative 1 and INTMIN");
      }
      c0v_push(S, int2val(b%a));
      break;
    }

    case IAND:{
      pc++;
      int32_t a= val2int(c0v_pop(S));
      int32_t b= val2int(c0v_pop(S));
      c0v_push(S, int2val(b&a));
      break;
    }

    case IOR:{
      pc++;
      int32_t a= val2int(c0v_pop(S));
      int32_t b= val2int(c0v_pop(S));
      c0v_push(S, int2val(b|a));
      break;
    }

    case IXOR:{
      pc++;
      int32_t a= val2int(c0v_pop(S));
      int32_t b= val2int(c0v_pop(S));
      c0v_push(S, int2val(b^a));
      break;
    }

    case ISHR:{
      pc++;
      int32_t a= val2int(c0v_pop(S));
      int32_t b= val2int(c0v_pop(S));
      if (a<0){
        c0_arith_error("negative shift value");
      }
      if(a>=32){
        c0_arith_error("shift value too large");
      }
      c0v_push(S, int2val(b>>a));
      break;
    }

    case ISHL:{
      pc++;
      int32_t a= val2int(c0v_pop(S));
      int32_t b= val2int(c0v_pop(S));
      if (a<0){
        c0_arith_error("negative shift value");
      }
      if(a>=32){
        c0_arith_error("shift value too large");
      }
      c0v_push(S, int2val(b<<a));
      break;

    }


    /* Pushing constants */

    case BIPUSH:{
      pc++;
      c0v_push(S, int2val((int32_t)(int8_t)(P[pc])));
      pc++;
      break;
    }

    case ILDC:{
      pc++;
      uint32_t c1= (uint32_t)(uint8_t)(P[pc]);
      pc++;
      uint32_t c2= (uint32_t)(uint8_t)(P[pc]);
      pc++;
      c0v_push(S, int2val(((int32_t)(bc0 ->int_pool[(c1<<8|c2)]))));
      break; 
    }

    case ALDC:{
      pc++;
      uint32_t c1= (uint32_t)(uint8_t)(P[pc]);
      pc++;
      uint32_t c2= (uint32_t)(uint8_t)(P[pc]);
      pc++;
      c0v_push(S, ptr2val(&(bc0 ->string_pool[(c1<<8|c2)])));
      break; 
    }

    case ACONST_NULL:{
      pc++;
      c0v_push(S, ptr2val(NULL));
      break;
    }


    /* Operations on local variables */

    case VLOAD:{
      pc++;
      size_t i= (size_t)(uint8_t)(P[pc]);
      pc++;
      c0v_push(S, V[i]);
      break;
    }

    case VSTORE:{
      pc++;
      size_t i= (size_t)(uint8_t)(P[pc]);
      pc++;
      V[i]= c0v_pop(S);
      break;
    }


    /* Assertions and errors */

    case ATHROW:{
      pc++;
      c0_value res= c0v_pop(S);
      c0_user_error((char*)(val2ptr(res)));
      break;
    }

    case ASSERT:{
      pc++;
      c0_value res= c0v_pop(S);
      if(val2int(c0v_pop(S))==0){
        c0_assertion_failure((char*)(val2ptr(res)));
      }
      break;

    }

    /* Control flow operations */

    case NOP:{
      pc++;
      break;
    }

    case IF_CMPEQ:{
      pc++;
      int16_t o1= (int16_t)(P[pc]);
      pc++;
      int16_t o2= (int16_t)(P[pc]);
      if (!val_equal(c0v_pop(S), c0v_pop(S))){
        pc++;
      }
      else{
        pc+= ((o1<<8)|o2)-2;
      }
      break; 
    }

    case IF_CMPNE:{
      pc++;
      int16_t o1= (int16_t)(P[pc]);
      pc++;
      int16_t o2= (int16_t)(P[pc]);
      if (val_equal(c0v_pop(S), c0v_pop(S))){
        pc++;
      }
      else{
        pc+= ((o1<<8)|o2)-2;
      }
      break; 
    }

    case IF_ICMPLT:{
      pc++;
      int16_t o1= (int16_t)(P[pc]);
      pc++;
      int16_t o2= (int16_t)(P[pc]);
      if (val2int(c0v_pop(S)) <=val2int(c0v_pop(S))){
        pc++;
      }
      else{
        pc+= ((o1<<8)|o2)-2;
      }
      break; 
    }

    case IF_ICMPGE:{
      pc++;
      int16_t o1= (int16_t)(P[pc]);
      pc++;
      int16_t o2= (int16_t)(P[pc]);
      if (val2int(c0v_pop(S))> val2int(c0v_pop(S))){
        pc++;
      }
      else{
        pc+= ((o1<<8)|o2)-2;
      }
      break; 
    }

    case IF_ICMPGT:{
      pc++;
      int16_t o1= (int16_t)(P[pc]);
      pc++;
      int16_t o2= (int16_t)(P[pc]);
      if (val2int(c0v_pop(S))>=val2int(c0v_pop(S))){
        pc++;
      }
      else{
        pc+= ((o1<<8)|o2)-2;
      }
      break; 
    }

    case IF_ICMPLE:{
      pc++;
      int16_t o1= (int16_t)(P[pc]);
      pc++;
      int16_t o2= (int16_t)(P[pc]);
      if (val2int(c0v_pop(S))<val2int(c0v_pop(S))){
        pc++;
      }
      else{
        pc+= ((o1<<8)|o2)-2;
      }
      break; 
    }

    case GOTO:{
      pc++;
      int16_t o1= (int16_t)(P[pc]);
      pc++;
      int16_t o2= (int16_t)(P[pc]);
      pc+= ((int16_t)(o1<<8)|o2)-2;
      break;
      
    }

//CHECKPOINT 
    /* Function call operations: */

    case INVOKESTATIC: {
      pc++;
      uint16_t c1= (uint16_t)(P[pc]);
      pc++;
      uint16_t c2= (uint16_t)(P[pc]);
      pc++;
      struct function_info res = bc0->function_pool[((c1<<8)|c2)];
      uint16_t i= res.num_args; 
      
      frame* tmp = xmalloc(sizeof(frame));
      tmp->pc= pc; 
      tmp->S= S;
      tmp->P=P;
      tmp->V =V; 
      push(callStack, tmp);
      pc=0; 
      V= xcalloc(sizeof(c0_value), (uint32_t)res.num_vars);
      
      while (i != (uint16_t)0){
        V[i-1]= c0v_pop(S);
        i-=1;
      } 
      pc= 0;
      P= res.code; 
      S= c0v_stack_new();
      break;

    }


    case INVOKENATIVE: {
      pc++;
      uint16_t c1= (uint16_t)(P[pc]);
      pc++;
      uint16_t c2= (uint16_t)(P[pc]);
      pc++;
      struct native_info ni = bc0->native_pool[(c1<<8)| c2];
      uint16_t args = ni.num_args; 
      uint16_t index= ni.function_table_index; 
      c0_value* tmp= xcalloc(sizeof(c0_value), ni.num_args);
      while (args!=(uint16_t)0){
        tmp[args-1]= c0v_pop(S);
        args--;
      }
      c0v_push(S, (*native_function_table[index])(tmp));
      free(tmp);
      break; 

    }
    /* Memory allocation and access operations: */

    case NEW:{
      pc++;
      uint8_t res= (uint8_t)(P[pc]);
      pc++;
      char *n= xcalloc(sizeof(char), res);
      //a char is one byte long 
      c0v_push(S, ptr2val(n));
      break; 
    }

    case IMLOAD:{
      pc++;
      int32_t *x= (int32_t*)(val2ptr(c0v_pop(S)));
      if(x==NULL){
        c0_memory_error("Value is NULL");
      }
      c0v_push(S, int2val(*x));
      break; 
    }

    case IMSTORE:{
      pc++;
      int32_t i = val2int(c0v_pop(S));
      int32_t *result = (int32_t*)(val2ptr(c0v_pop(S)));
      if(result==NULL){
        c0_memory_error("value is NULL");
      }
      *result= i; 
      break; 
    }

    case AMLOAD:{
      pc++;
      void **result= val2ptr(c0v_pop(S));
      if (result==NULL){
        c0_memory_error("value NULL");
      }
      c0v_push(S, ptr2val(*result));
      break; 
      
    }

    case AMSTORE: {
      pc++;
      void **res1= val2ptr(c0v_pop(S));
      void **res2= val2ptr(c0v_pop(S));
      if(res2==NULL){
        c0_memory_error("value is NULL");
      }
      *res2= res1; 
      break;
    }

    case CMLOAD:{
      pc++; 
      char *result= val2ptr(c0v_pop(S));
      if(result==NULL){
        c0_memory_error("value is NULL");
      }
      c0v_push(S, int2val((int32_t)(*result)));
      break; 
    }

    case CMSTORE: {
      pc++;
      int32_t elem = val2int(c0v_pop(S));
      char *elem1= val2ptr(c0v_pop(S));
      if(elem1==NULL) {
        c0_memory_error("NULL");
        
      }
      *elem1= elem & 0x7F;
      break; 
    }

    case AADDF:{
      pc++;
      uint8_t size= (uint8_t)P[pc];
      char* result= val2ptr(c0v_pop(S));
      if(result==NULL){
        c0_memory_error("NULL");
      }
      c0v_push(S, ptr2val(result+size));
      pc++;
      break;
    }


    /* Array operations: */

    case NEWARRAY:{
      pc++;
      uint8_t size= (uint8_t)(P[pc]);
      int32_t count = val2int(c0v_pop(S));
      c0_array *new= xcalloc(1, sizeof(c0_array));
      new->elt_size= size; 
      new->count= count; 
      new->elems= xcalloc(new->elt_size, new->count );
      c0v_push(S, ptr2val(new));
      pc= pc+2;
      break; 

    }

    case ARRAYLENGTH:{
      pc++;
      c0_array *new = (c0_array*)(val2ptr(c0v_pop(S)));
      c0v_push(S, int2val((int32_t)(new->count)));
      break; 
    }

    case AADDS:{
      pc++;
      int32_t i= val2int(c0v_pop(S));
      c0_array *new = (c0_array*)(val2ptr(c0v_pop(S)));
      if (new==NULL){
        c0_memory_error("val is NULL");
      }
      else if(i<0){
        c0_memory_error("invalid index");
      }
      else if (i >= (int32_t)new->count){
        c0_memory_error("index out of bounds");
      }
      c0_value res= ptr2val(&((char*)(new->elems))[(new->elt_size)*i]);
      c0v_push(S, res);
      break; 
    }


    /* BONUS -- C1 operations */

    case CHECKTAG:

    case HASTAG:

    case ADDTAG:

    case ADDROF_STATIC:

    case ADDROF_NATIVE:

    case INVOKEDYNAMIC:

    default:
      fprintf(stderr, "invalid opcode: 0x%02x\n", P[pc]);
      abort();
    }
  }

  /* cannot get here from infinite loop */
  assert(false);
}
#include "stdio.h"
#include "stdlib.h"
#include "hashtable.h"


#define OCUPADO 2
#define LIVRE 0
#define APAGADO 1
#define CAP 7

/*
  OPEN ADRESSING
*/

int hashO(int value,int size){
  return (value % size);
}

HashOpen initHOpen(int size){
  HashOpen res = (HashOpen) malloc(sizeof(struct hashOpen));
  if(!res) return NULL;
  res->values = (int*) malloc(sizeof(int) * size);
  if(!res->values){
    free(res);
    return NULL;
  }
  res->ocupados = (int*) malloc(sizeof(int) * size);
  if(!res->ocupados){
    free(res->values);
    free(res);
    return NULL;
  }else {
    int i;
    for(i=0;i<size;i++)
      res->ocupados[i] = LIVRE;
    res->size = size;
  }
  return res;
}

int add(HashOpen h,int i){
  int l, j = 0;
  l = hashO(i,h->size);
  while(j < h->size){
    if(h->ocupados[l] == OCUPADO) {
      l = hashO(l+1,h->size);
      j++;
    }else {
      h->values[l] = i;
      h->ocupados[l] = OCUPADO;
      return 1;
    }
  }
  return 0;
}

int rmv(HashOpen h,int i){
  int l, j = 0;
  l = hashO(i,h->size);
  while(j < h->size){
    if(h->ocupados[l] == LIVRE)
      return 0;
    else if (h->ocupados[l] == OCUPADO && h->values[l] == i){
      h->ocupados[l] = APAGADO;
      return 1;
    }else {
      l = l+1 % h->size;
      j++;
    }
  }
  return 0;
}

int search(HashOpen h ,int i){
  int l, j = 0;
  l = hashO(i,h->size);
  while(j < h->size){
    if(h->ocupados[l] == LIVRE)
      return 0;
    else if (h->ocupados[l] == OCUPADO && h->values[l] == i){
      return 1;
    }else {
      l = l+1 % h->size;
      j++;
    }
  }
  return 0;
}

void printHash(HashOpen h){
  int i;
  for(i = 0; i < h->size; i++){
    printf(" | %d - %d |\n",h->values[i], h->ocupados[i]);
  }

}


/*
 CLOSED ADDRESING
*/

int hash(int value){
  return (value % CAP);
}

void initHClosed(HashClosed *h){
  int i;
  for(i = 0; i < CAP; i++)
    h[i] = NULL;
}

int addClosed(HashClosed h,int value){
  int l;
  struct node *aux, *p;
  l = hash(value);
  for(aux = h[l]; aux; aux = aux->next){
    p = aux;
    if(aux->valor == value) return 0;
  }
  aux = (Node) malloc(sizeof(struct node));
  if(!aux) return 0;
  aux->valor = value;
  aux->next = NULL;
  p->next = aux;
  return 1;
}

int rmvClosed(HashClosed h,int value){
  int l;
  struct node *p,*aux;
  l = hash(value);
  p = h[l];
  for(aux = h[l]; aux; aux = aux->next){
    if(aux->valor == value){
      p->next = aux->next;
      free(aux);
      return 1;
    }
    p = aux;
  }
  return 0;
}

int searchClosed(HashClosed h,int value){
  int l;
  struct node *aux;
  l = hash(value);
  for(aux = h[l]; aux ; aux = aux->next){
    if(aux->valor == value) return 1;
  }
  return 0;
}

/*
  MAIN
*/

int main(){
  /*
  HashOpen h = initHOpen(7);

  add(h,3);
  add(h,10);
  add(h,1);
  add(h,15);
  add(h,16);
  printf("Search 3: %d \n", search(h,3));
  printf("Search 16: %d \n", search(h,16));
  rmv(h,3);
  printf("Search 3: %d \n", search(h,3));
  printHash(h);
  */

  HashClosed *h;
  initHClosed(h);

}

//////////////////////////////////////////////////////////////////////////////////////////////////////////

#define OCUPADO o
#define LIVRE l
#define REMOVIDO r

typedef struct set{
  int size;
  char *flag;
  int *value;
}


Set init(int tamanho){
  Set s = (Set)malloc(sizeof(struct set));
  if(!s) return NULL;
  s->size = tamanho;
  s->value = (int*) malloc(sizeof(int)*tamanho);
  s->flag = (char*) malloc(sizeof(char)*tamanho);
  if(!value || !flag){
    free(s->flag);
    free(s->value);
    free(s);
    return NULL;
  }
  for(int i=0;i<tamanho;i++){
    s->flag[i] = LIVRE
  }
  return s;
}

int hash(int valor,int size){
  return valor % size
}

int add(Set s, int valor){
  int a = hash(valor,s->size);
  int saltos = 0;
  while(saltos != s->size ){
    if(s->flag[a] != OCUPADO){
      s->value[a] = valor;
      s->flag[a] = OCUPADO;
      return 0;
    }
    else{
      a =  ++valor % s->size;
      saltos++;
    }
  }
  return 1;
}

//VERSÂO PROFESSOR ALCINO

int add(Set s, int valor){
  int a = hash(valor,s->size);
  int i;
  while(i=0; i<s->size; i++){
    if(s->flag[a] != OCUPADO){
      s->value[a] = valor;
      s->flag[a] = OCUPADO;
      return 0;
    }
    else
      a =  ++a % s->size;
  }
  return 1;
}
/*
 Para a função add.
 Considerando um Array com n posições livres , n posições ocupados , n posiçoes removidas
 Melhor caso - a posição i que é dada pelo hash é uma posição livre
 Pior caso - um cluster de ocupados e começar no inicio no cluster e percorrer tudo até ter a posição livre
*/


//ISTO ESTA ERRADO - versao cardoso
int elem(Set s,int valor){
  int a = hash(valor,s->size);
  int saltos = 0;
  while(saltos != s->size){
    if(s->flag[a] == LIVRE){
      return -1;
    }else if(s->value[a] != valor){ //FALTA COLOCAR QUE ESTÀ ocupado
      saltos++;
      a = ++a ‰ s->size;
    }else
      return s->value[a];
  }
}

//VERSÃO PROFESSOR ALCINO
int elem(Set s,int valor){
  int a = hash(valor,s->size);
  int i;
  while(i=0; i<s->size; i++){
    if(s->flag[a] == OCUPADO && s->value[a] == valor){
      return 0; //EXISTE o elemento
    }else if(s->flag[a] == LIVRE){
      return 1;
    }else{
      a = ++a ‰ s->size;
    }
  }
  return 1;
}

/*
 Para a função elem
 Considerando um Array com n posições livres , n posições ocupados , n posiçoes removidas
 Melhor caso - a posição i que é dada pelo hash é a posição que contêm o elemento ou é uma posição livre
 Pior caso - um cluster de ocupados e removidos e começar no inicio no cluster e percorrer tudo até ter a posição livre
*/


int rem(Set s,int valor){
  int a = hash(valor,s->size);
  int saltos;
  while(saltos != s->size){
    if(s->flag[a] == OCUPADO && s->value[a] == valor){
      s->flag[a] == REMOVIDO;
      return 0;
    } else if(s->flag[a] == LIVRE)
      return 1;
    else {
      saltos++;
      a = ++a % s->size;
    }
  }
  return 1;
}


int clearingHash(Set s, int valor){
  Set aux = init(s->size);
  if(!aux) return 1;
  for(int i = 0; i < s->size; i++){
    if(s->flag[i] == OCUPADO)
      add(aux,s->valor[i]);
  }
  free(s->flag);
  free(s->value);
  s->flag = aux->flag;
  s->value = aux->value;
  free(aux);
  return 0;
}
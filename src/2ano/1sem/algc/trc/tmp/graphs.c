#include "graphs.h"
#include "stdlib.h"
#include "stdio.h"

void initGraphM(GraphM g){
  int i,j;
  for(i = 0; i < MAX; i++){
    for(j = 0; j < MAX; j++){
      g[i][j] = -1;
    }
  }
}

void initGraphL(GraphL g){
  int i;
  for(i = 0; i < MAX; i++)
    g[i]->next = NULL;
}

void MtoL(GraphM gm, GraphL gl){
  int i,j;
  struct edge *aux;
  for(i = 0; i < MAX; i++){
    gl[i] = NULL;
    for(j = 0; j < MAX; j++){
      if(gm[i][j] != -1){
        aux = (Edge) malloc(sizeof(struct edge));
        aux->dest = j;
        aux->cost = gm[i][j];
        aux->next = gl[i];
        gl[i] = aux;
      }
    }
  }
}

void LtoM(GraphL gl, GraphM gm){
  int i;
  struct edge *aux;
  for(i = 0; i < MAX; i++){
    aux = gl[i];
    while(aux) gm[i][aux->dest] = aux->cost;
  }
}

int grauEntradaM(GraphM gm, int vertice){
  int i,sum = 0;
  for(i=0; i < MAX; i++){
    if(gm[i][vertice] != -1) sum++;
  }
  return sum;
}

int grauSaidaM(GraphM gm, int vertice){
  int i, sum = 0;
  for(i = 0; i < MAX; i++){
    if(gm[vertice][i] != -1) sum++;
  }
  return sum;
}

int grauEntradaL(GraphL gl, int vertice){
  int i,sum = 0;
  struct edge *aux;
  for(i = 0; i < MAX; i++){
    aux = gl[i];
    while(aux){
      if(aux->dest == vertice) sum++;
    }
  }
  return sum;
}

int grauSaidaL(GraphL gl, int vertice){
  int sum = 0;
  struct edge *aux;
  aux = gl[vertice];
  while(aux) sum++;
  return sum;
}


//fazer 5,6,7,8 - ficha 4 - representacoes

/*
  Travessias - TARJAN ---- SE EXISTIREM CICLOS NAO DEVE FUNCIONAR
*/
int vis[MAX]; //array visitados - WHITE (nao visitado), GRAY(visitado), BLACK(fechado)
int t; //inteiro para colocacao no array por ordem de traz para a frente
/*

 Esta funcao faz a travessia - depth search tree ate encontrar um nodo sem nodos precedentes.
 A ter em atencao:
  SE existir um ciclo - de um nodo existir descendencia para um nodo ja pintado (retornar o ciclo)

  ordem
   1) pintar ciclo actual de GRAY
   2) percorrer nodos descendentes desse nodo
   3) acabando de percorrer os nodos e fazer o backtrack pintar o nodo de BLACK

grafo gl , i - qual dos nodos deve ir buscar , res e o array com a topologia
*/


int auxTarjan(GraphL gl,int i,int tsort[]){
  int cycle = 0;
  struct edge *aux;
  vis[i] = GRAY;

  for(aux = gl[i]; aux && !cycle; aux = aux->next){
    if(vis[aux->dest] == GRAY) cycle = 1;
    else if(vis[aux->dest] == WHITE) cycle = auxTarjan(gl,aux->dest,tsort);
  }
  tsort[t--] = i;
  vis[i] = BLACK;
  return cycle;
}

int Tarjan(GraphL gl, int tsort[]){
  int i ,cycle = 0;
  t = MAX-1;
  //colocar tudo em nao visitado
  for(i = 0; i < MAX; i++) vis[i] = WHITE;

  for(i = 0; i < MAX && !cycle; i++){ //se existir ciclo deve parar.
    if(vis[i] == WHITE) cycle = auxTarjan(gl,i,tsort);
  }
  return cycle;
}


/*
  Travessia Kahn
*/

int inDegreeArr[MAX]; //array graus de entrada dos nodos
int queueNodos[MAX]; //queue para percorrer nodos
int front, back; //controlo da queue - front para controlar os que saem , back para adicionar os que entram

/*
  Normalmente usa-se uma queue para controlar esta travessia.

  Na funcao principal:

  1) calcular inDegree de todos os nodos
  2) passar os nodos com inDegree com 0 para a queue
  3) ciclo para percorrer cada um dos nodos com inDegree 0 para a funcao auxiliar.

  Na funcao auxiliar

  1) percorrer o nodo à procura dos descendentes e decrementa-los
  2) se existir novos nodos com 0 colocar na queue
  3) adicionar à topSort o nodo que foi trabalhado na funcao auxiliar e incrementar a frente da queue

*/
void inDegrees(GraphL gl){
  int i;
  struct edge *aux;
  for(i = 0; i < MAX; i++) inDegreeArr[i] = 0;

  for(i = 0; i < MAX; i++){
    aux = gl[i];
    while(aux){
      inDegreeArr[aux->dest]++;
      aux = aux->next;
    }
  }
}


void auxKahn(GraphL gl, int i, int tsort[]){
  int destino;
  struct edge *aux;
  for(aux = gl[i]; aux; aux = aux->next){
    destino = aux->dest;
    if(--inDegreeArr[destino] == 0) queueNodos[back++] = destino;
  }
  tsort[front++] = i;
}

int Kahn(GraphL gl, int tsort[]){
  t = 0;
  int i, grau;
  int front = back = 0;

  //percorrer inDegree para cada um dos nodos
  for(i = 0; i < MAX ; i++){
    if(grau == 0) queueNodos[back++] = i;
  }

  //iterar sobre a queue
  for(front; front < back;front++){
    auxKahn(gl,front,tsort);
  }

  if(front < MAX-1) return 1;
  else return 0;
}

/*
  arvores geradores minimas
    MST - arvores com o peso minimo de geração alcansáveis a partir de um nodo

    divisao em 3 conjuntos de nodos
    1) vertices que ja foram analisados
    2) vertices que se encontram na orla - vertices que vao ser analisados
    3) vertices que ainda nao estao em 1) e 2)
*/

//recebe grafo ligado e o vertice inicial

void mst(GraphL gl, int v,int parent[]){
  int stuck = 0; //para o caso de nao existir nada na fringe
  int nNodos = 0; //n de numeros que ja foram visitados
  int i; //para iterar o ciclo para unseen
  int z = v;// z - para guardar o vertice a trabalhar ,
  int y; // y guardar descendentes dos descendentes do nodo
  struct edge *aux = gl[v];
  int nodos[MAX]; //nodos do grafo e o seu estado
  int fringeLink[MAX]; //para ter nodos que estao na orla
  int fringeWgt[MAX]; //peso da ligacao em fringeLink
  int fringeList = NIL; //linkagem do apontador - inicia a null e anda ao contrario em cada unseen
  /*
    Como funciona o fringeLink

    (Fim da lista) NIL <--- nodo que nao estava na orla <--  outro nodo que nao estava na orla

    EXEMPLO:
     NIL <- 3 <- 5 <- 7 (apontador a apontar para este ultimo)

    Podia ser feito com uma lista ligada do tipo

    typedef struct orla{
      int nodo;
      int custo;
      struct orla *next;
    } Orla;

    Nesta versão de dois arrays o que acontece é a separacao da estrutura em 2 listas:
      - 1 com os custos para cada nodo na posicao dest do array
      - 2 com a linkagem para o next da estrutura.

    o array parent da a relacao da arvore do parente
  */


  for(i = 0; i < MAX ; i++) nodos[i] = UNSEEN;
  nodos[z] = INTREE;
  parent[z] = -1;

  while(nNodos < MAX && !stuck){
    //recurrencia no nodo para ver adjacentes aquele nodo
    aux = gl[z];
    while(aux){
      y = aux->dest;
      //se ja existir na ORLA e o caminho e menor que o ja existente
      if(nodos[y] == ORLA && fringeWgt[y] > aux->cost){
          parent[y] = z;
          fringeWgt[y] = aux->cost;
      } else if(nodos[y] == UNSEEN){ //se nao existir na orla e nao tiver sido visto adicionar a orla e adicionar o valor
          nodos[y] = ORLA;
          fringeWgt[y] = aux->cost;
          fringeLink[y] = fringeList;
          fringeList = y;
          parent[y] = z;
      }
      aux = aux->next;
    }
    //selecao do proximo caminho (VERSAO PROF)
    if(fringeList == NIL) stuck = 1; //se estiver parado
    else {
      int prev = 0; // para guardar a linkagem anterior quando ter a orla mais curta
      z = fringeList;
      for(y = fringeList; fringeLink[y] != NIL ; y =fringeLink[y]){
        if(fringeWgt[fringeLink[y]] < fringeWgt[z]){
          z = fringeLink[y];
          prev = y;
        }
      }
      if(z == fringeList) fringeList = fringeLink[z]; //no caso de so existir um arco candidato para colocar em NIL
      else fringeLink[prev] = fringeLink[z];
      fringeLink[z] = NIL;
      nodos[z] = INTREE;
      printf("analisando %d\n",z);
      nNodos++;
    }
  }
}

/*
  dkjistra
*/


void dkjistra(GraphL gl, int v, int parent[]){
  int i,d;
  int stuck = 0;
  int nNodos = 0;
  int nOrla = 0;
  int nodos[MAX]; //ter as distancias dos nodos
  int status[MAX]; //orla
  struct edge *aux;

  for(i = 0; i < MAX; i++){
    nodos[i] = INF;
    status[i] = UNSEEN;
    parent[i] = -2;
  }

  nodos[v] = 0;
  status[v] = INTREE;
  parent[v] = -1;
  while(nNodos < MAX -1 && !stuck){
    printf("\n\nanalisando nodo: %d\n",v);
    for(aux = gl[v]; aux; aux = aux->next){
      d = aux->dest; //destino do descendente
      if(status[d] == UNSEEN){
        status[d] = ORLA;
        nodos[d] = nodos[v] + aux->cost;
        parent[d] = v;
        nOrla++;
      } else if(status[d] == ORLA && nodos[d] > nodos[v] + aux->cost){
        nodos[d] = nodos[v] + aux->cost;
        parent[d] = v;
      }
    }
    printf("\ncustos e status\n");
    for(i = 0; i < MAX; i++) printf("| %d ->| %d , %d | \n",i,nodos[i],status[i]);
    printf("\n");
    printf("parent\n");
    for(i = 0; i < MAX; i++) printf("| %d | ",parent[i]);

    //selecao do novo nodo para analise
    if(nOrla == 0) stuck = 1;
    else {
      int prev = -1;
      for( i = 0; i < MAX ; i++){
        if(prev == -1 && status[i] == ORLA){ //quando apanha o primeiro caso
          v = i; prev = 0;
        }else if( status[i] == ORLA && nodos[i] < nodos[v])
          v = i;
      }
    }
    nOrla--;
    status[v] = INTREE;
    nNodos++;
  }

}

void printGraphL(GraphL gl){
  int i;
  struct edge *aux;
  for(i = 0; i < MAX; i++){
    printf("| %d | -> ",i);
    for(aux = gl[i];aux;aux = aux -> next) printf("( Destino: %d , Custo: %d ) ->",aux->dest,aux->cost);
    printf("\n");
  }
}

void printGraphM(GraphM gm){
  int i,j;
  for(i = 0; i < MAX; i++){
    for(j = 0; j < MAX; j++) printf("| %d |",gm[i][j]);
    printf("\n");
  }
}

/*
  Perguntas de exame
*/

int check_coloring(GraphL gl, Colors c){
  struct edge *aux;
  int i,y;
  for(i = 0; i < MAX; i++){
    aux = gl[i];
    while(aux){
      y = aux->dest;
      if(c[y] == c[i])
        return 0;
      aux = aux->next;
    }
  }
  return 1;
}


// ver com o prof -- complexidade lixada
int Maior_cont(GraphL gl){
  int cont[MAX];
  int vis[MAX];
  int freq[MAX];
  int i,y;
  int res = 0;
  struct edge *aux;

  for(i = 0; i < MAX; i++) {
    cont[i] = -1;
    vis[i] = -1;
    freq[i] = 0;
  }
  for(i = 0; i < MAX; i++){
    aux = gl[i];
    if(vis[i] == -1){
      vis[i] = 0;
      cont[i] = i;
    }
    while(aux){
      y = aux->dest;
      if(vis[y] == -1){
        cont[y] = i;
        vis[y] = 0;
      }
      else if(vis[y] != -1){
        cont[i] = cont[y];
      }
      aux = aux->next;
    }
  }

  for( i = 0; i < MAX ; i++){
    printf( "| %d | %d |\n",i,cont[i]);
    freq[cont[i]]++;
  }

  printf("\n");
  for( i = 0; i < MAX ; i++){
    printf( "| %d | %d |\n",i,freq[i]);

    if(res < freq[i]) res = freq[i];
  }
  return res;
}

//breath search graph
void bst(GraphL gl,int vertice){
  int sort[MAX];
  int vis[MAX];
  int front = back = 0;
  int i, y;
  struct edge *aux;
  sort[back++] = vertice;


  for(i = 0; i < MAX; i++)
    vis[i] = 0;

  vis[vertice] = 1;
  while(front != back){
    i = sort[front];
    for(aux = gl[i]; aux; aux = aux->next){
      y = aux->dest;
      if(!vis[y]){
        printf("nodo %d entrou pelo nodo - %d \n",y,i);
        sort[back++] = y;
        vis[y] = 1;
      }
    }
    front++;
  }

  for(i = 0; i < MAX; i++)
    printf(" | %d | ",sort[i]);
}

//depth search graph

void dsgAux(GraphL gl, int v,int sort[]){
  int i,y;
  struct edge *aux;
  for(aux = gl[v]; aux; aux = aux->next){
    y = aux->dest;
    printf("dest: %d\n",y);
    if(!vis[y]){
      vis[y] = 1;
      dsgAux(gl,y,sort);
    }
  }
  printf("guardando: %d --- t = %d\n ",v,t);
  sort[t--] = v;
}

void dsg(GraphL gl, int v, int sort[]){
  int i;
  t = MAX -1;

  for( i = 0; i < MAX; i++) vis[i] = 0;

  dsgAux(gl,v,sort);
}
/*
  MAIN
*/

int main(){
  GraphM gm = {
    {NE,  2, NE, NE, NE,  7,  3, NE, NE},
    { 2, NE,  4, NE, NE, NE,  6, NE, NE},
    {NE,  4, NE,  2, NE, NE, NE,  2, NE},
    {NE, NE,  2, NE,  1, NE, NE,  8, NE},
    {NE, NE, NE,  1, NE,  6, NE, NE,  2},
    { 7, NE, NE, NE,  6, NE, NE, NE,  5},
    { 3,  6, NE, NE, NE, NE, NE,  3,  1},
    {NE, NE,  2,  8, NE, NE,  3, NE,  4},
    {NE, NE, NE, NE,  2,  5,  1,  4, NE}
    };

  Colors c = {0,1,2,3,4,5,1,1,1};
  //printGraphM(gm);

  //PARA BST
  GraphM gm2 = {
    {NE,  2, NE, NE, NE,  7, NE, NE, NE},
    {NE, NE,  4, NE, NE, NE, NE, NE, NE},
    {NE, NE, NE,  2, NE, NE, NE,  2, NE},
    {NE, NE, NE, NE, NE, NE, 4, NE, NE},
    {NE, NE, NE, NE, NE, NE, NE, NE, NE},
    {NE, NE, NE, NE, 4, NE, NE, NE, NE},
    {NE, NE, NE, NE, NE, NE, NE,  3, NE},
    {NE, NE, NE, NE, NE, NE, NE, NE,  4},
    {NE, NE, NE, NE, NE, NE, NE, NE, NE}
    };

  GraphL gl;
  MtoL(gm2,gl);
  //printGraphL(gl);

  //int res;
  //res = Maior_cont(gl);
  //printf("%d\n",res);


  /*
  Ver graus de entrada / saida e Topological Sort com outra matriz
  */
  //int res[MAX];
  int i;
  //mst(gl,0,res);
  //dkjistra(gl,0,res);

  /*
  for(i = 0; i < MAX; i++){
    printf("| %d | ",res[i]);
  }
  */

  /*
  int flag = check_coloring(gl,c);
  if(flag)
    printf("Passou\n");
  else
    printf("N Passou\n");
  */

  //bst(gl,4);
  int sort[MAX];
  dsg(gl,0,sort);

  for(i = 0; i < MAX ; i++)
    printf(" | %d | ",sort[i]);
}

///////////////////////////////////////////////////////////////////////////////////////////////////////

#include "graphs.c"


// MINHAS SOLUÇÕES
MatrizAdj initMAdj(){
  MatrizAdj aux;
  for(int i = 0; i < V; i++){
    for(int v = 0; v < V; j++){
      aux[i][j] = -1;
    }
  }
  return aux;
}

ListAdj initLAdj(){
  ListAdj aux = (ListAdj) malloc(sizeof(struct edge))
  for(int i = 0; i < V; i++)
    aux->next = NULL
  return aux
}

void MAtoLA(MatrizAdj ma, ListAdj la){
  struct edge aux;
  for(int i = 0; i < V; i++){
    la[i] = NULL;
    for(int j= V-1; j > 0; j++){
      if( ma[i][j] >= 0){
        aux = (Edge) malloc(sizeof(struct edge));
        aux->custo = ma[i][j];
        aux->dest = j;
        aux->next = la[i]; //esta a adicionar ao contrario
        la[i] = aux;
      }
    }
  }
}

void LAtoMA(MatrizAdj ma, ListAdj la){
  struct edge aux;
  for(int i = 0; i < V; i++){
    for(aux = la[i]; aux; aux = aux->next){
      ma[i][aux->dest] = aux->value;
    }
  }
}
// Funcoes de saber quantos vertices entram num nodo


//melhor caso -  N
//pior caso - N + A
int inLA(ListAdj l,int v){
  struct edge aux;
  int r = 0;
  int flag;
  for(int i = 0; i < V; i++){
    flag = 0
    for(aux = l[i];aux || flag != 0;aux=aux->next){
      if(aux->dest = v){
        r++;
        flag = 1;
      }
    }
  }
  return r;
}

// complexidade igual = N
int inMA(MatrizAdj m, int v){
  int r = 0;
  for(int i = 0; i < V; i++){
    if(m[i][v] >= 0)
      r++;
  }
  return r;
}

// complexidade igual = N

int outMA(MatrizAdj m, int v){
  int r = 0;
  for(int j = 0; j < V; j++){
    if(m[v][j] >= 0)
      r++;
  }
  return r;
}

//melhor caso = 1 (Não tem arestas associadas a esse nó)
//pior caso = min(N,A)
int outLA(ListAdj l,int v){
  int r = 0;
  struct edge aux;
  for(aux = l[v];aux;aux=aux->next)
    r++;
  return r;
}

//complexidade desta funcao é 2N = N
int capMA(MatrizAdj m, int v){}

//melhor caso = N
//pior caso = N + A
int capLA(ListAdj l, int v){}

//complexidade N^2
int maxCapLA(ListAdj l){}

//para melhorar este em vez de invocar a funcao capLA para cada nodo podemos percorrer tudo e ao mesmo tempo ir trabalhar os valores de capacidade num array auxiliar e apresenta-lo no fim - complexidade N + A
int maxCapMA(MatrizAdj m){}

//complexidade N2
int ColorOKMatriz(MatrizAdj m,int color[]){
  for(int i = 0; i < V; i++){
    for(int j = 0; j < V;j++){
      if(m[i][j] >= 0 && i!=j && color[i] == color[j])
        return 1; // falhou
    }
  }
  return 0;
}

int ColorOKList(ListAdj l,int color[]){
  struct edge aux;
  for(int i = 0; i < V; i++){
    for(aux = l[i];aux;aux = aux->next){
      if(color[aux->dest] == color[i])
        return 1; //falhou
    }
  }
  return 0;
}




//SOLUÇÕES DO PROF


// complexidade nesta funcao e n^2 por causa da inicializao do ciclo
void LA2MA(MatrizAdj ma, ListAdj la){
 int i,j;
 Edge aux;
 for(i=0; i < V; i++)
  for(j=0; j < V; j++)
    r[i][j] = -1;
  for(i = 0; i < N ; i++){
    aux = g[i];
    while aux {
      r[i][aux->dest] = aux->peso;
      aux = aux -> prox;
    }
  }
}

/*
  Travessias ESTUDAR
*/

// funcao que ve em largura os nodos a que chega a partir de um nodo inicial
int BSG(ListAdj l,int aux[],int nInicial){
  struct edge nodo;
  for(i = 0; i < V; i++ ) vis[i] == WHITE;

  for(nodo = l[nInicial];nodo;nodo = nodo->next){

  }

}



/*
  Topological Sort
*/

int color[V]; //matriz com as cores do grafo
int t; //variavel para colocar no array de Topological Sort na posicao certa


int topSort_Tarjan(ListAdj l, int aux[]){
  int i,  cycle = 0;

  t = V - 1;
  for(i=0;i < V;i++) vis[i] == WHITE;

  for(i=0;i < V && !cycle; i++)
    if(vis[i] == WHITE) cycle = DF_sol(g,i,n,tsort);

  return cycle; //para no final dizer se tem ciclo à funcao de output . se tiver ciclo não existe
}


//confirmar esta funcao com o codeboard
int DFS_sol(ListAdj l, int i, int sort[]){

  int cycle;
  struct edge P;
  vist[i] = GRAY;

  for(p=l[i]; p && !cycle; p=p->next){

    if(vis[p->dest] == GRAY) cycle = 1;
    else if(vis[p->dest] == WHITE)
      cycle = DFS_sol(g,p->dest,t->sort);
  }

  vis[i] = BLACK
  tsort[t--] = i;

  return cycle;
}


void inDegrees(ListAdj l, int inD[]){
  struct edge aux;
  for(int i = 0; i < V; i++){
    inD[i] = 0;
  }

  for(i = 0 ; i < V; i++){
    for(aux = l[i];aux;aux = aux-> next){
      inD[aux->dest] += 1;
    }
  }
}

int topSort_Kahn(ListAdj l, int aux[]){
  int inD[], first, last, v; //first e last para a queue;
  struct edge node;

  inDegrees(l,inD);

  first = last = 0;
  for(v=0;v < V; v++)
    if(inD[v] == 0) tsort[last++] = v;

  while(first != last){
    v = tsort[first++];
    for(p=g[v];p;)

  /*
    Falta acabar
  */
  }
}

/*
  MST
*/
void mst(ListAdj l, int parent[]){

  int status[V];
  int fringeLink[V];
  int fringeWgt[V];
  struct edge *ptr;
  int x,y;
  int fringeList;
  int edgeCount;
  int stuck;
  int sum;

    /* inicializacao */

  x = 0;
  status[0] = INTREE;
  parent[0] = -1;

  stuck = 0;

  edgeCount = 0;

  fringeList = NIL;

  for (y = 1 ; y < n ; y++) status[y] = UNSEEN;

  while(edgeCount<n-1 && !stuck) {
    ptr = l[x];
    while(ptr){
      y = ptr->dest;
      if(status[y] = FRINGE && ptr->custo < fringeWgt[y]){
        fringeWgt[y] = ptr->custo;
        parent[y] = x;
      }else if(status[ptr->dest] == UNSEEN){
        status[y] = FRINGE;
        fringeLink[y] = fringeList;
        fringeList = y;
        parent[y] = x;
        fringeWgt[y] = ptr->custo;
      }
    ptr = ptr->next;
    }
    if(fringeList == NIL) stuck = 1;
    else {
      int prev = 0;
      x = fringeList;
      for(y=fringeList; fringeLink[y] != NIL; y=fringeLink[y]){
        if(fringeWgt[fringeList[y]] < fringeWgt[x]){
          x = fringeLink[y];
          prev = y;
        }
      }
      if (x == fringeList) fringe

      /* falta acabar

      */

      /* ISTO É MEU

      int aux = -1;
      while(fringeLink[fringeList] != NIL){
        if(aux == -1)
          aux = fringeWgt[fringeList];
        else if(aux > fringeWgt[fringeList]){
          aux = fringeWgt[fringeList];
        }
        fringeList = fringeLink[fringeList];
      }
      */
    edgeCount++;
      }
  }
}

  void printPath(int cam[N][N], int o , int d){
    if(cam[o][d] == -1)
      printf("%d -> %d\n",o,d);
    else{
      printPath(cam,o,cam[o][d]);
      printPath(cam,cam[o][d],d);
    }
  }

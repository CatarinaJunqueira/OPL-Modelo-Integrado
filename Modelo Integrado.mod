/*********************************************
 * OPL 12.8.0.0 Model
 * Author: Catarina
 * Creation Date: 15/06/2018 at 10:31:19
 *********************************************/

int P=...;
int H[1..P-1] =...; 
int W[1..P-1] =...; 
int T[1..P-1] =...; 
int N[1..P-1] =...; 
int R=...;
int C=...;
{int} omega[1..P-1]=...;
int patios[1..P-1][1..max(o in 1..P-1)H[o]][1..max(o in 1..P-1)W[o]]=...;
int M=...;
int theta=...;
int F[1..P-1][1..P-1] =...;

//M=0;
//for o=1:length(N)
//    M = M+(N(o)*((H(o))^2));
//end

tuple bindex {
int patio;
int i;
int j;
int n;
int t;
}

{bindex}  bindexes = {<o,i,j,n,t> | o in 1..P-1, i in 1..W[o], j in 1..H[o], n in omega[o], t in 1..T[o]};

tuple vindex {
int patio;
int n;
int t;
}

{vindex}  vindexes = {<o,n,t> | o in 1..P-1, n in omega[o], t in 1..T[o]};

tuple xindex {
int patio;
int i;
int j;
int k;
int l;
int n;
int t;
}

{xindex}  xindexes = {<o,i,j,k,l,n,t> | o in 1..P-1, i in 1..W[o], j in 1..H[o], k in 1..W[o], l in 1..H[o], n in omega[o], t in 1..T[o]};

tuple yindex {
int patio;
int i;
int j;
int n;
int t;
}

{yindex}  yindexes = {<o,i,j,n,t> | o in 1..P-1, i in 1..W[o], j in 1..H[o], n in omega[o], t in 1..T[o]};

tuple zindex {
int patio;
int n;
int t;
int r;
int c;
}

{zindex}  zindexes = {<o,n,t,r,c> | o in 1..P-1, n in omega[o], t in 1..T[o], r in 1..R, c in 1..C};

tuple qindex {
int patio;
int d;
int r;
int c;
}

{qindex}  qindexes = {<o,d,r,c> | o in 1..P-1, d in o+1..P, r in 1..R, c in 1..C};

tuple windex {
int patio;
int d;
int a;
int r;
int c;
}

{windex}  windexes = {<o,d,a,r,c> | o in 1..P-1, d in o+1..P, a in o+1..d-1, r in 1..R, c in 1..C};

tuple uindex {
int patio;
int r;
int c;
}

{uindex}  uindexes = {<o,r,c> | o in 1..P-1, r in 1..R, c in 1..C};

/* variáveis */
dvar boolean b[bindexes];                  // b_{ijnt}
dvar boolean v[vindexes];                  // v_{nt}
dvar boolean x[xindexes];                  // x_{ijklnt}
dvar boolean y[yindexes];                  // y_{ijnt}
dvar boolean z[zindexes];                  // z_{ntrc}
dvar boolean q[qindexes];                  // q_{odrc}
dvar boolean w[windexes];                  // w_{odarc}
dvar boolean u[uindexes];                  // u_{orc}


/* Função Objetivo */

minimize sum(o in 1..P-1, i in 1..W[o], j in 1..H[o], k in 1..W[o], l in 1..H[o], n in omega[o], t in 1..T[o])x[<o,i,j,k,l,n,t>] + sum(o in 1..P-1, d in o+1..P, a in o+1..d-1, r in 1..R, c in 1..C)w[<o,d,a,r,c>];

/* Restrições */

subject to{

//Restr. 0: vincular o patio inicial
//  forall(o in 1..P-1, i in 1..W[o], j in 1..H[o], n in omega[o]){
//   if (P[o,1][H[o]-j+1][i]) 
//   b[<o,i,j+1,n,1>] == 1;    
//}

//Restr. 1: garante que em cada período de tempo, cada contêiner deve estar dentro do pátio ou fora dele.
forall ( o in 1..P-1, n in omega[o], t in 1..T[o])
  sum(i in 1..W[o], j in 1..H[o]) b[<o,i,j,n,t>] + v[<o,n,t>] == 1; 

//Restr. 2: garante que em cada período de tempo, cada posição (i,j) no pátio deve estar ocupada por um único contêiner.  
forall(o in 1..P-1, i in 1..W[o], j in 1..H[o], t in 1..T[o])
  sum(n in omega[o])b[<o,i,j,n,t>] <=1;
  
//Restr. 3: garante que não hajam ‘buracos’ no pátio ao restringir que se há um contêiner posição $(i,j+1)$, então a posição $(i,j)$ abaixo também deve estar ocupada.
forall(o in 1..P-1, i in 1..W[o], j in 1..H[o]-1, t in 1..T[o])
  sum(n in omega[o])b[<o,i,j,n,t>] >= sum(n in omega[o])b[<o,i,j+1,n,t>];
  
//Restr. 4: restrição de equilíbrio de fluxo entre as variáveis de configuração e de movimento no pátio. Ele vincula o layout no período t com o layout no período t + 1 através das retiradas e realocações executadas.
forall(o in 1..P-1, i in 1..W[o], j in 1..H[o], n in omega[o], t in 2..T[o])
 b[<o,i,j,n,t-1>] - b[<o,i,j,n,t>] + sum(k in 1..W[o], l in 1..H[o])x[<o,k,l,i,j,n,t-1>] - sum(k in 1..W[o], l in 1..H[o])x[<o,i,j,k,l,n,t-1>] - y[<o,i,j,n,t-1>] == 0;
  
//Restr. 5: define a variável $v_{nt}$ e assegura que todos os contêineres sejam retirados do pátio 
forall( o in 1..P-1, n in omega[o], t in 2..T[o])
  v[<o,n,t>] == sum(i in 1..W[o], j in 1..H[o], tt in 1..t-1)y[<o,i,j,n,tt>];  
  
//Restr. 6: garante a política LIFO, ou seja, se no período t, o contêiner $n$ está abaixo do contêiner $q$ e o contêiner $n$ é remanejado, então no período $t + 1$ o contêiner $n$ não pode estar alocado em uma posição abaixo do contêiner $q$. 
forall(o in 1..P-1, i,k in 1..W[o], j,l in 1..H[o]-1, t in 1..T[o])
  M*(1-sum(n in omega[o])x[<o,i,j,k,l,n,t>]) >= sum(n in omega[o], jj in j+1..H[o], ll in l+1..H[o])x[<o,i,jj,k,ll,n,t>];
  
//Restr. 7: garante que sejam remanejados apenas os contêineres que estão acima, ou seja, na mesma coluna, de um contêiner a ser retirado. 
  forall(o in 1..P-1, n in omega[o], t in 1..T[o], i in 1..W[o])
    M*(1 - sum(j in 1..H[o])b[<o,i,j,n,t>]) >= sum(j in 1..H[o], k in 1..W[o], l in 1..H[o], n in omega[o], ii in 1..i-1)x[<o,ii,j,k,l,n,t>];
  
//Restr. 8: garante que nenhum contêiner pode ser remanejado para outra posição que esteja da mesma coluna na qual ele se encontra.  
 forall(o in 1..P-1, n in omega[o], i in 1..W[o], j,l in 1..H[o], t in 1..T[o]) 
  x[<o,i,j,i,l,n,t>] == 0;
  
 //Restr. 9: garante que um contêiner na posição $(i,j)$ só pode ser movido depois que o contêiner na posição $(i,j+1)$ é movido.
 forall(o in 1..P-1, i in 1..W[o], j in 1..H[o]-1, t in 1..T[o])
   sum(k in 1..W[o], l in 1..H[o], n in omega[o]) x[<o,i,j+1,k,l,n,t>] - sum(n in omega[o])b[<o,i,j+1,n,t>] + 1 >= sum(k in 1..W[o], l in 1..H[o], n in omega[o]) x[<o,i,j,k,l,n,t>] + sum(n in omega[o])y[<o,i,j,n,t>];
 
 // /* Restricoes de Integracao: */
 //Restr 10: garante que em cada período de tempo um contêiner seja retirado do pátio.
 forall(o in 1..P-1, t in 1..T[o])
  sum( n in omega[o])v[<o,n,t>] == t;
  
 //Restr 11: define a variável $v_{nt}$. Quando um contêiner $n$ é retirado do pátio, a variável $v_{nt}$ se torna 1 e se mantém igual a 1 nos períodos de tempo seguintes.
 forall(o in 1..P-1, n in omega[o], t in 1..T[o]-1)
   v[<o,n,t+1>] >= v[<o,n,t>];
    
 //Restr 12: garante que o contêiner $n$ seja carregado no navio no período de tempo $t$.
 forall(o in 1..P-1, n in omega[o], t in 1..T[o]-1)
   sum(r in 1..R, c in 1..C)z[<o,n,t,r,c>] == v[<o,n,t+1>];
  
 //Restr 13: assegura que uma posição $(r,c)$ no navio só pode ser ocupada por um contêiner, seja ele um contêiner que foi carregado no porto atual (porto $o$), em algum porto 
 //anterior (porto $o-1$) ou um contêiner que já estava no navio e está sendo remanejado em $o$.
 forall(o in 1..P-1, r in 1..R, c in 1..C, t in 1..T[o])
   sum(oo in 1..o-1, d in o+1..P, a in o+1..d)w[<oo,d,a,r,c>] + sum(d in o+1..P)q[<o,d,r,c>] + sum(n in omega[o])z[<o,n,t,r,c>] <= 1;
  
 //Restr 14: certifica que o contêiner $n$, depois de carregado, não mude de posição enquanto o navio estiver parado no mesmo porto.
 forall(o in 1..P-1, n in omega[o], r in 1..R, c in 1..C, t in 1..T[o]-1)
   z[<o,n,t+1,r,c>] >= z[<o,n,t,r,c>];
 
 //Restr 15: garante que se há um contêiner na posição $(r,c)$ do navio, ele deve ser um contêiner que acabou de ser embarcado, ou um contêiner de remanejamento.
 forall(o in 1..P-1, r in 1..R, c in 1..C, d in o+1..P)
   sum(a in o+1..d)w[<o,d,a,r,c>] == sum(n in omega[o])z[<o,n,T[o],r,c>] + q[<o,d,r,c>];
 
 //Restr 16: assegura que todos os $N_{o}$ contêineres do pátio $o$ já foram embarcados no navio.
 forall(o in 1..P-1, n in omega[o], t in 1..T[o]-1)
   sum(r in 1..R, c in 1..C)z[<o,n,T[o],r,c>]==1;  
  
 //Restr 17: garante que, durante o processo de carregamento do navio, nenhum contêiner seja alocado em uma posição flutuante ou que ocupe a posição de um contêiner que já estava no 
 // navio ou foi remanejado.
  forall(o in 1..P-1, r in 1..R, c in 1..C, t in 1..T[o])
    sum(n in omega[o])z[<o,n,t,r,c>] + sum(oo in 1..o-1, d in o+1..P, a in o+1..d)w[<oo,d,a,r,c>] + sum(d in o+1..P)q[<o,d,r,c>] >= sum(n in omega[o])z[<o,n,t,r+1,c>]; 
  
 //Restr 18: contabiliza o número total de contêineres que foram remanejados no porto $o$. 
 forall(o in 1..P-1, d in o+1..P)
   sum(oo in 1..o-1, c in 1..C, r in 1..R)w[<oo,d,o,r,c>] == sum(r in 1..R, c in 1..C)q[<o,d,r,c>];
 
  //Restr 19: mantém a estabilidade do navio.
 // forall(o in 1..P-1)
 //   sum(c in 1..C, r in (theta/C)+1..R)u[<o,r,c>]==0; 
  
  // /* Restricoes do Navio: */
  //Restr 20: é a restrição de conservação de fluxo, e indica que o número total de contêineres no porto $o$ deve ser igual ao número de contêineres que foram embarcados nos 
  // portos $p=1,2,...,o$ menos os contêineres que foram desembarcados nos portos $p=1,2,...,o$ . Esta restrição pode ser redundante, mas é mantida no modelo porque deixa-o mais rápido.
  forall(o in 1..P-1, d in o+1..P)
  sum(a in o+1..d, r in 1..R, c in 1..C)w[<o,d,a,r,c>] - sum(m in 1..o-1, r in 1..R, c in 1..C)w[<m,d,o,r,c>] == F[o,d];
  
  //Restr 21: garante que cada posição $(r, c)$ tenha no máximo um único contêiner.
  forall(o in 1..P-1, r in 1..R, c in 1..C)
    sum(m in 1..o, d in o+1..P, a in o+1..d)w[<m,d,a,r,c>] == u[<o,r,c>];  
  
  //Restr 22: é necessária para garantir que existam contêineres embaixo do contêiner que ocupa a célula $(r, c)$.
  forall(o in 1..P-1, r in 1..R-1, c in 1..C)
    u[<o,r,c>] - u[<o,r+1,c>] >= 0;
  
  //Restr. 23: define como um contêiner pode ser desembarcado no porto $d$ ao impor que se um contêiner que ocupa a posição $(r, c)$, então ele será desembarcado no porto $d$, se não 
  //houver um contêiner na posição $(r+1, c)$ acima dele.
   forall(d in 2..P, r in 1..R-1, c in 1..C)
     sum(o in 1..d-1, e in d..P)w[<o,e,d,r,c>] + sum(o in 1..d-1, e in d+1..P, a in d+1..e)w[<o,e,a,r+1,c>] <= 1;  
}
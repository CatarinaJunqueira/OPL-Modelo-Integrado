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

/* vari�veis */
dvar boolean b[bindexes];                  // b_{ijnt}
dvar boolean v[vindexes];                  // v_{nt}
dvar boolean x[xindexes];                  // x_{ijklnt}
dvar boolean y[yindexes];                  // y_{ijnt}
dvar boolean z[zindexes];                  // z_{ntrc}
dvar boolean q[qindexes];                  // q_{odrc}
dvar boolean w[windexes];                  // w_{odarc}
dvar boolean u[uindexes];                  // u_{orc}


/* Fun��o Objetivo */

minimize sum(o in 1..P-1, i in 1..W[o], j in 1..H[o], k in 1..W[o], l in 1..H[o], n in omega[o], t in 1..T[o])x[<o,i,j,k,l,n,t>] + sum(o in 1..P-1, d in o+1..P, a in o+1..d-1, r in 1..R, c in 1..C)w[<o,d,a,r,c>];

/* Restri��es */

subject to{

//Restr. 0: vincular o patio inicial
//  forall(o in 1..P-1, i in 1..W[o], j in 1..H[o], n in omega[o]){
//   if (P[o,1][H[o]-j+1][i]) 
//   b[<o,i,j+1,n,1>] == 1;    
//}

//Restr. 1: garante que em cada per�odo de tempo, cada cont�iner deve estar dentro do p�tio ou fora dele.
forall ( o in 1..P-1, n in omega[o], t in 1..T[o])
  sum(i in 1..W[o], j in 1..H[o]) b[<o,i,j,n,t>] + v[<o,n,t>] == 1; 

//Restr. 2: garante que em cada per�odo de tempo, cada posi��o (i,j) no p�tio deve estar ocupada por um �nico cont�iner.  
forall(o in 1..P-1, i in 1..W[o], j in 1..H[o], t in 1..T[o])
  sum(n in omega[o])b[<o,i,j,n,t>] <=1;
  
//Restr. 3: garante que n�o hajam �buracos� no p�tio ao restringir que se h� um cont�iner posi��o $(i,j+1)$, ent�o a posi��o $(i,j)$ abaixo tamb�m deve estar ocupada.
forall(o in 1..P-1, i in 1..W[o], j in 1..H[o]-1, t in 1..T[o])
  sum(n in omega[o])b[<o,i,j,n,t>] >= sum(n in omega[o])b[<o,i,j+1,n,t>];
  
//Restr. 4: restri��o de equil�brio de fluxo entre as vari�veis de configura��o e de movimento no p�tio. Ele vincula o layout no per�odo t com o layout no per�odo t + 1 atrav�s das retiradas e realoca��es executadas.
forall(o in 1..P-1, i in 1..W[o], j in 1..H[o], n in omega[o], t in 2..T[o])
 b[<o,i,j,n,t-1>] - b[<o,i,j,n,t>] + sum(k in 1..W[o], l in 1..H[o])x[<o,k,l,i,j,n,t-1>] - sum(k in 1..W[o], l in 1..H[o])x[<o,i,j,k,l,n,t-1>] - y[<o,i,j,n,t-1>] == 0;
  
//Restr. 5: define a vari�vel $v_{nt}$ e assegura que todos os cont�ineres sejam retirados do p�tio 
forall( o in 1..P-1, n in omega[o], t in 2..T[o])
  v[<o,n,t>] == sum(i in 1..W[o], j in 1..H[o], tt in 1..t-1)y[<o,i,j,n,tt>];  
  
//Restr. 6: garante a pol�tica LIFO, ou seja, se no per�odo t, o cont�iner $n$ est� abaixo do cont�iner $q$ e o cont�iner $n$ � remanejado, ent�o no per�odo $t + 1$ o cont�iner $n$ n�o pode estar alocado em uma posi��o abaixo do cont�iner $q$. 
forall(o in 1..P-1, i,k in 1..W[o], j,l in 1..H[o]-1, t in 1..T[o])
  M*(1-sum(n in omega[o])x[<o,i,j,k,l,n,t>]) >= sum(n in omega[o], jj in j+1..H[o], ll in l+1..H[o])x[<o,i,jj,k,ll,n,t>];
  
//Restr. 7: garante que sejam remanejados apenas os cont�ineres que est�o acima, ou seja, na mesma coluna, de um cont�iner a ser retirado. 
  forall(o in 1..P-1, n in omega[o], t in 1..T[o], i in 1..W[o])
    M*(1 - sum(j in 1..H[o])b[<o,i,j,n,t>]) >= sum(j in 1..H[o], k in 1..W[o], l in 1..H[o], n in omega[o], ii in 1..i-1)x[<o,ii,j,k,l,n,t>];
  
//Restr. 8: garante que nenhum cont�iner pode ser remanejado para outra posi��o que esteja da mesma coluna na qual ele se encontra.  
 forall(o in 1..P-1, n in omega[o], i in 1..W[o], j,l in 1..H[o], t in 1..T[o]) 
  x[<o,i,j,i,l,n,t>] == 0;
  
 //Restr. 9: garante que um cont�iner na posi��o $(i,j)$ s� pode ser movido depois que o cont�iner na posi��o $(i,j+1)$ � movido.
 forall(o in 1..P-1, i in 1..W[o], j in 1..H[o]-1, t in 1..T[o])
   sum(k in 1..W[o], l in 1..H[o], n in omega[o]) x[<o,i,j+1,k,l,n,t>] - sum(n in omega[o])b[<o,i,j+1,n,t>] + 1 >= sum(k in 1..W[o], l in 1..H[o], n in omega[o]) x[<o,i,j,k,l,n,t>] + sum(n in omega[o])y[<o,i,j,n,t>];
 
 // /* Restricoes de Integracao: */
 //Restr 10: garante que em cada per�odo de tempo um cont�iner seja retirado do p�tio.
 forall(o in 1..P-1, t in 1..T[o])
  sum( n in omega[o])v[<o,n,t>] == t;
  
 //Restr 11: define a vari�vel $v_{nt}$. Quando um cont�iner $n$ � retirado do p�tio, a vari�vel $v_{nt}$ se torna 1 e se mant�m igual a 1 nos per�odos de tempo seguintes.
 forall(o in 1..P-1, n in omega[o], t in 1..T[o]-1)
   v[<o,n,t+1>] >= v[<o,n,t>];
    
 //Restr 12: garante que o cont�iner $n$ seja carregado no navio no per�odo de tempo $t$.
 forall(o in 1..P-1, n in omega[o], t in 1..T[o]-1)
   sum(r in 1..R, c in 1..C)z[<o,n,t,r,c>] == v[<o,n,t+1>];
  
 //Restr 13: assegura que uma posi��o $(r,c)$ no navio s� pode ser ocupada por um cont�iner, seja ele um cont�iner que foi carregado no porto atual (porto $o$), em algum porto 
 //anterior (porto $o-1$) ou um cont�iner que j� estava no navio e est� sendo remanejado em $o$.
 forall(o in 1..P-1, r in 1..R, c in 1..C, t in 1..T[o])
   sum(oo in 1..o-1, d in o+1..P, a in o+1..d)w[<oo,d,a,r,c>] + sum(d in o+1..P)q[<o,d,r,c>] + sum(n in omega[o])z[<o,n,t,r,c>] <= 1;
  
 //Restr 14: certifica que o cont�iner $n$, depois de carregado, n�o mude de posi��o enquanto o navio estiver parado no mesmo porto.
 forall(o in 1..P-1, n in omega[o], r in 1..R, c in 1..C, t in 1..T[o]-1)
   z[<o,n,t+1,r,c>] >= z[<o,n,t,r,c>];
 
 //Restr 15: garante que se h� um cont�iner na posi��o $(r,c)$ do navio, ele deve ser um cont�iner que acabou de ser embarcado, ou um cont�iner de remanejamento.
 forall(o in 1..P-1, r in 1..R, c in 1..C, d in o+1..P)
   sum(a in o+1..d)w[<o,d,a,r,c>] == sum(n in omega[o])z[<o,n,T[o],r,c>] + q[<o,d,r,c>];
 
 //Restr 16: assegura que todos os $N_{o}$ cont�ineres do p�tio $o$ j� foram embarcados no navio.
 forall(o in 1..P-1, n in omega[o], t in 1..T[o]-1)
   sum(r in 1..R, c in 1..C)z[<o,n,T[o],r,c>]==1;  
  
 //Restr 17: garante que, durante o processo de carregamento do navio, nenhum cont�iner seja alocado em uma posi��o flutuante ou que ocupe a posi��o de um cont�iner que j� estava no 
 // navio ou foi remanejado.
  forall(o in 1..P-1, r in 1..R, c in 1..C, t in 1..T[o])
    sum(n in omega[o])z[<o,n,t,r,c>] + sum(oo in 1..o-1, d in o+1..P, a in o+1..d)w[<oo,d,a,r,c>] + sum(d in o+1..P)q[<o,d,r,c>] >= sum(n in omega[o])z[<o,n,t,r+1,c>]; 
  
 //Restr 18: contabiliza o n�mero total de cont�ineres que foram remanejados no porto $o$. 
 forall(o in 1..P-1, d in o+1..P)
   sum(oo in 1..o-1, c in 1..C, r in 1..R)w[<oo,d,o,r,c>] == sum(r in 1..R, c in 1..C)q[<o,d,r,c>];
 
  //Restr 19: mant�m a estabilidade do navio.
 // forall(o in 1..P-1)
 //   sum(c in 1..C, r in (theta/C)+1..R)u[<o,r,c>]==0; 
  
  // /* Restricoes do Navio: */
  //Restr 20: � a restri��o de conserva��o de fluxo, e indica que o n�mero total de cont�ineres no porto $o$ deve ser igual ao n�mero de cont�ineres que foram embarcados nos 
  // portos $p=1,2,...,o$ menos os cont�ineres que foram desembarcados nos portos $p=1,2,...,o$ . Esta restri��o pode ser redundante, mas � mantida no modelo porque deixa-o mais r�pido.
  forall(o in 1..P-1, d in o+1..P)
  sum(a in o+1..d, r in 1..R, c in 1..C)w[<o,d,a,r,c>] - sum(m in 1..o-1, r in 1..R, c in 1..C)w[<m,d,o,r,c>] == F[o,d];
  
  //Restr 21: garante que cada posi��o $(r, c)$ tenha no m�ximo um �nico cont�iner.
  forall(o in 1..P-1, r in 1..R, c in 1..C)
    sum(m in 1..o, d in o+1..P, a in o+1..d)w[<m,d,a,r,c>] == u[<o,r,c>];  
  
  //Restr 22: � necess�ria para garantir que existam cont�ineres embaixo do cont�iner que ocupa a c�lula $(r, c)$.
  forall(o in 1..P-1, r in 1..R-1, c in 1..C)
    u[<o,r,c>] - u[<o,r+1,c>] >= 0;
  
  //Restr. 23: define como um cont�iner pode ser desembarcado no porto $d$ ao impor que se um cont�iner que ocupa a posi��o $(r, c)$, ent�o ele ser� desembarcado no porto $d$, se n�o 
  //houver um cont�iner na posi��o $(r+1, c)$ acima dele.
   forall(d in 2..P, r in 1..R-1, c in 1..C)
     sum(o in 1..d-1, e in d..P)w[<o,e,d,r,c>] + sum(o in 1..d-1, e in d+1..P, a in d+1..e)w[<o,e,a,r+1,c>] <= 1;  
}
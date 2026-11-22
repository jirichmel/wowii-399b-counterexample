/* vc.c -- implementation C of the verify-math checks (bitmasks).
   Written from the definitions; shares no code with vp.py.
   Build: cc -O2 -o vc vc.c
   Modes:
     ./vc enum NMAX           all graphs up to isomorphism by vertex addition, n=1..NMAX,
                              canonical form = min code over degree-sorted relabelings;
                              statistics for connected graphs, hits listed in graph6
     ./vc g6 S1 S2 ...        invariants of the given graph6 strings
     ./vc iso S1 S2           backtracking isomorphism test
     ./vc f3del               F_3 minus one vertex / one edge
     ./vc fq Q                F_Q: invariants, robustness variants (M6)            */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXN 24
typedef struct { int n; uint32_t a[MAXN]; } G;

static int pc(uint32_t x){ return __builtin_popcount(x); }

static int g6dec(const char *s, G *g){
  int n = s[0]-63; if(n<1||n>62) return -1; if(n>MAXN) return -1;
  g->n=n; memset(g->a,0,sizeof g->a);
  int k=0; const char *p=s+1; int bitpos=0; int cur=0;
  for(int j=1;j<n;j++) for(int i=0;i<j;i++){
    if(bitpos==0){ if(!*p) return -1; cur=*p-63; p++; bitpos=6; }
    bitpos--; if((cur>>bitpos)&1){ g->a[i]|=1u<<j; g->a[j]|=1u<<i; }
    k++;
  }
  return 0;
}
static void g6enc(const G *g, char *out){
  int n=g->n; int o=0; out[o++]=(char)(n+63);
  int cur=0,cnt=0;
  for(int j=1;j<n;j++) for(int i=0;i<j;i++){
    cur=(cur<<1)|((g->a[i]>>j)&1); cnt++;
    if(cnt==6){ out[o++]=(char)(cur+63); cur=0; cnt=0; }
  }
  if(cnt){ cur<<= (6-cnt); out[o++]=(char)(cur+63); }
  out[o]=0;
}

static int connected(const G *g){
  uint32_t full=(g->n==32)?0xffffffffu:((1u<<g->n)-1);
  uint32_t seen=1, fr=1;
  while(fr){ uint32_t nf=0; for(int v=0;v<g->n;v++) if(fr>>v&1) nf|=g->a[v]; fr=nf&~seen; seen|=nf; }
  return seen==full;
}
/* least |D| with every vertex outside D having >=2 (exact: ==2) neighbours in D */
static int is2dom(const G *g, uint32_t D, uint32_t full){
  uint32_t one=0,two=0;
  for(int v=0;v<g->n;v++) if(D>>v&1){ two|=one&g->a[v]; one|=g->a[v]; }
  return ((full&~D)&~two)==0;
}
static int isexact2(const G *g, uint32_t D){
  for(int v=0;v<g->n;v++) if(!(D>>v&1)) if(pc(g->a[v]&D)!=2) return 0;
  return 1;
}
static int gamma2(const G *g, int exact){
  uint32_t full=(1u<<g->n)-1; int best=g->n;
  for(uint32_t D=0; D<=full; D++){
    int c=pc(D); if(c>=best) { if(D==full) break; else continue; }
    if(exact? isexact2(g,D) : is2dom(g,D,full)) best=c;
    if(D==full) break;
  }
  return best;
}
static int alpha_on(const G *g, uint32_t A){ /* independence number of G[A] */
  int best=0;
  /* enumerate subsets of A */
  uint32_t S=0;
  do{
    int c=pc(S);
    if(c>best){ int ok=1; for(int v=0;v<g->n&&ok;v++) if(S>>v&1) if(g->a[v]&S) ok=0; if(ok) best=c; }
    S=(S-A)&A;
  } while(S);
  return best;
}
static int alpha2(const G *g){
  uint32_t full=(1u<<g->n)-1; int best=0;
  for(uint32_t S=1; ; S++){
    int c=pc(S);
    if(c>best){ int ok=1; for(int v=0;v<g->n&&ok;v++) if(S>>v&1) if(pc(g->a[v]&S)>1) ok=0; if(ok) best=c; }
    if(S==full) break;
  }
  return best;
}
static int cmpint(const void*x,const void*y){ return *(int*)x-*(int*)y; }
static int wp_from(int n, int *d){ /* max k with k+d_k<=n, d ascending, 1-based */
  int s[MAXN]; memcpy(s,d,n*sizeof(int)); qsort(s,n,sizeof(int),cmpint);
  int best=0; for(int k=1;k<=n;k++) if(k+s[k-1]<=n) best=k; return best;
}
static int wp(const G *g){ int d[MAXN]; for(int v=0;v<g->n;v++) d[v]=pc(g->a[v]); return wp_from(g->n,d); }
static int wpo(const G *g){ int d[MAXN]; for(int v=0;v<g->n;v++) d[v]=g->n-1-pc(g->a[v]); return wp_from(g->n,d); }
static uint32_t degset(const G *g, int lo, int hi){ uint32_t A=0; for(int v=0;v<g->n;v++){int d=pc(g->a[v]); if(d>=lo&&d<=hi) A|=1u<<v;} return A; }

/* ---------- canonical form for n<=8 (code fits in 28 bits) ---------- */
static int cn, cperm_deg[MAXN], cpos_of[MAXN]; static const G *cg; static uint64_t cbest; static int cused[MAXN];
static int cvert[MAXN];
static void cdfs(int p, uint64_t code){
  if(p==cn){ if(code<cbest) cbest=code; return; }
  for(int v=0;v<cn;v++){
    if(cused[v]) continue; if(pc(cg->a[v])!=cperm_deg[p]) continue;
    uint64_t c=code;
    for(int i=0;i<p;i++) if(cg->a[v]>>cvert[i]&1) c|=1ull<<(p*(p-1)/2+i);
    cused[v]=1; cvert[p]=v; cdfs(p+1,c); cused[v]=0;
  }
}
static uint64_t canon(const G *g){
  cn=g->n; cg=g; int d[MAXN]; for(int v=0;v<cn;v++) d[v]=pc(g->a[v]);
  memcpy(cperm_deg,d,cn*sizeof(int)); qsort(cperm_deg,cn,sizeof(int),cmpint);
  memset(cused,0,sizeof cused); cbest=~0ull; cdfs(0,0); return cbest;
}
static void decode_code(int n, uint64_t code, G *g){
  g->n=n; memset(g->a,0,sizeof g->a);
  for(int j=1;j<n;j++) for(int i=0;i<j;i++) if(code>>(j*(j-1)/2+i)&1){ g->a[i]|=1u<<j; g->a[j]|=1u<<i; }
}
static int cmpu64(const void*x,const void*y){ uint64_t a=*(uint64_t*)x,b=*(uint64_t*)y; return a<b?-1:a>b; }

/* ---------- backtracking isomorphism ---------- */
static const G *ig1,*ig2; static int imap[MAXN], iused[MAXN];
static int idfs(int v){
  int n=ig1->n; if(v==n) return 1;
  for(int w=0;w<n;w++){
    if(iused[w]) continue; if(pc(ig1->a[v])!=pc(ig2->a[w])) continue;
    int ok=1; for(int u=0;u<v&&ok;u++) if(((ig1->a[v]>>u)&1)!=((ig2->a[w]>>imap[u])&1)) ok=0;
    if(!ok) continue; imap[v]=w; iused[w]=1; if(idfs(v+1)) return 1; iused[w]=0;
  }
  return 0;
}
static int isomorphic(const G *a, const G *b){
  if(a->n!=b->n) return 0; memset(iused,0,sizeof iused); ig1=a; ig2=b; return idfs(0);
}

static void report(const char *label, const G *g){
  char s[200]; g6enc(g,s); int m=0; for(int v=0;v<g->n;v++) m+=pc(g->a[v]); m/=2;
  uint32_t A3=degset(g,3,1000);
  int g2=gamma2(g,0), w=wp(g), wo=wpo(g), al=A3?alpha_on(g,A3):0;
  printf("%s g6=%s n=%d m=%d conn=%d gamma2=%d WP=%d WPother=%d |A3|=%d alphaA3=%d", label,s,g->n,m,connected(g),g2,w,wo,pc(A3),al);
  if(g->n<=20) printf(" alpha2=%d", alpha2(g));
  if(A3){ int r=w+3/al, ro=wo+3/al; printf(" viol_cat=%d viol_other=%d", g2>r, g2>ro); }
  printf("\n");
}

static void enumerate(int NMAX){
  uint64_t *cur=malloc(sizeof(uint64_t)); int ncur=1; cur[0]=0; /* n=1 */
  for(int n=2;n<=NMAX;n++){
    size_t cap=(size_t)ncur<<(n-1); uint64_t *nxt=malloc(cap*sizeof(uint64_t)); size_t k=0;
    for(int t=0;t<ncur;t++){
      G h; decode_code(n-1,cur[t],&h);
      for(uint32_t S=0;S<(1u<<(n-1));S++){
        G g=h; g.n=n; g.a[n-1]=S; for(int v=0;v<n-1;v++) if(S>>v&1) g.a[v]|=1u<<(n-1);
        nxt[k++]=canon(&g);
      }
    }
    qsort(nxt,k,sizeof(uint64_t),cmpu64);
    size_t u=0; for(size_t i=0;i<k;i++) if(i==0||nxt[i]!=nxt[i-1]) nxt[u++]=nxt[i];
    free(cur); cur=nxt; ncur=(int)u;
    /* statistics */
    int nconn=0, tight[MAXN]={0}, a3empty=0, maxal=-1, violcat=0, violoth=0, bad=0, violoth_e=0;
    for(int t=0;t<ncur;t++){ G g; decode_code(n,cur[t],&g); if(!connected(&g)) continue; nconn++;
      uint32_t A3=degset(&g,3,1000); int g2=gamma2(&g,0), w=wp(&g), wo=wpo(&g); int al=A3?alpha_on(&g,A3):0;
      if(g2>w+1) bad++;
      if(!A3){ a3empty++; if(g2>wo+1) violoth_e++; }
      if(g2==w+1){ tight[al]++; if(al>maxal) maxal=al; }
      if(A3){ if(g2>w+3/al) violcat++; if(g2>wo+3/al) violoth++; }
    }
    printf("n=%d graphs=%d connected=%d A3empty=%d gamma2>WP+1:%d viol_cat=%d viol_other=%d (A3empty with gamma2>WPother+1: %d)\n",
      n,ncur,nconn,a3empty,bad,violcat,violoth,violoth_e);
    printf("n=%d tight(gamma2=WP+1) by alphaA3:",n); for(int a=0;a<=n;a++) if(tight[a]) printf(" a=%d:%d",a,tight[a]); printf("  max=%d\n",maxal);
    for(int t=0;t<ncur;t++){ G g; decode_code(n,cur[t],&g); if(!connected(&g)) continue;
      uint32_t A3=degset(&g,3,1000); int g2=gamma2(&g,0), w=wp(&g), wo=wpo(&g); int al=A3?alpha_on(&g,A3):0;
      char s[64]; g6enc(&g,s);
      if(g2==w+1 && al==maxal) printf("  TIGHTMAX n=%d %s gamma2=%d WP=%d alphaA3=%d\n",n,s,g2,w,al);
      if(A3 && g2>wo+3/al) printf("  VIOLOTHER n=%d %s gamma2=%d WPother=%d alphaA3=%d rhs=%d\n",n,s,g2,wo,al,wo+3/al);
    }
    fflush(stdout);
  }
}

/* F_q per Definition 2: x1..x3 = 0..2, l1..l3 = 3..5, k1..kq = 6..5+q, w = 6+q, y1,y2 = 7+q, 8+q */
static void addE(G *g,int u,int v){ g->a[u]|=1u<<v; g->a[v]|=1u<<u; }
static void buildF(int q, G *g){
  memset(g,0,sizeof *g); g->n=q+9;
  int X=0,L=3,K=6,W=6+q,Y=7+q;
  for(int i=0;i<3;i++) addE(g,X+i,L+i);
  for(int i=0;i<q;i++) for(int j=i+1;j<q;j++) addE(g,K+i,K+j);
  for(int i=0;i<3;i++) for(int j=0;j<q;j++) addE(g,X+i,K+j);
  for(int j=0;j<q;j++) addE(g,W,K+j);
  for(int a=0;a<2;a++) for(int i=0;i<3;i++) addE(g,Y+a,X+i);
}
static void delvertex(const G *g, int v, G *h){
  h->n=g->n-1; memset(h->a,0,sizeof h->a); int map[MAXN],k=0;
  for(int u=0;u<g->n;u++) map[u]= (u==v)?-1:k++;
  for(int u=0;u<g->n;u++) if(u!=v) for(int w=0;w<g->n;w++) if(w!=v && (g->a[u]>>w&1)) h->a[map[u]]|=1u<<map[w];
}

int main(int argc, char **argv){
  if(argc<2){ fprintf(stderr,"usage\n"); return 1; }
  if(!strcmp(argv[1],"enum")){ enumerate(atoi(argv[2])); return 0; }
  if(!strcmp(argv[1],"g6")){ for(int i=2;i<argc;i++){ G g; if(g6dec(argv[i],&g)){printf("bad %s\n",argv[i]);continue;} report(argv[i],&g);} return 0; }
  if(!strcmp(argv[1],"match")){ /* each line of file A must be iso to exactly one line of file B, and vice versa */
    static G A[2000],B[2000]; int na=0,nb=0; char buf[256]; FILE *f=fopen(argv[2],"r");
    while(fscanf(f,"%255s",buf)==1) g6dec(buf,&A[na++]); fclose(f); f=fopen(argv[3],"r");
    while(fscanf(f,"%255s",buf)==1) g6dec(buf,&B[nb++]); fclose(f);
    int okA=0, okB=0;
    for(int i=0;i<na;i++){ int c=0; for(int j=0;j<nb;j++) c+=isomorphic(&A[i],&B[j]); okA+=(c==1); }
    for(int j=0;j<nb;j++){ int c=0; for(int i=0;i<na;i++) c+=isomorphic(&A[i],&B[j]); okB+=(c==1); }
    printf("match: |A|=%d |B|=%d A-lines with exactly one iso partner=%d B-lines=%d\n",na,nb,okA,okB); return 0; }
  if(!strcmp(argv[1],"edges")){ G g; g6dec(argv[2],&g); for(int i=0;i<g.n;i++) for(int j=i+1;j<g.n;j++) if(g.a[i]>>j&1) printf("%d-%d\n",i,j);
    fprintf(stderr,"degrees:"); for(int i=0;i<g.n;i++) fprintf(stderr," %d",pc(g.a[i])); fprintf(stderr,"\n"); return 0; }
  if(!strcmp(argv[1],"set")){ /* ./vc set G6 "v v v": is it 2-dominating? independent? all in A3? */
    G g; g6dec(argv[2],&g); uint32_t D=0; char *t=strtok(argv[3]," ,"); while(t){ D|=1u<<atoi(t); t=strtok(0," ,"); }
    uint32_t full=(1u<<g.n)-1, A3=degset(&g,3,1000); int ind=1; for(int v=0;v<g.n;v++) if(D>>v&1) if(g.a[v]&D) ind=0;
    printf("set 0x%x: 2dom=%d independent=%d subsetA3=%d\n",D,is2dom(&g,D,full),ind,(D&~A3)==0); return 0; }
  if(!strcmp(argv[1],"sets4with")){ /* number of 2-dominating sets of size K containing vertex V */
    G g; g6dec(argv[2],&g); int K=atoi(argv[3]), V=atoi(argv[4]); uint32_t full=(1u<<g.n)-1; int c=0, tot=0;
    for(uint32_t D=0;D<=full;D++){ if(pc(D)==K && (D>>V&1)){ tot++; c+=is2dom(&g,D,full);} if(D==full) break; }
    printf("size-%d sets containing %d: %d, 2-dominating: %d\n",K,V,tot,c); return 0; }
  if(!strcmp(argv[1],"iso")){ G a,b; g6dec(argv[2],&a); g6dec(argv[3],&b); printf("iso(%s,%s)=%d\n",argv[2],argv[3],isomorphic(&a,&b)); return 0; }
  if(!strcmp(argv[1],"isoF3")){ G f; buildF(3,&f); for(int i=2;i<argc;i++){ G b; g6dec(argv[i],&b); printf("iso(F3,%s)=%d\n",argv[i],isomorphic(&f,&b)); } return 0; }
  if(!strcmp(argv[1],"f3del")){
    G f; buildF(3,&f); report("F3",&f);
    const char *nm[12]={"x1","x2","x3","l1","l2","l3","k1","k2","k3","w","y1","y2"};
    int conn=0,vc=0,vo=0,tot=0;
    for(int v=0;v<12;v++){ G h; delvertex(&f,v,&h); char lab[64]; sprintf(lab,"F3-%s",nm[v]); tot++;
      if(connected(&h)){ conn++; uint32_t A3=degset(&h,3,1000); int g2=gamma2(&h,0),w=wp(&h),wo=wpo(&h),al=A3?alpha_on(&h,A3):0;
        if(A3&&g2>w+3/al) vc++; if(A3&&g2>wo+3/al) vo++; }
      report(lab,&h); }
    for(int u=0;u<12;u++) for(int v=u+1;v<12;v++) if(f.a[u]>>v&1){ G h=f; h.a[u]&=~(1u<<v); h.a[v]&=~(1u<<u);
      char lab[64]; sprintf(lab,"F3-%s%s",nm[u],nm[v]); tot++;
      if(connected(&h)){ conn++; uint32_t A3=degset(&h,3,1000); int g2=gamma2(&h,0),w=wp(&h),wo=wpo(&h),al=A3?alpha_on(&h,A3):0;
        if(A3&&g2>w+3/al) vc++; if(A3&&g2>wo+3/al) vo++; }
      report(lab,&h); }
    printf("SUMMARY total=%d connected=%d viol_cat=%d viol_other=%d\n",tot,conn,vc,vo);
    return 0;
  }
  if(!strcmp(argv[1],"fq")){
    int q=atoi(argv[2]); G f; buildF(q,&f); char lab[32]; sprintf(lab,"F%d",q); report(lab,&f);
    uint32_t A3=degset(&f,3,1000), Ale3=degset(&f,0,3);
    int w=wp(&f), g2=gamma2(&f,0), gx=gamma2(&f,1);
    int al=alpha_on(&f,A3), alle=Ale3?alpha_on(&f,Ale3):0;
    printf("F%d (a) |deg<=3|=%d alpha(G[deg<=3])=%d rhs=%d gamma2=%d violates=%d\n",q,pc(Ale3),alle,alle?w+3/alle:-1,g2,alle?g2>w+3/alle:-1);
    printf("F%d (b) exact-2-dom number=%d rhs=%d violates=%d\n",q,gx,w+3/al,gx>w+3/al);
    /* list one minimum exact set */
    uint32_t full=(1u<<f.n)-1; for(uint32_t D=0;;D++){ if(pc(D)==gx && isexact2(&f,D)){ printf("F%d (b) one minimum exact set mask=0x%x:",q,D); for(int v=0;v<f.n;v++) if(D>>v&1) printf(" %d",v); printf("\n"); break;} if(D==full) break; }
    return 0;
  }
  return 1;
}

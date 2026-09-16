/* s6: s5's depth-1 restricted closure + depth-2 residual certificates.
   Adds: for every residual (uncovered) contract-trace ORBIT representative,
   search a depth-2 certificate; emit to $EMIT2; self-verify from emitted text;
   emit an extra "res" plane in $EMIT. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int n,m,N; static int pw3[20];
static int perm6[6][4]={{0,1,2,3},{0,1,3,2},{0,2,1,3},{0,2,3,1},{0,3,1,2},{0,3,2,1}};
static int *permidx[6];
static unsigned char *K,*Kh,*good,*ctr,*proper,*newc,*resrep; static int *rnk,*rmin; static signed char *choice;
static int parse(char*p,int*out){int k=0;while(*p){while(*p==' '||*p=='\n')p++;if(*p<'1'||*p>'3')break;int idx=0,len=0;while(*p>='1'&&*p<='3'){int d=*p-'0';if(len<m)idx+=(d-1)*pw3[len];len++;p++;}out[k++]=idx;}return k;}

/* ---- growable text buffer for the certificate file ---- */
static char *ob; static size_t obn,obc;
static void oput(const char*s){size_t l=strlen(s); if(obn+l+1>obc){ while(obn+l+1>obc) obc=obc?obc*2:(1u<<20); ob=realloc(ob,obc);} memcpy(ob+obn,s,l); obn+=l; ob[obn]=0;}
static void opf(const char*f,...);
#include <stdarg.h>
static void opf(const char*f,...){char t[512];va_list ap;va_start(ap,f);vsnprintf(t,sizeof t,f,ap);va_end(ap);oput(t);}

/* ---- per-trace decode ---- */
static int strictmode=0;
/* build the admissible q' index list for p'=s[i] on a side of length L */
static int qlist(int i,int L,int*out){int c=0; if(strictmode){ for(int j=0;j<L;j++) if(j!=i && ((j-i)&1)) out[c++]=j; } else { for(int j=i+1;j<L;j+=2) out[c++]=j; } return c;}
static void decode(int idx,int*d){int t=idx,x=0;for(int p=0;p<m;p++){d[p]=t%3+1;t/=3;x^=d[p];}d[m]=x;}

typedef struct { int q; int isP; int c; int pp; int nq2; int qs[24]; int ms[24]; } Ent;

int main(void){
  static char*buf; size_t bs=1u<<27; buf=malloc(bs);
  if(scanf("ring %d\n",&n)!=1)return 1; m=n-1; pw3[0]=1;for(int i=1;i<20;i++)pw3[i]=pw3[i-1]*3; N=pw3[m];
  K=calloc(N,1);Kh=calloc(N,1);good=calloc(N,1);ctr=calloc(N,1);proper=calloc(N,1);newc=calloc(N,1);resrep=calloc(N,1);
  rnk=malloc(N*sizeof(int));rmin=malloc(N*sizeof(int));choice=malloc(N);
  for(int g=0;g<6;g++)permidx[g]=malloc(N*sizeof(int));
  for(int idx=0;idx<N;idx++){int t=idx,d[20],x=0;for(int p=0;p<m;p++){d[p]=t%3+1;t/=3;x^=d[p];}proper[idx]=(x!=0);
    for(int g=0;g<6;g++){int j=0;for(int p=0;p<m;p++)j+=(perm6[g][d[p]]-1)*pw3[p];permidx[g][idx]=j;}}
  int*tmp=malloc(sizeof(int)*8000000);
  if(!fgets(buf,bs,stdin)||strncmp(buf,"GOOD ",5))return 1; int ng=parse(buf+5,tmp);
  for(int i=0;i<ng;i++)for(int g=0;g<6;g++)good[permidx[g][tmp[i]]]=1;
  if(!fgets(buf,bs,stdin)||strncmp(buf,"CTR ",4))return 1; int nc=parse(buf+4,tmp);
  for(int i=0;i<nc;i++)for(int g=0;g<6;g++)ctr[permidx[g][tmp[i]]]=1;
  int nprop=0,ngood=0,nctr=0;
  for(int i=0;i<N;i++){Kh[i]=good[i]; K[i]=0; rnk[i]=good[i]?0:127; choice[i]=-1; nprop+=proper[i]; ngood+=good[i]; nctr+=ctr[i]&&proper[i];}
  int round;
  for(round=1;round<=126;round++){
    int added=0;
    for(int idx=0;idx<N;idx++){
      if(!proper[idx]||Kh[idx]) continue;
      int d[20]; decode(idx,d);
      int nz[20],k=0; for(int p=0;p<n;p++) if(d[p]!=1) nz[k++]=p;
      int found=-1;
      for(int a=0;a<k&&found<0;a++){ int p=nz[a]; int ok=1;
        for(int b=1;b<k&&ok;b+=2){ int q=nz[(a+b)%k]; int ic=0,ia=0;
          if(p<m) ic += (d[p]==2? pw3[p] : -pw3[p]); if(q<m) ic += (d[q]==2? pw3[q] : -pw3[q]);
          for(int j=1;j<b;j++){ int r=nz[(a+j)%k]; if(r<m) ia += (d[r]==2? pw3[r] : -pw3[r]); }
          if(!(Kh[idx+ic]||Kh[idx+ia]||Kh[idx+ic+ia])) ok=0; }
        if(ok) found=p; }
      if(found>=0){ newc[idx]=1; choice[idx]=found; added++; }
    }
    if(!added){ round--; break; }
    for(int idx=0;idx<N;idx++) if(newc[idx]){ newc[idx]=0; K[idx]=1; rnk[idx]=round; for(int g=0;g<6;g++) Kh[permidx[g][idx]]=1; }
  }
  for(int i=0;i<N;i++){ int b=127; for(int g=0;g<6;g++){ int r=rnk[permidx[g][i]]; if(r<b)b=r; } rmin[i]=b; }
  int bad=0,maxr=0,nK=0,nKh=0; for(int i=0;i<N;i++){ if(proper[i]&&K[i]) nK++; if(proper[i]&&Kh[i]) nKh++; if(ctr[i]&&proper[i]&&!Kh[i]) bad++; if(ctr[i]&&proper[i]&&rmin[i]<127&&rmin[i]>maxr) maxr=rmin[i]; }
  printf("ring %d proper %d good %d ctr %d direct %d closure %d rounds %d ctr-maxrank %d uncovered %d %s\n",n,nprop,ngood,nctr,nK,nKh,round,maxr,bad,bad?"FAIL":"PASS");
  { int nc2=0; for(int idx=0;idx<N;idx++){ if(!K[idx]) continue; int p=choice[idx];
      int d[20]; decode(idx,d); int nz[20],k=0,a=-1; for(int q=0;q<n;q++) if(d[q]!=1){ if(q==p)a=k; nz[k++]=q; }
      int ok=1; for(int b=1;b<k&&ok;b+=2){ int q=nz[(a+b)%k]; int ic=0,ia=0; if(p<m) ic+=(d[p]==2?pw3[p]:-pw3[p]); if(q<m) ic+=(d[q]==2?pw3[q]:-pw3[q]);
        for(int j=1;j<b;j++){ int r=nz[(a+j)%k]; if(r<m) ia+=(d[r]==2?pw3[r]:-pw3[r]); }
        if(!(rmin[idx+ic]<rnk[idx]||rmin[idx+ia]<rnk[idx]||rmin[idx+ic+ia]<rnk[idx])) ok=0; }
      if(!ok) nc2++; }
    printf("  choice-verify failures %d\n", nc2); }

  /* ================= depth-2 residual certificates ================= */
  int nres=0, nwarn=0, nvac=0;
  for(int mode=0;mode<2;mode++){
  strictmode = mode; obn=0; if(ob) ob[0]=0;
  nres=0; nwarn=0; nvac=0;
  Ent ent[24];
  for(int idx=0;idx<N;idx++){
    if(!(proper[idx]&&ctr[idx]&&!Kh[idx])) continue;
    int rep=idx; for(int g=0;g<6;g++){ int j=permidx[g][idx]; if(proper[j]&&ctr[j]&&j<rep) rep=j; }
    if(rep!=idx) continue;                 /* only orbit representatives */
    resrep[idx]=1; nres++;
    int d[20]; decode(idx,d);
    int dl[20]; for(int p=0;p<n;p++) dl[p]= (p<m)? (d[p]==2? pw3[p] : -pw3[p]) : 0;
    int nz[20],k=0; for(int p=0;p<n;p++) if(d[p]!=1) nz[k++]=p;
    int gotp=-1,ne=0,vac=0;
    for(int a=0;a<k&&gotp<0;a++){
      int p=nz[a]; int ok=1; ne=0; vac=0;
      for(int b=1;b<k&&ok;b+=2){
        int q=nz[(a+b)%k];
        int ic=dl[p]+dl[q], ia=0;
        for(int j=1;j<b;j++) ia+=dl[nz[(a+j)%k]];
        Ent*e=&ent[ne];
        e->q=q; e->isP=0;
        if(Kh[idx+ic]) { e->c=0; ne++; continue; }
        if(Kh[idx+ia]) { e->c=1; ne++; continue; }
        if(Kh[idx+ic+ia]){ e->c=2; ne++; continue; }
        /* depth 2 */
        int ins[20],Li=0,out[20],Lo=0;
        for(int j=1;j<b;j++) ins[Li++]=nz[(a+j)%k];
        for(int j=b+1;j<k;j++) out[Lo++]=nz[(a+j)%k];
        int dins=0,dout=0; for(int t=0;t<Li;t++) dins+=dl[ins[t]]; for(int t=0;t<Lo;t++) dout+=dl[out[t]];
        int foundp=0;
        for(int side=0; side<2 && !foundp; side++){
          int *s = side? out: ins; int L = side? Lo: Li;
          int dside = side? dout: dins, dother = side? dins: dout;
          for(int i=0;i<L && !foundp;i++){
            int pp=s[i];
            /* admissible q' : s[j], j>i, j-i odd */
            int allok=1,cnt=0; int qs[24],ms[24]; int jl[24]; int nj=qlist(i,L,jl);
            for(int z=0;z<nj;z++){ int j=jl[z];
              int qq=s[j];
              int lo=i<j?i:j, hi=i<j?j:i;
              int g0=ic, g1=dl[pp]+dl[qq], g2=0;
              for(int t=lo+1;t<hi;t++) g2+=dl[s[t]];
              int g3=dside-g1-g2, g4=dother;
              int gd[5]={g0,g1,g2,g3,g4};
              int mk=0;
              for(int msk=1;msk<32;msk++){ int dd=0; for(int t=0;t<5;t++) if(msk&(1<<t)) dd+=gd[t];
                if(Kh[idx+dd]){ mk=msk; break; } }
              if(!mk){ allok=0; break; }
              qs[cnt]=qq; ms[cnt]=mk; cnt++;
            }
            if(allok){ foundp=1; e->isP=1; e->pp=pp; e->nq2=cnt;
              for(int t=0;t<cnt;t++){ e->qs[t]=qs[t]; e->ms[t]=ms[t]; }
              if(cnt==0) vac++; }
          }
        }
        if(!foundp){ ok=0; break; }
        ne++;
      }
      if(ok) gotp=p;
    }
    if(gotp<0){ if(!mode) fprintf(stderr,"WARN no depth-2 certificate for residual %d\n",idx); nwarn++; continue; }
    nvac+=vac;
    opf("RES %d %d %d\n",idx,gotp,ne);
    for(int t=0;t<ne;t++){ Ent*e=&ent[t];
      if(!e->isP) opf("Q %d D %d\n",e->q,e->c);
      else { opf("Q %d P %d %d",e->q,e->pp,e->nq2);
        for(int u=0;u<e->nq2;u++) opf(" %d:%d",e->qs[u],e->ms[u]);
        oput("\n"); } }
  }
  { const char*ev = mode? "EMIT2S" : "EMIT2"; const char*fn=getenv(ev);
    if(fn){ FILE*f=fopen(fn,"w"); if(f){ if(obn) fwrite(ob,1,obn,f); fclose(f);} } }

  /* ================= self-check: verify purely from emitted text ================= */
  { long long tot=0; int maxt=0,ncert=0,vfail=0;
    char*cur=ob; 
    while(cur&&*cur){
      int idx,p,nq; int used;
      if(sscanf(cur,"RES %d %d %d%n",&idx,&p,&nq,&used)!=3){ vfail++; break; }
      cur+=used; while(*cur=='\n')cur++;
      int tests=0;
      int d[20]; decode(idx,d);
      int dl[20]; for(int z=0;z<n;z++) dl[z]=(z<m)?(d[z]==2?pw3[z]:-pw3[z]):0;
      int nz[20],k=0,a=-1; for(int z=0;z<n;z++) if(d[z]!=1){ if(z==p)a=k; nz[k++]=z; }
      if(a<0){ vfail++; }
      int nb=0; for(int b=1;b<k;b+=2) nb++;
      if(nb!=nq){ vfail++; }
      int bi=1;
      for(int t=0;t<nq;t++,bi+=2){
        int q; if(sscanf(cur,"Q %d%n",&q,&used)!=1){ vfail++; break; } cur+=used;
        if(a<0||bi>=k||q!=nz[(a+bi)%k]){ vfail++; }
        int ic=dl[p]+dl[q],ia=0; for(int j=1;j<bi;j++) ia+=dl[nz[(a+j)%k]];
        while(*cur==' ')cur++;
        if(*cur=='D'){ int c; if(sscanf(cur,"D %d%n",&c,&used)!=1){vfail++;break;} cur+=used;
          int dd = c==0?ic : c==1?ia : ic+ia;
          tests++; if(!Kh[idx+dd]) vfail++;
        } else if(*cur=='P'){ int pp,nq2; if(sscanf(cur,"P %d %d%n",&pp,&nq2,&used)!=2){vfail++;break;} cur+=used;
          int ins[20],Li=0,out[20],Lo=0;
          for(int j=1;j<bi;j++) ins[Li++]=nz[(a+j)%k];
          for(int j=bi+1;j<k;j++) out[Lo++]=nz[(a+j)%k];
          int dins=0,dout=0; for(int z=0;z<Li;z++)dins+=dl[ins[z]]; for(int z=0;z<Lo;z++)dout+=dl[out[z]];
          int *s=0,L=0,dside=0,dother=0,ii=-1;
          for(int z=0;z<Li;z++) if(ins[z]==pp){s=ins;L=Li;dside=dins;dother=dout;ii=z;}
          if(ii<0) for(int z=0;z<Lo;z++) if(out[z]==pp){s=out;L=Lo;dside=dout;dother=dins;ii=z;}
          if(ii<0){ vfail++; }
          int jl[24]; int expect=0; if(ii>=0) expect=qlist(ii,L,jl);
          if(expect!=nq2){ vfail++; }
          for(int u=0;u<nq2;u++){
            int qq,msk; if(sscanf(cur," %d:%d%n",&qq,&msk,&used)!=2){vfail++;break;} cur+=used;
            if(ii<0||u>=expect){ vfail++; continue; }
            int jj=jl[u];
            if(jj>=L||qq!=s[jj]){ vfail++; continue; }
            if(msk<1||msk>31){ vfail++; continue; }
            int lo=ii<jj?ii:jj, hi=ii<jj?jj:ii;
            int g0=ic,g1=dl[pp]+dl[qq],g2=0; for(int z=lo+1;z<hi;z++) g2+=dl[s[z]];
            int g3=dside-g1-g2,g4=dother; int gd[5]={g0,g1,g2,g3,g4};
            int dd=0; for(int z=0;z<5;z++) if(msk&(1<<z)) dd+=gd[z];
            tests++; if(!Kh[idx+dd]) vfail++;
          }
        } else { vfail++; break; }
        while(*cur=='\n'||*cur==' ')cur++;
      }
      ncert++; tot+=tests; if(tests>maxt) maxt=tests;
    }
    printf("  [%s] certificates %d verify-failures %d tests %lld maxtests %d vacuous-P %d\n",mode?"strict":"spec ",ncert,vfail,tot,maxt,nvac);
    printf("%s ring=%d rounds=%d direct=%d closure=%d ctrmaxrank=%d residual_orbits=%d tests=%lld maxtests=%d warn=%d vacuous=%d vfail=%d strict=%d\n",
           mode?"S6S":"S6",n,round,nK,nKh,maxr,nres,tot,maxt,nwarn,nvac,vfail,strictmode);
  }
  }

  if(getenv("EMIT")){
    FILE*f=fopen(getenv("EMIT"),"w"); int CH=1<<14; int nch=(N+CH-1)/CH; unsigned char *bits=malloc(N); char nm[32];
    #define DUMP(NAME) { fprintf(f,"%s %d\n",NAME,nch); for(int c=0;c<nch;c++){ char*h=malloc(CH/4+2); int hl=0; \
        for(int b=CH-4;b>=0;b-=4){ int v=0; for(int j=0;j<4;j++){ int i=c*CH+b+j; if(i<N&&bits[i]) v|=1<<j; } h[hl++]="0123456789abcdef"[v]; } \
        h[hl]=0; int s=0; while(s<hl-1&&h[s]=='0')s++; fprintf(f,"0x%s\n",h+s); free(h);} }
    for(int b=0;b<7;b++){ for(int i=0;i<N;i++){ int r=(proper[i]&&K[i])?rnk[i]:127; bits[i]=(r>>b)&1; } sprintf(nm,"rank%d",b); DUMP(nm); }
    for(int b=0;b<7;b++){ for(int i=0;i<N;i++){ int r=proper[i]?rmin[i]:127; bits[i]=(r>>b)&1; } sprintf(nm,"rmin%d",b); DUMP(nm); }
    for(int b=0;b<4;b++){ for(int i=0;i<N;i++){ int c=K[i]?choice[i]:0; bits[i]=(c>>b)&1; } sprintf(nm,"choice%d",b); DUMP(nm); }
    for(int i=0;i<N;i++) bits[i]=proper[i]&&good[i]; DUMP("good");
    for(int i=0;i<N;i++) bits[i]=proper[i]&&ctr[i]; DUMP("ctr");
    for(int i=0;i<N;i++) bits[i]=resrep[i]; DUMP("res");
    fclose(f); }
  return 0; }

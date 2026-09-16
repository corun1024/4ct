/* Validated Kempe-closure engine + certificate extraction.
   Iteration reproduces Lean's kempeTreeIter exactly (checked). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int n,m,N; static int pw3[20];
static unsigned char *good,*ctu,*banned,*proper,*ctrset,*dead_now,*stored; static unsigned char *Kh1;
static int *rnk, *orbrank;
static int perm6[6][4]={{0,1,2,3},{0,1,3,2},{0,2,1,3},{0,2,3,1},{0,3,1,2},{0,3,2,1}};
static int *permidx[6];
static int dig[20],chord[20],nch,stk[20],sp;
static int fdelta[10]; static const unsigned char *BAN; static int base_idx;
static long long ops, certops, certmatch;
static int no_flip_banned(int np){int tot=1<<np;for(int mk=0;mk<tot;mk++){int idx=base_idx;for(int i=0;i<np;i++)if(mk&(1<<i))idx+=fdelta[i];ops++;if(BAN[idx])return 0;}return 1;}
static int rec(int i,int np){ if(i==nch) return no_flip_banned(np); int rem=nch-i;
  if(sp+1<=rem-1){stk[sp++]=i; if(rec(i+1,np)){sp--;return 1;} sp--;}
  if(sp>0){int o=stk[sp-1]; sp--; int a=chord[o],b=chord[i];int d=0;
    if(a<m)d+=(dig[a]==2?pw3[a]:-pw3[a]); if(b<m)d+=(dig[b]==2?pw3[b]:-pw3[b]);
    fdelta[np]=d; if(rec(i+1,np+1)){sp++;stk[sp-1]=o;return 1;} sp++; stk[sp-1]=o;}
  return 0;}
static void decode(int idx){int t=idx,x=0;for(int p=0;p<m;p++){dig[p]=t%3+1;t/=3;x^=dig[p];}dig[m]=x;nch=0;for(int p=0;p<n;p++)if(dig[p]!=1)chord[nch++]=p;}
static int hasw(int idx){decode(idx); if(dig[m]==0) return 0; if(nch&1) return 0; base_idx=idx; sp=0; return rec(0,0);}

/* ---- certificate: enumerate every matching, pick best witness ---- */
static int *need_q; static int need_n; static unsigned char *inV;
static int cur_rank; static int best_wit; static int best_score;
static int *witbuf; static int nwit; static int recording; static unsigned char *PREFER;
static long long nmatch_here;
static int wit_np; static int wit_d[10];
static int score_of(int idx){ /* lower is better */
  if (Kh1[idx]) return 0;                  /* bulk-certified or good: free */
  if (orbrank[idx] >= cur_rank || orbrank[idx] < 0) return 1000000;
  if (PREFER && PREFER[idx]) return 1;
  if (inV[idx]) return 2;                  /* already in certificate */
  return 3 + orbrank[idx];
}
static int scan_flips(int np){
  int tot=1<<np,bs=1000000,bi=-1;
  for(int mk=0;mk<tot;mk++){int idx=base_idx;for(int i=0;i<np;i++)if(mk&(1<<i))idx+=fdelta[i];
    int s=score_of(idx); certops++; if(s<bs){bs=s;bi=idx; if(s==0) break;}}
  nmatch_here++;
  if(bi<0||bs>=1000000) return 0;
  if(bs>0){ /* need to add witness to V */
    if(!inV[bi]&&!Kh1[bi]){ inV[bi]=1; need_q[need_n++]=bi; }
  }
  if(recording){ int dup=0; for(int i=0;i<nwit;i++) if(witbuf[i]==bi) {dup=1;break;}
                 if(!dup) witbuf[nwit++]=bi; }
  return 1;
}
static int rec2(int i,int np){ int ok=1;
  if(i==nch){ return scan_flips(np); }
  int rem=nch-i;
  if(sp+1<=rem-1){stk[sp++]=i; if(!rec2(i+1,np)) ok=0; sp--;}
  if(sp>0){int o=stk[sp-1]; sp--; int a=chord[o],b=chord[i];int d=0;
    if(a<m)d+=(dig[a]==2?pw3[a]:-pw3[a]); if(b<m)d+=(dig[b]==2?pw3[b]:-pw3[b]);
    fdelta[np]=d; if(!rec2(i+1,np+1)) ok=0; sp++; stk[sp-1]=o;}
  return ok;}
static int parse(char*p,int*out,int*cnt){int k=0;while(*p){while(*p==' ')p++;if(*p<'1'||*p>'3')break;int idx=0,len=0;while(*p>='1'&&*p<='3'){int d=*p-'0';if(len<m)idx+=(d-1)*pw3[len];len++;p++;}out[k++]=idx;}*cnt=k;return 0;}
int main(void){static char*buf;size_t bs=1u<<26;buf=malloc(bs);
  if(scanf("ring %d\n",&n)!=1)return 1; m=n-1; pw3[0]=1;for(int i=1;i<20;i++)pw3[i]=pw3[i-1]*3; N=pw3[m];
  good=calloc(N,1);stored=calloc(N,1);ctu=calloc(N,1);banned=calloc(N,1);proper=calloc(N,1);ctrset=calloc(N,1);dead_now=calloc(N,1);
  rnk=malloc(N*sizeof(int)); orbrank=malloc(N*sizeof(int)); inV=calloc(N,1); need_q=malloc(N*sizeof(int));
  for(int g=0;g<6;g++)permidx[g]=malloc(N*sizeof(int));
  for(int idx=0;idx<N;idx++){int t=idx,d[20],x=0;for(int p=0;p<m;p++){d[p]=t%3+1;t/=3;x^=d[p];}proper[idx]=(x!=0);
    for(int g=0;g<6;g++){int j=0;for(int p=0;p<m;p++)j+=(perm6[g][d[p]]-1)*pw3[p];permidx[g][idx]=j;}}
  int*tmp=malloc(sizeof(int)*8000000);int ng,nc;
  if(!fgets(buf,bs,stdin)||strncmp(buf,"GOOD ",5))return 1; parse(buf+5,tmp,&ng);
  for(int i=0;i<ng;i++){stored[tmp[i]]=1;for(int g=0;g<6;g++)good[permidx[g][tmp[i]]]=1;}
  if(!fgets(buf,bs,stdin)||strncmp(buf,"CTR ",4))return 1; parse(buf+4,tmp,&nc);
  for(int i=0;i<nc;i++)for(int g=0;g<6;g++)ctrset[permidx[g][tmp[i]]]=1;
  for(int i=0;i<N;i++){ctu[i]=proper[i]; banned[i]=good[i]; rnk[i]= good[i]?0:-1;}
  int nprop=0,ngood=0,nctr=0; for(int i=0;i<N;i++){nprop+=proper[i];ngood+=good[i];nctr+=ctrset[i];}
  int cyc=0; long long totops=0;
/* CYCLE CAP -- raised from 60 to 400 on 2026-09-13.
   The Kempe closure loop below is the fixpoint that decides whether a
   configuration's contract traces can be killed.  It was capped at 60 cycles,
   which no configuration of ring <= 13 ever approached.  Two ring-14
   configurations need more: 561 settles at 86 cycles and 612 at 132.  With the
   old cap the loop exited before the fixpoint was reached and the engine
   printed NOT-RED -- that is, it reported two configurations as not
   C-reducible when both are.  A loop bound in a C helper masquerading as a
   fact about the mathematics.  If a configuration ever reports NOT-RED, check
   the cycle count against this cap BEFORE believing it. */
  for(int r=1;r<=400;r++){
    BAN=banned; int died=0; long long o0=ops;
    for(int i=0;i<N;i++) dead_now[i]=0;
    for(int i=0;i<N;i++) if(ctu[i] && !hasw(i)) { dead_now[i]=1; died++; }
    for(int i=0;i<N;i++) if(dead_now[i]) { ctu[i]=0; if(rnk[i]<0) rnk[i]=r; for(int g=0;g<6;g++) banned[permidx[g][i]]=1; }
    totops += ops-o0; cyc=r;
    if(!died) break;
  }
  int nlive=0; for(int i=0;i<N;i++) nlive+=ctu[i];
  int badctr=0; for(int i=0;i<N;i++) if(ctrset[i]&&ctu[i]) badctr++;
  for(int i=0;i<N;i++){int b=1000000; for(int g=0;g<6;g++){int rr=rnk[permidx[g][i]]; if(rr>=0&&rr<b)b=rr;} orbrank[i]= (b==1000000)?-1:b;}
  int maxr=0; for(int i=0;i<N;i++) if(rnk[i]>maxr)maxr=rnk[i];
  int maxcr=0; for(int i=0;i<N;i++) if(ctrset[i]&&orbrank[i]>maxcr)maxcr=orbrank[i];
  printf("ring %d proper %d good %d contract %d live %d cycles %d maxrank %d  contract-maxorbrank %d  %s  fullops %lld\n",
         n,nprop,ngood,nctr,nlive,cyc,maxr,maxcr,badctr?"NOT-RED":"RED",totops);
  if(badctr){printf("  (contract still live: no certificate)\n"); return 0;}

  /* ---- depth-1 restricted closure (bulk rule): Kh1 = perm-closure of directly certified ∪ good ---- */
  Kh1=calloc(N,1); { static unsigned char *newc1; newc1=calloc(N,1);
    for(int i=0;i<N;i++) Kh1[i]=good[i];
    for(int r=1;r<=126;r++){ int added=0;
      for(int idx=0;idx<N;idx++){ if(!proper[idx]||Kh1[idx]) continue;
        int t=idx,dd[20],x=0; for(int p=0;p<m;p++){dd[p]=t%3+1;t/=3;x^=dd[p];} dd[m]=x;
        int nz[20],k=0; for(int p=0;p<n;p++) if(dd[p]!=1) nz[k++]=p;
        int found=0;
        for(int a=0;a<k&&!found;a++){ int p=nz[a]; int ok=1;
          for(int b=1;b<k&&ok;b+=2){ int q=nz[(a+b)%k]; int ic=0,ia=0;
            if(p<m) ic += (dd[p]==2? pw3[p] : -pw3[p]); if(q<m) ic += (dd[q]==2? pw3[q] : -pw3[q]);
            for(int j=1;j<b;j++){ int rr=nz[(a+j)%k]; if(rr<m) ia += (dd[rr]==2? pw3[rr] : -pw3[rr]); }
            if(!(Kh1[idx+ic]||Kh1[idx+ia]||Kh1[idx+ic+ia])) ok=0; }
          if(ok) found=1; }
        if(found){ newc1[idx]=1; added++; } }
      if(!added) break;
      for(int idx=0;idx<N;idx++) if(newc1[idx]){ newc1[idx]=0; for(int g=0;g<6;g++) Kh1[permidx[g][idx]]=1; } } }
  { int nk=0, unc=0; for(int i=0;i<N;i++){ nk+=Kh1[i]&&proper[i]; unc += ctrset[i]&&proper[i]&&!Kh1[i]; }
    printf("  DEPTH1 closure %d uncovered-ctr %d\n", nk, unc); }
  /* certificate: BFS from contract traces, iterated to shrink the auxiliary set */
  {
  static unsigned char *prefer; prefer = calloc(N,1);
  int bestn = 1<<30; long long bestmat=0, bestops=0; int bestaux=0, ncontract_need=0;
  for (int pass = 0; pass < 4; pass++) {
    memset(inV, 0, N);
    need_n = 0;
    for(int i=0;i<N;i++) if(ctrset[i] && proper[i] && !Kh1[i]){ inV[i]=1; need_q[need_n++]=i; }
    ncontract_need = need_n;
    certops=0; long long nmat=0;
    for(int qi=0; qi<need_n; qi++){
      int t = need_q[qi];
      int best=t, br=rnk[t]<0?1000000:rnk[t];
      for(int g=0;g<6;g++){int u=permidx[g][t]; int rr=rnk[u]<0?1000000:rnk[u]; if(rr<br){br=rr;best=u;}}
      cur_rank = br;
      decode(best); base_idx=best; sp=0; nmatch_here=0;
      PREFER = prefer;
      if(!rec2(0,0)) printf("  WARN: no witness for %d (rank %d)\n",best,br);
      nmat += nmatch_here;
    }
    if (need_n < bestn) { bestn=need_n; bestmat=nmat; bestops=certops; bestaux=need_n-ncontract_need; }
    memcpy(prefer, inV, N);
  }
  printf("  CERT traces %d (contract %d, auxiliary %d) matchings %lld scan-tests %lld\n",
         bestn, bestn-bestaux, bestaux, bestmat, bestops);
  certops = bestmat;  /* a verifier told the witness does one test per matching */
  }
  printf("  RATIO fullops/cert-matchings = %.0f\n", certops? (double)totops/certops : 0.0);

  /* ---- emit the certificate ---- */
  if (getenv("EMIT")) {
    FILE *f = fopen(getenv("EMIT"), "w");
    witbuf = malloc(sizeof(int)*4096);
    /* entry set: best(t) for every queued t, plus a trivial entry for every
       good contract trace (and for every good trace used as a `perm` target). */
    static unsigned char *isEntry; isEntry = calloc(N,1);
    static int *entries; entries = malloc(sizeof(int)*N); int ne = 0;
    memset(inV,0,N); need_n=0;
    for(int i=0;i<N;i++) if(ctrset[i] && proper[i] && !Kh1[i]){ inV[i]=1; need_q[need_n++]=i; }
    PREFER = NULL;
    for(int qi=0; qi<need_n; qi++){
      int t = need_q[qi];
      int best=t, br=rnk[t]<0?1000000:rnk[t];
      for(int g=0;g<6;g++){int u=permidx[g][t]; int rr=rnk[u]<0?1000000:rnk[u]; if(rr<br){br=rr;best=u;}}
      if(!isEntry[best]){ isEntry[best]=1; entries[ne++]=best; }
      cur_rank = br; decode(best); base_idx=best; sp=0; recording=0; nmatch_here=0;
      rec2(0,0);
    }

    fprintf(f, "ring %d entries %d\n", n, ne);
    long long totans=0;
    for(int ei=0; ei<ne; ei++){
      int u = entries[ei];
      int r = rnk[u] < 0 ? 0 : rnk[u];
      decode(u); base_idx=u; sp=0; cur_rank=r; nwit=0; recording=1; nmatch_here=0;
      if (r > 0) { PREFER=NULL; if(!rec2(0,0)) { fprintf(stderr,"entry %d unjustified\n",u); return 3; } }
      else { witbuf[0]=u; nwit=1; }       /* a good trace answers itself */
      recording=0;
      /* print entry: complete trace digits */
      fprintf(f, "E ");
      { int t2=u,x=0,d[20]; for(int p=0;p<m;p++){d[p]=t2%3+1;t2/=3;x^=d[p];}
        for(int p=0;p<m;p++) fputc('0'+d[p], f); fputc('0'+x, f); }
      fprintf(f, " %d %d", r, nwit);
      for(int i=0;i<nwit;i++){
        int wtr = witbuf[i];
        int kind, gg = 0;
        if (Kh1[wtr]) { kind=0; }
        else {
          kind=1; gg=-1;
          for(int g=0;g<6;g++){ int v=permidx[g][wtr]; if(isEntry[v] && rnk[v]>=0 && rnk[v]<r){ gg=g; break; } }
          if(gg<0){ fprintf(stderr,"witness %d has no entry below rank %d\n", wtr, r); return 5; }
        }
        /* the answer stores the FLIP MASK over the leaf's partial trace */
        fprintf(f, " %s ", kind==0 ? "G" : "P");
        { int t2=wtr, du[20], dw[20], t3=u; unsigned mask=0; int xu=0, xw=0;
          for(int p=0;p<m;p++){ dw[p]=t2%3+1; t2/=3; du[p]=t3%3+1; t3/=3;
                                xu^=du[p]; xw^=dw[p];
                                if (du[p]!=dw[p]) mask |= (1u<<p); }
          /* the completion too: the mask must span the COMPLETE trace */
          if (xu != xw) mask |= (1u<<m);
          fprintf(f, "%u", mask); }
        if (kind==1) fprintf(f, " %d", gg);
        totans++;
      }
      fputc('\n', f);
    }
    /* settled-by-chord lists: entry `ei` is settled by chord (q,p) when one of
       its three flips along the chord is known, or permutes to an entry of
       strictly smaller rank — exactly `okBig` of the Lean side. */
    { static int *lst; lst = malloc(sizeof(int)*(ne+1));
      for(int q=0;q<n;q++) for(int p=q+1;p<n;p++){
        int cnt=0;
        for(int ei=0;ei<ne;ei++){ int u=entries[ei]; int r=rnk[u]<0?0:rnk[u];
          int t2=u,x=0,dd[20]; for(int pp=0;pp<m;pp++){dd[pp]=t2%3+1;t2/=3;x^=dd[pp];} dd[m]=x;
          if(dd[q]==1||dd[p]==1) continue;
          int ia=0,cntin=0; for(int rr=q+1;rr<p;rr++) if(dd[rr]!=1){ cntin++; if(rr<m) ia += (dd[rr]==2?pw3[rr]:-pw3[rr]); }
          if(cntin&1) continue;
          int ic=0; if(q<m) ic += (dd[q]==2?pw3[q]:-pw3[q]); if(p<m) ic += (dd[p]==2?pw3[p]:-pw3[p]);
          int cands[3]={u+ic,u+ia,u+ic+ia}; int ok=0;
          for(int c=0;c<3&&!ok;c++){ int v=cands[c]; if(Kh1[v]) {ok=1;break;}
            for(int g=0;g<6;g++){ int vv=permidx[g][v]; if(isEntry[vv] && rnk[vv]>=0 && rnk[vv]<r){ok=1;break;} } }
          if(ok) lst[cnt++]=ei; }
        fprintf(f,"OK %d %d %d",q,p,cnt); for(int i=0;i<cnt;i++) fprintf(f," %d",lst[i]); fputc('\n',f); } }
    fclose(f);
    { static unsigned char *inU; inU=calloc(N,1); int nu=0; for(int ei=0;ei<ne;ei++) if(!inU[entries[ei]]){inU[entries[ei]]=1;nu++;}
      /* count witnesses by re-reading nothing: approximate via file? simpler: count during emission */
      printf("  EMIT entries %d answers %lld (avg %.2f)\n", ne, totans, ne?(double)totans/ne:0.0); }
  }
  return 0;}

#include <bits/stdc++.h>
using namespace std;
using u64=uint64_t; using u128=__uint128_t;
u64 mulmod(u64 a,u64 b,u64 m){return (u128)a*b%m;}
u64 pw(u64 a,u64 b,u64 m){u64 v=1%m;for(;b;b>>=1,a=mulmod(a,a,m))if(b&1)v=mulmod(v,a,m);return v;}
long long dlog(u64 b,u64 h,u64 p,u64 m){
  u64 s=sqrtl(m)+1,v=1; unordered_map<u64,unsigned> baby; baby.reserve(s*2);
  for(u64 j=0;j<s;j++){baby.emplace(v,j);v=mulmod(v,b,p);}
  u64 f=pw(pw(b,s,p),p-2,p);v=h;
  for(u64 i=0;i<=s;i++,v=mulmod(v,f,p)){auto it=baby.find(v);if(it!=baby.end()){u64 r=i*s+it->second;if(r<m&&pw(b,r,p)==h)return r;}}
  return -1;
}
int main(int argc,char**argv){
  int N=argc>1?stoi(argv[1]):200000; u64 cap=argc>2?stoull(argv[2]):numeric_limits<u64>::max(); vector<int>spf(N+1),ps;
  for(int i=2;i<=N;i++){if(!spf[i]){spf[i]=i;ps.push_back(i);}for(int p:ps){if(p>spf[i]||(long long)i*p>N)break;spf[i*p]=p;}}
  cout<<"family,prime,period,residue,kind,base_mod_Dp,step_mod_Dp\n";
  for(int id=1;id<=2;id++){
    u64 A=id==1?740:370,D=id==1?2391:2177,k=id==1?136:666,s=id==1?199:930;
    int count=0;
    for(u64 p:ps){
      u64 B=pw(10,s,p),q0=((mulmod(A,pw(10,k,D*p),D*p)+1)%(D*p))/D;
      u64 C=((pw(10,s,D*p)+D*p-1)%(D*p))/D;
      long long r=-1; u64 m=1; string kind;
      if(D%p==0){
        kind="denominator_affine";
        if(C%p!=0){m=p;r=mulmod(q0,pw(C,p-2,p),p);}else if(q0==0)r=0;
      }else if(A%p==0||10%p==0||B==1){
        kind="constant"; if(q0==0)r=0;
      }else{
        kind="multiplicative";m=p-1;int z=p-1;vector<int>f;
        while(z>1){int v=spf[z];f.push_back(v);while(z%v==0)z/=v;}
        for(auto v:f)while(m%v==0&&pw(B,m/v,p)==1)m/=v;
        if(m>cap)continue;
        u64 v=mulmod(A,pw(10,k,p),p),h=p-pw(v,p-2,p);
        if(pw(h,m,p)==1)r=dlog(B,h,p,m);
      }
      if(r>=0){
        u64 base=(mulmod(A,pw(10,k+s*r,D*p),D*p)+1)%(D*p);
        u64 step=pw(10,s*m,D*p);
        if(base!=0||step!=1){cerr<<"certificate error "<<id<<" "<<p<<"\n";return 2;}
        cout<<id<<','<<p<<','<<m<<','<<r<<','<<kind<<','<<base<<','<<step<<'\n';count++;
      }
    }
    cerr<<"family="<<id<<" prime_bound="<<N<<" classes="<<count<<'\n';
  }
}

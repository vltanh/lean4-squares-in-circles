#include <algorithm>
#include <array>
#include <fstream>
#include <iostream>
#include <map>
#include <set>
#include <string>
#include <vector>
using namespace std;
string output_dir=".";
struct Enum {
 int k,N,budget; vector<pair<int,int>> edges;vector<vector<int>> perm;vector<vector<bool>> crosses;vector<int>a,deg;
 array<int,7> cost{0,0,1,2,1,2,4}, mult{0,1,1,2,1,1,2};
 map<int,long long> labelled;map<int,set<string>> canonical;
 explicit Enum(int kk):k(kk),budget(10-kk),deg(kk,0){
  for(int i=0;i<k;++i)for(int j=i+1;j<k;++j)edges.push_back({i,j});N=edges.size();a.resize(N);
  crosses.assign(N,vector<bool>(N));
  for(int i=0;i<N;++i)for(int j=0;j<N;++j){auto[u,v]=edges[i];auto[x,y]=edges[j];
    crosses[i][j]=u!=x&&u!=y&&v!=x&&v!=y&&((u<x&&x<v)!=(u<y&&y<v));}
  for(int sign:{-1,1})for(int shift=0;shift<k;++shift){vector<int>p(N);
   for(int i=0;i<N;++i){auto[u,v]=edges[i];u=(sign*u+shift+k)%k;v=(sign*v+shift+k)%k;if(u>v)swap(u,v);p[i]=find(edges.begin(),edges.end(),make_pair(u,v))-edges.begin();}perm.push_back(p);}
 }
 bool connected(){vector<int>s{0};int mask=1;for(size_t t=0;t<s.size();++t){int u=s[t];for(int e=0;e<N;++e)if(a[e]){auto[x,y]=edges[e];int v=(x==u?y:(y==u?x:-1));if(v>=0&&!(mask&(1<<v))){mask|=1<<v;s.push_back(v);}}}return mask==(1<<k)-1;}
 string canon(){string best(N,'9');for(auto&p:perm){string s(N,'0');for(int i=0;i<N;++i)s[p[i]]=char('0'+a[i]);best=min(best,s);}return best;}
 void rec(int pos,int used,int E,int direct){
  if(pos==N){if(used==0||E<k||*max_element(deg.begin(),deg.end())<3||!connected())return;
   ++labelled[k+used];canonical[k+used].insert(canon());return;}
  auto[u,v]=edges[pos];bool boundary=v==u+1||(u==0&&v==k-1);
  for(int type=0;type<7;++type){int c=cost[type],d=mult[type];if(used+c>budget||deg[u]+d>8||deg[v]+d>8)continue;
    if(type==1&&(!boundary||(k==3&&direct==1)))continue;
    bool ok=true;if(type>=2)for(int j=0;j<pos;++j)if(a[j]>=2&&crosses[pos][j]&&!(type==4&&a[j]==4)){ok=false;break;}if(!ok)continue;
    a[pos]=type;deg[u]+=d;deg[v]+=d;rec(pos+1,used+c,E+d,direct+(type==1));deg[u]-=d;deg[v]-=d;
  }a[pos]=0;
 }
 void run(){rec(0,0,0,0);ofstream f(output_dir+"/b0_k"+to_string(k)+".txt");long long lab=0;size_t ca=0;
  for(auto&[m,s]:canonical){cout<<"k="<<k<<" m="<<m<<" labeled="<<labelled[m]<<" orbits="<<s.size()<<"\n";lab+=labelled[m];ca+=s.size();for(auto&code:s)f<<m<<" "<<code<<"\n";}cout<<"TOTAL k="<<k<<" labeled="<<lab<<" orbits="<<ca<<endl;
 }
};
int main(int argc,char**argv){if(argc>1)output_dir=argv[1];for(int k=3;k<=7;++k)Enum(k).run();}

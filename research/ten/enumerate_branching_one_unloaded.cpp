#include <algorithm>
#include <array>
#include <chrono>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <map>
#include <set>
#include <string>
#include <vector>
using namespace std;

struct Enumerator {
    static constexpr array<int,7> cost{0,0,1,2,1,2,4};
    static constexpr array<int,7> mult{0,1,1,2,1,1,2};
    int k,n,budget,N;
    vector<pair<int,int>> pairs;
    vector<int> uedges,ledges,code,degree;
    vector<vector<int>> permutations;
    vector<vector<bool>> alternating;
    vector<bool> allowed_chord;
    map<int,long long> labelled_by_bodies;
    map<int,long long> canonical_by_bodies;
    set<string> canonical;
    long long u_assignments=0;

    explicit Enumerator(int loaded): k(loaded),n(loaded+1),budget(9-loaded),degree(n,0) {
        for(int i=0;i<n;++i) for(int j=i+1;j<n;++j) pairs.emplace_back(i,j);
        N=pairs.size(); code.assign(N,0); allowed_chord.assign(N,true);
        for(int e=0;e<N;++e) (pairs[e].second==k ? uedges:ledges).push_back(e);
        for(int sign: {1,-1}) for(int shift=0;shift<k;++shift) {
            vector<int> perm(N);
            for(int e=0;e<N;++e) {
                auto [a,b]=pairs[e];
                if(a!=k) a=(sign*a+shift+k)%k;
                if(b!=k) b=(sign*b+shift+k)%k;
                if(a>b) swap(a,b);
                perm[e]=find(pairs.begin(),pairs.end(),pair<int,int>(a,b))-pairs.begin();
            }
            permutations.push_back(perm);
        }
        alternating.assign(N,vector<bool>(N,false));
        for(int e:ledges) for(int f:ledges) {
            auto[a,b]=pairs[e]; auto[c,d]=pairs[f];
            alternating[e][f]=(a<c&&c<b&&b<d)||(c<a&&a<d&&d<b);
        }
    }

    bool connected() const {
        int mask=1, old=0;
        while(mask!=old) {
            old=mask;
            for(int e=0;e<N;++e) if(code[e]) {
                auto[a,b]=pairs[e];
                if(mask&((1<<a)|(1<<b))) mask|=(1<<a)|(1<<b);
            }
        }
        return mask==(1<<n)-1;
    }

    string canon() const {
        string best(N,'9');
        for(const auto& perm:permutations) {
            string current(N,'0');
            for(int e=0;e<N;++e) current[perm[e]]=char('0'+code[e]);
            best=min(best,current);
        }
        return best;
    }

    void record(int used,int E) {
        if(E<n || !connected()) return;
        ++labelled_by_bodies[n+used];
        auto inserted=canonical.insert(canon()).second;
        if(inserted) ++canonical_by_bodies[n+used];
    }

    void assign_loaded(int pos,int used,int E,int direct_count) {
        if(pos==(int)ledges.size()) {record(used,E); return;}
        int edge=ledges[pos]; auto[a,b]=pairs[edge];
        bool boundary=(b==a+1)||(a==0&&b==k-1);
        bool can_present=allowed_chord[edge];
        if(can_present) for(int j=0;j<pos;++j) {
            int prior=ledges[j];
            if(code[prior] && alternating[edge][prior]) {can_present=false;break;}
        }
        for(int typ=0;typ<7;++typ) {
            if(typ && !can_present) continue;
            if(typ==1 && (k==2 || !boundary || (k==3 && direct_count>=1))) continue;
            int next=used+cost[typ], d=mult[typ];
            if(next>budget || degree[a]+d>8 || degree[b]+d>8) continue;
            code[edge]=typ; degree[a]+=d; degree[b]+=d;
            assign_loaded(pos+1,next,E+d,direct_count+(typ==1));
            degree[a]-=d; degree[b]-=d;
        }
        code[edge]=0;
    }

    void finish_u(int used,int E) {
        vector<int> neighbors,types;
        for(int edge:uedges) if(code[edge]) {
            neighbors.push_back(pairs[edge].first);
            types.push_back(code[edge]);
        }
        if(degree[k]<3) return;
        if(neighbors.size()<3) {
            sort(types.begin(),types.end());
            if(types!=vector<int>{1,3}) return;
        }
        ++u_assignments;
        for(int edge:ledges) {
            auto[a,b]=pairs[edge]; bool inside=false,outside=false;
            for(int v:neighbors) if(v!=a&&v!=b) {
                if(a<v&&v<b) inside=true; else outside=true;
            }
            allowed_chord[edge]=!(inside&&outside);
        }
        assign_loaded(0,used,E,0);
    }

    void assign_u(int pos,int used,int E) {
        if(pos==k) {finish_u(used,E); return;}
        int edge=uedges[pos]; auto[a,b]=pairs[edge];
        for(int typ=0;typ<7;++typ) {
            int next=used+cost[typ],d=mult[typ];
            if(next>budget || degree[a]+d>8 || degree[b]+d>8) continue;
            code[edge]=typ; degree[a]+=d; degree[b]+=d;
            assign_u(pos+1,next,E+d);
            degree[a]-=d; degree[b]-=d;
        }
        code[edge]=0;
    }

    void run(const string& output_dir) {
        auto started=chrono::steady_clock::now();
        assign_u(0,0,0);
        ofstream out(output_dir+"/b1_k"+to_string(k)+".txt");
        for(const string& row:canonical) out<<row<<'\n';
        long long labelled=0;
        for(auto[m,count]:labelled_by_bodies) {
            labelled+=count;
            cout<<"k="<<k<<" bodies="<<m<<" labeled="<<count<<" canonical="<<canonical_by_bodies[m]<<'\n';
        }
        auto elapsed=chrono::duration<double>(chrono::steady_clock::now()-started).count();
        cout<<"TOTAL k="<<k<<" labeled="<<labelled<<" canonical="<<canonical.size()
            <<" u_assignments="<<u_assignments<<" seconds="<<elapsed<<endl;
    }
};

int main(int argc,char**argv) {
    string out=argc>1?argv[1]:".";
    filesystem::create_directories(out);
    if(argc>2) for(int i=2;i<argc;++i) {
        int k=stoi(argv[i]); if(k<2||k>7) return 2; Enumerator(k).run(out);
    } else for(int k=2;k<=7;++k) Enumerator(k).run(out);
}

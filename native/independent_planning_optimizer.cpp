// Separate exact target enumeration, using integer fractional-knapsack bounds.
#include <algorithm>
#include <cstdint>
#include <iostream>
#include <vector>
#include <chrono>
#include <stdexcept>
struct Project { int64_t p; std::vector<int64_t> c; int original; };
int main() {
  try {
    int n=0,m=0; int64_t target=0;
    if(!(std::cin>>n>>m>>target))throw std::runtime_error("input");
    if(n<0||n>62||m<1||m>16||target<0)throw std::runtime_error("dimensions");
    std::vector<int64_t> cap(m);for(auto&x:cap){std::cin>>x;if(x < -1000000000 || x>1000000000)throw std::runtime_error("capacity");}
    std::vector<Project> v(n);
    for(int j=0;j<n;++j) {
      v[j].original=j;std::cin>>v[j].p;v[j].c.resize(m);
      if(v[j].p<0||v[j].p>1000000000)throw std::runtime_error("profit");
      for(auto&x:v[j].c){std::cin>>x;if(x<0||x>1000000000)throw std::runtime_error("cost");}
    }
    if(!std::cin)throw std::runtime_error("input");
    std::sort(v.begin(),v.end(),[](auto&a,auto&b){return a.p>b.p;});
    std::vector<std::vector<std::vector<int>>> order(n,std::vector<std::vector<int>>(m));
    for(int i=0;i<n;++i)for(int k=0;k<m;++k) {
      auto&o=order[i][k];for(int j=i;j<n;++j)o.push_back(j);
      std::sort(o.begin(),o.end(),[&](int a,int b){
        if(v[a].c[k]==0||v[b].c[k]==0)return v[a].c[k]<v[b].c[k];
        return v[a].p*v[b].c[k]>v[b].p*v[a].c[k];
      });
    }
    uint64_t visits=0,candidates=0,ties=0,mask=0;int64_t best=-1;
    auto start=std::chrono::steady_clock::now();
    auto go=[&](auto&&self,int i,int64_t score,uint64_t bits)->void {
      ++visits;for(auto b:cap)if(b<0)return;
      if(i==n) {
        if(score<target)return;
        ++candidates;
        if(score>best){best=score;ties=1;mask=bits;}else if(score==best){++ties;mask=std::min(mask,bits);}
        return;
      }
      for(int k=0;k<m;++k) {
        int64_t slack=cap[k],bound=score;
        for(int j:order[i][k]) {
          if(v[j].c[k]<=slack){bound+=v[j].p;slack-=v[j].c[k];}
          else {bound+=(v[j].p*slack)/v[j].c[k];break;}
        }
        if(bound<target)return;
      }
      for(int k=0;k<m;++k)cap[k]-=v[i].c[k];
      self(self,i+1,score+v[i].p,bits|(uint64_t(1)<<(n-1-v[i].original)));
      for(int k=0;k<m;++k)cap[k]+=v[i].c[k];
      self(self,i+1,score,bits);
    };go(go,0,0,0);
    std::cout<<"{\"status\":\"complete\",\"target\":"<<target<<",\"candidates_at_or_above_target\":"<<candidates<<",\"maximum\":"<<best<<",\"maximizers\":"<<ties<<",\"mask\":"<<mask<<",\"visits\":"<<visits<<",\"seconds\":"<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<"}\n";
  }catch(const std::exception&e){std::cerr<<e.what()<<"\n";return 2;}
}

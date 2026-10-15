// Independent ROBDD intersection counter. No completion_planner linkage.
#include <algorithm>
#include <cstdint>
#include <iostream>
#include <vector>
#include <unordered_map>
#include <stdexcept>
#include <chrono>
#include <sys/resource.h>
#include "planning_certificate_trace.hpp"
using U = uint32_t;
struct Proven { U node, proof; };
struct Node { U lo, hi, level; };
struct BDD {
  Trace* trace=nullptr; std::vector<U> trace_ids{0,1};
  int resource=0; U last_threshold=0,last_apply=0;
  int n; size_t limit; uint64_t calls=0;
  std::vector<Node> nodes;
  std::vector<std::unordered_map<uint64_t,U>> unique;
  std::unordered_map<uint64_t,Proven> cache;
  BDD(int n_, size_t l):n(n_),limit(l),nodes{{0,0,U(n)},{1,1,U(n)}},unique(n) {}
  U mk(int level,U lo,U hi) {
    if(lo==hi) return lo;
    uint64_t key=(uint64_t(lo)<<32)|hi;
    auto &table=unique[level]; auto it=table.find(key);
    if(it!=table.end()) return it->second;
    if(nodes.size()>=limit) throw std::runtime_error("node limit");
    U id=nodes.size(); nodes.push_back({lo,hi,U(level)});
    if(trace) trace_ids.push_back(trace->node(level,trace_ids[lo],trace_ids[hi])); table.emplace(key,id); return id;
  }
  Proven conjunction(U a,U b) {
    ++calls;
    if(!a||!b) return {0,0};
    if(a==1||a==b) return {b,0};
    if(b==1) return {a,0};
    if(a>b) std::swap(a,b);
    uint64_t key=(uint64_t(a)<<32)|b;
    auto it=cache.find(key); if(it!=cache.end()) return it->second;
    int level=std::min(nodes[a].level,nodes[b].level);
    Node x=nodes[a],y=nodes[b];
    Proven lo=conjunction(x.level==level?x.lo:a,y.level==level?y.lo:b);
    Proven hi=conjunction(x.level==level?x.hi:a,y.level==level?y.hi:b);
    U result=mk(level,lo.node,hi.node),proof=0;
    if(trace) proof=trace->apply(trace_ids[a],trace_ids[b],trace_ids[result],lo.proof,hi.proof);
    Proven entry{result,proof};cache.emplace(key,entry);return entry;
  }
  U intersect(U a,U b) {auto p=conjunction(a,b);last_apply=p.proof;return p.node;}
  U threshold(const std::vector<int>&w,int cap) {
    std::vector<int> total(n+1); for(int i=n-1;i>=0;--i) total[i]=total[i+1]+w[i];
    std::vector<std::unordered_map<int,Proven>> memo(n);
    auto go=[&](auto&& self,int i,int b)->Proven {
      if(b<0) return {0,0};
      if(b>=total[i]) return {1,0};
      auto it=memo[i].find(b); if(it!=memo[i].end()) return it->second;
      Proven lo=self(self,i+1,b),hi=self(self,i+1,b-w[i]);
      U id=mk(i,lo.node,hi.node),proof=0;
      if(trace)proof=trace->threshold(resource,i,b,trace_ids[id],lo.proof,hi.proof);
      Proven p{id,proof};memo[i].emplace(b,p);return p;
    }; auto p=go(go,0,cap);last_threshold=p.proof;return p.node;
  }
  uint64_t count(U root,uint64_t fixed=0,uint64_t values=0) const {
    std::vector<int> free(n+1);
    for(int i=0;i<n;++i)free[i+1]=free[i]+!(fixed&(uint64_t(1)<<(n-1-i)));
    std::vector<uint64_t> c(nodes.size()); c[1]=1;
    for(size_t i=2;i<nodes.size();++i) {
      Node x=nodes[i];
      uint64_t lo=c[x.lo]<<(free[nodes[x.lo].level]-free[x.level+1]);
      uint64_t hi=c[x.hi]<<(free[nodes[x.hi].level]-free[x.level+1]);
      uint64_t bit=uint64_t(1)<<(n-1-x.level);
      c[i]=(fixed&bit)?((values&bit)?hi:lo):lo+hi;
    }
    return c[root]<<free[nodes[root].level];
  }
  // Rebuild only reachable nodes, releasing apply caches and unused diagrams.
  U compact(U root) {
    BDD next(n,limit); std::vector<U> map(nodes.size(),UINT32_MAX); map[0]=0;map[1]=1;
    auto go=[&](auto&& self,U id)->U {
      if(map[id]!=UINT32_MAX) return map[id];
      Node x=nodes[id]; U lo=self(self,x.lo),hi=self(self,x.hi);
      U result=next.mk(x.level,lo,hi);
      if(trace) { if(next.trace_ids.size()<=result)next.trace_ids.resize(result+1);next.trace_ids[result]=trace_ids[id]; }
      return map[id]=result;
    }; U result=go(go,root); next.calls=calls; next.trace=trace; *this=std::move(next); return result;
  }
};
int main(int argc,char**argv) {
  auto start=std::chrono::steady_clock::now();
  try {
    size_t limit=argc>1?std::stoull(argv[1]):20000000;
    int n,m; if(!(std::cin>>n>>m)||n<0||n>62||m<0||m>16) throw std::runtime_error("invalid dimensions");
    std::vector<int> cap(m); for(auto &x:cap){std::cin>>x;if(x < -1000000 || x>1000000)throw std::runtime_error("capacity range");}
    std::vector<std::vector<int>> weights(m,std::vector<int>(n));
    for(int j=0;j<n;++j)for(int k=0;k<m;++k) {
      std::cin>>weights[k][j]; if(weights[k][j]<0||weights[k][j]>1000000)throw std::runtime_error("cost range");
    }
    if(!std::cin)throw std::runtime_error("truncated input");
    Trace* trace=argc>2?new Trace(argv[2],n,m,cap,weights):nullptr;
    BDD bdd(n,limit); bdd.trace=trace; U root=1;
    for(int k=0;k<m;++k) {
      bdd.resource=k; U constraint=bdd.threshold(weights[k],cap[k]); root=bdd.intersect(root,constraint);
      if(trace)trace->stage(k,bdd.trace_ids[constraint],bdd.last_threshold,bdd.trace_ids[root],bdd.last_apply);
      root=bdd.compact(root);
      std::cerr<<"resource "<<k<<" nodes "<<bdd.nodes.size()<<" count "<<bdd.count(root)<<" calls "<<bdd.calls<<std::endl;
    }
    if(trace){trace->finish(bdd.trace_ids[root]);delete trace;bdd.trace=nullptr;}
    uint64_t global=bdd.count(root); double build_seconds=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();
    int q=0;std::cin>>q;if(q<0||q>8192)throw std::runtime_error("query limit");
    std::vector<uint64_t> answers;
    for(int i=0;i<q;++i) {
      uint64_t fixed,values;std::cin>>fixed>>values;
      if(!std::cin||(values&~fixed)||fixed>=(uint64_t(1)<<n))throw std::runtime_error("invalid masks");
      answers.push_back(bdd.count(root,fixed,values));
    }
    struct rusage usage{}; getrusage(RUSAGE_SELF,&usage);
    double seconds=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();
    std::cout<<"{\"status\":\"complete\",\"count\":"<<global<<",\"nodes\":"<<bdd.nodes.size()<<",\"apply_calls\":"<<bdd.calls<<",\"build_seconds\":"<<build_seconds<<",\"seconds\":"<<seconds<<",\"peak_rss_kib\":"<<usage.ru_maxrss<<",\"conditional_counts\":[";
    for(size_t i=0;i<answers.size();++i){if(i)std::cout<<",";std::cout<<answers[i];}
    std::cout<<"]}\n";
  } catch(const std::exception&e) {
    std::cout<<"{\"status\":\"incomplete\",\"reason\":\""<<e.what()<<"\"}\n";return 2;
  }
}

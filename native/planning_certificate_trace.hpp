// pp-bdd-trace/1: explicit little-endian words, never host struct serialization.
#pragma once
#include <fstream>
#include <array>
struct Trace {
  std::ofstream out;
  uint32_t nodes=2, thresholds=0, applies=0;
  std::vector<uint64_t> counts{0,1};
  std::vector<uint32_t> levels;
  Trace(const char* path,int n,int m,const std::vector<int>&caps,
        const std::vector<std::vector<int>>&w):out(path,std::ios::binary),levels{uint32_t(n),uint32_t(n)} {
    out.exceptions(std::ios::badbit|std::ios::failbit);
    out.write("PPBDD001",8); word(n);word(m);
    for(auto c:caps)word(c);
    for(auto &r:w)for(auto x:r)word(x);
  }
  void word(uint32_t v){char b[4];for(int i=0;i<4;++i)b[i]=char(v>>(8*i));out.write(b,4);}
  void record(std::array<uint32_t,8> a){for(auto x:a)word(x);}
  uint32_t node(uint32_t level,uint32_t lo,uint32_t hi){
    uint64_t count=(counts[lo]<<(levels[lo]-level-1))+(counts[hi]<<(levels[hi]-level-1));
    record({1,level,lo,hi,uint32_t(count),uint32_t(count>>32),0,0});
    counts.push_back(count);levels.push_back(level);return nodes++;
  }
  uint32_t threshold(uint32_t row,uint32_t level,uint32_t cap,uint32_t result,uint32_t lo,uint32_t hi){
    record({2,row,level,cap,result,lo,hi,0});return ++thresholds;
  }
  uint32_t apply(uint32_t a,uint32_t b,uint32_t result,uint32_t lo,uint32_t hi){
    record({3,a,b,result,lo,hi,0,0});return ++applies;
  }
  void stage(uint32_t row,uint32_t t,uint32_t tp,uint32_t root,uint32_t ap){
    uint64_t c=counts[root]<<levels[root];
    record({4,row,t,tp,root,ap,uint32_t(c),uint32_t(c>>32)});
    thresholds=applies=0;
  }
  void finish(uint32_t root){uint64_t c=counts[root]<<levels[root];record({5,root,uint32_t(c),uint32_t(c>>32),0,0,0,0});out.close();}
};

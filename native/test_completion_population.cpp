#include "completion_planner.cpp"
#include <iostream>
#include <random>
std::string field(const std::string&s,const std::string&name){auto start=s.find("\""+name+"\":")+name.size()+3;auto end=s.find_first_of(",}",start);return s.substr(start,end-start);}
int main(){std::mt19937 rng(20261012);for(int t=0;t<200;t++){int n=1+t%14,m=1+t%5;std::vector<U>lo(m),hi(m),c(n*m);std::vector<I>p(n);for(int k=0;k<m;k++){lo[k]=rng()%3;hi[k]=lo[k]+rng()%20;}for(auto &v:c)v=rng()%8;for(auto &v:p)v=I(rng()%11)-5;auto a=population(n,m,lo.data(),hi.data(),c.data(),p.data(),0,0,100000,10000000,8*1024*1024,1);auto b=recursive(n,m,lo.data(),hi.data(),c.data(),p.data(),10000000);for(auto key:{"count","ties","best","mask"})if(field(a,key)!=field(b,key)){std::cerr<<a<<"\n"<<b<<"\n";return 1;}}
 std::vector<U>lo(1),hi(1),c(64);std::vector<I>p(64);auto a=population(64,1,lo.data(),hi.data(),c.data(),p.data(),0,0,10,10000,1024*1024,1);if(field(a,"count")!="\"18446744073709551616\"")return 2;std::cout<<"200 independent folds and 64-bit boundary pass\n";}

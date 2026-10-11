// Compile separately with -fsanitize=address,undefined; not a production entry.
#include "counter.cpp"
#include <random>
#include <iostream>

int main() {
 std::mt19937 rng(4269);
 for (unsigned trial=0;trial<1000;trial++) {
  unsigned n=1+rng()%10,m=1+rng()%25;
  Formula f;std::ostringstream text;text<<n<<" "<<m<<"\n";
  for (unsigned i=0;i<m;i++) {
   std::vector<int> clause;
   while (clause.size()<3) {
    int x=1+rng()%n;if(rng()%2)x=-x;
    if(std::find(clause.begin(),clause.end(),x)==clause.end() &&
       std::find(clause.begin(),clause.end(),-x)==clause.end())clause.push_back(x);
    if(n<3 && clause.size()==n)break;
   }
   for(int x:clause)text<<x<<" ";text<<"0\n";f.push_back(clause);
  }
  unsigned expected=0;
  for(unsigned assignment=0;assignment<(1u<<n);assignment++) {
   bool accepted=true;
   for(auto& clause:f) {
    bool satisfied=false;
    for(int literal:clause)
     if(((assignment>>(std::abs(literal)-1))&1)==unsigned(literal>0))satisfied=true;
    if(!satisfied){accepted=false;break;}
   }
   expected+=accepted;
  }
  Counter counter(text.str().c_str(),1024*1024);
  counter.deadline=Clock::now()+std::chrono::seconds(10);
  if(counter.solve(f,n)!=expected) {
   std::cerr<<"exhaustive mismatch at trial "<<trial<<"\n";return 1;
  }
 }
 std::cout<<"1000 native formulas matched exhaustive counts\n";
}

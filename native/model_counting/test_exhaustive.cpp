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
 for(unsigned trial=0;trial<80;trial++){
  Formula f;std::vector<std::array<int,3>> definitions;unsigned previous=1;
  for(unsigned v=6;v<=265;v++){
   int a=int(previous)*(rng()%2?1:-1),b=int(v%5+1)*(rng()%2?1:-1),out=int(v)*(rng()%2?1:-1);
   f.push_back({-out,a});f.push_back({-out,b});f.push_back({out,-a,-b});
   definitions.push_back({out,a,b});previous=v;
  }
  for(unsigned i=0;i<trial%9;i++){
   std::vector<int> clause;
   while(clause.size()<3){int x=int(1+rng()%265)*(rng()%2?1:-1);
    if(std::find(clause.begin(),clause.end(),x)==clause.end()&&std::find(clause.begin(),clause.end(),-x)==clause.end())clause.push_back(x);}
   f.push_back(std::move(clause));
  }
  unsigned expected=0;
  for(unsigned input=0;input<32;input++){
   std::vector<uint8_t> point(266);for(unsigned v=1;v<=5;v++)point[v]=(input>>(v-1))&1;
   for(auto d:definitions){bool value=(point[std::abs(d[1])]==(d[1]>0))&&(point[std::abs(d[2])]==(d[2]>0));point[std::abs(d[0])]=value==(d[0]>0);}
   bool accepted=true;for(auto& clause:f){bool satisfied=false;for(int x:clause)if(point[std::abs(x)]==(x>0))satisfied=true;if(!satisfied){accepted=false;break;}}
   expected+=accepted;
  }
  std::ostringstream text;text<<265<<" "<<f.size()<<"\n";for(auto& clause:f){for(int x:clause)text<<x<<" ";text<<"0\n";}
  Counter counter(text.str().c_str(),trial%2?0:1024*1024);counter.deadline=Clock::now()+std::chrono::seconds(30);
  if(counter.solve(f,265)!=expected){std::cerr<<"gate circuit mismatch at trial "<<trial<<"\n";return 1;}
 }
 for(unsigned n:{270u,900u}){
  Formula f;std::ostringstream text;text<<n<<" "<<n-1<<"\n";
  for(unsigned v=1;v<n;v++){f.push_back({int(v),int(v+1)});text<<v<<" "<<v+1<<" 0\n";}
  cpp_int a=1,b=2;for(unsigned i=0;i<n;i++){cpp_int next=a+b;a=b;b=next;}
  Counter counter(text.str().c_str(),1024*1024);counter.deadline=Clock::now()+std::chrono::seconds(30);
  if(counter.solve(f,n)!=a){std::cerr<<"large path mismatch\n";return 1;}
 }
 std::cout<<"1000 exhaustive small formulas, 80 exhaustive-input gate circuits and 2 analytic paths matched\n";
}

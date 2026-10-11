// Exact unweighted #CNF with deterministic full-key component caching.
// Executable implementation; not a kernel-verified algorithm.
#include <boost/multiprecision/cpp_int.hpp>
#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cstring>
#include <sstream>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <map>
#include <vector>
#include <array>
using boost::multiprecision::cpp_int;
using Formula=std::vector<std::vector<int>>;
using Clock=std::chrono::steady_clock;
struct Limit:std::runtime_error {using std::runtime_error::runtime_error;};
struct Counter {
 unsigned n; Formula source; std::unordered_map<std::string,cpp_int> cache;
 size_t cache_bytes=0, cache_limit; uint64_t nodes=0,hits=0,splits=0,affine=0,eliminations=0,equivalences=0;
 Clock::time_point deadline; std::string reply;
 Counter(const char* text,size_t limit):cache_limit(limit){
  std::istringstream in(text); unsigned m; if(!(in>>n>>m)||n>200000||m>2000000)throw std::invalid_argument("native dimensions");
  for(unsigned i=0;i<m;i++){std::vector<int> c;int x;bool done=false;while(in>>x){if(!x){done=true;break;}if(x==INT32_MIN||unsigned(std::abs(x))>n)throw std::invalid_argument("native literal");c.push_back(x);}if(!done)throw std::invalid_argument("native clause");source.push_back(std::move(c));}
  std::string tail;if(in>>tail)throw std::invalid_argument("native trailing input");
 }
 void check(unsigned depth){if(depth>768)throw Limit("recursion depth limit");if(++nodes>10000000)throw Limit("search node limit");if(Clock::now()>deadline)throw Limit("query time limit");}
 static unsigned dense(Formula& f){unsigned maximum=0;for(auto& c:f)for(int x:c)maximum=std::max(maximum,unsigned(std::abs(x)));
  std::vector<unsigned> mapping(maximum+1);for(auto& c:f)for(int x:c)mapping[std::abs(x)]=1;
  unsigned used=0;for(unsigned v=1;v<=maximum;v++)if(mapping[v])mapping[v]=++used;
  for(auto& c:f){for(int& x:c){int v=mapping[std::abs(x)];x=x>0?v:-v;}std::sort(c.begin(),c.end());c.erase(std::unique(c.begin(),c.end()),c.end());}
  std::sort(f.begin(),f.end());f.erase(std::unique(f.begin(),f.end()),f.end());return used;}
 static std::string key(const Formula& f){std::string s;for(auto& c:f){for(int x:c)s.append(reinterpret_cast<const char*>(&x),sizeof(x));int z=0;s.append(reinterpret_cast<const char*>(&z),sizeof(z));}return s;}
 // Occurrence queues visit each falsified literal once, including long unit chains.
 bool propagate(Formula& f,unsigned vars,unsigned& forced){
  bool units=false;for(auto& c:f){if(c.empty())return false;if(c.size()==1)units=true;}if(!units)return true;
  std::vector<std::vector<unsigned>> occurrences(2*vars);
  auto id=[](int x){return 2*(unsigned(std::abs(x))-1)+(x<0);};
  std::vector<unsigned> remaining(f.size());std::vector<int> parity(f.size());
  std::vector<uint8_t> satisfied(f.size());std::vector<int8_t> assignment(vars+1);
  std::vector<int> queue;
  auto enqueue=[&](int x){unsigned v=std::abs(x);int val=x>0?1:-1;
   if(assignment[v])return assignment[v]==val;
   assignment[v]=val;queue.push_back(x);return true;};
  for(unsigned i=0;i<f.size();i++){
   if(f[i].empty())return false;
   remaining[i]=f[i].size();for(int x:f[i]){occurrences[id(x)].push_back(i);parity[i]^=x;}
   if(f[i].size()==1&&!enqueue(f[i][0]))return false;
  }
  for(size_t at=0;at<queue.size();at++){
   if((at&4095)==0&&Clock::now()>deadline)throw Limit("query time limit");
   int x=queue[at];for(unsigned i:occurrences[id(x)])satisfied[i]=1;
   for(unsigned i:occurrences[id(-x)])if(!satisfied[i]){
    parity[i]^=-x;if(--remaining[i]==0)return false;
    if(remaining[i]==1&&!enqueue(parity[i]))return false;
   }
  }
  forced=queue.size();if(!forced)return true;
  Formula out;out.reserve(f.size());for(unsigned i=0;i<f.size();i++)if(!satisfied[i]){
   std::vector<int> clause;for(int x:f[i])if(!assignment[std::abs(x)])clause.push_back(x);
   out.push_back(std::move(clause));
  }f=std::move(out);return true;
 }
 // Binary implication SCCs establish signed equivalences. Each eliminated
 // variable has exactly one extension, so it contributes no factor of two.
 unsigned quotient(Formula& f,unsigned vars,bool& contradiction){
  bool binary=false;for(auto& c:f)if(c.size()==2){binary=true;break;}if(!binary)return 0;
  auto id=[](int x){return 2*(unsigned(std::abs(x))-1)+(x<0);};
  std::vector<std::vector<unsigned>> graph(2*vars),reverse(2*vars);size_t edges=0;
  for(auto& c:f)if(c.size()==2){unsigned a=id(-c[0]),b=id(c[1]);
   graph[a].push_back(b);reverse[b].push_back(a);graph[b^1].push_back(a^1);reverse[a^1].push_back(b^1);edges+=2;}
  if(!edges)return 0;
  std::vector<uint8_t> seen(2*vars);std::vector<unsigned> order;order.reserve(2*vars);
  for(unsigned start=0;start<2*vars;start++)if(!seen[start]){
   std::vector<std::pair<unsigned,size_t>> stack{{start,0}};seen[start]=1;
   while(!stack.empty()){auto& frame=stack.back();if(frame.second<graph[frame.first].size()){
    unsigned v=graph[frame.first][frame.second++];if(!seen[v]){seen[v]=1;stack.push_back({v,0});}
   }else{order.push_back(frame.first);stack.pop_back();}}
   if((start&4095)==0&&Clock::now()>deadline)throw Limit("query time limit");
  }
  std::vector<unsigned> component(2*vars,UINT32_MAX);unsigned components=0;
  for(auto it=order.rbegin();it!=order.rend();++it)if(component[*it]==UINT32_MAX){
   std::vector<unsigned> stack{*it};component[*it]=components;
   while(!stack.empty()){unsigned v=stack.back();stack.pop_back();for(unsigned u:reverse[v])if(component[u]==UINT32_MAX){component[u]=components;stack.push_back(u);}}
   components++;
  }
  std::vector<int> representative(components);unsigned removed=0;
  for(unsigned v=1;v<=vars;v++){
   unsigned a=component[2*(v-1)],b=component[2*(v-1)+1];
   if(a==b){contradiction=true;return 0;}
   if(!representative[a]){representative[a]=v;representative[b]=-int(v);}else removed++;
  }
  if(!removed)return 0;
  Formula out;out.reserve(f.size());for(auto& c:f){std::vector<int> clause;
   for(int x:c)clause.push_back(representative[component[id(x)]]);
   std::sort(clause.begin(),clause.end());clause.erase(std::unique(clause.begin(),clause.end()),clause.end());
   bool tautology=false;for(int x:clause)if(std::binary_search(clause.begin(),clause.end(),-x)){tautology=true;break;}
   if(!tautology)out.push_back(std::move(clause));
  }f=std::move(out);equivalences+=removed;return removed;
 }
 bool affine_count(const Formula& f,unsigned vars,cpp_int& result){
  if(vars>8192)return false;
  std::map<std::vector<int>,std::vector<unsigned>> groups;
  for(auto& c:f){if(c.size()>12)return false;std::vector<int> v;for(int x:c)v.push_back(std::abs(x));std::sort(v.begin(),v.end());unsigned mask=0;for(int x:c)if(x<0)mask|=1u<<(std::lower_bound(v.begin(),v.end(),-x)-v.begin());groups[v].push_back(mask);}
  for(auto& g:groups){auto& masks=g.second;unsigned k=g.first.size();if(!k||masks.size()!=(1u<<(k-1)))return false;int parity=__builtin_parity(masks[0]);for(unsigned m:masks)if(__builtin_parity(m)!=parity)return false;}
  unsigned words=(vars+1+63)/64,rank=0;std::vector<std::vector<uint64_t>> basis(vars);bool inconsistent=false;
  for(auto& g:groups){std::vector<uint64_t> row(words);for(int v:g.first)row[(v-1)/64]^=uint64_t(1)<<((v-1)%64);if(!__builtin_parity(g.second[0]))row[vars/64]^=uint64_t(1)<<(vars%64);
   bool inserted=false;for(unsigned v=0;v<vars;v++)if((row[v/64]>>(v%64))&1){if(basis[v].empty()){basis[v]=std::move(row);rank++;inserted=true;break;}for(unsigned w=0;w<words;w++)row[w]^=basis[v][w];}
   if(!inserted&&((row[vars/64]>>(vars%64))&1)){inconsistent=true;break;}
  }
  result=inconsistent?cpp_int(0):(cpp_int(1)<<(vars-rank));affine++;return true;
 }

 bool eliminate(const Formula& f,unsigned vars,cpp_int& result){
  if(vars>256)return false;
  std::map<std::vector<int>,std::vector<unsigned>> groups;
  for(auto& c:f){if(c.size()>12)return false;std::vector<int> scope;for(int x:c)scope.push_back(std::abs(x));std::sort(scope.begin(),scope.end());unsigned mask=0;for(int x:c)if(x<0)mask|=1u<<(std::lower_bound(scope.begin(),scope.end(),-x)-scope.begin());groups[scope].push_back(mask);}
  // A filled primal graph gives the same bucket scope without repeatedly
  // scanning every factor for every candidate at every elimination step.
  using Bits=std::array<uint64_t,4>;std::vector<Bits> graph(vars+1);
  for(auto& g:groups)for(int v:g.first)for(int u:g.first)if(u!=v)graph[v][(u-1)/64]|=uint64_t(1)<<((u-1)%64);
  std::vector<uint8_t> live(vars+1,1);
  std::vector<unsigned> plan;uint64_t work=0;
  for(unsigned step=0;step<vars;step++){
   if(Clock::now()>deadline)throw Limit("query time limit");
   unsigned best=0;size_t width=100000;std::vector<int> united;
   for(unsigned v=1;v<=vars;v++){
    if(!live[v])continue;size_t degree=1;for(uint64_t word:graph[v])degree+=__builtin_popcountll(word);
    if(degree<width){width=degree;best=v;}
   }
   if(!best)break;if(width>18)return false;work+=uint64_t(1)<<width;if(work>8000000)return false;
   plan.push_back(best);live[best]=0;
   for(unsigned u=1;u<=vars;u++)if((graph[best][(u-1)/64]>>((u-1)%64))&1)united.push_back(u);
   for(int u:united){for(unsigned w=0;w<4;w++)graph[u][w]|=graph[best][w];
    graph[u][(u-1)/64]&=~(uint64_t(1)<<((u-1)%64));graph[u][(best-1)/64]&=~(uint64_t(1)<<((best-1)%64));}
  }
  struct Factor {std::vector<int> scope;std::vector<cpp_int> values;};std::vector<Factor> factors;
  for(auto& g:groups){Factor a{g.first,std::vector<cpp_int>(size_t(1)<<g.first.size(),cpp_int(1))};for(unsigned x:g.second)a.values[x]=0;factors.push_back(std::move(a));}
  cpp_int constant=1;
  for(unsigned v:plan){
   std::vector<int> united;std::vector<Factor> selected,next;
   for(auto& a:factors){if(std::binary_search(a.scope.begin(),a.scope.end(),int(v))){united.insert(united.end(),a.scope.begin(),a.scope.end());selected.push_back(std::move(a));}else next.push_back(std::move(a));}
   std::sort(united.begin(),united.end());united.erase(std::unique(united.begin(),united.end()),united.end());unsigned position=std::lower_bound(united.begin(),united.end(),int(v))-united.begin();
   std::vector<std::vector<std::pair<unsigned,unsigned>>> changes(united.size());
   for(unsigned j=0;j<selected.size();j++)for(unsigned bit=0;bit<selected[j].scope.size();bit++){unsigned at=std::lower_bound(united.begin(),united.end(),selected[j].scope[bit])-united.begin();changes[at].push_back({j,1u<<bit});}
   std::vector<unsigned> indices(selected.size());std::vector<int> scope=united;scope.erase(scope.begin()+position);Factor out{scope,std::vector<cpp_int>(size_t(1)<<scope.size())};
   for(unsigned i=0;i<(1u<<united.size());i++){
    if((i&4095)==0&&Clock::now()>deadline)throw Limit("query time limit");
    if(i){unsigned bit=__builtin_ctz(i);for(auto change:changes[bit])indices[change.first]^=change.second;}
    unsigned gray=i^(i>>1),output=(gray&((1u<<position)-1))|((gray>>(position+1))<<position);cpp_int product=1;
    for(unsigned j=0;j<selected.size();j++){if(selected[j].values[indices[j]]==0){product=0;break;}product*=selected[j].values[indices[j]];}
    out.values[output]+=product;
   }
   if(out.scope.empty())constant*=out.values[0];else next.push_back(std::move(out));factors=std::move(next);if(constant==0){result=0;return true;}
  }
  if(!factors.empty())throw std::logic_error("elimination scope remains");result=constant;eliminations++;return true;
 }
 cpp_int solve(Formula f,unsigned universe,unsigned depth=0){
  check(depth);unsigned used=dense(f);if(used>universe)throw std::logic_error("variable universe");unsigned forced=0;
  if(!propagate(f,used,forced))return 0;
  unsigned active=dense(f),free=universe-forced-active;
  if(f.empty())return cpp_int(1)<<free;
  auto k=key(f);auto found=cache.find(k);if(found!=cache.end()){hits++;return found->second<<free;}
  cpp_int value;
  bool contradiction=false;unsigned removed=quotient(f,active,contradiction);
  if(contradiction)value=0;
  else if(removed)value=solve(std::move(f),active-removed,depth+1);
  else if(f.size()==1)value=(cpp_int(1)<<active)-1;
  else if(!affine_count(f,active,value)){
   std::vector<unsigned> parent(active+1);for(unsigned i=0;i<=active;i++)parent[i]=i;
   auto root=[&](unsigned v){while(parent[v]!=v){parent[v]=parent[parent[v]];v=parent[v];}return v;};
   for(auto& c:f){unsigned r=root(std::abs(c[0]));for(int x:c){unsigned a=root(std::abs(x));if(a!=r)parent[a]=r;}}
   std::map<unsigned,Formula> parts;for(auto& c:f)parts[root(std::abs(c[0]))].push_back(c);
   if(parts.size()>1){splits++;value=1;for(auto& p:parts){unsigned count=dense(p.second);value*=solve(std::move(p.second),count,depth+1);if(value==0)break;}}
   else if(!eliminate(f,active,value)){
    std::vector<double> score(active+1);for(auto& c:f){double weight=1.0/(double(c.size())*c.size());for(int x:c)score[std::abs(x)]+=weight;}
    unsigned chosen=1;for(unsigned i=2;i<=active;i++)if(score[i]>score[chosen])chosen=i;
    Formula a=f,b=std::move(f);a.push_back({int(chosen)});b.push_back({-int(chosen)});value=solve(std::move(a),active,depth+1)+solve(std::move(b),active,depth+1);
   }
  }
  size_t bytes=k.size()+128+(value==0?0:(boost::multiprecision::msb(value)+8)/8);
  if(cache_bytes+bytes<=cache_limit){cache.emplace(std::move(k),value);cache_bytes+=bytes;}
  return value<<free;
 }
 std::string query(const int* lits,unsigned length,unsigned milliseconds){
  nodes=hits=splits=affine=eliminations=equivalences=0;deadline=Clock::now()+std::chrono::milliseconds(milliseconds);
  std::vector<int8_t> fixed(n+1);bool contradiction=false;unsigned assigned=0;
  for(unsigned i=0;i<length;i++){int x=lits[i];if(x==INT32_MIN||!x||unsigned(std::abs(x))>n)throw std::invalid_argument("assumption literal");unsigned v=std::abs(x);int val=x>0?1:-1;if(fixed[v]&&fixed[v]!=val)contradiction=true;if(!fixed[v]){assigned++;fixed[v]=val;}}
  Formula f;for(auto& c:source){std::vector<int> out;bool sat=false;for(int x:c){int a=fixed[std::abs(x)];if(a==(x>0?1:-1)){sat=true;break;}if(!a)out.push_back(x);}if(!sat)f.push_back(std::move(out));}
  cpp_int count=contradiction?cpp_int(0):solve(std::move(f),n-assigned);
  std::ostringstream out;out<<"{\"status\":\"EXACT\",\"count\":\""<<count<<"\",\"nodes\":"<<nodes<<",\"cache_hits\":"<<hits<<",\"component_splits\":"<<splits<<",\"affine_solves\":"<<affine<<",\"elimination_solves\":"<<eliminations<<",\"equivalence_variables\":"<<equivalences<<",\"cache_bytes\":"<<cache_bytes<<"}";return out.str();
 }
};
extern "C" {
 void* pp_cnf_new(const char* text,size_t bytes){try{return new Counter(text,bytes);}catch(...){return nullptr;}}
 void pp_cnf_delete(void* p){delete static_cast<Counter*>(p);}
 const char* pp_cnf_count(void* p,const int* lits,unsigned n,unsigned ms){if(!p)return "{\"status\":\"ERROR\",\"reason\":\"null counter\"}";auto& c=*static_cast<Counter*>(p);try{c.reply=c.query(lits,n,ms);}catch(const Limit& e){c.reply="{\"status\":\"WORK_LIMIT\",\"reason\":\""+std::string(e.what())+"\"}";}catch(const std::bad_alloc&){c.reply="{\"status\":\"WORK_LIMIT\",\"reason\":\"allocation failed\"}";}catch(...){c.reply="{\"status\":\"ERROR\",\"reason\":\"native counting error\"}";}return c.reply.c_str();}
}

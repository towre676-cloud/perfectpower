// Bounded binary allocation kernels. Pruning and feasibility use exact integers.
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <functional>
#include <limits>
#include <memory>
#include <numeric>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>
using U=uint64_t; using I=int64_t; using Wide=unsigned __int128;
constexpr int D=16;
struct Record { std::array<U,D> cost{}; U mask=0; I score=0; };
struct Answer { Wide count=0,ties=0; I best=0; U mask=0; };
void add(Answer &a,const Answer &b) {
 if(!b.count)return;
 if(!a.count||b.best>a.best){a.best=b.best;a.ties=b.ties;a.mask=b.mask;}
 else if(b.best==a.best){a.ties+=b.ties;a.mask=std::min(a.mask,b.mask);}
 a.count+=b.count;
}
std::string decimal(Wide x){if(!x)return "0";std::string s;while(x){s+=char('0'+x%10);x/=10;}std::reverse(s.begin(),s.end());return s;}
std::string json(const Answer&a,U visits,U records=0){std::ostringstream o;o<<"{\"count\":\""<<decimal(a.count)<<"\",\"ties\":\""<<decimal(a.ties)<<"\",\"best\":"<<a.best<<",\"mask\":\""<<a.mask<<"\",\"visits\":"<<visits<<",\"records\":"<<records<<"}";return o.str();}
char* copy(const std::string&s){auto p=(char*)std::malloc(s.size()+1);if(!p)return nullptr;std::memcpy(p,s.c_str(),s.size()+1);return p;}
struct Node {std::array<U,D> lo{},hi{};U minmask=0,maxmask=0;int begin=0,end=0,left=-1,right=-1;Answer aggregate;};
struct Model {
 int n,m,split; std::vector<Record> variables,records; std::vector<Node> tree; std::vector<U> left_masks; std::vector<Answer> left_tree; size_t left_base=0; bool indexed=false;
 std::array<U,D> lower{},upper{};U record_limit,visit_limit,visits=0; bool exhaustive=false;
 Model(int nn,int mm,const U*lo,const U*hi,const U*c,const I*p,U rl,U vl,bool full=false):n(nn),m(mm),split(full?0:nn/2),record_limit(rl),visit_limit(vl),exhaustive(full){
  if(full&&n>24)throw std::runtime_error("native exhaustive baseline supports at most 24 variables");
  if(n<1||n>42||m<1||m>D)throw std::runtime_error("MITM supports 1..42 binary variables and 1..16 resources");
  for(int k=0;k<m;k++){lower[k]=lo[k];upper[k]=hi[k];}
  for(int j=0;j<n;j++){Record v;for(int k=0;k<m;k++)v.cost[k]=c[j*m+k];v.score=p[j];v.mask=U(1)<<(n-1-j);variables.push_back(v);}
  records.reserve(std::min<U>(rl,U(1)<<(n-split)));
  Record start;generate(split,start);if(!records.empty())build(0,int(records.size()));
 }
 void tick(){if(++visits>visit_limit)throw std::runtime_error("native query node budget exceeded");}
 void generate(int j,Record&r){
  if(j==n){if(exhaustive){for(int k=0;k<m;k++)if(r.cost[k]<lower[k])return;}if(records.size()>=record_limit)throw std::runtime_error("MITM record budget exceeded");records.push_back(r);return;}
  generate(j+1,r);auto&v=variables[j];for(int k=0;k<m;k++)if(v.cost[k]>upper[k]-r.cost[k])return;
  for(int k=0;k<m;k++)r.cost[k]+=v.cost[k];r.score+=v.score;r.mask|=v.mask;
  generate(j+1,r);
  for(int k=0;k<m;k++)r.cost[k]-=v.cost[k];r.score-=v.score;r.mask^=v.mask;
 }
 int build(int begin,int end){
  int index=int(tree.size());tree.emplace_back();Node node;node.begin=begin;node.end=end;
  node.lo.fill(std::numeric_limits<U>::max());node.minmask=std::numeric_limits<U>::max();
  for(int j=begin;j<end;j++){auto&r=records[j];for(int k=0;k<m;k++){node.lo[k]=std::min(node.lo[k],r.cost[k]);node.hi[k]=std::max(node.hi[k],r.cost[k]);}node.minmask=std::min(node.minmask,r.mask);node.maxmask=std::max(node.maxmask,r.mask);add(node.aggregate,{1,1,r.score,r.mask});}
  if(end-begin>16){int axis=0;for(int k=1;k<m;k++)if((Wide(node.hi[k]-node.lo[k])*std::max<U>(1,upper[axis]))>(Wide(node.hi[axis]-node.lo[axis])*std::max<U>(1,upper[k])))axis=k;
   int mid=(begin+end)/2;std::nth_element(records.begin()+begin,records.begin()+mid,records.begin()+end,[axis,this](const Record&a,const Record&b){return exhaustive?a.mask<b.mask:a.cost[axis]<b.cost[axis];});
   node.left=build(begin,mid);node.right=build(mid,end);
  }tree[index]=node;return index;
 }
 Answer box(int index,const std::array<U,D>&lo,const std::array<U,D>&hi,U masklo,U maskhi){
  tick();const auto&node=tree[index];if(node.maxmask<masklo||node.minmask>maskhi)return {};
  bool inside=node.minmask>=masklo&&node.maxmask<=maskhi;
  for(int k=0;k<m;k++){if(node.lo[k]>hi[k]||node.hi[k]<lo[k])return {};inside=inside&&node.lo[k]>=lo[k]&&node.hi[k]<=hi[k];}
  if(inside)return node.aggregate;
  Answer a;if(node.left<0){for(int j=node.begin;j<node.end;j++){auto&r=records[j];if(r.mask<masklo||r.mask>maskhi)continue;bool ok=true;for(int k=0;k<m;k++)if(r.cost[k]<lo[k]||r.cost[k]>hi[k]){ok=false;break;}if(ok)add(a,{1,1,r.score,r.mask});}}
  else {add(a,box(node.left,lo,hi,masklo,maskhi));add(a,box(node.right,lo,hi,masklo,maskhi));}return a;
 }
 Answer query(int length,U prefix){
  visits=0;if(length<0||length>n||(length<64&&prefix>=(U(1)<<length)))throw std::runtime_error("invalid native prefix");
  if(records.empty())return {};
  U masklo=0,maskhi=(U(1)<<(n-split))-1;
  if(length>split){U right=prefix&((U(1)<<(length-split))-1);masklo=right<<(n-length);maskhi=masklo+((U(1)<<(n-length))-1);}
  if(indexed&&length<=split){
   U start=prefix<<(n-length),end=start+((U(1)<<(n-length))-1);
   size_t l=std::lower_bound(left_masks.begin(),left_masks.end(),start)-left_masks.begin();
   size_t h=std::upper_bound(left_masks.begin(),left_masks.end(),end)-left_masks.begin();
   l+=left_base;h+=left_base;Answer a;while(l<h){if(l&1)add(a,left_tree[l++]);if(h&1)add(a,left_tree[--h]);l/=2;h/=2;}return a;
  }
  bool retain=length==0;std::vector<Answer> entries;
  Record r;
  for(int j=0;j<std::min(length,split);j++)if((prefix>>(length-1-j))&1){auto&v=variables[j];for(int k=0;k<m;k++){if(v.cost[k]>upper[k]-r.cost[k])return {};r.cost[k]+=v.cost[k];}r.score+=v.score;r.mask|=v.mask;}
  Answer answer;
  std::function<void(int)>walk=[&](int j){tick();if(j==split){std::array<U,D>lo{},hi{};for(int k=0;k<m;k++){lo[k]=lower[k]>r.cost[k]?lower[k]-r.cost[k]:0;hi[k]=upper[k]-r.cost[k];}auto b=box(0,lo,hi,masklo,maskhi);b.best+=r.score;b.mask|=r.mask;add(answer,b);if(retain){left_masks.push_back(r.mask);entries.push_back(b);}return;}
   walk(j+1);auto&v=variables[j];for(int k=0;k<m;k++)if(v.cost[k]>upper[k]-r.cost[k])return;
   for(int k=0;k<m;k++)r.cost[k]+=v.cost[k];r.score+=v.score;r.mask|=v.mask;walk(j+1);
   for(int k=0;k<m;k++)r.cost[k]-=v.cost[k];r.score-=v.score;r.mask^=v.mask;
  };walk(std::min(length,split));
  if(retain){left_base=1;while(left_base<entries.size())left_base*=2;left_tree.resize(2*left_base);for(size_t i=0;i<entries.size();i++)left_tree[left_base+i]=entries[i];for(size_t i=left_base-1;i>0;i--){add(left_tree[i],left_tree[2*i]);add(left_tree[i],left_tree[2*i+1]);}indexed=true;}
  return answer;
 }
};
// Optimization only: exact fractional knapsack upper bounds for each resource.
std::string optimize(int n,int m,const U*lo,const U*hi,const U*c,const I*p,U limit){
 if(n<1||n>64||m<1||m>D)throw std::runtime_error("native optimizer dimensions exceeded");
 std::vector<int>order(n);std::iota(order.begin(),order.end(),0);
 // Ordering changes the search only; bounds and witness replay use exact integers.
 auto weight=[&](int j){Wide w=0;for(int k=0;k<m;k++)w+=Wide(c[j*m+k])*1000000/std::max<U>(1,hi[k]);return std::max<Wide>(1,w);};
 std::stable_sort(order.begin(),order.end(),[&](int a,int b){if(p[a]<=0||p[b]<=0)return p[a]>p[b];return Wide(p[a])*weight(b)>Wide(p[b])*weight(a);});
 std::vector<std::vector<int>>density(m,order);
 for(int k=0;k<m;k++)std::stable_sort(density[k].begin(),density[k].end(),[&](int a,int b){U ca=c[a*m+k],cb=c[b*m+k];if(ca==0||cb==0)return ca==0&&cb!=0;return (__int128(p[a])*cb)>(__int128(p[b])*ca);});
 std::array<U,D>used{},suffix{};std::vector<std::array<U,D>>maximum(n+1);std::vector<int>position(n);
 for(int j=0;j<n;j++)position[order[j]]=j;
 for(int j=n-1;j>=0;j--){maximum[j]=maximum[j+1];for(int k=0;k<m;k++)maximum[j][k]+=c[order[j]*m+k];}
 // Approximate coordinate descent chooses nonnegative dual coefficients only.
 // Every pruning bound below is recomputed in exact signed 128-bit arithmetic.
 std::array<long double,D> lambda{};
 for(int sweep=0;sweep<32;sweep++)for(int k=0;k<m;k++){
  std::vector<std::pair<long double,U>>breaks;
  for(int j=0;j<n;j++){U cost=c[j*m+k];if(!cost)continue;long double reduced=p[j];for(int h=0;h<m;h++)if(h!=k)reduced-=lambda[h]*c[j*m+h];if(reduced>0)breaks.emplace_back(reduced/cost,cost);}
  std::sort(breaks.begin(),breaks.end(),[](auto a,auto b){return a.first>b.first;});Wide consumed=0;lambda[k]=0;
  for(auto b:breaks){consumed+=b.second;if(consumed>hi[k]){lambda[k]=b.first;break;}}
 }
 constexpr I dual_scale=1000000;std::array<I,D> dual{};bool use_dual=true;
 for(int k=0;k<m;k++){long double scaled=lambda[k]*dual_scale;if(!(scaled>=0&&scaled<1e15L)){use_dual=false;break;}dual[k]=I(scaled);}
 std::vector<__int128>dual_positive(n+1);
 if(use_dual)for(int depth=n-1;depth>=0;depth--){int j=order[depth];__int128 reduced=__int128(p[j])*dual_scale;for(int k=0;k<m;k++)reduced-=__int128(dual[k])*c[j*m+k];dual_positive[depth]=dual_positive[depth+1]+std::max<__int128>(0,reduced);}
 Answer best;U visits=0;
 std::function<void(int,I,U)>walk=[&](int depth,I score,U mask){
  if(++visits>limit)throw std::runtime_error("optimization node budget exceeded");
  for(int k=0;k<m;k++)if(used[k]+maximum[depth][k]<lo[k])return;
  bool feasible=true;for(int k=0;k<m;k++)feasible=feasible&&used[k]>=lo[k];
  if(feasible&&(!best.count||score>best.best)){best={1,1,score,mask};}
  if(depth==n)return;
  if(use_dual&&best.count){__int128 numerator=__int128(score)*dual_scale+dual_positive[depth];for(int k=0;k<m;k++)numerator+=__int128(dual[k])*(hi[k]-used[k]);if(numerator<=__int128(best.best)*dual_scale)return;}
  I bound=score;for(int j=depth;j<n;j++)bound+=std::max<I>(0,p[order[j]]);
  for(int k=0;k<m;k++){U room=hi[k]-used[k];I b=score;for(int j:density[k]){if(position[j]<depth||p[j]<=0)continue;U cost=c[j*m+k];if(cost<=room){room-=cost;b+=p[j];}else{b+=I((Wide(p[j])*room)/cost);break;}}bound=std::min(bound,b);}
  if(best.count&&bound<=best.best)return;
  int j=order[depth];bool take=true;for(int k=0;k<m;k++)if(c[j*m+k]>hi[k]-used[k]){take=false;break;}
  if(take){for(int k=0;k<m;k++)used[k]+=c[j*m+k];walk(depth+1,score+p[j],mask|(U(1)<<(n-1-j)));for(int k=0;k<m;k++)used[k]-=c[j*m+k];}
  walk(depth+1,score,mask);
 };walk(0,0,0);return json(best,visits);
}
// Independent reference: branch on original variables and collapse feasible subcubes.
std::string recursive(int n,int m,const U*lo,const U*hi,const U*c,const I*p,U limit){
 if(n<1||n>30||m<1||m>D)throw std::runtime_error("recursive reference supports at most 30 variables");
 std::vector<std::array<U,D>>suffix(n+1);std::vector<I>positive(n+1);std::vector<int>zeros(n+1);std::vector<U>bestmask(n+1);
 for(int j=n-1;j>=0;j--){suffix[j]=suffix[j+1];for(int k=0;k<m;k++)suffix[j][k]+=c[j*m+k];positive[j]=positive[j+1]+std::max<I>(0,p[j]);zeros[j]=zeros[j+1]+(p[j]==0);bestmask[j]=bestmask[j+1]|(p[j]>0?U(1)<<(n-1-j):0);}
 std::array<U,D>used{};U visits=0;
 std::function<Answer(int,I,U)>walk=[&](int j,I score,U mask)->Answer{
  if(++visits>limit)throw std::runtime_error("recursive reference node budget exceeded");
  bool inside=true;for(int k=0;k<m;k++){if(used[k]>hi[k]||used[k]+suffix[j][k]<lo[k])return {};inside=inside&&used[k]>=lo[k]&&used[k]+suffix[j][k]<=hi[k];}
  if(inside)return {Wide(1)<<(n-j),Wide(1)<<zeros[j],score+positive[j],mask|bestmask[j]};
  if(j==n)return {};Answer a=walk(j+1,score,mask);bool take=true;for(int k=0;k<m;k++)if(c[j*m+k]>hi[k]-used[k])take=false;
  if(take){for(int k=0;k<m;k++)used[k]+=c[j*m+k];add(a,walk(j+1,score+p[j],mask|(U(1)<<(n-1-j))));for(int k=0;k<m;k++)used[k]-=c[j*m+k];}return a;
 };auto a=walk(0,0,0);return json(a,visits);
}
extern "C" {
void pp_free(char*p){std::free(p);}void pp_destroy(void*p){delete static_cast<Model*>(p);}
void* pp_create(int n,int m,const U*lo,const U*hi,const U*c,const I*p,U records,U visits,char**error){try{return new Model(n,m,lo,hi,c,p,records,visits);}catch(const std::exception&e){*error=copy(e.what());return nullptr;}}
void* pp_create_gray(int n,int m,const U*lo,const U*hi,const U*c,const I*p,U records,U visits,char**error){try{return new Model(n,m,lo,hi,c,p,records,visits,true);}catch(const std::exception&e){*error=copy(e.what());return nullptr;}}
char* pp_query(void*p,int length,U prefix){try{auto model=static_cast<Model*>(p);auto a=model->query(length,prefix);return copy(json(a,model->visits,model->records.size()));}catch(const std::exception&e){return copy(std::string("{\"error\":\"")+e.what()+"\"}");}}
char* pp_recursive(int n,int m,const U*lo,const U*hi,const U*c,const I*p,U limit){try{return copy(recursive(n,m,lo,hi,c,p,limit));}catch(const std::exception&e){return copy(std::string("{\"error\":\"")+e.what()+"\"}");}}
char* pp_optimize(int n,int m,const U*lo,const U*hi,const U*c,const I*p,U limit){try{return copy(optimize(n,m,lo,hi,c,p,limit));}catch(const std::exception&e){return copy(std::string("{\"error\":\"")+e.what()+"\"}");}}
}

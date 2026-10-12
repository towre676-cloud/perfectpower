// Bounded binary allocation kernels. Pruning and feasibility use exact integers.
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <functional>
#include <limits>
#include <memory>
#include <memory_resource>
#include <unordered_map>
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
// Exact suffix generating-function fold with whole-subcube contraction.
// A bounded PMR arena caps ALL memo keys, nodes and bucket storage.
struct Population {
 int n,m; U visits=0,hits=0,blocks=0,state_limit,visit_limit;
 std::vector<Record> items; std::vector<std::array<U,D>> totals,gcds;
 std::vector<I> positive;std::vector<int> zeros;std::vector<U> bestmask;
 std::unique_ptr<std::byte[]> arena;std::pmr::monotonic_buffer_resource pool;
 std::pmr::unordered_map<std::pmr::string,Answer> memo;
 std::vector<std::vector<std::pmr::vector<Answer>>> gf,gf_prefix;
 std::vector<std::pmr::vector<Answer>> pair_gf;int pair_start=0;U pair_queries=0;
 std::vector<std::vector<std::vector<std::pmr::vector<U>>>> implied; U eliminated=0; U gf_queries=0,setup_cells=0;
 void setup_tick(){if(++setup_cells+visits>visit_limit)throw std::runtime_error("population setup cell budget exceeded");}
 Population(int nn,int mm,U states,U visits_limit,U memory):n(nn),m(mm),state_limit(states),visit_limit(visits_limit),arena(new std::byte[memory]),pool(arena.get(),memory,std::pmr::null_memory_resource()),memo(&pool){}
 Answer walk(int depth,std::array<U,D>lo,std::array<U,D>hi){
  if(++visits+setup_cells>visit_limit)throw std::runtime_error("population visit budget exceeded");
  bool inside=true;
  for(int k=0;k<m;k++){
   if(lo[k]>totals[depth][k])return {};
   hi[k]=std::min(hi[k],totals[depth][k]);U g=gcds[depth][k];
   if(g){hi[k]-=hi[k]%g;U r=lo[k]%g;if(r)lo[k]+=g-r;}
   if(lo[k]>hi[k])return {};
   inside=inside&&lo[k]==0&&hi[k]==totals[depth][k];
  }
  if(inside){++blocks;return {Wide(1)<<(items.size()-depth),Wide(1)<<zeros[depth],positive[depth],bestmask[depth]};}
  if(!implied.empty())for(int k=0;k<m;k++)if(lo[k]==0&&hi[k]<totals[depth][k]){
   for(int h=0;h<m;h++)if(h!=k&&hi[h]<totals[depth][h]&&implied[k][h][depth][hi[h]]<=hi[k]){
    hi[k]=totals[depth][k];++eliminated;break;
   }
  }
  inside=true;for(int k=0;k<m;k++)inside=inside&&lo[k]==0&&hi[k]==totals[depth][k];
  if(inside){++blocks;return {Wide(1)<<(items.size()-depth),Wide(1)<<zeros[depth],positive[depth],bestmask[depth]};}
  int active=-1;bool single=true;
  for(int k=0;k<m;k++)if(lo[k]||hi[k]<totals[depth][k]){if(active!=-1){single=false;break;}active=k;}
  if(single&&active>=0&&!gf.empty()){
   ++gf_queries;Answer a;auto &hist=gf[active][depth];
   if(lo[active]==0)return gf_prefix[active][depth][hi[active]];
   for(U w=lo[active];w<=hi[active];w++)add(a,hist[w]);return a;
  }
  if(depth>=pair_start&&!pair_gf.empty()){
   int a=-1,b=-1;bool okay=true;
   for(int k=0;k<m;k++){if(lo[k]){okay=false;break;}if(hi[k]<totals[depth][k]){if(a<0)a=k;else if(b<0)b=k;else {okay=false;break;}}}
   if(okay&&b>=0){auto &table=pair_gf[(a*m+b)*(items.size()+1)+depth];if(!table.empty()){
    ++pair_queries;return table[hi[a]*(totals[depth][b]+1)+hi[b]];
   }}
  }
  // Varint keys avoid paying for unused resource coordinates or zero slack.
  std::array<char,1+20*D> bytes{};size_t used=0;bytes[used++]=char(depth);
  auto encode=[&](U x){while(x>=128){bytes[used++]=char((x&127)|128);x>>=7;}bytes[used++]=char(x);};
  for(int k=0;k<m;k++){encode(lo[k]);encode(hi[k]);}
  std::pmr::string key;
  if(state_limit>0)key.assign(bytes.data(),used);
  auto found=memo.find(key);if(found!=memo.end()){++hits;return found->second;}
  auto a=walk(depth+1,lo,hi);auto &v=items[depth];bool take=true;
  for(int k=0;k<m;k++)if(v.cost[k]>hi[k]){take=false;break;}
  if(take){for(int k=0;k<m;k++){lo[k]=lo[k]>v.cost[k]?lo[k]-v.cost[k]:0;hi[k]-=v.cost[k];}
   auto b=walk(depth+1,lo,hi);b.best+=v.score;b.mask|=v.mask;add(a,b);}
  if(state_limit==0)return a;
  if(memo.size()>=state_limit)throw std::runtime_error("population memo state budget exceeded");
  std::pmr::string retained(key,&pool);memo.emplace(std::move(retained),a);return a;
 }
};
std::string population(int n,int m,const U*lo,const U*hi,const U*c,const I*p,int length,U prefix,U states,U limit,U memory,int sorted,U fixed=0,U values=0,bool arbitrary=false){
 if(n<1||n>64||m<1||m>D||length<0||length>n||(length<64&&prefix>=(U(1)<<length)))throw std::runtime_error("invalid population dimensions or prefix");
 if(!limit||memory<1024||memory>U(1024)*1024*1024)throw std::runtime_error("invalid population budgets");
 if(arbitrary&&((values&~fixed)||(n<64&&(fixed>>n))))throw std::runtime_error("invalid fixed original coordinates");
 Population model(n,m,states,limit,memory);
 try {
 std::array<U,D>lower{},upper{},used{};I score=0;U mask=0;
 for(int k=0;k<m;k++){lower[k]=lo[k];upper[k]=hi[k];}
 for(int j=0;j<n;j++){
  Record v;v.mask=U(1)<<(n-1-j);v.score=p[j];for(int k=0;k<m;k++)v.cost[k]=c[j*m+k];
  if(arbitrary?(fixed&v.mask):j<length){if(arbitrary?(values&v.mask):((prefix>>(length-1-j))&1)){for(int k=0;k<m;k++){if(v.cost[k]>upper[k]-used[k])return json({},0);used[k]+=v.cost[k];}score+=v.score;mask|=v.mask;}}
  else model.items.push_back(v);
 }
 if(sorted)std::stable_sort(model.items.begin(),model.items.end(),[&](const Record&a,const Record&b){
  Wide wa=0,wb=0;for(int k=0;k<m;k++){wa+=Wide(a.cost[k])*1000000/std::max<U>(1,hi[k]);wb+=Wide(b.cost[k])*1000000/std::max<U>(1,hi[k]);}return wa>wb;});
 int size=model.items.size();model.totals.resize(size+1);model.gcds.resize(size+1);model.positive.resize(size+1);model.zeros.resize(size+1);model.bestmask.resize(size+1);
 for(int j=size-1;j>=0;j--){auto &v=model.items[j];model.totals[j]=model.totals[j+1];model.gcds[j]=model.gcds[j+1];
  for(int k=0;k<m;k++){model.totals[j][k]+=v.cost[k];model.gcds[j][k]=std::gcd(model.gcds[j][k],v.cost[k]);}
  model.positive[j]=model.positive[j+1]+std::max<I>(0,v.score);model.zeros[j]=model.zeros[j+1]+(v.score==0);model.bestmask[j]=model.bestmask[j+1]|(v.score>0?v.mask:0);
 }
 // Univariate suffix polynomials preserve coefficients and best/tie aggregates.
 bool small=true;for(int k=0;k<m;k++)small=small&&model.totals[0][k]<=10000;
 Wide gf_bytes=0;for(auto &t:model.totals)for(int k=0;k<m;k++)gf_bytes+=Wide(t[k]+1)*(2*sizeof(Answer)+(m-1)*sizeof(U));
 if(small&&gf_bytes<=memory/2){
 model.implied.resize(m);for(int k=0;k<m;k++){model.implied[k].resize(m);for(int h=0;h<m;h++)if(h!=k){
  auto &table=model.implied[k][h];table.reserve(size+1);for(int j=0;j<=size;j++)table.emplace_back(&model.pool);table[size]={0};
  for(int j=size-1;j>=0;j--){auto &v=model.items[j];auto &old=table[j+1];auto &row=table[j];row.resize(model.totals[j][h]+1);
   for(size_t b=0;b<row.size();b++){model.setup_tick();row[b]=old[std::min(b,old.size()-1)];if(b>=v.cost[h])row[b]=std::max(row[b],v.cost[k]+old[std::min(b-v.cost[h],old.size()-1)]);}
  }
 }}
 model.gf.resize(m);model.gf_prefix.resize(m);for(int k=0;k<m;k++){
  model.gf[k].reserve(size+1);for(int j=0;j<=size;j++)model.gf[k].emplace_back(&model.pool);model.gf[k][size]={{1,1,0,0}};
  for(int j=size-1;j>=0;j--){auto &v=model.items[j];auto &old=model.gf[k][j+1];auto &hist=model.gf[k][j];hist.resize(model.totals[j][k]+1);
   for(size_t w=0;w<old.size();w++){model.setup_tick();add(hist[w],old[w]);auto b=old[w];b.best+=v.score;b.mask|=v.mask;add(hist[w+v.cost[k]],b);}
  }
  model.gf_prefix[k].reserve(size+1);for(auto &hist:model.gf[k]){model.gf_prefix[k].emplace_back(hist,&model.pool);auto &row=model.gf_prefix[k].back();for(size_t w=1;w<row.size();w++){model.setup_tick();add(row[w],row[w-1]);}}
 }}
 // Two-resource truncated suffix products, bounded to the inexpensive tail.
 model.pair_start=std::max(0,size-24);model.pair_gf.reserve(m*m*(size+1));
 for(int z=0;z<m*m*(size+1);z++)model.pair_gf.emplace_back(&model.pool);
 for(int a=0;a<m;a++)for(int b=a+1;b<m;b++){
  Wide bytes=0;for(int j=model.pair_start;j<=size;j++)bytes+=Wide(model.totals[j][a]+1)*(model.totals[j][b]+1)*sizeof(Answer);
  if(bytes>memory/(2*m*m))continue;
  for(int j=size;j>=model.pair_start;j--){auto &hist=model.pair_gf[(a*m+b)*(size+1)+j];U width=model.totals[j][b]+1;hist.resize((model.totals[j][a]+1)*width);
   if(j==size){hist[0]={1,1,0,0};continue;}
   auto &v=model.items[j];auto &old=model.pair_gf[(a*m+b)*(size+1)+j+1];U oldwidth=model.totals[j+1][b]+1;
   auto at=[&](U x,U y){return old[std::min(x,model.totals[j+1][a])*oldwidth+std::min(y,model.totals[j+1][b])];};
   for(U x=0;x<=model.totals[j][a];x++)for(U y=0;y<width;y++){
    model.setup_tick();Answer out=at(x,y);if(x>=v.cost[a]&&y>=v.cost[b]){auto take=at(x-v.cost[a],y-v.cost[b]);take.best+=v.score;take.mask|=v.mask;add(out,take);}hist[x*width+y]=out;
   }
  }
 }
 for(int k=0;k<m;k++){lower[k]=lower[k]>used[k]?lower[k]-used[k]:0;upper[k]-=used[k];}
 auto a=model.walk(0,lower,upper);if(a.count){a.best+=score;a.mask|=mask;}
 auto out=json(a,model.visits,model.memo.size());out.pop_back();return out+",\"setup_cells\":"+std::to_string(model.setup_cells)+",\"cache_hits\":"+std::to_string(model.hits)+",\"accepted_subcubes\":"+std::to_string(model.blocks)+",\"eliminated_constraints\":"+std::to_string(model.eliminated)+",\"bivariate_queries\":"+std::to_string(model.pair_queries)+",\"univariate_queries\":"+std::to_string(model.gf_queries)+",\"memo_arena_bytes\":"+std::to_string(memory)+"}";
 }catch(const std::exception &error){
  std::string reason=dynamic_cast<const std::bad_alloc*>(&error)?"population memo memory budget exceeded":error.what();
  return "{\"error\":\""+reason+"\",\"visits\":"+std::to_string(model.visits)+",\"setup_cells\":"+std::to_string(model.setup_cells)+",\"records\":"+std::to_string(model.memo.size())+"}";
 }
}

extern "C" {
char* pp_population_fixed(int n,int m,const U*lo,const U*hi,const U*c,const I*p,U fixed,U values,U states,U limit,U memory){try{return copy(population(n,m,lo,hi,c,p,0,0,states,limit,memory,1,fixed,values,true));}catch(const std::exception &e){return copy(std::string("{\"error\":\"")+e.what()+"\"}");}}
char* pp_population(int n,int m,const U*lo,const U*hi,const U*c,const I*p,int length,U prefix,U states,U limit,U memory,int sorted){try{return copy(population(n,m,lo,hi,c,p,length,prefix,states,limit,memory,sorted));}catch(const std::bad_alloc&){return copy("{\"error\":\"population memo memory budget exceeded\"}");}catch(const std::exception&e){return copy(std::string("{\"error\":\"")+e.what()+"\"}");}}
void pp_free(char*p){std::free(p);}void pp_destroy(void*p){delete static_cast<Model*>(p);}
void* pp_create(int n,int m,const U*lo,const U*hi,const U*c,const I*p,U records,U visits,char**error){try{return new Model(n,m,lo,hi,c,p,records,visits);}catch(const std::exception&e){*error=copy(e.what());return nullptr;}}
void* pp_create_gray(int n,int m,const U*lo,const U*hi,const U*c,const I*p,U records,U visits,char**error){try{return new Model(n,m,lo,hi,c,p,records,visits,true);}catch(const std::exception&e){*error=copy(e.what());return nullptr;}}
char* pp_query(void*p,int length,U prefix){try{auto model=static_cast<Model*>(p);auto a=model->query(length,prefix);return copy(json(a,model->visits,model->records.size()));}catch(const std::exception&e){return copy(std::string("{\"error\":\"")+e.what()+"\"}");}}
char* pp_recursive(int n,int m,const U*lo,const U*hi,const U*c,const I*p,U limit){try{return copy(recursive(n,m,lo,hi,c,p,limit));}catch(const std::exception&e){return copy(std::string("{\"error\":\"")+e.what()+"\"}");}}
char* pp_optimize(int n,int m,const U*lo,const U*hi,const U*c,const I*p,U limit){try{return copy(optimize(n,m,lo,hi,c,p,limit));}catch(const std::exception&e){return copy(std::string("{\"error\":\"")+e.what()+"\"}");}}
}

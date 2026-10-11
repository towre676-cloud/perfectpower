// Independent exhaustive affine local score scan, both literal DNA strands.
// No seed heuristic, no pruning, no E-value calculation. O(mn) time, O(n) memory.
#include <algorithm>
#include <iostream>
#include <string>
#include <vector>
using namespace std;
int score(const string& q,const string& s) {
    const int neg=-100000000;
    vector<int> m(s.size()+1,0),d(s.size()+1,neg),i(s.size()+1,neg);
    vector<int> nm(m),nd(d),ni(i); int best=0;
    for(char a:q) {
        nm[0]=0;nd[0]=ni[0]=neg;
        for(size_t j=1;j<=s.size();++j) {
            nm[j]=max(0,max({m[j-1],d[j-1],i[j-1]})+(a==s[j-1]?2:-3));
            nd[j]=max(m[j]-7,d[j]-2);
            ni[j]=max(nm[j-1]-7,ni[j-1]-2);
            best=max({best,nm[j],nd[j],ni[j]});
        }
        m.swap(nm); d.swap(nd); i.swap(ni);
    }
    return best;
}
string reverse_complement(string s) {
    reverse(s.begin(),s.end());
    const string a="ACGTRYSWKMBDHVNU",b="TGCAYRSWMKVHDBNA";
    for(char& c:s) { auto p=a.find(c);if(p==string::npos) throw runtime_error("non-DNA letter");c=b[p]; }
    return s;
}
int main() {
    string q,s;
    while(cin>>q>>s) cout<<score(q,s)<<'\t'<<score(q,reverse_complement(s))<<'\n';
}

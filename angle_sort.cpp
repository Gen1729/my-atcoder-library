#include <iostream>
#include <string>
#include <algorithm>
#include <vector>
#include <set>
#include <cmath>
#include <iomanip>
#include <stack>
#include <queue>
#include <deque>
#include <bitset>
#include <tuple>
#include <map>
#include <bit>
#include <array>
#include <limits>
#include <type_traits>
#include <utility>
#include <functional>
#include <fstream>
#include <climits>
#include <numeric>
#include <cassert>
//#include <atcoder/all>

#define fi first
#define se second
#define rep(i,n) for(ll i=0;i<(n);i++)
#define rrep(i,n) for(ll i=(n)-1;i>=0;i--)
#define orep(i,n) for(ll i=1;i<=(n);i++)

#define nfor(i,s,n) for(ll i=(s);i<(n);i++)
#define dfor(i,s,n) for(ll i=(s)-1;i>=n;i--)
#define INF 2000000000000000000//9223372036854775807

#define all(a)  a.begin(),a.end()
#define rall(a) a.rbegin(),a.rend()

#define chmax(x,y) x = max(x,y)
#define chmin(x,y) x = min(x,y)

#define pb push_back
#define pob pop_back

#define vc vector

#define for_sz(s) (long long)(s.size())

#define YES cout << "Yes" << endl;
#define NO cout << "No" << endl;
#define YN {cout << "Yes" << endl;}else{cout << "No" << endl;}
#define dame cout << -1 << endl;

#define vc_unique(v) v.erase(unique(v.begin(), v.end()), v.end())
#define vc_remove(v,x) v.erase(remove(v.begin(), v.end(),x), v.end())
#define vc_rotate(v) rotate(v.begin(), v.begin()+1, v.end())

#define pop_cnt(s) ll(popcount(uint64_t(s)))
#define next_p(v) next_permutation(v.begin(),v.end())

#ifndef ONLINE_JUDGE
#define _GLIBCXX_DEBUG
#endif

using namespace std;
//using namespace atcoder;
using ll = long long;
using ull = unsigned long long;
using ld = long double;
using pll = pair<ll,ll>;
using vvvvvl = vector<vector<vector<vector<vector<ll> > > > >;
using vvvvl = vector<vector<vector<vector<ll> > > >;
using vvvl = vector<vector<vector<ll> > >;
using vvl = vector<vector<ll> >;
using vl = vector<ll>;
using vb = vector<bool>;
using vvb = vector<vector<bool> >;
using Graph = vector<vector<ll> >;

template<class T> using pq = priority_queue<T,vc<T>,less<T> >;
template<class T> using pq_g = priority_queue<T,vc<T>,greater<T> >;

ll dx[4] = {0,1,0,-1};ll ddx[8] = {1,1,0,-1,-1,-1,0,1};
ll dy[4] = {1,0,-1,0};ll ddy[8] = {0,1,1,1,0,-1,-1,-1};

bool out_grid(ll i, ll j, ll h, ll w){//trueならcontinueする
    return(!(0 <= i && i < h && 0 <= j && j<w));
}

ll MOD = 998244353;

ll modpow(ll x,ll y,ll m){
    ll a = x;
    a %= m;
    ll cnt = 0;
    ll ans = 1;
    while(y > 0){
        if((1ll << cnt) & y){
            y ^= (1ll << cnt);
            ans *= a;
            ans %= m;
        }
        a = a*a;
        a %= m;
        cnt++;
    }
    return ans;
}

ll npow(ll x,ll y){
    ll a = x;
    ll cnt = 0;
    ll ans = 1;
    while(y > 0){
        if((1ll << cnt) & y){
            y ^= (1ll << cnt);
            ans *= a;
        }
        a = a*a;
        cnt++;
    }
    return ans;
}

struct Edge {
    ll to;
    ll cost;
};

ll gcd(ll a, ll b) { return b?gcd(b,a%b):a;}
ll lcm(ll a, ll b) { return a/gcd(a,b)*b;}

// ai+bj=g
// Ai+Bj=gcd(A,B)なるi,jを求める
ll extgcd(ll a, ll b, ll& i, ll& j) {
    if (b == 0) { i = 1; j = 0; return a;}
    ll p = a/b, g = extgcd(b,a-b*p,j,i);
    j -= p*i;
    return g;
}

void print(ld x){printf("%.20Lf\n", x);}

////////////////////////////////////////////////////////////////
// 偏角ソート：整数ベクトル (x,y)
namespace angle_sort {

using ll = long long;
using P = pair<ll,ll>;
using i128 = __int128_t;

inline bool is_zero(const P& a){ return a.first==0 && a.second==0; }

inline i128 cross(const P& a, const P& b){
    return (i128)a.first*(i128)b.second - (i128)a.second*(i128)b.first;
}
inline i128 dot(const P& a, const P& b){
    return (i128)a.first*(i128)b.first + (i128)a.second*(i128)b.second;
}
inline i128 norm2(const P& a){
    return (i128)a.first*(i128)a.first + (i128)a.second*(i128)a.second;
}

inline bool same_dir(const P& base, const P& v){
    return cross(base, v)==0 && dot(base, v)>0;
}

inline int half_from_base(const P& v, const P& base){
    i128 s = cross(base, v);
    if(s > 0) return 0;
    if(s < 0) return 1;
    i128 c = dot(base, v);
    return (c >= 0 ? 0 : 1);
}

inline bool angle_less_from_base(const P& a, const P& b, const P& base){
    int ha = half_from_base(a, base);
    int hb = half_from_base(b, base);
    if(ha != hb) return ha < hb;

    i128 cr = cross(a, b);
    if(cr != 0) return cr > 0;

    return false;
}

enum class SameAnglePlacement { First, Last };

inline void sort_by_angle(vector<P>& pts, P base,
                          SameAnglePlacement placement = SameAnglePlacement::First){
    assert(!is_zero(base) && "base must not be (0,0)");
    for(const auto& p: pts) assert(!is_zero(p) && "point (0,0) is not allowed");

    auto is_same_as_base = [&](const P& v)->bool{
        return same_dir(base, v);
    };

    stable_sort(pts.begin(), pts.end(), [&](const P& a, const P& b){
        bool sa = is_same_as_base(a);
        bool sb = is_same_as_base(b);
        if(sa != sb){
            if(placement == SameAnglePlacement::First) return sa;
            else return !sa;
        }

        if(angle_less_from_base(a, b, base)) return true;
        if(angle_less_from_base(b, a, base)) return false;

        i128 na = norm2(a), nb = norm2(b);
        if(na != nb) return na < nb;

        if(a.first != b.first) return a.first < b.first;
        return a.second < b.second;
    });
}

} // namespace angle_sort


// 引数には(x,y)としてvector<pair<ll,ll>>を渡す
// 基準点決め、その偏角を基準にそこから半時計周りにソートする
// 基準となる偏角と同じ偏角を持つ頂点をソートした列の最初に入れるか最後に入れるかを引数で指する
// (0,0)を受け取ったらassertで知らせる
// 同じ偏角の点では絶対値の昇順で並べる
int main() {
    vector<pair<long long,long long>> v = {{1,0},{2,0},{0,1},{-1,0},{0,-1},{3,0}};
    // 基準を (1,0) 
    angle_sort::sort_by_angle(v, {1,0}, angle_sort::SameAnglePlacement::First);

    for(auto [x,y] : v){
        cout << x << " " << y << endl;
    }

    // v は (1,0),(2,0),(3,0),(0,1),(-1,0),(0,-1) のように並ぶ（同偏角は距離昇順）
}
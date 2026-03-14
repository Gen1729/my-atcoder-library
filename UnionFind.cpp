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
#include <functional>
#include <fstream>
#include <climits>
#include <numeric>
#include <atcoder/all>

#define fi first
#define se second
#define rep(i,n) for(ll i=0;i<(n);i++)
#define rrep(i,n) for(ll i=(n)-1;i>=0;i--)
#define orep(i,n) for(ll i=1;i<=(n);i++)

#define nfor(i,s,n) for(ll i=(s);i<(n);i++)
#define dfor(i,s,n) for(ll i=(s)-1;i>=n;i--)
#define INF 2e18//9223372036854775807

#define all(a)  a.begin(),a.end()
#define rall(a) a.rbegin(),a.rend()

#define chmax(x,y) x = max(x,y)
#define chmin(x,y) x = min(x,y)

#define pb push_back
#define pob pop_back

#define vc vector

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
using ll = long long;
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

void print(ld x){printf("%.20Lf\n", x);}

////////////////////////////////////////////////////////////////
struct UnionFind {
	vector<ll> par; // 親ノード
	vector<ll> rank; // ランク
	vector<ll> sz;

	UnionFind(ll n = 1) {
		init(n);
	}

	void init(ll n = 1) {
		par.resize(n); rank.resize(n); sz.resize(n,1);
        rep(i,n) par[i] = i, rank[i] = 0;
	}

    ll root(ll x) {
		if (par[x] == x) {
			return x;
		}
		else {
			ll r = root(par[x]);
			return par[x] = r;
		}
	}

	bool issame(ll x, ll y) {
		return root(x) == root(y);
	}

	bool merge(ll x, ll y) {
		x = root(x); y = root(y);
		if (x == y) return false;
        if (rank[x] < rank[y]) swap(x, y);
		if (rank[x] == rank[y]) ++rank[x];
		par[y] = x;
		sz[x] += sz[y];
		return true;
	}

	ll forsize(ll x){
		x = root(x);
		return sz[x];
	}
};

// struct UnionFind {
//     vc<ll> par; // par[i]:iの親の番号　(例) par[3] = 2 : 3の親が2
//     vc<ll> t_size;
    
//     UnionFind(ll N) : par(N),t_size(N) { //最初は全てが根であるとして初期化
//         rep(i,N) par[i] = i;
//         t_size.resize(N,1);
//     }
    
//     ll root(ll x) { // データxが属する木の根を再帰で得る：root(x) = {xの木の根}
//         if (par[x] == x) return x;
//         return par[x] = root(par[x]);//経路圧縮
//     }
    
//     void unite(ll x, ll y) { // xとyの木を併合
//         ll rx = root(x); //xの根をrx
//         ll ry = root(y); //yの根をry
//         if (rx == ry) return; //xとyの根が同じ(=同じ木にある)時はそのまま
//         // union by size (小さいほうが子になる）
//         if (t_size[rx] > t_size[ry]){
//             t_size[rx] += t_size[ry];
//             par[ry] = rx;
//         }else{
//             t_size[ry] += t_size[rx];
//             par[rx] = ry;
//         }
//     }
    
//     bool isSame(ll x, ll y) { // 2つのデータx, yが属する木が同じならtrueを返す
//         ll rx = root(x);
//         ll ry = root(y);
//         return rx == ry;
//     }

//     ll size(int i)
// 	{
// 		return t_size[root(i)];
// 	}
// };

template<class Abel> struct WeightUnionFind {
	vector<ll> par;
	vector<ll> rank;
	vector<Abel> diff_weight;

	WeightUnionFind(ll n = 1, Abel SUM_UNITY = 0) {
		init(n, SUM_UNITY);
	}

	void init(ll n = 1, Abel SUM_UNITY = 0) {
		par.resize(n); rank.resize(n); diff_weight.resize(n);
		rep(i,n) par[i] = i, rank[i] = 0, diff_weight[i] = SUM_UNITY;
	}

	int root(ll x) {
		if (par[x] == x) {
			return x;
		}
		else {
			ll r = root(par[x]);
			diff_weight[x] += diff_weight[par[x]];
			return par[x] = r;
		}
	}

	Abel weight(ll x) {
		root(x);
		return diff_weight[x];
	}

	bool issame(ll x, ll y) {
		return root(x) == root(y);
	}

	bool merge(ll x, ll y, Abel w) {
		w += weight(x); w -= weight(y);
		x = root(x); y = root(y);
		if (x == y) return false;
		if (rank[x] < rank[y]) swap(x, y), w = -w;
		if (rank[x] == rank[y]) ++rank[x];
		par[y] = x;
		diff_weight[y] = w;
		return true;
	}

	Abel diff(ll x, ll y) {
		return weight(y) - weight(x);
	}
};

// Abelは型指定
// merge(x, y, w): weight(y) = weight(x) + wとなるようにxとyをマージします。これは、xとyを含むそれぞれのグループを結合し、それらの間にwという関係性を設定することを意味します。
// issame(x, y): xとyが同じグループにいるかどうかを判定します。これは、共通のルートノードを持つかどうかで判断されます。
// diff(x, y): xとyが同じグループにいるとき、weight(y) - weight(x)を返します。
// なお、xとyがすでに同じグループにいるときにmerge(x, y, w)を呼ぶ場合や、xとyが同じグループにいないときにdiff(x, y)を呼ぶ場合は未定義動作となり、その処理はライブラリの実装者に委ねられます。

int main() {
    int N;
    cin >> N;
    UnionFind tree(N);

    WeightUnionFind<ll> uf(N);
    
    return 0;
}
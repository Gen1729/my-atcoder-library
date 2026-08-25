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
#include <cstdbool>
#include <cstdint>
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

template<class T>
void cutoutV(vc<vc<T>> &G, ll H, ll W, ll mx, ll Mx, ll my, ll My){
    if(!(0 <= mx && mx < H && 0 < Mx && Mx <= H && mx < Mx))return;
    if(!(0 <= my && my < H && 0 < My && My <= H && my < My))return;

    rep(i,Mx - mx)rep(j,My - my){
        G[i][j] = G[i + mx][j + my];
    }
    G.resize(Mx - mx, vc<T>(My - my));
    return;
}

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
// ai+bj=gcd(a,b)なるi,jを求める
ll extgcd(ll a, ll b, ll& i, ll& j) {
    if (b == 0) { i = 1; j = 0; return a;}
    ll p = a/b, g = extgcd(b,a-b*p,j,i);
    j -= p*i;
    return g;
}

vl topological_sort(const vvl& G){
    ll N = (ll)G.size();
    vl indeg(N, 0), order;
    queue<ll> que;
    rep(u, N){
        for(ll v : G[u]) indeg[v]++;
    }
    rep(i, N){
        if(indeg[i] == 0) que.push(i);
    }
    while(!que.empty()){
        ll u = que.front();
        que.pop();
        order.pb(u);
        for(ll v : G[u]){
            indeg[v]--;
            if(indeg[v] == 0) que.push(v);
        }
    }
    return order;
}

ll MOD = 998244353;

void print(ld x){printf("%.20Lf\n", x);}

//using mint = modint998244353;
////////////////////////////////////////////////////////////////

struct HLD {
    ll n;
    vector<vector<ll>> adj;
    
    // 記事で言及されている配列
    vector<ll> vertex; // 行きがけ順で i 番目に訪れる頂点
    vector<ll> id;     // v の行きがけ順で何番目に訪れるか
    vector<ll> head;   // v を通る heavy path の先頭（最も根側にある頂点）
    vector<ll> depth;  // 頂点 v の深さ
    vector<ll> parent; // 頂点 v の親
    
    vector<ll> sub_size; // 部分木の頂点数

    HLD(ll n) : n(n), adj(n), vertex(n), id(n), head(n), depth(n), parent(n), sub_size(n) {}

    // 無向辺の追加
    void add_edge(ll u, ll v) {
        adj[u].push_back(v);
        adj[v].push_back(u);
    }

    // 構築（デフォルトでは頂点0を根とする）
    void build(ll root = 0) {
        dfs_sz(root, -1, 0);
        ll time = 0;
        dfs_hld(root, -1, root, time);
    }

    // LCA（最小共通祖先）クエリ
    ll lca(ll u, ll v) {
        while (head[u] != head[v]) {
            if (id[u] > id[v]) {
                u = parent[head[u]];
            } else {
                v = parent[head[v]];
            }
        }
        return depth[u] < depth[v] ? u : v;
    }

private:
    // heavy childを求める
    void dfs_sz(ll v, ll p, ll d) {
        parent[v] = p;
        depth[v] = d;
        sub_size[v] = 1;

        if (p != -1) {
            for (size_t i = 0; i < adj[v].size(); ++i) {
                if (adj[v][i] == p) {
                    swap(adj[v][i], adj[v].back());
                    adj[v].pop_back();
                    break;
                }
            }
        }
        
        for (ll &u : adj[v]) {
            dfs_sz(u, v, d + 1);
            sub_size[v] += sub_size[u];
            if (sub_size[u] > sub_size[adj[v][0]]) {
                swap(u, adj[v][0]);
            }
        }
    }

    // vertex, id, head を計算する
    void dfs_hld(ll v, ll p, ll h, ll &time) {
        vertex[time] = v;
        id[v] = time++;
        head[v] = h;

        for (ll u : adj[v]) {
            if (u == adj[v][0]) {
                dfs_hld(u, v, h, time);
            } else {
                dfs_hld(u, v, u, time);
            }
        }
    }
};

int main() {
    // 頂点数 6 の木を作成
    ll n = 6;
    HLD hld(n);
    
    /* 
       木の構造:
             0
           /   \
          1     2
         / \
        3   4
             \
              5
    */
    hld.add_edge(0, 1);
    hld.add_edge(0, 2);
    hld.add_edge(1, 3);
    hld.add_edge(1, 4);
    hld.add_edge(4, 5);
    
    // 頂点 0 を根として HLD を構築
    hld.build(0);
    
    // LCA機能の利用例
    cout << "--- LCA クエリのテスト ---\n";
    cout << "LCA(3, 5) = " << hld.lca(3, 5) << " (期待値: 1)\n";
    cout << "LCA(2, 5) = " << hld.lca(2, 5) << " (期待値: 0)\n";
    cout << "LCA(4, 1) = " << hld.lca(4, 1) << " (期待値: 1)\n\n";
    
    // 構築された配列の中身を確認してパスクエリにどう活用できるか見る
    cout << "--- HLD 配列の確認 ---\n";
    cout << "v : id | head | depth | parent\n";
    for (ll i = 0; i < n; ++i) {
        cout << i << " : "
                  << hld.id[i] << "  | "
                  << hld.head[i] << "    | "
                  << hld.depth[i] << "     | "
                  << hld.parent[i] << "\n";
    }

    cout << "\n--- 行きがけ順 (vertex 配列) ---\n";
    for (ll i = 0; i < n; ++i) {
        cout << "vertex[" << i << "] = " << hld.vertex[i] << "\n";
    }

    return 0;
}
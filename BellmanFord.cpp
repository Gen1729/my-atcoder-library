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
/**
 * ベルマンフォード法による最短経路計算
 * * @param G グラフの隣接リスト (to, cost)
 * @param start 始点頂点
 * @param dist 最短距離を格納する配列（参照渡し）
 * @return true: 負の閉路が存在する, false: 存在しない
 */
bool bellman_ford(const vector<vector<pair<ll, ll>>>& G, int start, vector<ll>& dist) {
    int V = G.size();
    dist.assign(V, INF);
    dist[start] = 0;

    // 負の閉路がない場合、最短経路の遷移回数は最大でも V-1 回
    // 負の閉路の検出も含めて V 回ループを回す
    for (int i = 0; i < V; ++i) {
        bool updated = false;
        
        // 全ての辺を走査して緩和処理を行う
        for (int from = 0; from < V; ++from) {
            if (dist[from] == INF) continue; // まだ到達していない頂点はスキップ
            
            for (const auto& edge : G[from]) {
                ll to = edge.first;
                ll cost = edge.second;
                
                if (dist[to] > dist[from] + cost) {
                    dist[to] = dist[from] + cost;
                    updated = true;
                    
                    // V 回目のループでも更新がある場合は、負の閉路が存在する
                    if (i == V - 1) {
                        return true; 
                    }
                }
            }
        }
        
        // 更新が一度も発生しなければ、その時点で最短距離が確定している
        if (!updated) break;
    }
    
    return false;
}

int main() {
    // 頂点数と辺の数
    int V = 4;
    int M = 5;
    
    // グラフの初期化
    vector<vector<pair<ll,ll>>> G(V);
    
    // 辺の追加 (from, to, cost)
    // ここでは手動で有向グラフを構築しています
    G[0].push_back({1, 2});   // 0 -> 1 (コスト 2)
    G[0].push_back({2, 5});   // 0 -> 2 (コスト 5)
    G[1].push_back({2, 1});   // 1 -> 2 (コスト 1)
    G[1].push_back({3, 4});   // 1 -> 3 (コスト 4)
    G[2].push_back({3, -2});  // 2 -> 3 (コスト -2) ※負の辺

    // 最短距離を格納する配列
    vector<ll> dist;
    
    // 始点を 0 としてベルマンフォードを実行
    int start_node = 0;
    bool has_negative_cycle = bellman_ford(G, start_node, dist);
    
    if (has_negative_cycle) {
        cout << "グラフ内に負の閉路が検出されました！" << endl;
    } else {
        cout << "始点 " << start_node << " からの最短距離:" << endl;
        for (int i = 0; i < V; ++i) {
            if (dist[i] == INF) {
                cout << "頂点 " << i << ": 到達不可能 (INF)" << endl;
            } else {
                cout << "頂点 " << i << ": " << dist[i] << endl;
            }
        }
    }
    
    return 0;
}
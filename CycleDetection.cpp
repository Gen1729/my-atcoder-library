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

// https://github.com/Gen1729/my-atcoder-library/blob/main/CycleDetection.cpp
// ========== 無向グラフのサイクル検出 ==========
class UndirectedGraph {
private:
    ll n;
    vvl adj;
    vb visited;
    vl parent;
    vl cycle;
    
    // DFSによるサイクル検出
    bool dfs(ll v, ll par) {
        visited[v] = true;
        parent[v] = par;
        
        for (ll u : adj[v]) {
            if (!visited[u]) {
                if (dfs(u, v)) return true;
            }
            // 親以外の訪問済みノードに到達した場合、サイクル
            else if (u != par) {
                // サイクルを復元
                cycle.clear();
                cycle.push_back(u);
                ll curr = v;
                while (curr != u) {
                    cycle.push_back(curr);
                    curr = parent[curr];
                }
                cycle.push_back(u);
                return true;
            }
        }
        return false;
    }
    
public:
    UndirectedGraph(ll n) : n(n), adj(n), visited(n, false), parent(n, -1) {}
    
    void addEdge(ll u, ll v) {
        adj[u].push_back(v);
        adj[v].push_back(u);
    }
    
    bool hasCycle() {
        fill(visited.begin(), visited.end(), false);
        fill(parent.begin(), parent.end(), -1);
        cycle.clear();
        
        // 全ての連結成分を確認
        for (ll i = 0; i < n; i++) {
            if (!visited[i]) {
                if (dfs(i, -1)) return true;
            }
        }
        return false;
    }
    
    vl getCycle() {
        return cycle;
    }
};

// ========== 有向グラフのサイクル検出 ==========
class DirectedGraph {
private:
    ll n;
    vvl adj;
    vl color; // 0: 未訪問, 1: 訪問中, 2: 訪問済み
    vl parent;
    vl cycle;
    
    // DFSによるサイクル検出（3色法）
    bool dfs(ll v) {
        color[v] = 1; // 訪問中
        
        for (ll u : adj[v]) {
            if (color[u] == 1) {
                // 訪問中のノードに到達 → バックエッジ → サイクル
                // サイクルを復元
                cycle.clear();
                cycle.push_back(u);
                ll curr = v;
                while (curr != u) {
                    cycle.push_back(curr);
                    curr = parent[curr];
                }
                cycle.push_back(u);
                reverse(cycle.begin(), cycle.end());
                return true;
            }
            if (color[u] == 0) {
                parent[u] = v;
                if (dfs(u)) return true;
            }
        }
        
        color[v] = 2; // 訪問済み
        return false;
    }
    
public:
    DirectedGraph(ll n) : n(n), adj(n), color(n, 0), parent(n, -1) {}
    
    void addEdge(ll u, ll v) {
        adj[u].push_back(v);
    }
    
    bool hasCycle() {
        fill(color.begin(), color.end(), 0);
        fill(parent.begin(), parent.end(), -1);
        cycle.clear();
        
        for (ll i = 0; i < n; i++) {
            if (color[i] == 0) {
                if (dfs(i)) return true;
            }
        }
        return false;
    }
    
    vl getCycle() {
        return cycle;
    }
    
    // トポロジカルソートを使ったサイクル検出（Kahn's Algorithm）
    bool hasCycleKahn() {
        vl indeg(n, 0);
        
        // 入次数を計算
        for (ll i = 0; i < n; i++) {
            for (ll j : adj[i]) {
                indeg[j]++;
            }
        }
        
        queue<ll> q;
        for (ll i = 0; i < n; i++) {
            if (indeg[i] == 0) q.push(i);
        }
        
        ll cnt = 0;
        while (!q.empty()) {
            ll v = q.front();
            q.pop();
            cnt++;
            
            for (ll u : adj[v]) {
                indeg[u]--;
                if (indeg[u] == 0) q.push(u);
            }
        }
        
        // 全てのノードが処理されなければサイクルあり
        return cnt != n;
    }
};

// ========== Union-Find (無向グラフ用の別解法) ==========
class UnionFind {
private:
    vl par, rank;
    
public:
    UnionFind(ll n) : par(n), rank(n, 0) {
        iota(par.begin(), par.end(), 0);
    }
    
    ll find(ll x) {
        if (par[x] == x) return x;
        return par[x] = find(par[x]);
    }
    
    bool unite(ll x, ll y) {
        x = find(x);
        y = find(y);
        if (x == y) return false; // 既に同じ集合 → サイクル
        
        if (rank[x] < rank[y]) swap(x, y);
        par[y] = x;
        if (rank[x] == rank[y]) rank[x]++;
        return true;
    }
};

bool hasCycleUF(ll n, vc<pll>& edges) {
    UnionFind uf(n);
    for (auto [u, v] : edges) {
        if (!uf.unite(u, v)) return true;
    }
    return false;
}

// ========== テストコード ==========
ll main() {
    cout << "=== 無向グラフのサイクル検出 ===" << endl;
    
    // サイクルあり
    UndirectedGraph ug1(4);
    ug1.addEdge(0, 1);
    ug1.addEdge(1, 2);
    ug1.addEdge(2, 0);
    ug1.addEdge(2, 3);
    if (ug1.hasCycle()) {
        cout << "グラフ1: サイクルあり" << endl;
        cout << "  サイクル: ";
        for (ll v : ug1.getCycle()) cout << v << " ";
        cout << endl;
    } else {
        cout << "グラフ1: サイクルなし" << endl;
    }
    
    // サイクルなし
    UndirectedGraph ug2(4);
    ug2.addEdge(0, 1);
    ug2.addEdge(1, 2);
    ug2.addEdge(2, 3);
    if (ug2.hasCycle()) {
        cout << "グラフ2: サイクルあり" << endl;
        cout << "  サイクル: ";
        for (ll v : ug2.getCycle()) cout << v << " ";
        cout << endl;
    } else {
        cout << "グラフ2: サイクルなし" << endl;
    }
    
    cout << "\n=== 有向グラフのサイクル検出 ===" << endl;
    
    // サイクルあり
    DirectedGraph dg1(4);
    dg1.addEdge(0, 1);
    dg1.addEdge(1, 2);
    dg1.addEdge(2, 0);
    dg1.addEdge(2, 3);
    if (dg1.hasCycle()) {
        cout << "グラフ1: サイクルあり" << endl;
        cout << "  サイクル: ";
        for (ll v : dg1.getCycle()) cout << v << " ";
        cout << endl;
    } else {
        cout << "グラフ1: サイクルなし" << endl;
    }
    cout << "  Kahnアルゴリズム: " << (dg1.hasCycleKahn() ? "サイクルあり" : "サイクルなし") << endl;
    
    // サイクルなし (DAG)
    DirectedGraph dg2(4);
    dg2.addEdge(0, 1);
    dg2.addEdge(1, 2);
    dg2.addEdge(2, 3);
    if (dg2.hasCycle()) {
        cout << "グラフ2: サイクルあり" << endl;
        cout << "  サイクル: ";
        for (ll v : dg2.getCycle()) cout << v << " ";
        cout << endl;
    } else {
        cout << "グラフ2: サイクルなし" << endl;
    }
    cout << "  Kahnアルゴリズム: " << (dg2.hasCycleKahn() ? "サイクルあり" : "サイクルなし") << endl;
    
    // 複雑なサイクルの例
    cout << "\n=== 複雑なサイクルの例 ===" << endl;
    DirectedGraph dg3(6);
    dg3.addEdge(0, 1);
    dg3.addEdge(1, 2);
    dg3.addEdge(2, 3);
    dg3.addEdge(3, 4);
    dg3.addEdge(4, 1); // 1→2→3→4→1 のサイクル
    dg3.addEdge(3, 5);
    if (dg3.hasCycle()) {
        cout << "グラフ3: サイクルあり" << endl;
        cout << "  サイクル: ";
        for (ll v : dg3.getCycle()) cout << v << " ";
        cout << endl;
    }
    
    cout << "\n=== Union-Findによる無向グラフのサイクル検出 ===" << endl;
    vc<pll> edges1 = {{0, 1}, {1, 2}, {2, 0}};
    cout << "エッジリスト1: " << (hasCycleUF(3, edges1) ? "サイクルあり" : "サイクルなし") << endl;
    
    vc<pll> edges2 = {{0, 1}, {1, 2}, {2, 3}};
    cout << "エッジリスト2: " << (hasCycleUF(4, edges2) ? "サイクルあり" : "サイクルなし") << endl;
    
    return 0;
}
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
#include <cassert>
//#include <atcoder/all>

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
//using namespace atcoder;
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

struct Edge {
    ll to;
    ll cost;
};

////////////////////////////////////////////////////////////////
// LCA (Binary Lifting)
// - lca(u,v): 最小共通祖先
// - dist(u,v): 辺数距離
////////////////////////////////////////////////////////////////
struct LCA {
    ll n, LOG;
    vvl parent; // parent[k][v] = v の 2^k 個上
    vl depth;
    vvl g;

    LCA() {}
    LCA(const vvl& graph, ll root = 0) {
        build(graph, root);
    }

    void build(const vvl& graph, ll root = 0) {
        g = graph;
        n = (ll)g.size();
        LOG = 1;
        while ((1 << LOG) <= n) LOG++;

        parent.assign(LOG, vl(n, -1));
        depth.assign(n, -1);

        // iterative DFS/BFS で深さと親(2^0)を計算
        queue<ll> q;
        depth[root] = 0;
        parent[0][root] = -1;
        q.push(root);

        while (!q.empty()) {
            ll v = q.front(); q.pop();
            for (ll to : g[v]) {
                if (to == parent[0][v]) continue;
                if (depth[to] != -1) continue;
                depth[to] = depth[v] + 1;
                parent[0][to] = v;
                q.push(to);
            }
        }

        // doubling table
        for (ll k = 0; k + 1 < LOG; k++) {
            for (ll v = 0; v < n; v++) {
                if (parent[k][v] == -1) parent[k+1][v] = -1;
                else parent[k+1][v] = parent[k][ parent[k][v] ];
            }
        }
    }

    ll lca(ll u, ll v) const {
        if (depth[u] < depth[v]) swap(u, v);

        // u を v と同じ深さまで上げる
        ll diff = depth[u] - depth[v];
        for (ll k = 0; k < LOG; k++) {
            if (diff & (1 << k)) u = parent[k][u];
        }

        if (u == v) return u;

        // 同時に上げる
        for (ll k = LOG - 1; k >= 0; k--) {
            if (parent[k][u] != parent[k][v]) {
                u = parent[k][u];
                v = parent[k][v];
            }
        }
        return parent[0][u];
    }

    ll dist(ll u, ll v) const {
        ll w = lca(u, v);
        return depth[u] + depth[v] - 2 * depth[w];
    }
};

int main() {
    ll N;
    cin >> N;

    vvl g(N);
    for (ll i = 0; i < N - 1; i++) {
        ll a, b;
        cin >> a >> b;
        --a; --b;
        g[a].push_back(b);
        g[b].push_back(a);
    }

    ll root = 0;
    LCA lca(g, root);

    ll Q;
    cin >> Q;
    while (Q--) {
        ll u, v;
        cin >> u >> v;
        --u; --v;

        ll w = lca.lca(u, v);
        ll d = lca.dist(u, v);

        cout << (w + 1) << " " << d << "\n";
    }

    return 0;
}
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
// Ai+Bj=gcd(A,B)なるi,jを求める
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

// https://github.com/Gen1729/my-atcoder-library/blob/main/%20CentroidDecomposition.cpp
// 共通部分 再帰的重心分解
struct CentroidDecomposition {
    int N;
    vector<vector<int>> G;
    vector<bool> removed;
    vector<int> sub;
    vector<int> parent, depth;

    CentroidDecomposition(int n)
        : N(n),
          G(n),
          removed(n, false),
          sub(n),
          parent(n, -1),
          depth(n, 0) {}

    void add_edge(int u, int v) {
        G[u].push_back(v);
        G[v].push_back(u);
    }

    // 部分木サイズ
    int dfs_size(int v, int p = -1) {
        sub[v] = 1;
        for (int to : G[v]) {
            if (to == p || removed[to]) continue;
            sub[v] += dfs_size(to, v);
        }
        return sub[v];
    }

    // 重心探索
    int dfs_centroid(int v, int p, int total) {
        for (int to : G[v]) {
            if (to == p || removed[to]) continue;
            if (sub[to] > total / 2)
                return dfs_centroid(to, v, total);
        }
        return v;
    }

    int centroid(int root) {
        int total = dfs_size(root);
        return dfs_centroid(root, -1, total);
    }

    template<class F>
    void decompose(int root, F&& process, int par = -1, int dep = 0) {
        int c = centroid(root);

        process(c, par, dep);

        removed[c] = true;
        parent[c] = par;
        depth[c] = dep;

        for (int to : G[c]) {
            if (removed[to]) continue;
            decompose(to, process, c, dep + 1);
        }
    }
};

///////////////////////////////////////////////////////////////////////////

// パターン１.距離列挙型
struct DistanceEnumeration {
    CentroidDecomposition cd;
    long long ans = 0;
    int K;

    DistanceEnumeration(int n, int k)
        : cd(n), K(k) {}

    void add_edge(int u, int v) {
        cd.add_edge(u, v);
    }

    vector<int> dist;

    // 部分木内距離列挙
    void dfs_dist(int v, int p, int d) {
        dist.push_back(d);

        for (int to : cd.G[v]) {
            if (to == p || cd.removed[to]) continue;
            dfs_dist(to, v, d + 1);
        }
    }

    void solve() {
        
        // process内を実装する
        // 重心:c
        // cの親:par(親なしなら-1)
        // cの再帰の深さ:dep(0から)

        // 例：距離 ≤ K の頂点組数
        auto process = [&](int c, int par, int dep) {
            multiset<int> S;
            S.insert(0); // 重心自身

            for (int to : cd.G[c]) {
                if (cd.removed[to]) continue;

                dist.clear();
                dfs_dist(to, c, 1);

                // この部分木と以前部分木とのペア
                for (int d : dist) {
                    ans += distance(
                        S.begin(),
                        S.upper_bound(K - d)
                    );
                }

                // 後から追加
                for (int d : dist) {
                    S.insert(d);
                }
            }
        };

        // 再帰的に重心分解を行う
        cd.decompose(0, process);
    }
};
// パターン１.距離列挙型
int main() {
    int N, K;
    cin >> N >> K;

    DistanceEnumeration solver(N, K);

    for (int i = 0; i < N - 1; i++) {
        int u, v;
        cin >> u >> v;
        --u, --v;
        solver.add_edge(u, v);
    }

    solver.solve();

    cout << solver.ans << endl;
}

// パターン２.最近点更新型
struct NearestPoint {
    CentroidDecomposition cd;

    vector<vector<pair<int,int>>> path;
    vector<int> best;

    NearestPoint(int n)
        : cd(n), path(n), best(n, (int)1e9) {}

    void add_edge(int u, int v) {
        cd.add_edge(u, v);
    }

    void dfs_path(int v, int p, int d, int cent) {
        path[v].push_back({cent, d});

        for (int to : cd.G[v]) {
            if (to == p || cd.removed[to]) continue;
            dfs_path(to, v, d + 1, cent);
        }
    }

    // 例：https://codeforces.com/problemset/problem/342/E
    void build() {
        auto process = [&](int c, int par, int dep) {
            path[c].push_back({c, 0});

            for (int to : cd.G[c]) {
                if (cd.removed[to]) continue;
                dfs_path(to, c, 1, c);
            }
        };

        cd.decompose(0, process);
    }

    // 赤点追加
    void update(int v) {
        for (auto [c, d] : path[v]) {
            best[c] = min(best[c], d);
        }
    }

    // 最近赤距離
    int query(int v) {
        int ans = 1e9;

        for (auto [c, d] : path[v]) {
            ans = min(ans, best[c] + d);
        }

        return ans;
    }
};
// パターン２.最近点更新型
int main(){
    ll N;
    cin >> N;
    NearestPoint solver(N);

    solver.build();

    solver.update(0); // 頂点0を赤

    cout << solver.query(5) << endl; // 5からの最近点距離を出力
}

// パターン３.パス条件カウント型
// パターン１の一般化
struct PathCondition {
    CentroidDecomposition cd;
    long long ans = 0;
    int K;
    vector<int> val;

    PathCondition(int n, int k)
        : cd(n), K(k), val(n) {}

    void add_edge(int u, int v) {
        cd.add_edge(u, v);
    }

    vector<int> sums;

    // 部分木和列挙
    void dfs_sum(int v, int p, int s) {
        sums.push_back(s);

        for (int to : cd.G[v]) {
            if (to == p || cd.removed[to]) continue;
            dfs_sum(to, v, s + val[to]);
        }
    }

    void solve() {
        // 例：「パス和 = K」
        auto process = [&](int c, int par, int dep) {
            map<int,int> cnt;
            cnt[val[c]]++;

            for (int to : cd.G[c]) {
                if (cd.removed[to]) continue;

                sums.clear();
                dfs_sum(to, c, val[c] + val[to]);

                // 条件を満たすものを数える
                for (int x : sums) {
                    ans += cnt[K - x];
                }

                // 後追加
                for (int x : sums) {
                    cnt[x]++;
                }
            }
        };

        cd.decompose(0, process);
    }
};
// パターン３.パス条件カウント型
int main(){
    int N, K;
    cin >> N >> K;

    PathCondition solver(N, K);

    for (int i = 0; i < N; i++) {
        cin >> solver.val[i];
    }

    for (int i = 0; i < N - 1; i++) {
        int u, v;
        cin >> u >> v;
        --u, --v;
        solver.add_edge(u, v);
    }

    solver.solve();

    cout << solver.ans << endl;
}
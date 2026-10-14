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
#include <random>
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

// https://github.com/Gen1729/my-atcoder-library/blob/main/%20automaton.cpp
//================================================================
// Automaton DP Library
//================================================================

// And<A, B>
// 2つのDFAの両方を受理する場合に受理
template<class A, class B>
struct And {
    using State = pair<typename A::State, typename B::State>;
    using Alphabet = typename A::Alphabet;
    A a; B b;
    And(A a, B b) : a(a), b(b) {}
    State init() const { return {a.init(), b.init()}; }
    State next(const State& q, const Alphabet& c) const {
        return {a.next(q.fi, c), b.next(q.se, c)};
    }
    bool accept(const State& q) const {
        return a.accept(q.fi) && b.accept(q.se);
    }
};

// Or<A, B>
// 2つのDFAのいずれかを受理する場合に受理
template<class A, class B>
struct Or {
    using State = pair<typename A::State, typename B::State>;
    using Alphabet = typename A::Alphabet;
    A a; B b;
    Or(A a, B b) : a(a), b(b) {}
    State init() const { return {a.init(), b.init()}; }
    State next(const State& q, const Alphabet& c) const {
        return {a.next(q.fi, c), b.next(q.se, c)};
    }
    bool accept(const State& q) const {
        return a.accept(q.fi) || b.accept(q.se);
    }
};

// Not<A>
// DFA Aが受理「しない」場合に受理
template<class A>
struct Not {
    using State = typename A::State;
    using Alphabet = typename A::Alphabet;
    A a;
    Not(A a) : a(a) {}
    State init() const { return a.init(); }
    State next(const State& q, const Alphabet& c) const {
        return a.next(q, c);
    }
    bool accept(const State& q) const {
        return !a.accept(q);
    }
};

// Le (Less than or Equal)
struct Le {
    using State = int;
    using Alphabet = ll;
    vector<Alphabet> limit;
    int less_state, greater_state;
    Le(const vector<Alphabet>& limit) : limit(limit) {
        less_state = limit.size() + 1;
        greater_state = limit.size() + 2;
    }
    Le(const string& s) {
        for(char c : s) limit.pb(c - '0');
        less_state = limit.size() + 1;
        greater_state = limit.size() + 2;
    }
    State init() const { return 0; }
    State next(const State& q, const Alphabet& c) const {
        if (q == less_state || q == greater_state) return q;
        if (q >= (int)limit.size()) return greater_state;
        if (c < limit[q]) return less_state;
        if (c > limit[q]) return greater_state;
        return q + 1; // 完全に一致している文字数
    }
    bool accept(const State& q) const {
        return q != greater_state;
    }
};

// Lt (Less Than)
struct Lt {
    using State = int;
    using Alphabet = ll;
    vector<Alphabet> limit;
    int less_state, greater_state;
    Lt(const vector<Alphabet>& limit) : limit(limit) {
        less_state = limit.size() + 1;
        greater_state = limit.size() + 2;
    }
    Lt(const string& s) {
        for(char c : s) limit.pb(c - '0');
        less_state = limit.size() + 1;
        greater_state = limit.size() + 2;
    }
    State init() const { return 0; }
    State next(const State& q, const Alphabet& c) const {
        if (q == less_state || q == greater_state) return q;
        if (q >= (int)limit.size()) return greater_state;
        if (c < limit[q]) return less_state;
        if (c > limit[q]) return greater_state;
        return q + 1;
    }
    bool accept(const State& q) const {
        return q == less_state;
    }
};

// MultipleOf(M)
// Mの倍数かどうか判定
struct MultipleOf {
    using State = ll;
    using Alphabet = ll;
    ll m;
    MultipleOf(ll m) : m(m) {}
    State init() const { return 0; }
    State next(const State& q, const Alphabet& c) const {
        return (q * 10 + c) % m;
    }
    bool accept(const State& q) const { return q == 0; }
};

// Seen(Target)
// 特定の文字(Target)を含んでいるか判定
struct Seen {
    using State = bool;
    using Alphabet = ll;
    ll target;
    Seen(ll target) : target(target) {}
    State init() const { return false; }
    State next(const State& q, const Alphabet& c) const {
        return q || (c == target);
    }
    bool accept(const State& q) const { return q; }
};

// ContainsAhoCorasick
// 複数パターンのいずれかを部分文字列として含むか判定
struct ContainsAhoCorasick {
    using State = ll;
    using Alphabet = ll;
    
    struct Node {
        map<Alphabet, ll> nxt;
        ll fail = -1;
        bool accept = false;
    };
    vector<Node> nodes;
    
    ContainsAhoCorasick(const vector<vector<Alphabet>>& patterns) {
        nodes.pb(Node());
        for (const auto& pat : patterns) {
            ll curr = 0;
            for (Alphabet c : pat) {
                if (!nodes[curr].nxt.count(c)) {
                    nodes[curr].nxt[c] = nodes.size();
                    nodes.pb(Node());
                }
                curr = nodes[curr].nxt[c];
            }
            nodes[curr].accept = true;
        }
        
        queue<ll> q;
        for (const auto& p : nodes[0].nxt) {
            nodes[p.se].fail = 0;
            q.push(p.se);
        }
        while (!q.empty()) {
            ll u = q.front(); q.pop();
            if (nodes[nodes[u].fail].accept) nodes[u].accept = true;
            for (const auto& p : nodes[u].nxt) {
                Alphabet c = p.fi;
                ll v = p.se;
                ll f = nodes[u].fail;
                while (f != -1 && !nodes[f].nxt.count(c)) {
                    if (f == 0) { f = -1; break; }
                    f = nodes[f].fail;
                }
                nodes[v].fail = (f == -1) ? 0 : nodes[f].nxt.at(c);
                q.push(v);
            }
        }
    }
    
    State init() const { return 0; }
    State next(const State& q, const Alphabet& c) const {
        if (nodes[q].accept) return q; // 受理に入れば固定
        ll curr = q;
        while (curr != -1 && !nodes[curr].nxt.count(c)) {
            if (curr == 0) { curr = -1; break; }
            curr = nodes[curr].fail;
        }
        if (curr == -1) return 0;
        return nodes[curr].nxt.at(c);
    }
    bool accept(const State& q) const {
        return nodes[q].accept;
    }
};

// count_dfa
// ループ内での map の使用を避け、BFSで遷移テーブルを事前構築する
template<class Dfa>
ll count_dfa(const Dfa& dfa, const vector<typename Dfa::Alphabet>& sigma, ll length) {
    using State = typename Dfa::State;
    
    // 状態を整数IDにマッピングする
    map<State, int> state_id;
    vector<State> id_to_state;
    
    auto get_id = [&](const State& s) {
        auto it = state_id.lower_bound(s);
        if (it != state_id.end() && it->fi == s) {
            return it->se;
        }
        int id = state_id.size();
        state_id.emplace_hint(it, s, id);
        id_to_state.pb(s);
        return id;
    };
    
    get_id(dfa.init());
    vector<vector<int>> tr;
    
    // BFSにより到達可能状態の全遷移を静的な2次元配列として構成
    int p = 0;
    while (p < (int)id_to_state.size()) {
        State cur = id_to_state[p];
        tr.emplace_back(sigma.size());
        for (int i = 0; i < (int)sigma.size(); ++i) {
            tr[p][i] = get_id(dfa.next(cur, sigma[i]));
        }
        p++;
    }
    
    int num_states = id_to_state.size();
    vector<ll> dp(num_states, 0);
    dp[0] = 1;
    
    // 高速なDPループ (配列アクセスのみ)
    for (ll i = 0; i < length; ++i) {
        vector<ll> next_dp(num_states, 0);
        for (int u = 0; u < num_states; ++u) {
            if (!dp[u]) continue;
            for (int c = 0; c < (int)sigma.size(); ++c) {
                int v = tr[u][c];
                next_dp[v] += dp[u];
                if (next_dp[v] >= MOD) next_dp[v] -= MOD;
            }
        }
        dp = move(next_dp);
    }
    
    ll ans = 0;
    for (int u = 0; u < num_states; ++u) {
        if (dfa.accept(id_to_state[u])) {
            ans += dp[u];
            if (ans >= MOD) ans -= MOD;
        }
    }
    return ans;
}

// 演算子オーバーロード
template <class A, class B>
And<A, B> operator&(A a, B b) {
    return And<A, B>(a, b);
}

template <class A, class B>
Or<A, B> operator|(A a, B b) {
    return Or<A, B>(a, b);
}

template <class A>
Not<A> operator~(A a) {
    return Not<A>(a);
}
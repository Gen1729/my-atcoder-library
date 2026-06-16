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

// ========================================
// 1. 区間和セグメントツリー
// ========================================
struct SumSegTree {
    ll n;
    vl dat;
    
    SumSegTree(ll n_) : n(1) {
        while (n < n_) n *= 2;
        dat.assign(2 * n - 1, 0);
    }
    
    SumSegTree(const vl& v) : n(1) {
        ll n_ = v.size();
        while (n < n_) n *= 2;
        dat.assign(2 * n - 1, 0);
        for (ll i = 0; i < n_; i++) dat[n - 1 + i] = v[i];
        for (ll i = n - 2; i >= 0; i--) dat[i] = dat[2 * i + 1] + dat[2 * i + 2];
    }
    
    // i番目の要素をxに更新 (0-indexed)
    void update(ll i, ll x) {
        i += n - 1;
        dat[i] = x;
        while (i > 0) {
            i = (i - 1) / 2;
            dat[i] = dat[2 * i + 1] + dat[2 * i + 2];
        }
    }
    
    // 区間[l, r)の和を取得
    ll query(ll l, ll r) { return query_sub(l, r, 0, 0, n); }
    
    ll query_sub(ll l, ll r, ll k, ll lk, ll rk) {
        if (r <= lk || rk <= l) return 0;
        if (l <= lk && rk <= r) return dat[k];
        ll vl = query_sub(l, r, 2 * k + 1, lk, (lk + rk) / 2);
        ll vr = query_sub(l, r, 2 * k + 2, (lk + rk) / 2, rk);
        return vl + vr;
    }
    
    // i番目の要素を取得
    ll operator[](ll i) { return dat[i + n - 1]; }
};

// ========================================
// 2. 区間最大値セグメントツリー
// ========================================
struct MaxSegTree {
    ll n;
    vl dat;
    
    MaxSegTree(ll n_) : n(1) {
        while (n < n_) n *= 2;
        dat.assign(2 * n - 1, -INF);
    }
    
    MaxSegTree(const vl& v) : n(1) {
        ll n_ = v.size();
        while (n < n_) n *= 2;
        dat.assign(2 * n - 1, -INF);
        for (ll i = 0; i < n_; i++) dat[n - 1 + i] = v[i];
        for (ll i = n - 2; i >= 0; i--) dat[i] = max(dat[2 * i + 1], dat[2 * i + 2]);
    }
    
    // i番目の要素をxに更新 (0-indexed)
    void update(ll i, ll x) {
        i += n - 1;
        dat[i] = x;
        while (i > 0) {
            i = (i - 1) / 2;
            dat[i] = max(dat[2 * i + 1], dat[2 * i + 2]);
        }
    }
    
    // 区間[l, r)の最大値を取得
    ll query(ll l, ll r) { return query_sub(l, r, 0, 0, n); }
    
    ll query_sub(ll l, ll r, ll k, ll lk, ll rk) {
        if (r <= lk || rk <= l) return -INF;
        if (l <= lk && rk <= r) return dat[k];
        ll vl = query_sub(l, r, 2 * k + 1, lk, (lk + rk) / 2);
        ll vr = query_sub(l, r, 2 * k + 2, (lk + rk) / 2, rk);
        return max(vl, vr);
    }
    
    // i番目の要素を取得
    ll operator[](ll i) { return dat[i + n - 1]; }
};

// ========================================
// 3. 区間最小値セグメントツリー
// ========================================
struct MinSegTree {
    ll n;
    vl dat;
    
    MinSegTree(ll n_) : n(1) {
        while (n < n_) n *= 2;
        dat.assign(2 * n - 1, INF);
    }
    
    MinSegTree(const vl& v) : n(1) {
        ll n_ = v.size();
        while (n < n_) n *= 2;
        dat.assign(2 * n - 1, INF);
        for (ll i = 0; i < n_; i++) dat[n - 1 + i] = v[i];
        for (ll i = n - 2; i >= 0; i--) dat[i] = min(dat[2 * i + 1], dat[2 * i + 2]);
    }
    
    // i番目の要素をxに更新 (0-indexed)
    void update(ll i, ll x) {
        i += n - 1;
        dat[i] = x;
        while (i > 0) {
            i = (i - 1) / 2;
            dat[i] = min(dat[2 * i + 1], dat[2 * i + 2]);
        }
    }
    
    // 区間[l, r)の最小値を取得
    ll query(ll l, ll r) { return query_sub(l, r, 0, 0, n); }
    
    ll query_sub(ll l, ll r, ll k, ll lk, ll rk) {
        if (r <= lk || rk <= l) return INF;
        if (l <= lk && rk <= r) return dat[k];
        ll vl = query_sub(l, r, 2 * k + 1, lk, (lk + rk) / 2);
        ll vr = query_sub(l, r, 2 * k + 2, (lk + rk) / 2, rk);
        return min(vl, vr);
    }
    
    // i番目の要素を取得
    ll operator[](ll i) { return dat[i + n - 1]; }
};

// ========================================
// 4. 汎用セグメントツリー
// ========================================
template<typename F>
struct SegTree {
    ll n;
    vl dat;
    ll e;  // 単位元
    F op; // 二項演算
    
    SegTree(ll n_, ll e_, F op_) : n(1), e(e_), op(op_) {
        while (n < n_) n *= 2;
        dat.assign(2 * n - 1, e);
    }
    
    SegTree(const vl& v, ll e_, F op_) : n(1), e(e_), op(op_) {
        ll n_ = v.size();
        while (n < n_) n *= 2;
        dat.assign(2 * n - 1, e);
        for (ll i = 0; i < n_; i++) dat[n - 1 + i] = v[i];
        for (ll i = n - 2; i >= 0; i--) dat[i] = op(dat[2 * i + 1], dat[2 * i + 2]);
    }
    
    // i番目の要素をxに更新 (0-indexed)
    void update(ll i, ll x) {
        i += n - 1;
        dat[i] = x;
        while (i > 0) {
            i = (i - 1) / 2;
            dat[i] = op(dat[2 * i + 1], dat[2 * i + 2]);
        }
    }
    
    // 区間[l, r)のクエリを取得
    ll query(ll l, ll r) { return query_sub(l, r, 0, 0, n); }
    
    ll query_sub(ll l, ll r, ll k, ll lk, ll rk) {
        if (r <= lk || rk <= l) return e;
        if (l <= lk && rk <= r) return dat[k];
        ll vl = query_sub(l, r, 2 * k + 1, lk, (lk + rk) / 2);
        ll vr = query_sub(l, r, 2 * k + 2, (lk + rk) / 2, rk);
        return op(vl, vr);
    }
    
    // i番目の要素を取得
    ll operator[](ll i) { return dat[i + n - 1]; }
};

// ========================================
// 使用例
// ========================================

ll main() {
    // 1. 区間和 (初期値: 0)
    SumSegTree sum_seg(10);
    sum_seg.update(0, 5);
    sum_seg.update(1, 3);
    cout << sum_seg.query(0, 2) << endl; // 8
    
    // 2. 区間最大値 (初期値: -1e18)
    MaxSegTree max_seg(10);
    max_seg.update(0, 5);
    max_seg.update(1, 3);
    max_seg.update(2, 8);
    cout << max_seg.query(0, 3) << endl; // 8
    
    // 3. 区間最小値 (初期値: 1e18)
    MinSegTree min_seg(10);
    min_seg.update(0, 5);
    min_seg.update(1, 3);
    min_seg.update(2, 8);
    cout << min_seg.query(0, 3) << endl; // 3
    
    // 4. 汎用 (区間GCD)
    auto gcd_op = [](ll a, ll b) { return __gcd(a, b); };
    SegTree<decltype(gcd_op)> gcd_seg(10, 0LL, gcd_op);
    gcd_seg.update(0, 12);
    gcd_seg.update(1, 18);
    gcd_seg.update(2, 24);
    cout << gcd_seg.query(0, 3) << endl; // 6
    
    return 0;
}
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

// 1. 範囲和クエリ + 区間加算 + 区間更新
class SumSegmentTree {
private:
    vc<ll> tree, lazy_add, lazy_set;
    vc<bool> has_set;
    int n;
    
    void push(int v, int tl, int tr) {
        if (has_set[v]) {
            tree[v] = lazy_set[v] * (tr - tl);
            if (tl != tr - 1) {
                lazy_set[2 * v] = lazy_set[v];
                lazy_set[2 * v + 1] = lazy_set[v];
                has_set[2 * v] = has_set[2 * v + 1] = true;
                lazy_add[2 * v] = lazy_add[2 * v + 1] = 0;
            }
            has_set[v] = false;
        }
        if (lazy_add[v] != 0) {
            tree[v] += lazy_add[v] * (tr - tl);
            if (tl != tr - 1) {
                if (has_set[2 * v]) lazy_set[2 * v] += lazy_add[v];
                else lazy_add[2 * v] += lazy_add[v];

                if (has_set[2 * v + 1]) lazy_set[2 * v + 1] += lazy_add[v];
                else lazy_add[2 * v + 1] += lazy_add[v];
            }
            lazy_add[v] = 0;
        }
    }
    
    void range_add(int v, int tl, int tr, int l, int r, ll val) {
        push(v, tl, tr);
        if (l >= tr || r <= tl) return;
        if (l <= tl && tr <= r) {
            lazy_add[v] += val;
            push(v, tl, tr);
            return;
        }
        int tm = (tl + tr) / 2;
        range_add(2 * v, tl, tm, l, r, val);
        range_add(2 * v + 1, tm, tr, l, r, val);
        push(2 * v, tl, tm);
        push(2 * v + 1, tm, tr);
        tree[v] = tree[2 * v] + tree[2 * v + 1];
    }
    
    void range_set(int v, int tl, int tr, int l, int r, ll val) {
        push(v, tl, tr);
        if (l >= tr || r <= tl) return;
        if (l <= tl && tr <= r) {
            lazy_set[v] = val;
            has_set[v] = true;
            lazy_add[v] = 0;
            push(v, tl, tr);
            return;
        }
        int tm = (tl + tr) / 2;
        range_set(2 * v, tl, tm, l, r, val);
        range_set(2 * v + 1, tm, tr, l, r, val);
        push(2 * v, tl, tm);
        push(2 * v + 1, tm, tr);
        tree[v] = tree[2 * v] + tree[2 * v + 1];
    }
    
    ll query(int v, int tl, int tr, int l, int r) {
        if (l >= tr || r <= tl) return 0;
        push(v, tl, tr);
        if (l <= tl && tr <= r) return tree[v];
        int tm = (tl + tr) / 2;
        return query(2 * v, tl, tm, l, r) + query(2 * v + 1, tm, tr, l, r);
    }
    
public:
    SumSegmentTree(vc<ll>& arr) {
        n = arr.size();
        tree.resize(4 * n, 0);
        lazy_add.resize(4 * n, 0);
        lazy_set.resize(4 * n, 0);
        has_set.resize(4 * n, false);
        build(arr, 1, 0, n);
    }
    
    void build(vc<ll>& arr, int v, int tl, int tr) {
        if (tl == tr - 1) {
            tree[v] = arr[tl];
        } else {
            int tm = (tl + tr) / 2;
            build(arr, 2 * v, tl, tm);
            build(arr, 2 * v + 1, tm, tr);
            tree[v] = tree[2 * v] + tree[2 * v + 1];
        }
    }
    
    void add(int l, int r, ll val) { // 区間加算 [l, r)
        range_add(1, 0, n, l, r, val);
    }
    
    void set(int l, int r, ll val) { // 区間更新 [l, r)
        range_set(1, 0, n, l, r, val);
    }
    
    ll query(int l, int r) { // 範囲和 [l, r)
        return query(1, 0, n, l, r);
    }
};

// 2. 範囲最小値クエリ + 区間加算 + 区間更新
class MinSegmentTree {
private:
    vc<ll> tree, lazy_add, lazy_set;
    vc<bool> has_set;
    int n;
    
    void push(int v) {
        if (has_set[v]) {
            tree[v] = lazy_set[v];
            if (2 * v + 1 < tree.size()) {
                lazy_set[2 * v] = lazy_set[v];
                lazy_set[2 * v + 1] = lazy_set[v];
                has_set[2 * v] = has_set[2 * v + 1] = true;
                lazy_add[2 * v] = lazy_add[2 * v + 1] = 0;
            }
            has_set[v] = false;
        }
        if (lazy_add[v] != 0) {
            tree[v] += lazy_add[v];
            if (2 * v + 1 < tree.size()) {
                if (has_set[2 * v]) lazy_set[2 * v] += lazy_add[v];
                else lazy_add[2 * v] += lazy_add[v];

                if (has_set[2 * v + 1]) lazy_set[2 * v + 1] += lazy_add[v];
                else lazy_add[2 * v + 1] += lazy_add[v];
            }
            lazy_add[v] = 0;
        }
    }
    
    void range_add(int v, int tl, int tr, int l, int r, ll val) {
        push(v);
        if (l >= tr || r <= tl) return;
        if (l <= tl && tr <= r) {
            lazy_add[v] += val;
            push(v);
            return;
        }
        int tm = (tl + tr) / 2;
        range_add(2 * v, tl, tm, l, r, val);
        range_add(2 * v + 1, tm, tr, l, r, val);
        push(2 * v);
        push(2 * v + 1);
        tree[v] = min(tree[2 * v], tree[2 * v + 1]);
    }
    
    void range_set(int v, int tl, int tr, int l, int r, ll val) {
        push(v);
        if (l >= tr || r <= tl) return;
        if (l <= tl && tr <= r) {
            lazy_set[v] = val;
            has_set[v] = true;
            lazy_add[v] = 0;
            push(v);
            return;
        }
        int tm = (tl + tr) / 2;
        range_set(2 * v, tl, tm, l, r, val);
        range_set(2 * v + 1, tm, tr, l, r, val);
        push(2 * v);
        push(2 * v + 1);
        tree[v] = min(tree[2 * v], tree[2 * v + 1]);
    }
    
    ll query(int v, int tl, int tr, int l, int r) {
        if (l >= tr || r <= tl) return LLONG_MAX;
        push(v);
        if (l <= tl && tr <= r) return tree[v];
        int tm = (tl + tr) / 2;
        return min(query(2 * v, tl, tm, l, r), query(2 * v + 1, tm, tr, l, r));
    }
    
public:
    MinSegmentTree(vc<ll>& arr) {
        n = arr.size();
        tree.resize(4 * n, LLONG_MAX);
        lazy_add.resize(4 * n, 0);
        lazy_set.resize(4 * n, 0);
        has_set.resize(4 * n, false);
        build(arr, 1, 0, n);
    }
    
    void build(vc<ll>& arr, int v, int tl, int tr) {
        if (tl == tr - 1) {
            tree[v] = arr[tl];
        } else {
            int tm = (tl + tr) / 2;
            build(arr, 2 * v, tl, tm);
            build(arr, 2 * v + 1, tm, tr);
            tree[v] = min(tree[2 * v], tree[2 * v + 1]);
        }
    }
    
    void add(int l, int r, ll val) { // 区間加算 [l, r)
        range_add(1, 0, n, l, r, val);
    }
    
    void set(int l, int r, ll val) { // 区間更新 [l, r)
        range_set(1, 0, n, l, r, val);
    }
    
    ll query(int l, int r) { // 範囲最小値 [l, r)
        return query(1, 0, n, l, r);
    }
};

// 3. 範囲最大値クエリ + 区間加算 + 区間更新
class MaxSegmentTree {
private:
    vc<ll> tree, lazy_add, lazy_set;
    vc<bool> has_set;
    int n;
    
    void push(int v) {
        if (has_set[v]) {
            tree[v] = lazy_set[v];
            if (2 * v + 1 < tree.size()) {
                lazy_set[2 * v] = lazy_set[v];
                lazy_set[2 * v + 1] = lazy_set[v];
                has_set[2 * v] = has_set[2 * v + 1] = true;
                lazy_add[2 * v] = lazy_add[2 * v + 1] = 0;
            }
            has_set[v] = false;
        }
        if (lazy_add[v] != 0) {
            tree[v] += lazy_add[v];
            if (2 * v + 1 < tree.size()) {
                if (has_set[2 * v]) lazy_set[2 * v] += lazy_add[v];
                else lazy_add[2 * v] += lazy_add[v];

                if (has_set[2 * v + 1]) lazy_set[2 * v + 1] += lazy_add[v];
                else lazy_add[2 * v + 1] += lazy_add[v];
            }
            lazy_add[v] = 0;
        }
    }
    
    void range_add(int v, int tl, int tr, int l, int r, ll val) {
        push(v);
        if (l >= tr || r <= tl) return;
        if (l <= tl && tr <= r) {
            lazy_add[v] += val;
            push(v);
            return;
        }
        int tm = (tl + tr) / 2;
        range_add(2 * v, tl, tm, l, r, val);
        range_add(2 * v + 1, tm, tr, l, r, val);
        push(2 * v);
        push(2 * v + 1);
        tree[v] = max(tree[2 * v], tree[2 * v + 1]);
    }
    
    void range_set(int v, int tl, int tr, int l, int r, ll val) {
        push(v);
        if (l >= tr || r <= tl) return;
        if (l <= tl && tr <= r) {
            lazy_set[v] = val;
            has_set[v] = true;
            lazy_add[v] = 0;
            push(v);
            return;
        }
        int tm = (tl + tr) / 2;
        range_set(2 * v, tl, tm, l, r, val);
        range_set(2 * v + 1, tm, tr, l, r, val);
        push(2 * v);
        push(2 * v + 1);
        tree[v] = max(tree[2 * v], tree[2 * v + 1]);
    }
    
    ll query(int v, int tl, int tr, int l, int r) {
        if (l >= tr || r <= tl) return LLONG_MIN;
        push(v);
        if (l <= tl && tr <= r) return tree[v];
        int tm = (tl + tr) / 2;
        return max(query(2 * v, tl, tm, l, r), query(2 * v + 1, tm, tr, l, r));
    }
    
public:
    MaxSegmentTree(vc<ll>& arr) {
        n = arr.size();
        tree.resize(4 * n, LLONG_MIN);
        lazy_add.resize(4 * n, 0);
        lazy_set.resize(4 * n, 0);
        has_set.resize(4 * n, false);
        build(arr, 1, 0, n);
    }
    
    void build(vc<ll>& arr, int v, int tl, int tr) {
        if (tl == tr - 1) {
            tree[v] = arr[tl];
        } else {
            int tm = (tl + tr) / 2;
            build(arr, 2 * v, tl, tm);
            build(arr, 2 * v + 1, tm, tr);
            tree[v] = max(tree[2 * v], tree[2 * v + 1]);
        }
    }
    
    void add(int l, int r, ll val) { // 区間加算 [l, r)
        range_add(1, 0, n, l, r, val);
    }
    
    void set(int l, int r, ll val) { // 区間更新 [l, r)
        range_set(1, 0, n, l, r, val);
    }
    
    ll query(int l, int r) { // 範囲最大値 [l, r)
        return query(1, 0, n, l, r);
    }
};

// 4. 汎用遅延評価セグメントツリー
template<typename T>
class GenericLazySegmentTree {
private:
    vc<T> tree, lazy_add, lazy_set;
    vc<bool> has_set;
    int n;
    T identity;
    function<T(T, T)> op;
    
    void push(int v) {
        if (has_set[v]) {
            tree[v] = lazy_set[v];
            if (2 * v + 1 < tree.size()) {
                lazy_set[2 * v] = lazy_set[v];
                lazy_set[2 * v + 1] = lazy_set[v];
                has_set[2 * v] = has_set[2 * v + 1] = true;
                lazy_add[2 * v] = lazy_add[2 * v + 1] = T{};
            }
            has_set[v] = false;
        }
        if (lazy_add[v] != T{}) {
            tree[v] = tree[v] + lazy_add[v]; // 型Tで+演算子が定義されている前提
            if (2 * v + 1 < tree.size()) {
                if (has_set[2 * v]) lazy_set[2 * v] += lazy_add[v];
                else lazy_add[2 * v] += lazy_add[v];

                if (has_set[2 * v + 1]) lazy_set[2 * v + 1] += lazy_add[v];
                else lazy_add[2 * v + 1] += lazy_add[v];
            }
            lazy_add[v] = T{};
        }
    }
    
    void range_add(int v, int tl, int tr, int l, int r, T val) {
        push(v);
        if (l >= tr || r <= tl) return;
        if (l <= tl && tr <= r) {
            lazy_add[v] = lazy_add[v] + val;
            push(v);
            return;
        }
        int tm = (tl + tr) / 2;
        range_add(2 * v, tl, tm, l, r, val);
        range_add(2 * v + 1, tm, tr, l, r, val);
        push(2 * v);
        push(2 * v + 1);
        tree[v] = op(tree[2 * v], tree[2 * v + 1]);
    }
    
    void range_set(int v, int tl, int tr, int l, int r, T val) {
        push(v);
        if (l >= tr || r <= tl) return;
        if (l <= tl && tr <= r) {
            lazy_set[v] = val;
            has_set[v] = true;
            lazy_add[v] = T{};
            push(v);
            return;
        }
        int tm = (tl + tr) / 2;
        range_set(2 * v, tl, tm, l, r, val);
        range_set(2 * v + 1, tm, tr, l, r, val);
        push(2 * v);
        push(2 * v + 1);
        tree[v] = op(tree[2 * v], tree[2 * v + 1]);
    }
    
    T query(int v, int tl, int tr, int l, int r) {
        if (l >= tr || r <= tl) return identity;
        push(v);
        if (l <= tl && tr <= r) return tree[v];
        int tm = (tl + tr) / 2;
        return op(query(2 * v, tl, tm, l, r), query(2 * v + 1, tm, tr, l, r));
    }
    
public:
    GenericLazySegmentTree(vc<T>& arr, T id, function<T(T, T)> operation) 
        : identity(id), op(operation) {
        n = arr.size();
        tree.resize(4 * n, identity);
        lazy_add.resize(4 * n, T{});
        lazy_set.resize(4 * n, T{});
        has_set.resize(4 * n, false);
        build(arr, 1, 0, n);
    }
    
    void build(vc<T>& arr, int v, int tl, int tr) {
        if (tl == tr - 1) {
            tree[v] = arr[tl];
        } else {
            int tm = (tl + tr) / 2;
            build(arr, 2 * v, tl, tm);
            build(arr, 2 * v + 1, tm, tr);
            tree[v] = op(tree[2 * v], tree[2 * v + 1]);
        }
    }
    
    void add(int l, int r, T val) { // 区間加算 [l, r)
        range_add(1, 0, n, l, r, val);
    }
    
    void set(int l, int r, T val) { // 区間更新 [l, r)
        range_set(1, 0, n, l, r, val);
    }
    
    T query(int l, int r) { // 範囲クエリ [l, r)
        return query(1, 0, n, l, r);
    }
};

// 使用例
int main() {
    vc<ll> arr = {1, 2, 3, 4, 5};
    
    // 範囲和セグメントツリー
    SumSegmentTree sum_seg(arr);
    cout << sum_seg.query(1, 4) << endl; // [1, 4) = 2 + 3 + 4 = 9
    sum_seg.add(1, 4, 10);               // [1, 4)に10を加算
    cout << sum_seg.query(1, 4) << endl; // [1, 4) = 12 + 13 + 14 = 39
    sum_seg.set(2, 4, 100);              // [2, 4)を100に更新
    cout << sum_seg.query(0, 5) << endl; // 全体の和 = 1 + 12 + 100 + 100 + 5 = 218
    
    // 範囲最小値セグメントツリー
    MinSegmentTree min_seg(arr);
    cout << min_seg.query(1, 4) << endl; // [1, 4) = min(2, 3, 4) = 2
    min_seg.add(1, 4, 10);               // [1, 4)に10を加算
    cout << min_seg.query(1, 4) << endl; // [1, 4) = min(12, 13, 14) = 12
    
    // 範囲最大値セグメントツリー
    MaxSegmentTree max_seg(arr);
    cout << max_seg.query(1, 4) << endl; // [1, 4) = max(2, 3, 4) = 4
    max_seg.add(1, 4, 10);               // [1, 4)に10を加算
    cout << max_seg.query(1, 4) << endl; // [1, 4) = max(12, 13, 14) = 14
    
    // 汎用セグメントツリー（和）
    auto add_op = [](ll a, ll b) { return a + b; };
    GenericLazySegmentTree<ll> generic_sum(arr, 0LL, add_op);
    cout << generic_sum.query(1, 4) << endl; // [1, 4) = 2 + 3 + 4 = 9
    generic_sum.add(1, 4, 5);
    cout << generic_sum.query(1, 4) << endl; // [1, 4) = 7 + 8 + 9 = 24

    auto gcd_op = [](ll a, ll b) { return __gcd(a, b); };
    GenericLazySegmentTree<ll> generic_gcd(arr, 0LL, gcd_op);
    cout << generic_gcd.query(2, 5) << endl; // [2, 5) = gcd(3,4,5) = 1
    generic_gcd.add(1, 4, 5);
    cout << generic_gcd.query(2, 5) << endl; // [2, 5) = gcd(8,9,5) = 1
    
    return 0;
}
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
    ll n;
    
    void push(ll v, ll tl, ll tr) {
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
    
    void range_add(ll v, ll tl, ll tr, ll l, ll r, ll val) {
        push(v, tl, tr);
        if (l >= tr || r <= tl) return;
        if (l <= tl && tr <= r) {
            lazy_add[v] += val;
            push(v, tl, tr);
            return;
        }
        ll tm = (tl + tr) / 2;
        range_add(2 * v, tl, tm, l, r, val);
        range_add(2 * v + 1, tm, tr, l, r, val);
        push(2 * v, tl, tm);
        push(2 * v + 1, tm, tr);
        tree[v] = tree[2 * v] + tree[2 * v + 1];
    }
    
    void range_set(ll v, ll tl, ll tr, ll l, ll r, ll val) {
        push(v, tl, tr);
        if (l >= tr || r <= tl) return;
        if (l <= tl && tr <= r) {
            lazy_set[v] = val;
            has_set[v] = true;
            lazy_add[v] = 0;
            push(v, tl, tr);
            return;
        }
        ll tm = (tl + tr) / 2;
        range_set(2 * v, tl, tm, l, r, val);
        range_set(2 * v + 1, tm, tr, l, r, val);
        push(2 * v, tl, tm);
        push(2 * v + 1, tm, tr);
        tree[v] = tree[2 * v] + tree[2 * v + 1];
    }
    
    ll query(ll v, ll tl, ll tr, ll l, ll r) {
        if (l >= tr || r <= tl) return 0;
        push(v, tl, tr);
        if (l <= tl && tr <= r) return tree[v];
        ll tm = (tl + tr) / 2;
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
    
    void build(vc<ll>& arr, ll v, ll tl, ll tr) {
        if (tl == tr - 1) {
            tree[v] = arr[tl];
        } else {
            ll tm = (tl + tr) / 2;
            build(arr, 2 * v, tl, tm);
            build(arr, 2 * v + 1, tm, tr);
            tree[v] = tree[2 * v] + tree[2 * v + 1];
        }
    }
    
    void add(ll l, ll r, ll val) { // 区間加算 [l, r)
        range_add(1, 0, n, l, r, val);
    }
    
    void set(ll l, ll r, ll val) { // 区間更新 [l, r)
        range_set(1, 0, n, l, r, val);
    }
    
    ll query(ll l, ll r) { // 範囲和 [l, r)
        return query(1, 0, n, l, r);
    }
    
    // 二分探索: 位置 l から右に見て、累積和が sum 以上になる最小の位置を返す
    // 見つからない場合は n を返す
    ll lower_bound(ll l, ll sum) {
        return lower_bound(1, 0, n, l, sum);
    }
    
private:
    ll lower_bound(ll v, ll tl, ll tr, ll l, ll sum) {
        push(v, tl, tr);
        if (tr <= l || tree[v] < sum) return n;
        if (tl == tr - 1) return tl;
        
        push(2 * v, tl, (tl + tr) / 2);
        ll tm = (tl + tr) / 2;
        
        if (tm <= l) {
            return lower_bound(2 * v + 1, tm, tr, l, sum);
        }
        
        ll left_sum = (l <= tl) ? tree[2 * v] : query(2 * v, tl, tm, l, tm);
        if (left_sum >= sum) {
            return lower_bound(2 * v, tl, tm, l, sum);
        } else {
            return lower_bound(2 * v + 1, tm, tr, l, sum - left_sum);
        }
    }
};

// 2. 範囲最小値クエリ + 区間加算 + 区間更新
class MinSegmentTree {
private:
    vc<ll> tree, lazy_add, lazy_set;
    vc<bool> has_set;
    ll n;
    
    void push(ll v) {
        if (has_set[v]) {
            tree[v] = lazy_set[v];
            if (2 * v + 1 < (ll)tree.size()) {
                lazy_set[2 * v] = lazy_set[v];
                lazy_set[2 * v + 1] = lazy_set[v];
                has_set[2 * v] = has_set[2 * v + 1] = true;
                lazy_add[2 * v] = lazy_add[2 * v + 1] = 0;
            }
            has_set[v] = false;
        }
        if (lazy_add[v] != 0) {
            tree[v] += lazy_add[v];
            if (2 * v + 1 < (ll)tree.size()) {
                if (has_set[2 * v]) lazy_set[2 * v] += lazy_add[v];
                else lazy_add[2 * v] += lazy_add[v];

                if (has_set[2 * v + 1]) lazy_set[2 * v + 1] += lazy_add[v];
                else lazy_add[2 * v + 1] += lazy_add[v];
            }
            lazy_add[v] = 0;
        }
    }
    
    void range_add(ll v, ll tl, ll tr, ll l, ll r, ll val) {
        push(v);
        if (l >= tr || r <= tl) return;
        if (l <= tl && tr <= r) {
            lazy_add[v] += val;
            push(v);
            return;
        }
        ll tm = (tl + tr) / 2;
        range_add(2 * v, tl, tm, l, r, val);
        range_add(2 * v + 1, tm, tr, l, r, val);
        push(2 * v);
        push(2 * v + 1);
        tree[v] = min(tree[2 * v], tree[2 * v + 1]);
    }
    
    void range_set(ll v, ll tl, ll tr, ll l, ll r, ll val) {
        push(v);
        if (l >= tr || r <= tl) return;
        if (l <= tl && tr <= r) {
            lazy_set[v] = val;
            has_set[v] = true;
            lazy_add[v] = 0;
            push(v);
            return;
        }
        ll tm = (tl + tr) / 2;
        range_set(2 * v, tl, tm, l, r, val);
        range_set(2 * v + 1, tm, tr, l, r, val);
        push(2 * v);
        push(2 * v + 1);
        tree[v] = min(tree[2 * v], tree[2 * v + 1]);
    }
    
    ll query(ll v, ll tl, ll tr, ll l, ll r) {
        if (l >= tr || r <= tl) return LLONG_MAX;
        push(v);
        if (l <= tl && tr <= r) return tree[v];
        ll tm = (tl + tr) / 2;
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
    
    void build(vc<ll>& arr, ll v, ll tl, ll tr) {
        if (tl == tr - 1) {
            tree[v] = arr[tl];
        } else {
            ll tm = (tl + tr) / 2;
            build(arr, 2 * v, tl, tm);
            build(arr, 2 * v + 1, tm, tr);
            tree[v] = min(tree[2 * v], tree[2 * v + 1]);
        }
    }
    
    void add(ll l, ll r, ll val) { // 区間加算 [l, r)
        range_add(1, 0, n, l, r, val);
    }
    
    void set(ll l, ll r, ll val) { // 区間更新 [l, r)
        range_set(1, 0, n, l, r, val);
    }
    
    ll query(ll l, ll r) { // 範囲最小値 [l, r)
        return query(1, 0, n, l, r);
    }
    
    // 二分探索: 位置 l から右に見て、値が val 以下になる最小の位置を返す
    // 見つからない場合は n を返す
    ll lower_bound(ll l, ll val) {
        return lower_bound(1, 0, n, l, val);
    }
    
private:
    ll lower_bound(ll v, ll tl, ll tr, ll l, ll val) {
        push(v);
        if (tr <= l || tree[v] > val) return n;
        if (tl == tr - 1) return tl;
        
        ll tm = (tl + tr) / 2;
        push(2 * v);
        
        if (tm <= l) {
            return lower_bound(2 * v + 1, tm, tr, l, val);
        }
        
        ll left_res = lower_bound(2 * v, tl, tm, l, val);
        if (left_res < n) return left_res;
        return lower_bound(2 * v + 1, tm, tr, l, val);
    }
};

// 3. 範囲最大値クエリ + 区間加算 + 区間更新
class MaxSegmentTree {
private:
    vc<ll> tree, lazy_add, lazy_set;
    vc<bool> has_set;
    ll n;
    
    void push(ll v) {
        if (has_set[v]) {
            tree[v] = lazy_set[v];
            if (2 * v + 1 < (ll)tree.size()) {
                lazy_set[2 * v] = lazy_set[v];
                lazy_set[2 * v + 1] = lazy_set[v];
                has_set[2 * v] = has_set[2 * v + 1] = true;
                lazy_add[2 * v] = lazy_add[2 * v + 1] = 0;
            }
            has_set[v] = false;
        }
        if (lazy_add[v] != 0) {
            tree[v] += lazy_add[v];
            if (2 * v + 1 < (ll)tree.size()) {
                if (has_set[2 * v]) lazy_set[2 * v] += lazy_add[v];
                else lazy_add[2 * v] += lazy_add[v];

                if (has_set[2 * v + 1]) lazy_set[2 * v + 1] += lazy_add[v];
                else lazy_add[2 * v + 1] += lazy_add[v];
            }
            lazy_add[v] = 0;
        }
    }
    
    void range_add(ll v, ll tl, ll tr, ll l, ll r, ll val) {
        push(v);
        if (l >= tr || r <= tl) return;
        if (l <= tl && tr <= r) {
            lazy_add[v] += val;
            push(v);
            return;
        }
        ll tm = (tl + tr) / 2;
        range_add(2 * v, tl, tm, l, r, val);
        range_add(2 * v + 1, tm, tr, l, r, val);
        push(2 * v);
        push(2 * v + 1);
        tree[v] = max(tree[2 * v], tree[2 * v + 1]);
    }
    
    void range_set(ll v, ll tl, ll tr, ll l, ll r, ll val) {
        push(v);
        if (l >= tr || r <= tl) return;
        if (l <= tl && tr <= r) {
            lazy_set[v] = val;
            has_set[v] = true;
            lazy_add[v] = 0;
            push(v);
            return;
        }
        ll tm = (tl + tr) / 2;
        range_set(2 * v, tl, tm, l, r, val);
        range_set(2 * v + 1, tm, tr, l, r, val);
        push(2 * v);
        push(2 * v + 1);
        tree[v] = max(tree[2 * v], tree[2 * v + 1]);
    }
    
    ll query(ll v, ll tl, ll tr, ll l, ll r) {
        if (l >= tr || r <= tl) return LLONG_MIN;
        push(v);
        if (l <= tl && tr <= r) return tree[v];
        ll tm = (tl + tr) / 2;
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
    
    void build(vc<ll>& arr, ll v, ll tl, ll tr) {
        if (tl == tr - 1) {
            tree[v] = arr[tl];
        } else {
            ll tm = (tl + tr) / 2;
            build(arr, 2 * v, tl, tm);
            build(arr, 2 * v + 1, tm, tr);
            tree[v] = max(tree[2 * v], tree[2 * v + 1]);
        }
    }
    
    void add(ll l, ll r, ll val) { // 区間加算 [l, r)
        range_add(1, 0, n, l, r, val);
    }
    
    void set(ll l, ll r, ll val) { // 区間更新 [l, r)
        range_set(1, 0, n, l, r, val);
    }
    
    ll query(ll l, ll r) { // 範囲最大値 [l, r)
        return query(1, 0, n, l, r);
    }
    
    // 二分探索: 位置 l から右に見て、値が val 以上になる最小の位置を返す
    // 見つからない場合は n を返す
    ll lower_bound(ll l, ll val) {
        return lower_bound(1, 0, n, l, val);
    }
    
private:
    ll lower_bound(ll v, ll tl, ll tr, ll l, ll val) {
        push(v);
        if (tr <= l || tree[v] < val) return n;
        if (tl == tr - 1) return tl;
        
        ll tm = (tl + tr) / 2;
        push(2 * v);
        
        if (tm <= l) {
            return lower_bound(2 * v + 1, tm, tr, l, val);
        }
        
        ll left_res = lower_bound(2 * v, tl, tm, l, val);
        if (left_res < n) return left_res;
        return lower_bound(2 * v + 1, tm, tr, l, val);
    }
};

// 4. 汎用遅延評価セグメントツリー
template<typename T>
class GenericLazySegmentTree {
private:
    vc<T> tree, lazy_add, lazy_set;
    vc<bool> has_set;
    ll n;
    T identity;
    function<T(T, T)> op;
    
    void push(ll v) {
        if (has_set[v]) {
            tree[v] = lazy_set[v];
            if (2 * v + 1 < (ll)tree.size()) {
                lazy_set[2 * v] = lazy_set[v];
                lazy_set[2 * v + 1] = lazy_set[v];
                has_set[2 * v] = has_set[2 * v + 1] = true;
                lazy_add[2 * v] = lazy_add[2 * v + 1] = T{};
            }
            has_set[v] = false;
        }
        if (lazy_add[v] != T{}) {
            tree[v] = tree[v] + lazy_add[v]; // 型Tで+演算子が定義されている前提
            if (2 * v + 1 < (ll)tree.size()) {
                if (has_set[2 * v]) lazy_set[2 * v] += lazy_add[v];
                else lazy_add[2 * v] += lazy_add[v];

                if (has_set[2 * v + 1]) lazy_set[2 * v + 1] += lazy_add[v];
                else lazy_add[2 * v + 1] += lazy_add[v];
            }
            lazy_add[v] = T{};
        }
    }
    
    void range_add(ll v, ll tl, ll tr, ll l, ll r, T val) {
        push(v);
        if (l >= tr || r <= tl) return;
        if (l <= tl && tr <= r) {
            lazy_add[v] = lazy_add[v] + val;
            push(v);
            return;
        }
        ll tm = (tl + tr) / 2;
        range_add(2 * v, tl, tm, l, r, val);
        range_add(2 * v + 1, tm, tr, l, r, val);
        push(2 * v);
        push(2 * v + 1);
        tree[v] = op(tree[2 * v], tree[2 * v + 1]);
    }
    
    void range_set(ll v, ll tl, ll tr, ll l, ll r, T val) {
        push(v);
        if (l >= tr || r <= tl) return;
        if (l <= tl && tr <= r) {
            lazy_set[v] = val;
            has_set[v] = true;
            lazy_add[v] = T{};
            push(v);
            return;
        }
        ll tm = (tl + tr) / 2;
        range_set(2 * v, tl, tm, l, r, val);
        range_set(2 * v + 1, tm, tr, l, r, val);
        push(2 * v);
        push(2 * v + 1);
        tree[v] = op(tree[2 * v], tree[2 * v + 1]);
    }
    
    T query(ll v, ll tl, ll tr, ll l, ll r) {
        if (l >= tr || r <= tl) return identity;
        push(v);
        if (l <= tl && tr <= r) return tree[v];
        ll tm = (tl + tr) / 2;
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
    
    void build(vc<T>& arr, ll v, ll tl, ll tr) {
        if (tl == tr - 1) {
            tree[v] = arr[tl];
        } else {
            ll tm = (tl + tr) / 2;
            build(arr, 2 * v, tl, tm);
            build(arr, 2 * v + 1, tm, tr);
            tree[v] = op(tree[2 * v], tree[2 * v + 1]);
        }
    }
    
    void add(ll l, ll r, T val) { // 区間加算 [l, r)
        range_add(1, 0, n, l, r, val);
    }
    
    void set(ll l, ll r, T val) { // 区間更新 [l, r)
        range_set(1, 0, n, l, r, val);
    }
    
    T query(ll l, ll r) { // 範囲クエリ [l, r)
        return query(1, 0, n, l, r);
    }
    
    // 二分探索: 位置 l から右に見て、条件を満たす最小の位置を返す
    // pred(value): 条件を満たすかを判定する関数
    // 見つからない場合は n を返す
    template<typename Pred>
    ll lower_bound(ll l, Pred pred) {
        return lower_bound(1, 0, n, l, pred);
    }
    
private:
    template<typename Pred>
    ll lower_bound(ll v, ll tl, ll tr, ll l, Pred pred) {
        push(v);
        if (tr <= l || !pred(tree[v])) return n;
        if (tl == tr - 1) return tl;
        
        ll tm = (tl + tr) / 2;
        push(2 * v);
        
        if (tm <= l) {
            return lower_bound(2 * v + 1, tm, tr, l, pred);
        }
        
        ll left_res = lower_bound(2 * v, tl, tm, l, pred);
        if (left_res < n) return left_res;
        return lower_bound(2 * v + 1, tm, tr, l, pred);
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
    
    // 二分探索の使用例
    cout << "\n--- 二分探索の例 ---" << endl;
    
    // 範囲和セグメントツリーでの二分探索
    // 位置1から右に見て累積和が20以上になる最初の位置
    SumSegmentTree sum_seg2(arr);
    ll pos = sum_seg2.lower_bound(0, 10);
    cout << "累積和が10以上になる位置: " << pos << endl; // 位置3 (1+2+3+4=10)
    
    // 範囲最小値セグメントツリーでの二分探索
    // 位置0から右に見て値が3以下の最初の位置
    MinSegmentTree min_seg2(arr);
    pos = min_seg2.lower_bound(0, 3);
    cout << "値が3以下の最初の位置: " << pos << endl; // 位置0 (値1)
    
    // 範囲最大値セグメントツリーでの二分探索
    // 位置0から右に見て値が4以上の最初の位置
    MaxSegmentTree max_seg2(arr);
    pos = max_seg2.lower_bound(0, 4);
    cout << "値が4以上の最初の位置: " << pos << endl; // 位置3 (値4)
    
    // 汎用セグメントツリーでの二分探索（ラムダ式で条件指定）
    GenericLazySegmentTree<ll> generic_sum2(arr, 0LL, add_op);
    pos = generic_sum2.lower_bound(0, [](ll x) { return x >= 3; });
    cout << "条件を満たす最初の位置: " << pos << endl; // 位置2 (値3)
    
    return 0;
}
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

////////////////////////////////////////////////////////////////

// https://github.com/Gen1729/my-atcoder-library/blob/main/SparseTable.cpp
struct MinSparseTable {
    vvl table;
    vl log2_;

    // 半開区間 [l, r) で RMQ (Range Minimum Query)
    MinSparseTable(const vl& a) {
        ll n = a.size();
        ll LOG = floor(log(n)/log(2)) + 2;
        table.assign(LOG, vl(n));
        log2_.resize(n + 1);

        table[0] = a;
        for (ll k = 1; k < LOG; k++)
            for (ll i = 0; i + (1ll << k) <= n; i++)
                table[k][i] = min(table[k-1][i], table[k-1][i + (1ll << (k-1))]);

        log2_[1] = 0;
        for (ll i = 2; i <= n; i++)
            log2_[i] = log2_[i/2] + 1;
    }

    // 半開区間 [l, r) の最小値
    ll query(ll l, ll r) {
        ll k = log2_[r - l];
        return min(table[k][l], table[k][r - (1ll << k)]);
    }
};

struct MaxSparseTable {
    vvl table;
    vl log2_;

    // 半開区間 [l, r) で RMQ (Range Minimum Query)
    MaxSparseTable(const vl& a) {
        ll n = a.size();
        ll LOG = floor(log(n)/log(2)) + 2;
        table.assign(LOG, vl(n));
        log2_.resize(n + 1);

        table[0] = a;
        for (ll k = 1; k < LOG; k++)
            for (ll i = 0; i + (1ll << k) <= n; i++)
                table[k][i] = max(table[k-1][i], table[k-1][i + (1ll << (k-1))]);

        log2_[1] = 0;
        for (ll i = 2; i <= n; i++)
            log2_[i] = log2_[i/2] + 1;
    }

    // 半開区間 [l, r) の最小値
    ll query(ll l, ll r) {
        ll k = log2_[r - l];
        return max(table[k][l], table[k][r - (1ll << k)]);
    }
};

int main() {
    vl a = {3, 1, 4, 1, 5, 9, 2, 6};

    MinSparseTable st(a);

    // [1, 5) → a[1..4] = {1,4,1,5} → min = 1
    cout << st.query(1, 5) << "\n";  // 1

    // [2, 7) → a[2..6] = {4,1,5,9,2} → min = 1
    cout << st.query(2, 7) << "\n";  // 1

    // [5, 8) → a[5..7] = {9,2,6} → min = 2
    cout << st.query(5, 8) << "\n";  // 2
}
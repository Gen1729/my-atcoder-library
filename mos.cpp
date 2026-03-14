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
vl ans;
struct Mo{
    ll n,block,L,R;
    vl l,r,ord;
    Mo(){}
    Mo(ll N,ll Q):n(N){
        block = max(1LL,n/max(1LL,(ll)sqrt(Q)));
        L = 0;
        R = 0;
    }
    void add(ll L_,ll R_){
        l.pb(L_);
        r.pb(R_);
    }
    void build(){
        ll q=(ll)l.size();
        ord.resize(q);
        for(ll i=0;i<q;i++) ord[i] = i;
        sort(all(ord),[&](ll a,ll b){
            ll ab = l[a] / block,bb = l[b] / block;
            if(ab != bb) return ab < bb;
            if(ab & 1) return r[a] > r[b];
            return r[a] < r[b];
        });
    }
    void add_left(ll i){
        //配列のi番目を追加する
    }
    void add_right(ll i){
        //配列のi番目を追加する
    }
    void remove_left(ll i){
        //配列のi番目を削除する
    }
    void remove_right(ll i){
        //配列のi番目を削除する
    }
    void output(ll qi){
        //qi番目のクエリでどう答えるか
    }
    void process(){
        for(ll idx:ord){
            while(L > l[idx]) add_left(--L);
            while(R < r[idx]) add_right(R++);
            while(L < l[idx]) remove_left(L++);
            while(R > r[idx]) remove_right(--R);
            output(idx);
        }
    }
};

int main(){
    ll N,Q;
    cin >> N >> Q;
    Mo X(N,Q);

    ans.resize(Q);

    rep(i,Q){
        ll l,r;
        cin >> l >> r;
        X.add(l,r); // [l.r) 0-index
    }

    X.build();
    X.process();

    rep(i,Q)cout << ans[i] << endl;
}
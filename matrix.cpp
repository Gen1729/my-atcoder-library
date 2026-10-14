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

#define sz(s) (int)(s.size())

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

void print(ld x){printf("%.20Lf\n", x);}

////////////////////////////////////////////////////////////////

// https://github.com/Gen1729/my-atcoder-library/blob/main/matrix.cpp
template<typename T>
struct mat {
    // 行列m
    vector<vector<T>> m;
    // コンストラクタ:第1引数⇒行数、第2引数⇒列数、第3引数⇒初期値
    mat():m(vector<vector<T>>()){}
    mat(int h,int w):m(vector<vector<T>>(h,vector<T>(w))){}
    mat(int h,int w, T d):m(vector<vector<T>>(h,vector<T>(w,d))){}
    // 添字演算子
    const vector<T>& operator[](const int i) const { return m[i]; } //読み取り
    vector<T>& operator[](const int i){ return m[i]; } //書き込み
    // 行数・列数（動的に取得）
    int nrow() const { return (int)m.size(); }
    int ncol() const { return m.empty() ? 0 : (int)m[0].size(); }
    // 行列同士の演算
    mat& operator+=(const mat& a){ assert(ncol() == a.ncol() && nrow() == a.nrow()); rep(i,nrow()) rep(j,ncol()) m[i][j] += a[i][j]; return *this; }
    mat& operator-=(const mat& a){ assert(ncol() == a.ncol() && nrow() == a.nrow()); rep(i,nrow()) rep(j,ncol()) m[i][j] -= a[i][j]; return *this; }
    mat& operator*=(const mat& a){ assert(ncol() == a.nrow()); mat<T> m2(nrow(), a.ncol(), 0); rep(i,nrow()) rep(j,a.ncol()) rep(k,ncol()) m2[i][j] += m[i][k]*a[k][j]; m = std::move(m2.m); return *this; }
    mat operator+(const mat& a) const { return mat(*this) += a;}
    mat operator-(const mat& a) const { return mat(*this) -= a;}
    mat operator*(const mat& a) const { return mat(*this) *= a;}
    bool operator==(const mat& a){ assert(ncol() == a.ncol() && nrow() == a.nrow()); bool flg = true; rep(i,nrow()) rep(j,ncol()) if(m[i][j] != a[i][j]) flg = false; return flg; }
    // 行列とスカラの演算
    mat& operator+=(const T& a){ rep(i,nrow()) rep(j,ncol()) m[i][j] += a; return *this; }
    mat& operator-=(const T& a){ rep(i,nrow()) rep(j,ncol()) m[i][j] -= a; return *this; }
    mat& operator*=(const T& a){ rep(i,nrow()) rep(j,ncol()) m[i][j] *= a; return *this; }
    mat& operator/=(const T& a){ rep(i,nrow()) rep(j,ncol()) m[i][j] /= a; return *this; }
    mat& operator%=(const T& a){ rep(i,nrow()) rep(j,ncol()) m[i][j] %= a; return *this; }
    mat operator+(const T& a) const { return mat(*this) += a;}
    mat operator-(const T& a) const { return mat(*this) -= a;}
    mat operator*(const T& a) const { return mat(*this) *= a;}
    mat operator/(const T& a) const { return mat(*this) /= a;}
    mat operator%(const T& a) const { return mat(*this) %= a;}
    // 回転（degの数だけ時計回りに90度回転）
    mat& rot(int deg){
        mat<T> m2(ncol(), nrow());
        if(deg == 1 || deg == 3){
            if(deg == 1) rep(i,nrow()) rep(j,ncol()) m2[j][nrow() - i - 1] = m[i][j];
            if(deg == 3) rep(i,nrow()) rep(j,ncol()) m2[ncol() - j - 1][i] = m[i][j];
        } else if(deg == 2){
            rep(i,nrow()) rep(j,ncol()) m2[nrow() - i - 1][ncol() - j - 1] = m[i][j];
        }
        m = std::move(m2.m);
        return *this;
    }
    // 標準出力
    void show(){
        rep(i,nrow()) rep(j,ncol()){
            if(j != 0) cout << " ";
            cout << m[i][j];
            if(j==ncol()-1) cout << endl;
        }
        return ;
    }
};

// 2次元配列の生成
// 行列の演算（加減乗除、代入）
// 2次元配列の回転
// 2次元配列の出力

int main(){

    mat<int> m(2,3,2),m2(3,2,1); // オブジェクトの作成
    m[0][0] = 1; // 一部の要素を書き換え
    m.show(); // 表示
    cout << endl;

    mat<int> m3 = m * m2; // 行列同士の掛け算
    m3.show();
    cout << endl;

    m.rot(1); //時計回りに90度回転 数字の数だけ回転
    m.show();

    return 0;
}

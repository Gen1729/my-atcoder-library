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
#include <cstdbool>
#include <cstdint>
#include <atcoder/all>

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
const int MAX = 510000;

ll fac[MAX], finv[MAX], inv[MAX];

// テーブルを作る前処理
void COMinit() {
    fac[0] = fac[1] = 1;
    finv[0] = finv[1] = 1;
    inv[1] = 1;
    for (ll i = 2; i < MAX; i++){
        fac[i] = fac[i - 1] * i % MOD;
        inv[i] = MOD - inv[MOD%i] * (MOD / i) % MOD;
        finv[i] = finv[i - 1] * inv[i] % MOD;
    }
}
// 二項係数計算
ll COM(ll n, ll k){
    if (n < k) return 0;
    if (n < 0 || k < 0) return 0;
    return fac[n] * (finv[k] * finv[n - k] % MOD) % MOD;
}

// mod pが素数でないがn,kが小さいとき
const int MAX_C = 5000;
vvl Com(MAX_C,vl(MAX_C,0));
void calc_com() {
    Com[0][0] = 1;
    for (int i = 1; i < MAX_C; ++i) {
        Com[i][0] = 1;
        for (int j = 1; j < MAX_C; ++j) {
            Com[i][j] = (Com[i-1][j-1] + Com[i-1][j]) % MOD;
        }
    }
}

//約数列挙
vl makediv(ll n) {
    vl ld, ud;
    for (ll i = 1; i * i <= n; i++) {
        if (n % i == 0) {
            ld.push_back(i);
            if (n / i != i) {
                ud.push_back(n / i);
            }
        }
    }
    reverse(ud.begin(), ud.end());
    ld.insert(ld.end(), ud.begin(), ud.end());
    return ld;
}
//素因数分解
vc<pll> prime_factorization(ll n) {
    vc<pll> ret;
    for (ll i = 2; i * i <= n; i++) {
        if (n % i == 0) {
            ll a = 0;
            while (n % i == 0) {
                a++;
                n /= i;
            }
            ret.pb({i, a});
        }
    }
    if (n > 1){
        ret.pb({n, 1});
    }
    return ret;
}
//前計算をすることでlognで素因数分解
struct PrimeFact {
    vl spf;
    PrimeFact(ll N) { init(N); }
    void init(ll N) { // 前処理。spf を求める
        spf.assign(N + 1, 0);
        for (ll i = 0; i <= N; i++) spf[i] = i;
        for (ll i = 2; i * i <= N; i++) {
            if (spf[i] == i) {
                for (ll j = i * i; j <= N; j += i) {
                    if (spf[j] == j) {
                        spf[j] = i;
                    }
                }
            }
        }
    }
    map<ll, ll> get(ll n) { // nの素因数分解を求める
        map<ll, ll> m;
        while (n != 1) {
            m[spf[n]]++;
            n /= spf[n];
        }
        return m;
    }
};
//逆元計算
ll modinv(ll a, ll m) {
	ll b = m, u = 1, v = 0;
	while (b) {
		ll t = a / b;
		a -= t * b; swap(a, b);
		u -= t * v; swap(u, v);
	}
	u %= m;
	if (u < 0) u += m;
	return u;
}
//最大公約数
ll GCD(ll A,ll B){
    while(A >= 1 && B >= 1){
        if(A >= B){
            A = (A%B);
        }else{
            B = (B%A);
        }
    }
    if(A != 0)return A;
    return B;
}

// エラトステレスの篩
vector<bool> Eratosthenes(ll N) {
    vector<bool> isprime(N+1, true);
    isprime[0] = isprime[1] = false;

    for (ll p = 2; p <= N; ++p) {
        if (!isprime[p]) continue;

        for (ll q = p * 2; q <= N; q += p) {
            isprime[q] = false;
        }
    }

    return isprime;
}

//区間ふるい
vector<bool> SegmentedSieve(ll A,ll B) {
    // √B 以下の素数を炙り出すための篩
    // ここでは大きめにサイズ 1100000 まで確保しておく
    vector<bool> isprime(10000000, true);

    // A 以上 B 以下の整数 v が素数かどうか
    // その答えは isprime2[v-A] に格納される
    vector<bool> isprime2(B - A + 1, true);

    // ふるい
    for (long long p = 2; p * p <= B; ++p) {
        // すでに合成数であるものはスキップする
        if (!isprime[p]) continue;

        // p 以外の p の倍数から素数ラベルを剥奪
        for (long long q = p * 2; q * q <= B; q += p) {
            isprime[q] = false;
        }

        // start: A 以上の最小の p の倍数
        long long start = (A + p - 1) / p * p;
        if (start == p) start = p * 2;

        // A 以上 B 以下の整数のうち、p の倍数をふるう
        for (long long q = start; q <= B; q += p) {
            isprime2[q - A] = false;
        }
    }

    return isprime2;
}

// Miller-Rabin
// miller_rabin(n) : 1以下の整数もしくは合成数ならfalse、素数ならtrueを返す
uint64_t modmul(uint64_t a, uint64_t b, uint64_t n) {
    return (uint64_t)(((__uint128_t)a) * ((__uint128_t)b) % ((__uint128_t)n));
}
uint64_t modpow(uint64_t a, uint64_t b, uint64_t n) {
    uint64_t t = ((b & 1) == 0) ? 1 : a;
    for (b >>= 1; b != 0; b >>= 1) {
        a = modmul(a, a, n);
	if ((b & 1) == 1) { t = modmul(t, a, n); } 
    }
    return t;
}
const uint64_t bases[] = {2,325,9375,28178,450775,9780504,1795265022};
bool miller_rabin(uint64_t n) {
    if (n == 2) { return true; }
    if (n < 2 || (n & 1) == 0) { return false; }
    uint64_t n1 = n - 1, d = n - 1;
    uint32_t s = 0;
    for (; (d & 1) == 0; d >>= 1) { s += 1; }
    for (const auto& base : bases) {
        uint64_t a = base;
        if (a >= n) {
	    a %= n;
	    if (a == 0) { continue; }
	}
        uint64_t t = modpow(a, d, n);
        if (t == 1) { continue; }
        for (uint32_t j = 1; t != n1; ++j) {
            if (j >= s) { return false; }
            t = modmul(t, t, n);
        }
    }
    return true;
}

//n進法をm進法に変換
void ntom(string str, ll n, ll m, string &res) {
    unsigned long long sum = 0;
    for (char c : str) {
        sum = sum * n + (c - '0');
    }
    res = "";
    do {
        int num = sum % m;
        res = res + static_cast<char>(num + '0');
        sum /= m;
    } while (sum);
    reverse(all(res));
}

// A Bに巨大数を配列にしたもの　A+Bを計算する 符号はtrueなら+ falseなら-
void integer_addition(vl &A, vl &B, bool Asign, bool Bsign, vl &res, bool &res_sign){

    ll Asz = A.size();
    ll Bsz = B.size();

    ll sz = max(A.size(),B.size());
    res.resize(sz,0);

    bool sign = (Asign == Bsign);

    rep(i,sz){
        ll a = 0,b = 0;
        if(Asz > i){
            a = A[i];
        }
        if(Bsz > i){
            b = B[i];
        }
        if(sign)res[i] = a + b;
        else res[i] = a - b;
    }

    if(sign){
        rep(i,sz){
            if(i == sz - 1 && res[i] / 10 > 0){
                res.pb(res[i] / 10);
            }else if(i != sz - 1){
                res[i+1] += res[i] / 10;
            }
            res[i] %= 10;
        }
        res_sign = true;
    }else{
        rep(i,sz-1){
            if(res[i] < 0){
                res[i] += 10;
                res[i+1] -= 1;
            }
        }
        res_sign = true;
        if(res[sz-1] < 0){
            res[sz - 1] += 10;

            rep(i,sz){
                res[i] = 9 - res[i];
            }
            res[0]++;
            rep(i,sz){
                if(res[i] == 10){
                    res[i] = 0;
                    res[i+1]++;
                }else{
                    break;
                }
            }

            res_sign = false;
        }
    }

    while(res.size() > 1){
        if(res.back() == 0){
            res.pob();
        }else{
            break;
        }
    }

    if(!Asign)res_sign = 1 - res_sign;
    if(res.size() == 1 && res[0] == 0)res_sign = true;

    return;
}

int main() {
    long long N;
    cin >> N;
    vl res = makediv(N);
    rep(i,res.size()) cout << res[i] << " ";
    cout << endl;

    vc<pll> ret = prime_factorization(N);
    rep(i,ret.size()) cout << "{" << ret[i].fi << "," << ret[i].se << "}" << endl;;
    cout << endl;

    cout << modinv(N,MOD) << endl;

    // 前処理
    COMinit();

    // 計算例
    cout << COM(100000, 50000) << endl;

    vc<bool> isP = Eratosthenes(50);

    string s = "21";
    const int n = 8, m = 9; // n進数 -> m進数
    string ress;
    ntom(s, n, m, ress);
    cout << s << ' ' << ress << '\n';

}
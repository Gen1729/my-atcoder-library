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
// ai+bj=gcd(a,b)なるi,jを求める
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

// https://github.com/Gen1729/my-atcoder-library/blob/main/Fraction.cpp
class Fraction
{
private:
	long long numer;	// 分子
	long long denom;	// 分母

	friend const bool operator==(const Fraction& a, const Fraction& b);
	friend const bool operator!=(const Fraction& a, const Fraction& b);
	friend const bool operator>=(const Fraction& a, const Fraction& b);
	friend const bool operator<=(const Fraction& a, const Fraction& b);
	friend const bool operator>(const Fraction& a, const Fraction& b);
	friend const bool operator<(const Fraction& a, const Fraction& b);

	friend const Fraction operator+(const Fraction& a, const Fraction& b);
	friend const Fraction operator-(const Fraction& a, const Fraction& b);
	friend const Fraction operator*(const Fraction& a, const Fraction& b);
	friend const Fraction operator/(const Fraction& a, const Fraction& b);

public:
	Fraction();
	Fraction(long long);
	Fraction(long long, long long);
	Fraction(const Fraction&);

	void set(long long, long long);
	void set(const Fraction&);
	void setNumer(long long);
	void setDenom(long long);

	long long getNumer();
	long long getDenom();

	static long long gcd(long long, long long);	// 最大公約数
	static long long lcm(long long, long long);	// 最小公倍数
	void normal();	// 約分

	std::string toString();
	long double toLongDouble();

	bool equals(const Fraction&) const;
	long long compare(const Fraction&) const;

	Fraction& operator=(const Fraction& b);

	Fraction& operator+=(const Fraction& b);
	Fraction& operator-=(const Fraction& b);
	Fraction& operator*=(const Fraction& b);
	Fraction& operator/=(const Fraction& b);

	Fraction operator+();
	Fraction operator-();

	Fraction& operator++();
	Fraction  operator++(int);

	Fraction& operator--();
	Fraction  operator--(int);
};

long long Fraction::gcd(long long a, long long b)
{
	a = abs(a);
	b = abs(b);
	if (a < b) std::swap(a, b);

	long long tmp;
	while (b != 0) {
		tmp = b;
		b = a % b;
		a = tmp;
	}

	return a;
}
long long Fraction::lcm(long long a, long long b)
{
	a = abs(a);
	b = abs(b);
	if (a > b) std::swap(a, b);

	if (a == 1) return b;

	long long i = a;
	while (i % b != 0)
	{
		i += a;
	}
	return i;
}

Fraction::Fraction()
{
	set(0, 1);
}
Fraction::Fraction(long long n)
{
	set(n, 1);
}
Fraction::Fraction(long long numer, long long denom)
{
	set(numer, denom);
}
Fraction::Fraction(const Fraction& b)
{
	set(b);
}

void Fraction::set(long long numer, long long denom)
{
	this->numer = numer;
	this->denom = denom;
	normal();
}
void Fraction::set(const Fraction& b)
{
	this->numer = b.numer;
	this->denom = b.denom;
}
void Fraction::setNumer(long long numer)
{
	this->numer = numer;
	normal();
}
void Fraction::setDenom(long long denom)
{
	this->denom = denom;
	normal();
}

inline long long Fraction::getNumer()
{
	return numer;
}
inline long long Fraction::getDenom()
{
	return denom;
}

void Fraction::normal()
{
	long long gcd = this->gcd(getNumer(), getDenom());

	if (gcd == 1)
	{
		// 分母は常に正
		if (denom < 0)
		{
			numer *= -1;
			denom *= -1;
		}

		return;
	}

	long long numer = getNumer() / gcd;
	long long denom = getDenom() / gcd;

	// 分母は常に正
	if (denom < 0)
	{
		numer *= -1;
		denom *= -1;
	}

	set(numer, denom);
}

std::string Fraction::toString()
{
	std::string str = "";

	if (getDenom() == 1)
		str = std::to_string(getNumer());
	else
		str = std::to_string(getNumer()) + "/" + std::to_string(getDenom());

	return str;
}
long double Fraction::toLongDouble()
{
	return (long double)getNumer() / getDenom();
}

bool Fraction::equals(const Fraction& b) const {
	return numer == b.numer && denom == b.denom;
}
long long Fraction::compare(const Fraction& b) const  {
	long long lcm = this->lcm(denom, b.denom);

	return (lcm / denom) * numer - (lcm / b.denom) * b.numer;
}

const bool operator==(const Fraction& a, const Fraction& b) { return  a.equals(b); }
const bool operator!=(const Fraction& a, const Fraction& b) { return !a.equals(b); }
const bool operator>=(const Fraction& a, const Fraction& b) { return a.compare(b) >= 0; }
const bool operator<=(const Fraction& a, const Fraction& b) { return a.compare(b) <= 0; }
const bool operator>(const Fraction& a, const Fraction& b) { return a.compare(b) > 0; }
const bool operator<(const Fraction& a, const Fraction& b) { return a.compare(b) < 0; }

Fraction& Fraction::operator=(const Fraction& b) {
	this->set(b);

	return *this;
}

const Fraction operator+(const Fraction& a, const Fraction& b) {
	long long lcm = Fraction::lcm(a.denom, b.denom);
	long long numer = a.numer * (lcm / a.denom) + b.numer * (lcm / b.denom);

	return Fraction(numer, lcm);
}
const Fraction operator-(const Fraction& a, const Fraction& b) {
	return operator+(a, Fraction(-b.numer, b.denom));
}
const Fraction operator*(const Fraction& a, const Fraction& b) {
	long long gcd = Fraction::gcd(a.numer, b.denom);
	long long numer = a.numer / gcd;
	long long denom = b.denom / gcd;

	gcd = Fraction::gcd(b.numer, a.denom);
	numer *= b.numer / gcd;
	denom *= a.denom / gcd;

	return Fraction(numer, denom);
}
const Fraction operator/(const Fraction& a, const Fraction& b) {
	return operator*(a, Fraction(b.denom, b.numer));
}

Fraction& Fraction::operator+=(const Fraction& b) { return *this = *this + b; }
Fraction& Fraction::operator-=(const Fraction& b) { return *this = *this - b; }
Fraction& Fraction::operator*=(const Fraction& b) { return *this = *this * b; }
Fraction& Fraction::operator/=(const Fraction& b) { return *this = *this / b; }

Fraction Fraction::operator+() { return Fraction(this->numer, this->denom); };
Fraction Fraction::operator-() { return Fraction(-(this->numer), this->denom); };

Fraction& Fraction::operator++() { return *this += 1; }
Fraction& Fraction::operator--() { return *this += -1; }
Fraction Fraction::operator++(int) {
	Fraction tmp = *this;
	*this += 1;
	return tmp;
}
Fraction Fraction::operator--(int) {
	Fraction tmp = *this;
	*this += -1;
	return tmp;
}

int main(){
	// 1. 生成
	Fraction a;              // 0/1
	Fraction b(3);           // 3/1
	Fraction c(6, 8);        // 3/4 に約分される
	Fraction d(c);           // コピーコンストラクタ

	cout << "a = " << a.toString() << endl;
	cout << "b = " << b.toString() << endl;
	cout << "c = " << c.toString() << endl;
	cout << "d = " << d.toString() << endl;

	// 2. setter / getter
	a.set(10, 20);           // 1/2 に約分される
	b.setNumer(7);           // 7/1
	b.setDenom(3);           // 7/3

	cout << "a = " << a.toString() << endl;
	cout << "b numer = " << b.getNumer() << ", denom = " << b.getDenom() << endl;

	// 3. 文字列化・実数化
	cout << "a as long double = " << fixed << setprecision(10) << a.toLongDouble() << endl;
	cout << "c as string = " << c.toString() << endl;

	// 4. 代入
	Fraction e;
	e = Fraction(5, 6);
	cout << "e = " << e.toString() << endl;

	// 5. 四則演算
	Fraction f = a + c;
	Fraction g = a - c;
	Fraction h = a * c;
	Fraction i = a / c;

	cout << "a + c = " << f.toString() << endl;
	cout << "a - c = " << g.toString() << endl;
	cout << "a * c = " << h.toString() << endl;
	cout << "a / c = " << i.toString() << endl;

	// 6. 代入付き四則演算
	Fraction j = a;
	j += c;
	cout << "j += c -> " << j.toString() << endl;
	j -= c;
	cout << "j -= c -> " << j.toString() << endl;
	j *= c;
	cout << "j *= c -> " << j.toString() << endl;
	j /= c;
	cout << "j /= c -> " << j.toString() << endl;

	// 7. 単項演算
	cout << "+a = " << (+a).toString() << endl;
	cout << "-a = " << (-a).toString() << endl;

	// 8. 比較
	cout << boolalpha;
	cout << "a == c : " << (a == c) << endl;
	cout << "a != c : " << (a != c) << endl;
	cout << "a < c  : " << (a < c) << endl;
	cout << "a <= c : " << (a <= c) << endl;
	cout << "a > c  : " << (a > c) << endl;
	cout << "a >= c : " << (a >= c) << endl;

	// 9. インクリメント / デクリメント
	Fraction k(1, 2);
	cout << "k = " << k.toString() << endl;
	cout << "++k = " << (++k).toString() << endl;
	cout << "k++ = " << (k++).toString() << endl;
	cout << "after k++ , k = " << k.toString() << endl;
	cout << "--k = " << (--k).toString() << endl;
	cout << "k-- = " << (k--).toString() << endl;
	cout << "after k-- , k = " << k.toString() << endl;

	// 10. static 関数
	cout << "Fraction::gcd(24, 18) = " << Fraction::gcd(24, 18) << endl;
	cout << "Fraction::lcm(12, 18) = " << Fraction::lcm(12, 18) << endl;

	// 11. normal() の利用例
	Fraction m;
	m.set(100, 250);
	m.normal();
	cout << "m normalized = " << m.toString() << endl;

	return 0;
}
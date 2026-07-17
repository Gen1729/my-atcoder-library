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
const double eps = 1e-9;
bool equal(double a, double b) { return abs(a-b) < eps;}
const double PI = acos(-1.0);

///////////////////////////////////////////////////////////////
// geom/vector.cpp 相当
///////////////////////////////////////////////////////////////
struct V {
    double x, y;
    V(double x=0, double y=0): x(x), y(y) {}
    V& operator+=(const V& v) { x += v.x; y += v.y; return *this;}
    V operator+(const V& v) const { return V(*this) += v;}
    V& operator-=(const V& v) { x -= v.x; y -= v.y; return *this;}
    V operator-(const V& v) const { return V(*this) -= v;}
    V& operator*=(double s) { x *= s; y *= s; return *this;}
    V operator*(double s) const { return V(*this) *= s;}
    V& operator/=(double s) { x /= s; y /= s; return *this;}
    V operator/(double s) const { return V(*this) /= s;}
    double dot(const V& v) const { return x*v.x + y*v.y;}
    double cross(const V& v) const { return x*v.y - v.x*y;}
    double norm2() const { return x*x + y*y;}
    double norm() const { return sqrt(norm2());}
    double angleRad(const V& v) const { return atan2(abs(cross(v)), dot(v));}
    double angleDeg(const V& v) const { return angleRad(v) * 180.0 / PI;}
    V normalize() const { return *this/norm();}
    V rotate90() const { return V(y, -x);}
    int ort() const { // orthant
        if (abs(x) < eps && abs(y) < eps) return 0;
        if (y > 0) return x>0 ? 1 : 2;
        else return x>0 ? 4 : 3;
    }
    bool operator<(const V& v) const {
        int o = ort(), vo = v.ort();
        if (o != vo) return o < vo;
        return cross(v) > 0;
    }
};
istream& operator>>(istream& is, V& v) {
    is >> v.x >> v.y; return is;
}
ostream& operator<<(ostream& os, const V& v) {
    os<<"("<<v.x<<","<<v.y<<")"; return os;
}

///////////////////////////////////////////////////////////////
// geom/line.cpp 相当
///////////////////////////////////////////////////////////////
struct Line {
    V s, t;
    Line(V s=V(0,0), V t=V(0,0)):s(s),t(t){}
    V dir() const { return t-s;}
    V normalize() const { return dir().normalize();}
    double norm() const { return dir().norm();}
    /* +1: s-t,s-p : ccw
    * -1: s-t,s-p : cw
    * +2: t-s-p
    * -2: s-t-p
    *  0: s-p-t */
    int ccw(const V& p) const {
        if (dir().cross(p-s) > eps) return +1;
        if (dir().cross(p-s) < -eps) return -1;
        if (dir().dot(p-s) < -eps) return +2;
        if (dir().dot(t-p) < -eps) return -2;
        return 0;
    }
    bool touch(const Line& l) const {
        int a = ccw(l.s)*ccw(l.t), b = l.ccw(s)*l.ccw(t);
        return !a || !b || (a == -1 && b == -1);
    }
};
///////////////////////////////////////////////////////////////
// geom/circle.cpp 相当
///////////////////////////////////////////////////////////////
struct Circle {
    V o; double r;
    Circle(V o=V(), double r=0) : o(o), r(r) {}
    vector<V> crossPoint(const Circle& c) {
        V v = c.o-o;
        double l = v.norm();
        if (equal(l, 0)) return {};
        if (equal(l+r+c.r, max({l,r,c.r})*2)) {
        if (equal(l+r,c.r)) return {o - v*(r/l)};
            return {o + v*(r/l)};
        }
        if (l+r+c.r < max({l,r,c.r})*2) return {};
        double x = (l*l + r*r - c.r*c.r) / (2*l);
        double y = sqrt(r*r - x*x);
        V mid = o + v*(x/l);
        v = v.rotate90();
        return {mid + v*(y/l), mid - v*(y/l)};
    }
    bool isInside(const V& p) const {
        return (p-o).norm() < r+eps;
    }
};

int main() {
    cout << fixed << setprecision(12);

    // 1) 線分交差チェック
    V p1, p2, p3, p4;
    cin >> p1 >> p2 >> p3 >> p4;

    Line l1(p1, p2), l2(p3, p4);
    cout << "segment_touch: " << (l1.touch(l2) ? "Yes" : "No") << "\n";
    cout << "ccw(l1, p3): " << l1.ccw(p3) << "\n";
    // ccwは
    // 左回り(+1) / 右回り(-1)
    // 線上かつ区間外(+2/-2)
    // 線分上(0)
    // を判定できる
    cout << "ccw(l1, p4): " << l1.ccw(p4) << "\n";

    // 2) 円と円の交点
    V c1o, c2o;
    double r1, r2;
    cin >> c1o >> r1 >> c2o >> r2;

    Circle c1(c1o, r1), c2(c2o, r2);
    auto cps = c1.crossPoint(c2);

    cout << "circle_cross_points_count: " << cps.size() << "\n";
    rep(i, (ll)cps.size()) {
        cout << "cp[" << i << "]: " << cps[i].x << " " << cps[i].y << "\n";
    }

    // 3) 点の内外判定
    V q;
    cin >> q;
    cout << "point_in_c1: " << (c1.isInside(q) ? "Yes" : "No") << "\n";

    // 4) ベクトル演算デモ（p1->p2, p1->p3）
    V a = p2 - p1;
    V b = p3 - p1;
    cout << "dot(a,b): " << a.dot(b) << "\n";
    cout << "cross(a,b): " << a.cross(b) << "\n";
    cout << "|a|: " << a.norm() << "\n";
    // a,bの順番は問わない 0度から180度の範囲で返す
    cout << "angle_rad(a,b): " << a.angleRad(b) << "\n";
    cout << "angle_deg(a,b): " << a.angleDeg(b) << "\n";

    return 0;
}
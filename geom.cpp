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
const ld INFld = 1LL<<60;
const ld EPS = 1e-10;
const ld PI = acosl(-1.0);

using Point = pair<ld, ld>;
using Vector = Point;

// 座標（ベクトル）の足し算、引き算（定数倍なども補助として実装）
Point operator+(const Point& a, const Point& b) {
    return {a.first + b.first, a.second + b.second};
}
Point operator-(const Point& a, const Point& b) {
    return {a.first - b.first, a.second - b.second};
}
Point operator*(const Point& a, ld k) {
    return {a.first * k, a.second * k};
}
Point operator/(const Point& a, ld k) {
    return {a.first / k, a.second / k};
}

// ベクトルの内積・外積・長さの2乗
// 内積 (Dot product)
ld dot(const Vector& a, const Vector& b) {
    return a.first * b.first + a.second * b.second;
}

// 外積 (Cross product)
ld cross(const Vector& a, const Vector& b) {
    return a.first * b.second - a.second * b.first;
}

// 長さの2乗 (Squared norm)
ld norm2(const Vector& a) {
    return a.first * a.first + a.second * a.second;
}

// 2点 p1, p2 の中点を求める
Point midpoint(const Point& p1, const Point& p2) {
    return (p1 + p2) / 2.0;
}

// 2点 p1, p2 間の距離を求める
ld distance2(const Point& p1, const Point& p2) {
    return norm2(p1 - p2); // hypotl(p1.first - p2.first, p1.second - p2.second) でも可
}

// ax+by+c=0 の形の直線
struct Line {
    ld a, b, c;
};

// 2点を結ぶ直線、垂直二等分線の計算
// 2点 p1, p2 を通る直線 ax+by+c=0 を返す
Line get_line(const Point& p1, const Point& p2) {
    Line l;
    l.a = p1.second - p2.second; // y1 - y2
    l.b = p2.first - p1.first;   // x2 - x1
    l.c = p1.first * p2.second - p2.first * p1.second; // x1*y2 - x2*y1
    return l;
}

// 2点 p1, p2 の垂直二等分線 ax+by+c=0 を返す
Line get_perpendicular_bisector(const Point& p1, const Point& p2) {
    Line l;
    l.a = p2.first - p1.first;   // x2 - x1
    l.b = p2.second - p1.second; // y2 - y1
    // - (a * 中点のx座標 + b * 中点のy座標)
    l.c = -0.5 * ((p2.first * p2.first - p1.first * p1.first) + 
                  (p2.second * p2.second - p1.second * p1.second));
    return l;
}

// 点 p と直線 l の距離の2乗を返す
ld distance_between_point_and_line2(const Point& p, const Line& l) {
    ld numerator = l.a * p.first + l.b * p.second + l.c;
    return numerator * numerator / (l.a * l.a + l.b * l.b);
}

// 点 p と線分 a-b の距離の2乗を返す
ld distance_between_point_and_segment2(const Point& p,
                                       const Point& a,
                                       const Point& b) {
    Vector ab = b - a;
    ld ab_norm2 = norm2(ab);
    if (ab_norm2 < EPS) return distance2(p, a);

    ld t = dot(p - a, ab) / ab_norm2;
    t = max(0.0L, min(1.0L, t));
    Point projection = a + ab * t;
    return distance2(p, projection);
}

// 点 p を通り、直線 l に垂直な直線を返す
Line get_perpendicular_line(const Point& p, const Line& l) {
    return {l.b, -l.a, l.a * p.second - l.b * p.first};
}

// 2直線の交点
// 交差しない（平行）の場合は {INFld, INFld} を返す
Point get_intersection(const Line& l1, const Line& l2) {
    ld det = l1.a * l2.b - l2.a * l1.b;
    if (abs(det) < EPS) {
        return {INFld, INFld}; // 平行
    }
    ld x = (l1.b * l2.c - l2.b * l1.c) / det;
    ld y = (l1.c * l2.a - l2.c * l1.a) / det;
    return {x, y};
}

// ccw (Counter-Clockwise)
// p0 を基準としたときの p1 と p2 の位置関係を返す
// 1: 反時計回り (COUNTER_CLOCKWISE)
// -1: 時計回り (CLOCKWISE)
// 2: p2, p0, p1 の順で一直線上 (ONLINE_BACK)
// -2: p0, p1, p2 の順で一直線上 (ONLINE_FRONT)
// 0: p0, p2, p1 の順で一直線上 (ON_SEGMENT)
int ccw(const Point& p0, const Point& p1, const Point& p2) {
    Vector a = p1 - p0;
    Vector b = p2 - p0;
    
    if (cross(a, b) > EPS) return 1;
    if (cross(a, b) < -EPS) return -1;
    if (dot(a, b) < -EPS) return 2;
    if (norm2(a) < norm2(b)) return -2;
    return 0;
}

// 線分 p1-p2 と線分 p3-p4 が交差するかを返す
bool intersect(const Point& p1, const Point& p2,
               const Point& p3, const Point& p4) {
    auto orientation = [](const Point& a, const Point& b, const Point& c) {
        return cross(b - a, c - a);
    };
    auto on_segment = [](const Point& a, const Point& b, const Point& p) {
        return abs(cross(b - a, p - a)) < EPS
            && min(a.first, b.first) - EPS <= p.first
            && p.first <= max(a.first, b.first) + EPS
            && min(a.second, b.second) - EPS <= p.second
            && p.second <= max(a.second, b.second) + EPS;
    };

    ld o1 = orientation(p1, p2, p3);
    ld o2 = orientation(p1, p2, p4);
    ld o3 = orientation(p3, p4, p1);
    ld o4 = orientation(p3, p4, p2);

    if (((o1 > EPS && o2 < -EPS) || (o1 < -EPS && o2 > EPS))
        && ((o3 > EPS && o4 < -EPS) || (o3 < -EPS && o4 > EPS))) {
        return true;
    }
    return (abs(o1) < EPS && on_segment(p1, p2, p3))
        || (abs(o2) < EPS && on_segment(p1, p2, p4))
        || (abs(o3) < EPS && on_segment(p3, p4, p1))
        || (abs(o4) < EPS && on_segment(p3, p4, p2));
}

// 線分 p1-p2 と線分 p3-p4 の距離の2乗を返す
ld distance_between_segment_and_segment2(const Point& p1, const Point& p2,
             const Point& p3, const Point& p4) {
    if (intersect(p1, p2, p3, p4)) return 0.0;

    return min({
        distance_between_point_and_segment2(p1, p3, p4),
        distance_between_point_and_segment2(p2, p3, p4),
        distance_between_point_and_segment2(p3, p1, p2),
        distance_between_point_and_segment2(p4, p1, p2)
    });
}

// 多角形の面積を返す
ld polygon_area(const vc<Point>& polygon) {
    ld signed_double_area = 0.0;
    for (size_t i = 0; i < polygon.size(); i++) {
        signed_double_area += cross(polygon[i], polygon[(i + 1) % polygon.size()]);
    }
    return abs(signed_double_area) / 2.0;
}

// 多角形の重心を面積公式で求める
Point polygon_area_formula(const vc<Point>& polygon) {
    if (polygon.empty()) return {INFld, INFld};

    ld signed_double_area = 0.0;
    Point weighted_sum = {0.0, 0.0};
    for (size_t i = 0; i < polygon.size(); i++) {
        const Point& current = polygon[i];
        const Point& next = polygon[(i + 1) % polygon.size()];
        ld cross_value = cross(current, next);
        signed_double_area += cross_value;
        weighted_sum = weighted_sum + (current + next) * cross_value;
    }
    if (abs(signed_double_area) < EPS) return {INFld, INFld};
    return weighted_sum / (3.0 * signed_double_area);
}

// 下側凸包を求める関数
// 点群をx座標優先でソートした状態から、下側の境界線を走査して構築します。
vc<Point> lower_hull(vc<Point> ps) {
    int n = ps.size();
    if (n <= 2) return ps;
    
    // x座標が昇順（等しい場合はy座標が昇順）になるようにソート
    sort(ps.begin(), ps.end());

    vc<Point> res;
    for (int i = 0; i < n; i++) {
        // 時計回り（右折）または一直線上の場合は直前の点を取り除く
        // 厳密な凸包（途中の3点が一直線上に並ばない）にするため cross <= EPS としています
        while (res.size() >= 2 && cross(res.back() - res[res.size() - 2], ps[i] - res.back()) < 0) {
            res.pop_back();
        }
        res.push_back(ps[i]);
    }
    return res;
}

// 上側凸包を求める関数
// 点群をx座標優先でソートした状態から、上側の境界線を走査して構築します。
vc<Point> upper_hull(vc<Point> ps) {
    int n = ps.size();
    if (n <= 2) return ps;

    // x座標が昇順（等しい場合はy座標が昇順）になるようにソート
    sort(ps.begin(), ps.end());

    vc<Point> res;
    for (int i = 0; i < n; i++) {
        // 反時計回り（左折）または一直線上の場合は直前の点を取り除く
        while (res.size() >= 2 && cross(res.back() - res[res.size() - 2], ps[i] - res.back()) > 0) {
            res.pop_back();
        }
        res.push_back(ps[i]);
    }
    return res;
}

// 下側凸包と上側凸包を合成して反時計回りの全凸包を求める関数
vc<Point> convex_hull(vc<Point> ps) {
    int n = ps.size();
    if (n <= 2) return ps;

    vc<Point> lower = lower_hull(ps);
    vc<Point> upper = upper_hull(ps);

    // lower は左から右への下側境界
    // upper は左から右への上側境界なので、逆順に連結することで右から左への上側境界にする
    // 両端の重複要素（端点）を除外して結合する
    vc<Point> res = lower;
    for (int i = (int)upper.size() - 2; i > 0; i--) {
        res.push_back(upper[i]);
    }
    return res;
}

int main() {
    // 出力の精度を設定
    cout << fixed << setprecision(12);
    
    // 1. ベクトルの足し算・引き算
    Point p1 = {2.0, 3.0};
    Point p2 = {1.0, 5.0};
    Point p_add = p1 + p2;
    Point p_sub = p1 - p2;
    cout << "--- Vector Operations ---" << endl;
    cout << "p1 + p2 = (" << p_add.first << ", " << p_add.second << ")" << endl;
    cout << "p1 - p2 = (" << p_sub.first << ", " << p_sub.second << ")" << endl;

    // 中点の計算
    Point mid = midpoint(p1, p2);
    cout << "--- Midpoint & Distance ---" << endl;
    cout << "Midpoint of p1 and p2: (" << mid.first << ", " << mid.second << ")" << endl;

    // 距離の計算
    ld dist = distance2(p1, p2);
    cout << "Distance between p1 and p2: " << dist << endl;
    
    // 2. 内積・外積・長さの2乗
    Vector v1 = {3.0, 4.0};
    Vector v2 = {4.0, -3.0};
    cout << "\n--- Vector Products & Length ---" << endl;
    cout << "Dot(v1, v2): " << dot(v1, v2) << " (0なら直交)" << endl;
    cout << "Cross(v1, v2): " << cross(v1, v2) << endl;
    cout << "Norm(v1) [squared]: " << norm2(v1) << " (長さは5なので2乗は25)" << endl;
    
    // 3 & 4. 直線と垂直二等分線
    Point a = {0.0, 0.0};
    Point b = {4.0, 0.0};
    Line l_ab = get_line(a, b);
    Line l_bisect = get_perpendicular_bisector(a, b);
    cout << "\n--- Line Equations (ax + by + c = 0) ---" << endl;
    cout << "Line AB: " << l_ab.a << "x + " << l_ab.b << "y + " << l_ab.c << " = 0" << endl;
    cout << "Bisector of AB: " << l_bisect.a << "x + " << l_bisect.b << "y + " << l_bisect.c << " = 0" << endl;
    
    // 5. 2直線の交点
    // l1: x + y - 2 = 0, l2: x - y = 0  (交点は 1.0, 1.0)
    Line l1 = {1.0, 1.0, -2.0};
    Line l2 = {1.0, -1.0, 0.0};
    Point intersection = get_intersection(l1, l2);
    cout << "\n--- Intersection ---" << endl;
    cout << "Intersection of l1 & l2: (" << intersection.first << ", " << intersection.second << ")" << endl;
    
    // 6. CCW (位置関係)
    Point p0 = {0.0, 0.0};
    Point p_target1 = {1.0, 0.0};
    Point p_target2 = {0.0, 1.0};
    cout << "\n--- CCW ---" << endl;
    cout << "CCW(p0, p_target1, p_target2): " << ccw(p0, p_target1, p_target2) << " (1なら反時計回り)" << endl;

    // 7. 線分の交差判定
    Point segment1_start = {0.0, 0.0};
    Point segment1_end = {4.0, 4.0};
    Point segment2_start = {0.0, 4.0};
    Point segment2_end = {4.0, 0.0};
    Point segment3_start = {5.0, 0.0};
    Point segment3_end = {5.0, 4.0};
    cout << "\n--- Segment Intersection ---" << endl;
    cout << "Crossing segments: "
        << intersect(segment1_start, segment1_end, segment2_start, segment2_end) << endl; // 1
    cout << "Non-crossing segments: "
        << intersect(segment1_start, segment1_end, segment3_start, segment3_end) << endl; // 0

    // 8. 点と直線・線分間の距離
    Point point = {2.0, 3.0};
    Line perpendicular = get_perpendicular_line(point, l_ab);
    Point parallel_segment_start = {0.0, 3.0};
    Point parallel_segment_end = {4.0, 3.0};
    cout << "\n--- Geometry Distances ---" << endl;
    cout << "Point-line distance squared: "
        << distance_between_point_and_line2(point, l_ab) << endl;
    cout << "Point-segment distance squared: "
        << distance_between_point_and_segment2(point, a, b) << endl;
    cout << "Perpendicular line through point: "
        << perpendicular.a << "x + " << perpendicular.b << "y + "
        << perpendicular.c << " = 0" << endl;
    cout << "Segment distance squared: "
        << distance_between_segment_and_segment2(a, b, parallel_segment_start, parallel_segment_end) << endl;
    cout << "Crossing segment distance squared: "
        << distance_between_segment_and_segment2(segment1_start, segment1_end,
                    segment2_start, segment2_end) << endl;

    // 9. 多角形の面積と面積公式
    vc<Point> triangle = {{0.0, 0.0}, {4.0, 0.0}, {0.0, 3.0}};
    Point triangle_center = polygon_area_formula(triangle);
    cout << "\n--- Polygon ---" << endl;
    cout << "Triangle area: " << polygon_area(triangle) << endl;
    cout << "Triangle area formula: (" << triangle_center.first << ", "
        << triangle_center.second << ")" << endl;

    // 10. 凸包 (Convex Hull - Monotone Chain)
    vc<Point> pts = {
        {0.0, 0.0}, {2.0, 0.0}, {4.0, 0.0},
        {1.0, 1.0}, {2.0, 3.0}, {3.0, 1.0},
        {0.0, 4.0}, {4.0, 4.0}, {2.0, 2.0}
    };

    vc<Point> l_hull = lower_hull(pts);
    vc<Point> u_hull = upper_hull(pts);
    vc<Point> full_hull = convex_hull(pts);

    cout << "\n--- Convex Hull ---" << endl;
    cout << "Lower Hull:" << endl;
    for (const auto& p : l_hull) {
        cout << "  (" << p.first << ", " << p.second << ")" << endl;
    }

    cout << "Upper Hull:" << endl;
    for (const auto& p : u_hull) {
        cout << "  (" << p.first << ", " << p.second << ")" << endl;
    }

    cout << "Full Convex Hull (Counter-Clockwise):" << endl;
    for (const auto& p : full_hull) {
        cout << "  (" << p.first << ", " << p.second << ")" << endl;
    }

    return 0;
}
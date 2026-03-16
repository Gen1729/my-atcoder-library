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
// [l, r) の範囲で「x以上」が初めて現れる位置を返す
int my_lower_bound(const vector<int>& a, int x) {
    int l = 0, r = (int)a.size();
    while (l < r) {
        int mid = l + (r - l) / 2;
        if (a[mid] < x) {
            l = mid + 1;
        } else {
            r = mid;
        }
    }
    return l; // a.size() の場合は見つからない(末尾)
}

// [l, r) の範囲で「xより大きい」が初めて現れる位置を返す
int my_upper_bound(const vector<int>& a, int x) {
    int l = 0, r = (int)a.size();
    while (l < r) {
        int mid = l + (r - l) / 2;
        if (a[mid] <= x) {
            l = mid + 1;
        } else {
            r = mid;
        }
    }
    return l; // a.size() の場合は見つからない(末尾)
}

int main(){
    string S = "abcdefghijklmnopqrstuvwxyz";
    cout << S.size() << endl;
    ll l = 2;
    ll r = 5;
    cout << S.substr(l) << endl;//[l,)
    cout << S.substr(l, r) << endl;//[l,l+r)
    cout << S << endl;
    reverse(all(S));
    cout << S << endl;
    reverse(S.begin() + 2,S.end() - 5);
    cout << S << endl;

    ll a = 4;
    ll b = 6;
    // VScodeだとエラーが出るが使える
    // cout << __gcd(a, b) << endl;//最大公約数
    // cout << a / __gcd(a, b) * b << endl;//最小公倍数

    // 例 1: set に対して色々な操作を行う（1 個目は "End"、2 個目は "46" と出力される）
    set<int> Set;
    Set.insert(37); // その時点での Set の要素は {37}
    Set.insert(15); // その時点での Set の要素は {15, 37}
    Set.insert(37); // その時点での Set の要素は {15, 37}
    auto itr1 = Set.lower_bound(40);
    if (itr1 == Set.end()) cout << "End" << endl;
    else cout << (*itr1) << endl;
    Set.erase(37); // その時点での Set の要素は {15}
    Set.insert(46); // その時点での Set の要素は {15, 46}
    auto itr2 = Set.lower_bound(20);
    if (itr2 == Set.end()) cout << "End" << endl;
    else cout << (*itr2) << endl;

    Set.clear();

    // 例 2: a[1],a[2],...,a[N] を小さい順に出力する（同じ要素が複数ある場合 1 回だけ出力する）
    set<int> Set2;
    vl number = {1,2,3,4,5,6,7,8};
    for (auto nn : number) Set2.insert(nn);
    auto itr = Set2.begin();
    while (itr != Set2.end()) {
        cout << (*itr) << endl;
        itr++;
    }

    multiset<int> ms;
    ms.insert(7);
    ms.insert(5);
    ms.insert(2);
    ms.insert(7);
    ms.insert(5);

    auto itr3 = ms.begin();
    while (itr3 != Set2.end()) {
        cout << (*itr3) << endl;
        itr3++;
    }
    //multisetで一つだけ削除。イテレータを指定で削除（setも同じ）
    auto it = ms.find(42);
    if (it != ms.end()) {
        ms.erase(it);
    }

    //tuple
    tuple<int, int, int> A;
    cin >> get<0>(A) >> get<1>(A) >> get<2>(A);
    cout << get<0>(A) + get<1>(A) + get<2>(A) << endl;
    
    // 例 2: vector にも tuple を入れられます、この例はソートするプログラムです
    vector<tuple<double, int, int>> B; int N;
    cin >> N;
    for (int i = 1; i <= N; i++) {
        double p1; int p2, p3;
        cin >> p1 >> p2 >> p3;
        B.push_back(make_tuple(p1, p2, p3));
    }
    sort(B.begin(), B.end());
    for (int i = 0; i < N; i++) printf("%.5lf %d %d\n", get<0>(B[i]), get<1>(B[i]), get<2>(B[i]));

    //順列
    int n, sam[109]; cin >> n;
    for (int i = 0; i < n; i++) cin >> sam[i];
    do {
        for (int i = 0; i < n; i++) {
            if (i) cout << ",";
            cout << sam[i];
        }
        cout << endl;
    } while(next_permutation(a, a + n));

    //ラムダ式
    //function<返り値の型(引数の型1, 引数の型2, ...)> 関数名 = [&](引数の型1 引数名1, 引数の型2, 引数名2, ...) { 関数の処理 };
    function<ll(ll)> dfs = [&](ll n) {
        if(n <= 0)return 0ll;
        return dfs(n-1);
    };
    
    //ワーシャルフロイドラムダ式
    vvl dist(N,vl(N,INF));
    function<void(ll)> dfs = [&](ll n) {
        for (int k = 0; k < n; k++){       // 経由する頂点
            for (int i = 0; i < n; i++) {    // 始点
                for (int j = 0; j < n; j++) {  // 終点
                    dist[i][j] = min(dist[i][j], dist[i][k] + dist[k][j]);
                }
            }
        }
    };

    vector<int> a = {1, 2, 2, 2, 4, 5};

    int x = 2;
    int lb = my_lower_bound(a, x); // 1
    int ub = my_upper_bound(a, x); // 4

    cout << "lower_bound index = " << lb << "\n";
    cout << "upper_bound index = " << ub << "\n";


    ll L = (1ll << N);//Nは15ぐらいまで

    for(ll m = 1; m < L; m++) for(ll k = m; k > 0; k = (k - 1) & m) {
        //部分集合[k]と[m-k]から[m]を構築する
    }
}
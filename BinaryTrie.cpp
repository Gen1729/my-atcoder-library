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

// https://github.com/Gen1729/my-atcoder-library/blob/main/BinaryTrie.cpp
struct BinaryTrie{
    ll sz;  // 追加済みノード数（次に使う ID）
    ll LOG; // 扱う整数の最大ビット長
    ll s;   // XOR バイアス（全体にかける仮想 XOR 値）
    struct Node{
        ll f;    // このノードに入るときの実ビット（0 / 1）
        ll pre;  // 親ノードの ID
        ll cnt;  // このノードを根とする部分木にある要素数
        vl nxt;  // nxt[0], nxt[1] = 0/1 の子ノード ID（存在しなければ -1）
    };
    struct Cursor{
        BinaryTrie* bt; // このカーソルが参照している BinaryTrie
        ll p;          // 現在指しているノード ID
        ll dep;        // 根からの深さ（何ビット進んだか）
        Cursor(BinaryTrie* bt=nullptr, ll p=0, ll dep=0):bt(bt),p(p),dep(dep){}
        bool valid() const { return bt != nullptr && p != -1; }
        bool atRoot() const { return valid() && p == 0; }
        ll depth() const { return dep; }
        bool canGo(ll bit) const {
            if(!valid() || bit < 0 || bit > 1 || dep >= bt->LOG) return false;
            ll k = bt->LOG - 1 - dep;
            ll real = bit ^ ((bt->s >> k) & 1);
            return bt->nodes[p].nxt[real] != -1;
        }
        Cursor move(ll bit) const {
            if(!canGo(bit)) return Cursor(nullptr, -1, 0);
            ll k = bt->LOG - 1 - dep;
            ll real = bit ^ ((bt->s >> k) & 1);
            ll np = bt->nodes[p].nxt[real];
            return Cursor(bt, np, dep + 1);
        }
        bool go(ll bit) {
            if(!canGo(bit)) return false;
            ll k = bt->LOG - 1 - dep;
            ll real = bit ^ ((bt->s >> k) & 1);
            p = bt->nodes[p].nxt[real];
            dep++;
            return true;
        }
        bool go0() { return go(0); }
        bool go1() { return go(1); }
        bool has0() const { return canGo(0); }
        bool has1() const { return canGo(1); }
        bool up() {
            if(!valid() || p == 0) return false;
            p = bt->nodes[p].pre;
            dep--;
            return true;
        }
        ll subtreeCount() const {
            if(!valid()) return 0;
            return bt->nodes[p].cnt;
        }
        ll childSubtreeCount(ll bit) const {
            if(!canGo(bit)) return 0;
            ll k = bt->LOG - 1 - dep;
            ll real = bit ^ ((bt->s >> k) & 1);
            ll np = bt->nodes[p].nxt[real];
            return np == -1 ? 0 : bt->nodes[np].cnt;
        }
        ll subtreeCount0() const { return childSubtreeCount(0); }
        ll subtreeCount1() const { return childSubtreeCount(1); }
        Cursor child(ll bit) const { return move(bit); }
        Cursor child0() const { return move(0); }
        Cursor child1() const { return move(1); }
        ll bit() const {
            if(!valid() || p == 0 || dep == 0) return -1;
            ll k = bt->LOG - dep;
            return bt->nodes[p].f ^ ((bt->s >> k) & 1);
        }
        ll actualBit() const {
            if(!valid() || p == 0 || dep == 0) return -1;
            return bt->nodes[p].f;
        }
    };
    vector<Node> nodes;
    BinaryTrie():sz(1),LOG(60),s(0),nodes(1,{-1,-1,0,{-1,-1}}){}
    Cursor root(){ return Cursor(this, 0, 0); } // ルート位置のカーソルを返す
    void insert(ll v){
        ll p = 0; // 今見ているノード ID
        v ^= s;   // 挿入値に現在の XOR バイアスを反映
        nodes[0].cnt++;
        for(ll k=LOG-1;k>=0;k--){
            if(nodes[p].nxt[(v>>k)&1]==-1){
                nodes.pb({(v>>k)&1,p,0,{-1,-1}});
                p=nodes[p].nxt[(v>>k)&1]=sz++;
            }else p=nodes[p].nxt[(v>>k)&1];
            nodes[p].cnt++;
        }
    }
    void erase(ll v){
        if(!count(v)) return;
        ll p = 0; // 消す対象を辿る現在ノード ID
        v ^= s;   // 現在の XOR バイアスを反映した値として辿る
        nodes[0].cnt--;
        for(ll k=LOG-1;k>=0;k--){
            p=nodes[p].nxt[(v>>k)&1];
            nodes[p].cnt--;
        }
    }
    bool count(ll v){
        ll p = 0; // 探索中のノード ID
        v ^= s;   // 現在の XOR バイアスを反映して探索
        for(ll k=LOG-1;k>=0;k--){
            if(nodes[p].nxt[(v>>k)&1]==-1) return false;
            p=nodes[p].nxt[(v>>k)&1];
            if(nodes[p].cnt==0) return false;
        }
        return true;
    }
    void XOR(ll v){s^=v;} // 全体にかける XOR バイアスを更新
    // 上から i 番目 (0-indexed) の桁が bit である要素数を返す。
    // XOR バイアス s を反映した見え方で数える。
    ll countBitFromTop(ll i, ll bit){
        if(i < 0 || i >= LOG || (bit != 0 && bit != 1)) return 0;
        ll p = 0;                         // ルートからたどるので最初は根
        ll k = LOG - 1 - i;               // 実際に見るビット位置
        ll want = ((s >> k) & 1) ^ bit;   // 実木で辿るべき枝番号
        if(nodes[p].nxt[want] == -1) return 0;
        return nodes[nodes[p].nxt[want]].cnt;
    }
    // 現在の XOR バイアス下で、v より小さい要素数を返す。
    // つまり lower_bound の位置（0-indexed）になる。
    ll orderOf(ll v){
        ll p = 0;
        ll ans = 0;
        for(ll k = LOG - 1; k >= 0; k--){
            ll sv = (s >> k) & 1;      // この桁での XOR バイアス
            ll bit = (v >> k) & 1;     // 比較したい値 v のこの桁
            ll low = sv;               // visible bit が 0 になる実際の枝
            ll high = sv ^ 1;          // visible bit が 1 になる実際の枝
            if(bit == 1 && nodes[p].nxt[low] != -1) ans += nodes[nodes[p].nxt[low]].cnt;
            if(nodes[p].nxt[bit ^ sv] == -1) return ans;
            p = nodes[p].nxt[bit ^ sv];
        }
        return ans;
    }
    ll rank(ll v){ return orderOf(v); }
    ll Kth(ll K){
        if(K<0||nodes[0].cnt<=K) return -1;
        ll p=0, res=0; // p = 現在位置, res = ここまで構築した答え
        for(ll k=LOG-1;k>=0;k--){
            res <<= 1;                 // 次のビットを追加するため左シフト
            ll nx = (s>>k)&1;          // XOR バイアス込みで最初に見る枝
            if(nodes[p].nxt[nx]==-1) nx^=1, res++; // 片側が無ければ反対側へ
            else if(nodes[nodes[p].nxt[nx]].cnt<=K) K-=nodes[nodes[p].nxt[nx]].cnt, nx^=1, res++; // K が右側にある
            p=nodes[p].nxt[nx];
        }
        return res;
    }
    ll operator[](ll k){
        return Kth(k);
    }
};

int main(){
    // BinaryTrieの基本的な使い方の例（XORバイアス付きの多重集合）。
    BinaryTrie bt; // 実際のデータを持つ trie 本体

    // 値の追加（多重集合なので重複OK）。
    bt.insert(5);   // 0101
    bt.insert(10);  // 1010
    bt.insert(5);   // 重複追加
    bt.insert(7);   // 0111

    // 存在確認（1回以上入っていればtrue）。
    cout << "count(5) = " << bt.count(5) << endl;   // 1 (true)
    cout << "count(6) = " << bt.count(6) << endl;   // 0 (false)

    // K番目（0-indexed）の値を取得（現在のXORバイアス下での順序）。
    // 現在の多重集合: {5,5,7,10} -> 昇順: 5,5,7,10
    cout << "Kth(0) = " << bt.Kth(0) << endl; // 5
    cout << "Kth(2) = " << bt[2] << endl;     // 7（operator[]はKthの別名）

    // 1個だけ削除（存在しない値なら何もしない）。
    bt.erase(5); // 多重集合は {5,7,10}
    cout << "after erase(5), Kth(0) = " << bt.Kth(0) << endl; // 5

    // XORバイアスを全体に適用（ノード自体は変更しない）。
    // 以降は「値 XOR s」として扱われる。
    bt.XOR(6); // s = 6

    // ポインタ（カーソル）で木を辿る。
    auto cur = bt.root(); // ルートを指すカーソル
    if(cur.has0()){ // 0方向の子があれば遷移
        cout << "root -> go0: " << cur.go0() << endl;//0方面に移動
    }
    cout << "current displayed bit: " << cur.bit() << endl;//XORバイアスありの時のbit
    cout << "current actual bit: " << cur.actualBit() << endl;//XORバイアスなしの時のbit
    cout << "subtree count: " << cur.subtreeCount() << endl;//今のポインタから部分木の個数を数える
    cout << "child0 subtree count: " << cur.subtreeCount0() << endl;//次の桁が0の部分木
    cout << "child1 subtree count: " << cur.subtreeCount1() << endl;//次の桁が1の部分木
    cout << "go up: " << cur.up() << endl;//根方向に移動

    ll dep = cur.depth(); // 根からの深さ 根の深さは0
    // 下位bit側から0始まりで数えるならLOG - dep
    // 上から何番目の bit かを 0 始まりで見るなら: dep - 1


    // 上から 0 番目の桁（最上位ビット）が 0 / 1 の個数を数える。
    cout << "top bit = 0: " << bt.countBitFromTop(0, 0) << endl;
    cout << "top bit = 1: " << bt.countBitFromTop(0, 1) << endl;

    // XORバイアスで順序が変わるが、Kthはその順序で取得できる。
    // 元の {5,7,10} は 6 をXORして {3,1,12} に変化。
    // XOR後の昇順は 1,3,12
    cout << "after XOR(6), Kth(0) = " << bt.Kth(0) << endl; // 1
    cout << "after XOR(6), Kth(2) = " << bt.Kth(2) << endl; // 12
    
    // rank(x):XORバイアス下でのx未満の要素数
    cout << "rank(1) = " << bt.rank(1) << endl; // 0
    cout << "rank(2) = " << bt.rank(1) << endl; // 1
    cout << "rank(12) = " << bt.rank(12) << endl; // 2

    // 同じXORをもう一度かけてバイアスを戻す。
    bt.XOR(6); // s = 0
    cout << "after XOR(6) again, Kth(0) = " << bt.Kth(0) << endl; // 5

    return 0;
}
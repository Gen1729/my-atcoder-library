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
struct BinaryTrie{
  ll sz,LOG,s;
  struct Node{
    ll f,pre,cnt;
    vl nxt;
  };
  vector<Node> nodes;
  BinaryTrie():sz(1),LOG(60),s(0),nodes(1,{-1,-1,0,{-1,-1}}){}
  void insert(ll v){
    ll p=0;
    v^=s;
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
    ll p=0;
    v^=s;
    nodes[0].cnt--;
    for(ll k=LOG-1;k>=0;k--){
      p=nodes[p].nxt[(v>>k)&1];
      nodes[p].cnt--;
    }
  }
  bool count(ll v){
    ll p=0;
    v^=s;
    for(ll k=LOG-1;k>=0;k--){
      if(nodes[p].nxt[(v>>k)&1]==-1) return false;
      p=nodes[p].nxt[(v>>k)&1];
      if(nodes[p].cnt==0) return false;
    }
    return true;
  }
  void XOR(ll v){s^=v;}
  ll Kth(ll K){
    if(K<0||nodes[0].cnt<=K) return -1;
    ll p=0,res=0;
    for(ll k=LOG-1;k>=0;k--){
      res<<=1;
      ll nx=(s>>k)&1;
      if(nodes[p].nxt[nx]==-1) nx^=1,res++;
      else if(nodes[nodes[p].nxt[nx]].cnt<=K) K-=nodes[nodes[p].nxt[nx]].cnt,nx^=1,res++;
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
  BinaryTrie bt;

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

  // XORバイアスで順序が変わるが、Kthはその順序で取得できる。
  // 元の {5,7,10} は 6 をXORして {3,1,12} に変化。
  // XOR後の昇順は 1,3,12
  cout << "after XOR(6), Kth(0) = " << bt.Kth(0) << endl; // 1
  cout << "after XOR(6), Kth(2) = " << bt.Kth(2) << endl; // 12

  // 同じXORをもう一度かけてバイアスを戻す。
  bt.XOR(6); // s = 0
  cout << "after XOR(6) again, Kth(0) = " << bt.Kth(0) << endl; // 5

  return 0;
}
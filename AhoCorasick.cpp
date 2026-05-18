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

#define sz(s) (long long)(s.size())

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

class AhoCorasick {
public:
	AhoCorasick(int alphabet_size = 26, char base_char = 'a')
		: alpha(alphabet_size), base(base_char) {
		nodes.emplace_back(alpha, -1, 0);
		current = 0;
	}

	int add(const string &pattern) {
		int v = 0;
		for (char ch : pattern) {
			int c = ch - base;
			if (c < 0 || c >= alpha) {
				return -1;
			}
			if (nodes[v].next[c] == -1) {
				nodes[v].next[c] = (int)nodes.size();
				nodes.emplace_back(alpha, v, (char)(base + c));
			}
			v = nodes[v].next[c];
		}
		int id = (int)pattern_lengths.size();
		nodes[v].out.push_back(id);
		pattern_lengths.push_back((int)pattern.size());
		return id;
	}

	void build() {
		queue<int> q;
		for (int c = 0; c < alpha; ++c) {
			int u = nodes[0].next[c];
			if (u != -1) {
				nodes[u].link = 0;
				q.push(u);
			} else {
				nodes[0].next[c] = 0;
			}
		}

		while (!q.empty()) {
			int v = q.front();
			q.pop();
			for (int c = 0; c < alpha; ++c) {
				int u = nodes[v].next[c];
				if (u != -1) {
					nodes[u].link = nodes[nodes[v].link].next[c];
					const auto &link_out = nodes[nodes[u].link].out;
					nodes[u].out.insert(nodes[u].out.end(), link_out.begin(), link_out.end());
					q.push(u);
				} else {
					nodes[v].next[c] = nodes[nodes[v].link].next[c];
				}
			}
		}
	}

	vector<vector<int>> match_positions(const string &text) const {
		vector<vector<int>> res(pattern_lengths.size());
		int v = 0;
		for (int i = 0; i < (int)text.size(); ++i) {
			v = next_state(v, text[i]);
			for (int id : nodes[v].out) {
				res[id].push_back(i - pattern_lengths[id] + 1);
			}
		}
		return res;
	}

	int next_state(int v, char ch) const {
		if (v < 0 || v >= (int)nodes.size()) {
			return 0;
		}
		int c = ch - base;
		if (c < 0 || c >= alpha) {
			return 0;
		}
		return nodes[v].next[c];
	}

	void reset_state() {
		current = 0;
	}

	void set_state(int v) {
		if (0 <= v && v < (int)nodes.size()) {
			current = v;
		} else {
			current = 0;
		}
	}

	int step(char ch) {
		current = next_state(current, ch);
		return current;
	}

	int get_state() const {
		return current;
	}

	int node_count() const {
		return (int)nodes.size();
	}

	vector<string> node_strings() const {
		vector<string> res(nodes.size());
		for (int v = 1; v < (int)nodes.size(); ++v) {
			int p = nodes[v].parent;
			res[v] = res[p] + nodes[v].pch;
		}
		return res;
	}

private:
	struct Node {
		vector<int> next;
		int link = 0;
		vector<int> out;
		int parent = -1;
		char pch = 0;
		Node(int alpha, int parent_id, char parent_ch)
			: next(alpha, -1), parent(parent_id), pch(parent_ch) {}
	};

	int alpha;
	char base;
	vector<Node> nodes;
	vector<int> pattern_lengths;
	int current = 0;
};

int main() {
	AhoCorasick ac(26, 'a'); // a-zの26文字
	vector<string> patterns = {"he", "she", "his", "hers"};
	for (const auto &p : patterns) {
		ac.add(p);
	}
	ac.build();

	string text = "ahishers";
	auto positions = ac.match_positions(text);

	for (int i = 0; i < (int)patterns.size(); ++i) {
		cout << patterns[i] << ":";
		for (int pos : positions[i]) {
			cout << " " << pos;
		}
		cout << "\n";
	}

    int n = ac.node_count(); // 頂点数を返す
    auto strs = ac.node_strings(); // strs[v] が頂点 v の文字列

    cout << n << endl;
    rep(i,n){
		cout << i << " " << strs[i] << endl;
	}

	ac.reset_state();
	for (char ch : text) {
		ac.step(ch);
		cout << ac.get_state() << "\n";
	}

	ac.set_state(0);         // 現在頂点を指定
	ac.step('h');            // 1文字遷移
	int v = ac.get_state();  // 現在頂点番号
	int u = ac.next_state(v, 'e'); // 明示的に次頂点
	
	return 0;
}

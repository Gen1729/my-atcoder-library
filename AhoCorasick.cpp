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

// https://github.com/Gen1729/my-atcoder-library/blob/main/AhoCorasick.cpp
class AhoCorasick {
public:
	AhoCorasick(ll alphabet_size = 26, char base_char = 'a')
		: alpha(alphabet_size), base(base_char) {
		nodes.emplace_back(alpha, -1, 0);
		trie_children.emplace_back();
		current = 0;
	}

	ll add(const string &pattern) {
		ll v = 0;
		for (char ch : pattern) {
			ll c = ch - base;
			if (c < 0 || c >= alpha) {
				return -1;
			}
			if (nodes[v].next[c] == -1) {
				nodes[v].next[c] = (ll)nodes.size();
				nodes.emplace_back(alpha, v, (char)(base + c));
				trie_children.emplace_back();
				trie_children[v].push_back(nodes[v].next[c]);
				terminal.push_back(false);
				output.push_back(false);
			}
			v = nodes[v].next[c];
		}
		ll id = (ll)pattern_lengths.size();
		end_node.push_back(v);
		if (v >= 0 && v < (ll)terminal.size()) {
			terminal[v] = true;
		}
		pattern_lengths.push_back((ll)pattern.size());
		return id;
	}

	void build() {
		queue<ll> q;
		order.clear();
		order.push_back(0);
		for (ll c = 0; c < alpha; ++c) {
			ll u = nodes[0].next[c];
			if (u != -1) {
				nodes[u].link = 0;
				q.push(u);
				order.push_back(u);
			} else {
				nodes[0].next[c] = 0;
			}
		}

		while (!q.empty()) {
			ll v = q.front();
			q.pop();
			for (ll c = 0; c < alpha; ++c) {
				ll u = nodes[v].next[c];
				if (u != -1) {
					nodes[u].link = nodes[nodes[v].link].next[c];
					q.push(u);
					order.push_back(u);
				} else {
					nodes[v].next[c] = nodes[nodes[v].link].next[c];
				}
			}
		}
		for (ll i = 1; i < (ll)order.size(); ++i) {
			ll v = order[i];
			ll p = nodes[v].link;
			output[v] = terminal[v] || output[p];
		}
	}

	vector<long long> count_matches(const string &text) const {
		vector<long long> cnt(nodes.size(), 0);
		ll v = 0;
		for (char ch : text) {
			v = next_state(v, ch);
			cnt[v]++;
		}
		for (ll i = (ll)order.size() - 1; i > 0; --i) {
			ll u = order[i];
			cnt[nodes[u].link] += cnt[u];
		}
		vector<long long> res(pattern_lengths.size(), 0);
		for (ll i = 0; i < (ll)pattern_lengths.size(); ++i) {
			res[i] = cnt[end_node[i]];
		}
		return res;
	}

	ll next_state(ll v, char ch) const {
		if (v < 0 || v >= (ll)nodes.size()) {
			return 0;
		}
		ll c = ch - base;
		if (c < 0 || c >= alpha) {
			return 0;
		}
		return nodes[v].next[c];
	}

	void reset_state() {
		current = 0;
	}

	void set_state(ll v) {
		if (0 <= v && v < (ll)nodes.size()) {
			current = v;
		} else {
			current = 0;
		}
	}

	ll step(char ch) {
		current = next_state(current, ch);
		return current;
	}

	ll get_state() const {
		return current;
	}

	bool is_terminal(ll v) const {
		if (v < 0 || v >= (ll)output.size()) {
			return false;
		}
		return output[v];
	}

	const vl &children(ll v) const {
		static const vl empty;
		if (v < 0 || v >= (ll)trie_children.size()) {
			return empty;
		}
		return trie_children[v];
	}

	vl suffix_terminal_nodes(ll v) const {
		vl res;
		if (v < 0 || v >= (ll)nodes.size()) {
			return res;
		}
		while (v != 0) {
			if (terminal[v]) {
				res.push_back(v);
			}
			v = nodes[v].link;
		}
		return res;
	}

	vl suffix_terminal_nodes() const {
		return suffix_terminal_nodes(current);
	}

	string node_string(ll v) const {
		if (v <= 0 || v >= (ll)nodes.size()) {
			return string();
		}
		string res;
		while (v != 0) {
			res.push_back(nodes[v].pch);
			v = nodes[v].parent;
		}
		reverse(res.begin(), res.end());
		return res;
	}

	ll node_count() const {
		return (ll)nodes.size();
	}

	vector<string> node_strings() const {
		vector<string> res(nodes.size());
		for (ll v = 1; v < (ll)nodes.size(); ++v) {
			ll p = nodes[v].parent;
			res[v] = res[p] + nodes[v].pch;
		}
		return res;
	}

//private:
	struct Node {
		vl next;
		ll link = 0; // 失敗リンク先の頂点
		ll parent = -1; // 親頂点
		char pch = 0; // 頂点が表す文字
		Node(ll alpha, ll parent_id, char parent_ch)
			: next(alpha, -1), parent(parent_id), pch(parent_ch) {}
	};

	ll alpha;
	char base;
	vector<Node> nodes;
	vl pattern_lengths;
	vl end_node;
	vl order;
	vvl trie_children; // trie_children[v] でvの子供一覧
	vb terminal = vb(1, false);
	vb output = vb(1, false);
	ll current = 0;
};

int main() {
	AhoCorasick ac(26, 'a'); // a-zの26文字
	vector<string> patterns = {"he", "she", "his", "hers"};
	for (const auto &p : patterns) {
		ll id = ac.add(p);
		// pに対応する頂点番号
		ll vertex_num = ac.end_node[id];
	}
	ac.build();

	string text = "ahishers";
	auto counts = ac.count_matches(text);

	for (ll i = 0; i < (ll)patterns.size(); ++i) {
		cout << patterns[i] << ":";
		for (ll cnt : counts) {
			cout << " " << cnt;
		}
		cout << "\n";
	}

    ll n = ac.node_count(); // 頂点数を返す
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
	ll v = ac.get_state();  // 現在頂点番号
	ll u = ac.next_state(v, 'e'); // 明示的に次頂点

	bool D = ac.is_terminal(v); // vのsuffixに一致している文字列があるか判定

	string s = ac.node_string(v); // vが表す文字列

	for (ll u : ac.children(v)) {
		// v -> u の Trie 辺一覧
	}

	auto nodes = ac.suffix_terminal_nodes(v); // v の suffix に一致するパターン終端ノード一覧
	for(auto nv : nodes){
		cout << nv << " ";
	}
	cout << endl;

	// 失敗リンク先の頂点やその頂点の持つ文字や親頂点は
	// nodes[v].link nodes[v].pch nodes[v].parentで受け取れます
	
	return 0;
}

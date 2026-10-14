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

// https://github.com/Gen1729/my-atcoder-library/blob/main/Trie.cpp
template <int CHAR_SIZE, char BASE>
class Trie {
private:
    // Trie木の各ノードを表す構造体
    struct Node {
        std::vector<int> next;      // 子ノードのインデックス（存在しない場合は -1）
        int pass_count;            // このノードを通過した単語の数
        std::vector<int> accept_ids; // このノードで終了する単語のIDリスト

        Node() : next(CHAR_SIZE, -1), pass_count(0) {}
    };

    std::vector<Node> nodes;  // 全ノードを保持する動的配列（nodes[0] が根）
    int inserted_words_count; // 今までに挿入された累計単語数（単語IDとしても使用）

    // 文字を [0, CHAR_SIZE-1] のインデックスに変換する内部関数
    int get_char_idx(char c) const {
        return c - BASE;
    }

    // 指定ノード以下の部分木に含まれる全単語のIDを再帰的に収集する内部関数
    void collect_ids(int node_idx, std::vector<int>& result) const {
        if (node_idx == -1) return;

        // このノードで終了する単語のIDを追加
        for (int id : nodes[node_idx].accept_ids) {
            result.push_back(id);
        }

        // 全ての子ノードへ再帰
        for (int c = 0; c < CHAR_SIZE; ++c) {
            if (nodes[node_idx].next[c] != -1) {
                collect_ids(nodes[node_idx].next[c], result);
            }
        }
    }

public:
    // コンストラクタ：根ノード (index 0) を初期化
    Trie() : inserted_words_count(0) {
        nodes.emplace_back();
    }

    // 1. 単語 word を挿入し、割り当てられた単語IDを返す関数
    int insert(const std::string& word) {
        int node_idx = 0;
        nodes[node_idx].pass_count++; // 根ノードを通る単語数を加算

        for (char c : word) {
            int char_idx = get_char_idx(c);
            // 子ノードが存在しなければ新規作成
            if (nodes[node_idx].next[char_idx] == -1) {
                nodes[node_idx].next[char_idx] = static_cast<int>(nodes.size());
                nodes.emplace_back();
            }
            node_idx = nodes[node_idx].next[char_idx];
            nodes[node_idx].pass_count++; // ノードを通る単語数を加算
        }

        int word_id = inserted_words_count++;
        nodes[node_idx].accept_ids.push_back(word_id);
        return word_id;
    }

    // 2. 単語 word が挿入されているか検索する関数
    bool search(const std::string& word) const {
        int node_idx = 0;
        for (char c : word) {
            int char_idx = get_char_idx(c);
            if (nodes[node_idx].next[char_idx] == -1) {
                return false;
            }
            node_idx = nodes[node_idx].next[char_idx];
        }
        return !nodes[node_idx].accept_ids.empty();
    }

    // 3. 今までに挿入した累計単語数を返す関数
    int count_words() const {
        return inserted_words_count;
    }

    // 4. Trie木の全ノード数を返す関数
    int size() const {
        return static_cast<int>(nodes.size());
    }

    // 指定した文字列（接頭辞）を通る単語の数を返す関数
    int count_pass(const std::string& prefix) const {
        int node_idx = 0;
        for (char c : prefix) {
            int char_idx = get_char_idx(c);
            if (nodes[node_idx].next[char_idx] == -1) {
                return 0;
            }
            node_idx = nodes[node_idx].next[char_idx];
        }
        return nodes[node_idx].pass_count;
    }

    // 条件指定1: 単語 S の prefix となっている挿入済単語の ID を全て返す関数
    std::vector<int> get_prefixes_of(const std::string& S) const {
        std::vector<int> res;
        int node_idx = 0;

        // 根ノード（空文字列が対応）に単語が完了していれば追加
        for (int id : nodes[node_idx].accept_ids) {
            res.push_back(id);
        }

        for (char c : S) {
            int char_idx = get_char_idx(c);
            if (nodes[node_idx].next[char_idx] == -1) {
                break;
            }
            node_idx = nodes[node_idx].next[char_idx];
            // 途中で単語が完了していればそのIDを追加
            for (int id : nodes[node_idx].accept_ids) {
                res.push_back(id);
            }
        }
        return res;
    }

    // 条件指定2: 単語 T を prefix としている挿入済単語の ID を全て返す関数
    std::vector<int> get_words_with_prefix(const std::string& T) const {
        std::vector<int> res;
        int node_idx = 0;

        for (char c : T) {
            int char_idx = get_char_idx(c);
            if (nodes[node_idx].next[char_idx] == -1) {
                return res; // 接頭辞 T を持つ単語は存在しない
            }
            node_idx = nodes[node_idx].next[char_idx];
        }

        // T に到達したノード以下の部分木からIDをすべて収集
        collect_ids(node_idx, res);
        return res;
    }
};

// ==========================================
// 使用例
// ==========================================
int main() {
    Trie<26,'a'> trie;

    // 単語の挿入
    std::vector<std::string> words = {"app", "apple", "application", "apt", "bat"};
    std::cout << "--- 単語の挿入 ---" << std::endl;
    for (const auto& w : words) {
        int id = trie.insert(w);
        std::cout << "Inserted: " << w << " (ID: " << id << ")" << std::endl;
    }

    // 基本機能の検証
    std::cout << "\n--- 基本機能 ---" << std::endl;
    std::cout << "挿入した総単語数: " << trie.count_words() << std::endl;
    std::cout << "Trie木のノード数: " << trie.size() << std::endl;
    std::cout << "\"apple\" の検索結果: " << (trie.search("apple") ? "Found" : "Not Found") << std::endl;
    std::cout << "\"appli\" の検索結果: " << (trie.search("appli") ? "Found" : "Not Found") << std::endl;
    std::cout << "\"app\" を通る単語の数: " << trie.count_pass("app") << std::endl;

    // 条件指定1: 単語 S の prefix となっている挿入済単語の ID
    std::string S = "applepie";
    std::cout << "\n--- S = \"" << S << "\" の prefix である単語の ID ---" << std::endl;
    std::vector<int> prefix_ids = trie.get_prefixes_of(S);
    for (int id : prefix_ids) {
        std::cout << "ID: " << id << " (" << words[id] << ")" << std::endl;
    }

    // 条件指定2: 単語 T を prefix としている挿入済単語の ID
    std::string T = "app";
    std::cout << "\n--- T = \"" << T << "\" を prefix に持つ単語の ID ---" << std::endl;
    std::vector<int> with_prefix_ids = trie.get_words_with_prefix(T);
    for (int id : with_prefix_ids) {
        std::cout << "ID: " << id << " (" << words[id] << ")" << std::endl;
    }

    return 0;
}
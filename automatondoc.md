# Automaton DP Library (C++)

このライブラリは、決定性有限オートマトン (DFA) の概念を用いて**桁DPや文字列DPを合成・簡略化**するためのC++テンプレートライブラリです。Rust等で見られる「TraitベースのDFA合成」アプローチをC++のテンプレートを用いて再現しています。

## 概要

オートマトンは `State`, `Alphabet`, `init()`, `next()`, `accept()` を持つ構造体として定義されます。このライブラリでは、様々な条件を表す単純なDFAを組み合わせ（`And`, `Or`, `Not`）、最終的な複合DFAを作成し、`count_dfa` 関数で条件を満たす数え上げを行います。

## 提供される構造体一覧

### 1. 基本 DFA

*   **`MultipleOf`**
    *   **仕様**: 入力された数列を10進数の数として捉え、特定の数 `M` の倍数であるかを判定します。
    *   **使用例**: `MultipleOf(3)` （3の倍数判定）
*   **`Seen`**
    *   **仕様**: 入力された列の中に、特定の文字（数値）が1度でも出現したかを判定します。
    *   **使用例**: `Seen(3)` （「3」が含まれているか判定）
*   **`ContainsAhoCorasick`**
    *   **仕様**: Aho-Corasick法を用いて、複数のパターンのうち少なくとも1つを部分文字列として含むかを判定します。
    *   **使用例**: `ContainsAhoCorasick({{1, 2}, {3, 4}})` （数列 `[1, 2]` または `[3, 4]` を含むか判定）

### 2. コンビネータ (合成 DFA)

*   **`And<A, B>`**: DFA `A` と `B` の両方が受理する場合に受理します。
*   **`Or<A, B>`**: DFA `A` と `B` のどちらかが受理する場合に受理します。
*   **`Not<A>`**: DFA `A` が受理**しない**場合に受理します。

### 3. 制約 DFA (桁DP用)

*   **`Le` (Less than or Equal)**
    *   **仕様**: 渡された限界文字列 `S` 以下の辞書順であるか判定します。
    *   **注意**: 探索する長さ `length` と限界文字列 `S` の**長さを揃える必要があります**（先頭を `0` 埋めするなど）。
    *   **使用例**: `Le("0038347")`
*   **`Lt` (Less Than)**
    *   **仕様**: `Le` と同様ですが、限界文字列 `S` **未満**（厳密に小さい）であるか判定します。

### 4. 実行関数

*   **`count_dfa(dfa, sigma, length)`**
    *   **仕様**: 状態遷移DPを実行します。アルファベット集合 `sigma` を用いて、長さ `length` で生成される遷移のうち、最終的に `dfa` が受理するパスの総数を計算します（答えは `MOD = 998244353` で計算されます）。

---

## 使用例

「3の倍数 または 3が含まれる数」のうち、 $A$ 以上 $B$ 以下のものを求める場合の実装例です。

```cpp
int main() {
    string A,B;
    cin >> A >> B;
    
    // 問題によって0埋めするか判断する 今回はしない
    ll lenA = A.size();
    ll lenB = B.size();
    
    // アルファベットの定義 (0〜9)
    vector<ll> sigma = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9};
    
    // 1. 3の倍数を判定する DFA
    MultipleOf mod3(3);
    
    // 2. 3が含まれるかを判定する DFA
    Seen seen3(3);
    
    // 3. ナベアツ数の DFA (mod3 OR seen3)
    Or<MultipleOf, Seen> nabeatsu(mod3, seen3);
    
    // 4. A未満とB以下を判定する DFA
    Lt lt(A);
    Le le(B);
    
    // 5. ナベアツ数 かつ K以下 を判定する DFA
    And<Or<MultipleOf, Seen>, Lt> dfa1(nabeatsu, lt);
    And<Or<MultipleOf, Seen>, Le> dfa2(nabeatsu, le);

    ll ans = 0;
    
    // 6. count_dfa で文字列を探索
    ans -= count_dfa(dfa1, sigma, lenA);
    ans += count_dfa(dfa2, sigma, lenB);
    
    cout << ans << endl;
    return 0;
}
```
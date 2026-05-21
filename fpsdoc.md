# fps.cppの使い方 (optさんライブラリ)

## メンバ関数リスト

$z$ を不定元とする形式的冪級数 $f,g$ に対する演算を行います．

`FormalPowerSeries` 構造体は， 
$f$ の 
$z^0$ から 
$z^N$ の係数のみ保持します．

演算の結果，
$z^{-1}$ 以下や 
$z^{N+1}$ 以上の項が発生した場合，その情報は**捨てます**．

つまり，演算によって vector のサイズは変更されません．この仕様は他の多くの FPS ライブラリとは異なる気がするので，注意してください．

### 基本的な演算

- `F operator-()` : 
$-f$ を返す
- `F &operator+=(const F &g)` : 
$f \gets f+g$ と更新
- `F &operator-=(const F &g)` : 
$f \gets f-g$ と更新
- `F &operator*=(const T &c)` : 
$f \gets cf$ と更新（
$c$ は定数）
- `F &operator/=(const T &c)` : 
$f \gets f/c$ と更新（
$c$ は定数）
- `F &operator<<=(const int d)` : 
$f \gets fx^d$ と更新
- `F &operator>>=(const int d)` : 
$f \gets f/x^d$ と更新

時間計算量は 
$O(N)$ です．

### 乗法の逆元

- `F inv(int d = -1)` : 
$1/f$ を返す．
$d-1$ 次の項で打ち切る．デフォルトでは 
$N$ 次の項で打ち切る.

`atcoder::convolution` を使っているため，mod が **NTT-friendly な場合にしか使えません**．

時間計算量は 
$O(N \log N)$ です．

### 乗除算

#### fast版

- `F multiply_inplace(const F &g, int d = -1)` : 
$f \gets fg$ と更新
- `F divide_inplace(const F &g, int d = -1)` : 
$f \gets f/g$ と更新

- `F multiply(const F &g, int d = -1)` : 
$h \gets fg$ と更新
- `F divide(const F &g, int d = -1)` : 
$h \gets f/g$ と更新

$d-1$ 次の項で打ち切る．デフォルトでは 
$N$ 次の項で打ち切る.

#### naive版

- `F multiply_inplace(const F &g)` : 
$f \gets fg$ と更新
- `F divide_inplace(const F &g)` : 
$f \gets f/g$ と更新

- `F multiply(const F &g)` : 
$h \gets fg$ と更新
- `F divide(const F &g)` : 
$h \gets f/g$ と更新


fast 版と naive 版の2種類あり，上のコードではともにコメントアウトしてあります．

問題に応じて，必要な方のみコメントアウトを解除して使います．

fast 版は mod が **NTT-friendly な場合にしか使えません**．

時間計算量は fast 版が 
$O((N+M)\log{(N+M)})$，naive 版が 
$O(NM)$ です（$M$ は $g$  の次数）．

### スパースな乗除算

- `F multiply_inplace(const vector<pair<int, T>> g)` : 
$f \gets fg$ と更新
- `F divide_inplace(const vector<pair<int, T>> g)` : 
$f \gets f/g$ と更新

- `F multiply(const vector<pair<int, T>> g)` : 
$h \gets fg$ と更新
- `F divide(const vector<pair<int, T>> g)` : 
$h \gets f/g$ と更新

$g$ の非ゼロ係数が少ないときに使います．
$g$ は 
(次数,係数)の pair を並べた vector として渡します．vector は昇順ソートされていることを仮定しています．

時間計算量は 
$O(NK)$ です（ $K$ は $g$  の非ゼロ係数の数）．

### $(1+cz^d)$ の乗除算

- `void multiply_inplace(const int d, const T c)` : 
$f \gets f \times (1+cz^d)$ と更新
- `void divide_inplace(const int d, const T c)` : 
$f \gets f/(1+cz^d)$ と更新

スパースな乗除算の特殊形です．この形は頻出な上，定数倍高速化ができるため別の関数にしています．

時間計算量は 
$O(N)$ です．

### 関数値評価

- `T eval(const T &a)` : 
$f$ に 
$z = a$ を「代入」したときの値を返す

時間計算量は 
$O(N)$ です．

## 使い方

以下のコードの記載が必要です.

```
using mint = modint998244353;
using fps = FormalPowerSeries<mint>;
using sfps = vector<pair<int, mint>>;
```

$f = 3 + z + 4z^2 + z^3 + 5z^4$ と $g = 2 + 7z + z^2$
に対し，積 $fg$ を計算したい場合は

```
fps f = {3, 1, 4, 1, 5};
fps g = {2, 7, 1};

f.multiply_inplace(g);
fps h = f.multiply(g);
```

とします．$h$ の中身は$fg$を4次までで打ち切った
`{6, 23, 18, 31, 21}`となります．

以下のように長めの式も書けます:

```
fps h = (f - (f << 2) + fps{2}).divide(g);
```

$g=1-z$ に対して $f/g$ を計算したいとき、$g$ の非ゼロ係数が少ないことに着目して

```
fps f = {3, 1, 4, 1, 5};
sfps g = {{0, 1}, {1, -1}}; // 0次の係数が1、1次の係数が-1
f.divide_inplace(g);
```

と書くこともできます．こうすると f の中身は {3, 4, 8, 9, 14} となります．

全く同じ計算を，以下のようにも書けます:

```
fps f = {3, 1, 4, 1, 5};
f.divide_inplace(1, -1);
```

こちらの方が定数倍が軽いです．

以下のようにサイズ変更・代入・参照が可能です。
```
fps f = {1};
f.resize(N+1);
f[2] = 3;
cout << f[5].val() << endl;
```

## 問題への適用例：TDPC: F - 準急

この問題の答えは，

$\frac{(1-z)(z-z^K)}{1-2z+z^{K+1}}$

の $z^N$ の係数に等しいです．

よって，以下のように実装できます．「スパースな乗除算」を使わないと TLE してしまうので注意してください．

```
// ここに FPS ライブラリを貼る

using mint = modint998244353;
using fps = FormalPowerSeries<mint>;
using sfps = vector<pair<int, mint>>;

int main() {
    int n, k; cin >> n >> k;

    fps f = {1, -1};
    f.resize(n+1);

    f.multiply_inplace(sfps{{1, 1}, {k, -1}});
    f.divide_inplace(sfps{{0, 1}, {1, -2}, {k+1, 1}});

    cout << f[n].val() << '\n';
}
```

## 注意
- `std::vector<T>` を継承しています．`T` には AtCoder Library の `modint` を渡すことを想定しています．
- 除算 $f/g$ では $g$ の定数項が非ゼロであることを要求します．
- mod が NTT-friendly な場合にしか使えない関数があることに注意してください．
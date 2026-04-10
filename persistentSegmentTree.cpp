#pragma once
#include <iostream>
#include <vector>
#include <cassert>
#include <cstdint>
#include <limits>

/*
Persistent Lazy Segment Tree (functional / path-copying)

Template parameters:
  S            : segment value type
  F            : lazy function type
  op(S,S)->S   : monoid operation
  e()->S       : monoid identity
  mapping(F,S,int len)->S : apply lazy function to a segment value (len = segment length)
  composition(F fnew, F fold)->F : compose lazy functions.
      Semantics: applying fold then fnew == applying composition(fnew, fold)
  id()->F      : lazy identity
*/
template <
    class S, class F,
    S (*op)(const S&, const S&),
    S (*e)(),
    S (*mapping)(const F&, const S&, int),
    F (*composition)(const F&, const F&),
    F (*id)()
>
class PersistentLazySegTree {
private:
    struct Node {
        S val;
        F lz;
        Node* lch;
        Node* rch;
        Node(const S& v = e(), const F& f = id(), Node* l = nullptr, Node* r = nullptr)
            : val(v), lz(f), lch(l), rch(r) {}
    };

    int n_ = 0;
    std::vector<Node*> roots_;

    static Node* clone_node(Node* t) {
        if (!t) return new Node();
        return new Node(*t);
    }

    static S node_val(Node* t) {
        return t ? t->val : e();
    }

    static void apply_all(Node* t, const F& f, int len) {
        t->val = mapping(f, t->val, len);
        t->lz = composition(f, t->lz);
    }

    static void pull(Node* t) {
        t->val = op(node_val(t->lch), node_val(t->rch));
    }

    static void push(Node* t, int l, int r) {
        if (t->lz == id()) return;
        if (r - l == 1) {
            t->lz = id();
            return;
        }
        int m = (l + r) >> 1;
        t->lch = clone_node(t->lch);
        t->rch = clone_node(t->rch);
        apply_all(t->lch, t->lz, m - l);
        apply_all(t->rch, t->lz, r - m);
        t->lz = id();
    }

    static Node* build_rec(const std::vector<S>& a, int l, int r) {
        Node* t = new Node();
        if (r - l == 1) {
            if (l < (int)a.size()) t->val = a[l];
            else t->val = e();
            return t;
        }
        int m = (l + r) >> 1;
        t->lch = build_rec(a, l, m);
        t->rch = build_rec(a, m, r);
        pull(t);
        return t;
    }

    static Node* range_apply_rec(Node* cur, int l, int r, int ql, int qr, const F& f) {
        if (qr <= l || r <= ql) return cur;
        Node* t = clone_node(cur);
        if (ql <= l && r <= qr) {
            apply_all(t, f, r - l);
            return t;
        }
        push(t, l, r);
        int m = (l + r) >> 1;
        t->lch = range_apply_rec(t->lch, l, m, ql, qr, f);
        t->rch = range_apply_rec(t->rch, m, r, ql, qr, f);
        pull(t);
        return t;
    }

    static S range_prod_rec(Node* cur, int l, int r, int ql, int qr) {
        if (!cur || qr <= l || r <= ql) return e();
        if (ql <= l && r <= qr) return cur->val;
        int m = (l + r) >> 1;
        S lv = range_prod_rec(cur->lch, l, m, ql, qr);
        S rv = range_prod_rec(cur->rch, m, r, ql, qr);
        int il = std::max(l, ql), ir = std::min(r, qr);
        if (il >= ir) return e();
        // partial overlap: current node lazy must affect children query range
        // Instead of push (which would mutate), reflect lazy on merged result.
        S res = op(lv, rv);
        if (!(cur->lz == id())) {
            res = mapping(cur->lz, res, ir - il);
        }
        return res;
    }

    static Node* point_set_rec(Node* cur, int l, int r, int p, const S& x) {
        Node* t = clone_node(cur);
        if (r - l == 1) {
            t->val = x;
            t->lz = id();
            return t;
        }
        push(t, l, r);
        int m = (l + r) >> 1;
        if (p < m) t->lch = point_set_rec(t->lch, l, m, p, x);
        else       t->rch = point_set_rec(t->rch, m, r, p, x);
        pull(t);
        return t;
    }

    static Node* point_apply_rec(Node* cur, int l, int r, int p, const F& f) {
        Node* t = clone_node(cur);
        if (r - l == 1) {
            apply_all(t, f, 1);
            return t;
        }
        push(t, l, r);
        int m = (l + r) >> 1;
        if (p < m) t->lch = point_apply_rec(t->lch, l, m, p, f);
        else       t->rch = point_apply_rec(t->rch, m, r, p, f);
        pull(t);
        return t;
    }

public:
    PersistentLazySegTree() = default;

    explicit PersistentLazySegTree(const std::vector<S>& a) {
        build(a);
    }

    void build(const std::vector<S>& a) {
        n_ = (int)a.size();
        Node* r = build_rec(a, 0, n_);
        roots_.clear();
        roots_.push_back(r); // version 0
    }

    int size() const { return n_; }
    int versions() const { return (int)roots_.size(); }

    // create new version by range apply [l, r)
    int apply(int ver, int l, int r, const F& f) {
        assert(0 <= ver && ver < versions());
        assert(0 <= l && l <= r && r <= n_);
        Node* nr = range_apply_rec(roots_[ver], 0, n_, l, r, f);
        roots_.push_back(nr);
        return versions() - 1;
    }

    // create new version by point set: a[p] = x
    int set(int ver, int p, const S& x) {
        assert(0 <= ver && ver < versions());
        assert(0 <= p && p < n_);
        Node* nr = point_set_rec(roots_[ver], 0, n_, p, x);
        roots_.push_back(nr);
        return versions() - 1;
    }

    // create new version by point apply: a[p] <- f(a[p])
    int apply_point(int ver, int p, const F& f) {
        assert(0 <= ver && ver < versions());
        assert(0 <= p && p < n_);
        Node* nr = point_apply_rec(roots_[ver], 0, n_, p, f);
        roots_.push_back(nr);
        return versions() - 1;
    }

    // range product [l, r)
    S prod(int ver, int l, int r) const {
        assert(0 <= ver && ver < versions());
        assert(0 <= l && l <= r && r <= n_);
        return range_prod_rec(roots_[ver], 0, n_, l, r);
    }

    S all_prod(int ver) const {
        assert(0 <= ver && ver < versions());
        return roots_[ver]->val;
    }
};

// 以下使用例
// sum+add, min+add, max+addの使用例があります。

using ll = long long;
using S = long long;
using F = long long;

// =====================================
// sum + add
// =====================================
S op_sum(const S& a, const S& b) { return a + b; }
S e_sum() { return 0LL; }

// mapping: add f to each element in segment => sum increases by f * len
S mapping_add(const F& f, const S& x, int len) {
    return x + f * (long long)len;
}

// composition(fnew, fold): apply fold then fnew => total add = fold + fnew
F composition_add(const F& fnew, const F& fold) {
    return fnew + fold;
}

F id_add() { return 0LL; }

// Instantiate
using PST = PersistentLazySegTree<
    S, F,
    op_sum, e_sum,
    mapping_add,
    composition_add,
    id_add
>;

// =====================================
// min + add
// =====================================
S op_min(const S& a, const S& b) { return std::min(a, b); }
S e_min() { return std::numeric_limits<S>::max() / 4; } // 十分大きい値

S mapping_add_min(const F& f, const S& x, int /*len*/) {
    // min に +f を作用
    return x + f;
}

F composition_add_min(const F& fnew, const F& fold) {
    // 先に fold, 後で fnew を適用 => 合計加算
    return fnew + fold;
}

F id_add_min() { return 0LL; }

using PersistentLazySegTreeMinAdd = PersistentLazySegTree<
    S, F,
    op_min, e_min,
    mapping_add_min,
    composition_add_min,
    id_add_min
>;

// =====================================
// max + add
// =====================================
S op_max(const S& a, const S& b) { return std::max(a, b); }
S e_max() { return std::numeric_limits<S>::lowest() / 4; } // 十分小さい値

S mapping_add_max(const F& f, const S& x, int /*len*/) {
    // max に +f を作用
    return x + f;
}

F composition_add_max(const F& fnew, const F& fold) {
    return fnew + fold;
}

F id_add_max() { return 0LL; }

using PersistentLazySegTreeMaxAdd = PersistentLazySegTree<
    S, F,
    op_max, e_max,
    mapping_add_max,
    composition_add_max,
    id_add_max
>;

int main() {
    // -------------------------
    // sum+add
    // -------------------------
    std::vector<ll> A = {1, 2, 3, 4, 5};
    PST seg(A); // version 0

    // v1: range add +10 to [1,4): [1,12,13,14,5]
    int v1 = seg.apply(0, 1, 4, 10);

    // v2: point set idx=2 -> 100 on top of v1: [1,12,100,14,5]
    int v2 = seg.set(v1, 2, 100);

    // v3: point apply idx=0 += 7 on top of v2: [8,12,100,14,5]
    int v3 = seg.apply_point(v2, 0, 7);

    std::cout << "v0 sum[0,5) = " << seg.prod(0, 0, 5) << "\n"; // 15
    std::cout << "v1 sum[0,5) = " << seg.prod(v1, 0, 5) << "\n"; // 45
    std::cout << "v2 sum[1,4) = " << seg.prod(v2, 1, 4) << "\n"; // 126
    std::cout << "v3 sum[0,3) = " << seg.prod(v3, 0, 3) << "\n"; // 120

    // old versions remain unchanged
    std::cout << "v0 sum[1,4) (still) = " << seg.prod(0, 1, 4) << "\n"; // 9

    std::vector<ll> a = {5, 1, 7, 3, 9};
    // -------------------------
    // min+add
    // -------------------------
    PersistentLazySegTreeMinAdd segMin(a); // v0
    int v1_min = segMin.apply(0, 1, 4, 10);   // [5,11,17,13,9]
    int v2_min = segMin.set(v1_min, 2, -100); // [5,11,-100,13,9]

    std::cout << "[min+add]\n";
    std::cout << "v0 min[0,5) = " << segMin.prod(0, 0, 5) << "\n";      // 1
    std::cout << "v1 min[0,5) = " << segMin.prod(v1_min, 0, 5) << "\n"; // 5
    std::cout << "v2 min[0,5) = " << segMin.prod(v2_min, 0, 5) << "\n"; // -100
    std::cout << "v0 min[1,4) = " << segMin.prod(0, 1, 4) << "\n";      // 1 (永続性確認)

    // -------------------------
    // max+add
    // -------------------------
    PersistentLazySegTreeMaxAdd segMax(a); // v0
    int v1_max = segMax.apply(0, 0, 3, -2);   // [3,-1,5,3,9]
    int v2_max = segMax.apply_point(v1_max, 1, 100); // [3,99,5,3,9]

    std::cout << "\n[max+add]\n";
    std::cout << "v0 max[0,5) = " << segMax.prod(0, 0, 5) << "\n";      // 9
    std::cout << "v1 max[0,5) = " << segMax.prod(v1_max, 0, 5) << "\n"; // 9
    std::cout << "v2 max[0,5) = " << segMax.prod(v2_max, 0, 5) << "\n"; // 99
    std::cout << "v1 max[0,3) = " << segMax.prod(v1_max, 0, 3) << "\n"; // 5

    return 0;
}
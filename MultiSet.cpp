#include <bits/stdc++.h>
using namespace std;
using ll=long long;
using tup2=tuple<ll,ll>;
#define pb push_back

struct Set{
  struct Node{
    Node *l=0,*r=0;
    ll p,c=1,v,s;
    Node(ll x,ll pr):p(pr),v(x),s(x){}
  };
  Node *rt=0;
  mt19937_64 rng{chrono::steady_clock::now().time_since_epoch().count()};
  ll e(){
    return 0;
  }
  ll op(ll a,ll b){
    return a+b;
  }
  ll cnt(Node *t){
    if(t) return t->c;
    else return 0;
  }
  ll get(Node *t){
    if(t) return t->s;
    else return e();
  }
  void up(Node *t){
    if(!t) return;
    t->c=1+cnt(t->l)+cnt(t->r);
    t->s=op(op(get(t->l),t->v),get(t->r));
  }
  void split(Node *t,ll k,Node *&l,Node *&r){
    if(!t){
      l=r=0;
      return;
    }
    if(t->v<k) split(t->r,k,t->r,r),l=t;
    else split(t->l,k,l,t->l),r=t;
    up(t);
  }
  void splitk(Node *t,ll k,Node *&l,Node *&r){
    if(!t){
      l=r=0;
      return;
    }
    ll c=cnt(t->l);
    if(k<=c) splitk(t->l,k,l,t->l),r=t;
    else splitk(t->r,k-c-1,t->r,r),l=t;
    up(t);
  }
  void merge(Node *&t,Node *l,Node *r){
    if(!l||!r) t=l?l:r;
    else if(l->p>r->p) merge(l->r,l->r,r),t=l;
    else merge(r->l,l,r->l),t=r;
    up(t);
  }
  Set(){}
  void insert(ll x){
    Node *l,*r;
    split(rt,x,l,r);
    merge(rt,l,new Node(x,rng()));
    merge(rt,rt,r);
  }
  void erase(ll x){
    Node *l,*r,*m;
    split(rt,x,l,r);
    if(cnt(r)){
      splitk(r,1,m,r);
      if(m->v!=x) merge(r,m,r);
    }
    merge(rt,l,r);
  }
  ll size(){
    return cnt(rt);
  }
  ll count(ll x){
    Node *l,*r,*m;
    split(rt,x,l,r);
    split(r,x+1,m,r);
    ll res=cnt(m);
    merge(r,m,r);
    merge(rt,l,r);
    return res;
  }
  ll kth(ll k){
    if(k<0||k>=cnt(rt)) return e();
    Node *t=rt;
    while(t){
      ll c=cnt(t->l);
      if(k==c) return t->v;
      if(k<c) t=t->l;
      else k-=(c+1),t=t->r;
    }
    return e();
  }
  ll rank(ll x){
    Node *l,*r;
    split(rt,x,l,r);
    ll res=cnt(l);
    merge(rt,l,r);
    return res;
  }
  ll lower_bound(ll x) {
    Node *t=rt,*res=0;
    while(t){
      if(t->v>=x) res=t,t=t->l;
      else t=t->r;
    }
    if(res) return res->v;
    else return -1;
  }
  ll query(ll l,ll r){
    if(l>=r||l>=cnt(rt)) return e();
    Node *a,*b,*c;
    splitk(rt,r,b,c);
    splitk(b,l,a,b);
    ll res=get(b);
    merge(b,a,b);
    merge(rt,b,c);
    return res;
  }
};

int main(){
  Set s;
  
  // 1. insert(x): 要素xを挿入 (重複可能)
  cout << "=== insert ===" << endl;
  s.insert(5);
  s.insert(3);
  s.insert(7);
  s.insert(3);  // 重複挿入
  s.insert(10);
  cout << "挿入後のサイズ: " << s.size() << endl;  // 5
  
  // 2. size(): 要素数を取得
  cout << "\n=== size ===" << endl;
  cout << "要素数: " << s.size() << endl;  // 5
  
  // 3. count(x): xの個数をカウント
  cout << "\n=== count ===" << endl;
  cout << "3の個数: " << s.count(3) << endl;  // 2
  cout << "5の個数: " << s.count(5) << endl;  // 1
  cout << "100の個数: " << s.count(100) << endl;  // 0
  
  // 4. kth(k): k番目の要素を取得 (0-indexed)
  cout << "\n=== kth ===" << endl;
  cout << "0番目: " << s.kth(0) << endl;  // 3
  cout << "1番目: " << s.kth(1) << endl;  // 3
  cout << "2番目: " << s.kth(2) << endl;  // 5
  cout << "3番目: " << s.kth(3) << endl;  // 7
  cout << "4番目: " << s.kth(4) << endl;  // 10
  
  // 5. rank(x): x未満の要素数を取得
  cout << "\n=== rank ===" << endl;
  cout << "3未満の要素数: " << s.rank(3) << endl;  // 0
  cout << "5未満の要素数: " << s.rank(5) << endl;  // 2
  cout << "8未満の要素数: " << s.rank(8) << endl;  // 4
  
  // 6. lower_bound(x): x以上の最小要素を取得
  cout << "\n=== lower_bound ===" << endl;
  cout << "3以上の最小: " << s.lower_bound(3) << endl;  // 3
  cout << "4以上の最小: " << s.lower_bound(4) << endl;  // 5
  cout << "11以上の最小: " << s.lower_bound(11) << endl;  // -1 (存在しない)
  
  // 7. query(l, r): [l, r)の範囲の要素の和を取得
  cout << "\n=== query ===" << endl;
  cout << "範囲[0,5)の和: " << s.query(0, 5) << endl;  // 3+3+5+7+10=28
  cout << "範囲[1,3)の和: " << s.query(1, 3) << endl;  // 3+5=8
  cout << "範囲[2,4)の和: " << s.query(2, 4) << endl;  // 5+7=12
  
  // 8. erase(x): xを1つ削除
  cout << "\n=== erase ===" << endl;
  s.erase(3);  // 3を1つ削除
  cout << "3を削除後のサイズ: " << s.size() << endl;  // 4
  cout << "3の個数: " << s.count(3) << endl;  // 1
  
  // 削除後の状態確認
  cout << "\n削除後の要素:" << endl;
  for(int i = 0; i < s.size(); i++){
    cout << s.kth(i) << " ";
  }
  cout << endl;  // 3 5 7 10
  
  // 9. 複数の操作の組み合わせ例
  cout << "\n=== 複合操作 ===" << endl;
  Set s2;
  s2.insert(1);
  s2.insert(2);
  s2.insert(2);
  s2.insert(3);
  s2.insert(4);
  
  cout << "2番目から4番目の和: " << s2.query(2, 4) << endl;  // 2+3=5
  cout << "2のランク: " << s2.rank(2) << endl;  // 1
  cout << "2以上の最小値: " << s2.lower_bound(2) << endl;  // 2
  
  return 0;
}
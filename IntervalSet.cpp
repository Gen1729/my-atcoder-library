#include <bits/stdc++.h>
using namespace std;
using ll=long long;
#define pb push_back
using tup2=tuple<ll,ll>;
#define tup make_tuple


struct IntervalSet{
  set<tup2> s;
  IntervalSet(){
    s.insert(tup(-INF,-INF));
    s.insert(tup(INF,INF));
  }
  void on_ins(ll l,ll r){
    if(l>=r) return;
    //自由に記入 [l,r)が挿入された時
  }
  void on_rem(ll l,ll r){
    if(l>=r) return;
    //自由に記入 [l,r)が削除された時
  }
  set<tup2>::iterator find(ll x){
    auto it=s.lower_bound(tup(x,INF));
    it--;
    auto [l,r]=*it;
    if(l<=x&&x<r) return it;
    return s.end();
  }
  tup2 insert(ll l,ll r){
    if(l>=r) return tup(0,0);
    auto it=s.lower_bound(tup(l,-INF));
    it--;
    if(get<1>(*it)>=l){
      on_rem(get<0>(*it),get<1>(*it));
      l=get<0>(*it);
      r=max(r,get<1>(*it));
      s.erase(it);
    }
    it=s.lower_bound(tup(l,-INF));
    while(get<0>(*it)<=r){
      on_rem(get<0>(*it),get<1>(*it));
      r=max(r,get<1>(*it));
      s.erase(it++);
    }
    on_ins(l,r);
    s.insert(tup(l,r));
    return tup(l,r);
  }
  void remove(ll l,ll r){
    if(l>=r) return;
    auto it=s.lower_bound(tup(l,-INF));
    it--;
    if(get<1>(*it)>l){
      tup2 left=*it;
      on_rem(get<0>(left),get<1>(left));
      s.erase(it);
      if(get<0>(left)<l){
        on_ins(get<0>(left),l);
        s.insert(tup(get<0>(left),l));
      }
      if(get<1>(left)>r){
        on_ins(r,get<1>(left));
        s.insert(tup(r,get<1>(left)));
      }
    }
    it=s.lower_bound(tup(l,-INF));
    while(get<0>(*it)<r){
      tup2 right=*it;
      on_rem(get<0>(right),get<1>(right));
      s.erase(it++);
      if(get<1>(right)>r){
        on_ins(r,get<1>(right));
        s.insert(tup(r,get<1>(right)));
        break;
      }
    }
  }
  bool same(ll x,ll y){
    auto it=find(x);
    if(it==s.end()) return false;
    auto [l,r]=*it;
    return (l<=y&&y<r);
  }
  ll size(){
    return (ll)s.size()-2;
  }
};

int main(){
    IntervalSet is;

    // insert(l, r) : [l, r) を追加。重なる区間はマージされる。
    // 戻り値 : マージ後の区間 [L, R)
    auto [L, R] = is.insert(3, 7);   // [3,7) を追加
    is.insert(5, 10);                 // → [3,10) にマージ
    is.insert(1, 3);                  // → [1,10) にマージ

    // remove(l, r) : [l, r) を削除。区間の一部だけ削除すると分割される。
    is.remove(4, 6);   // [1,4) と [6,10) に分割される

    // find(x) : x を含む区間のイテレータを返す。含む区間がなければ s.end()
    auto it = is.find(2);
    if(it != is.s.end()){
        auto [l, r] = *it;  // l=1, r=4
    }

    // same(x, y) : x と y が同一の区間に含まれるか判定
    bool b = is.same(1, 3);  // true  (どちらも [1,4) に含まれる)
    bool c = is.same(1, 7);  // false (7 は [6,10) に含まれる)

    // size() : 現在管理している区間の個数を返す
    ll n = is.size();  // 2 ( [1,4) と [6,10) )
}
method Main() {
  print "Hello wordny";
}

method SimpleMethod(x : int, b :bool) {
  var y := x + 3;
  print y, " ", b, "\n";
}

method MethodWithResults(x : int) returns (r : int, s : int) {
  r := x;
  s := x + 3;
}
// dafny run
// dafny run --target:go
// dafy translate js Hello.dfy

/*
built in types
type T = U type synonum
Type T  abstract type
datatype
codatatype
newtype
class
trait
type t = u : U | P(u)   subset type


built i n
bool int real char bv0 bv1 bv2
object 
ORDINAL

set<Type> iset<> multiset
seq<Type>
map<>
imap<> inifnite 

-> --> ~> arrow ttypes
~> are partial (have preconditions) and can read heap.
-> total arrow
--> partial arrow

array2<Type>
nat string


type safe
types are nominal
types may be empty
polymorphism. polymorphic, predicatve

trats datatype newtype class and abstract types have membrs


false, true
&& ||
shortcircuts
==> <==
<==>


*/

predicate HashMnimum(s : set<int>) {
  exists m :: m in s && forall x :: x in s ==> m <= x
}

predicate sIndexOfMinimum(i : int, s : seq<int>){
  && 0 <= i < |s|
     //  && forall j :: 0 <= j < |s| ==>
}

/*
unbounded integrs

seprated digits by _
euclidean div nod
comparsons are chaining 0 <= i < j < 100
type nat = x : int |  0 <= x

Reals unbounded no floting point support
'D' characters '\U{10_aBcD}' unicode
type string = seq<char>

bitvectors
&  | ^  more binding power than short ciruit
<< 
>>
RotateLft
RotateRight
unsigned


newtype
nwtype int32 = x : int | -0x8000_0000 <= x < 0x800000
newtype byte = x | 0 <= x < 256
different from subset types. Every intermediatecexpression by also support 
dafny figures out if can fit in machine word

predictate sPrmt(x:int) {

}
*/
newtype int32 = x : int | -0x8000_0000 <= x < 0x800000

method Example1s(){
  var a : int;
  var b : int32;
  var c : bv32;
  a := 25;
  b := 25;
  c := 25;
  var e;
  e := 25 as int32;

}


method Combine(a : set<real>, b : set<real>) returns (c : set<real>){
  c := a + b;
  assert |c| <= |a| + |b|;
  c := c + {2.0, 37.3};
}
method Suffle(s : seq<char>) returns (r : string) {
  var n := |s| / 2;
  r := s[n..] + ['a','b'] + s[..n] + "xyz";
}

method Squares(n : nat){
  var s := set i | 0  <= i < n;
  var t := set i | 0  <= i < n :: i * i;
  var m := map i | 0 <= i < n :: i * i;
  //var w := map i | 0 <= i < n :: i * i := i; // map from squares to to n
  var q := seq(n, i => i * i); // lambda expressions
}

datatype List<X> = Nil |  Cons(head: X, tail : List<X>)

datatype Rainbow = L | G | W

datatype Expr = Const(value : int) | Plus(0 : Expr, 1 : Expr)

datatype Record = Record(name: string, age:nat)

method Print(expr: Expr){
  match expr
  case Const(value) => print value;
  case Plus(left,right) => Print(left); print " + "; Print(right);
}
// can also use disctiminators. expr.Const?
// var Const(n) := expr; is irrefutsable pattern

method Double(expr:Expr){
  if expr.Const? {
    var u := expr.(value := 2 * expr.value);
  }
}

datatype Macklemore = Macklemore(rhyme:string) // single fields compile to just the type itself

// Tuples. They are just datatype but with special syntax
// (1,2,3,'a')

// codatatype
codatatype Stream<X> = Next(head : X, tail: Stream<X>)


// subset types / refinemnt types/ predicate types
type Even = x : int | x % 2 == 0


/*
type IntList = List<int>
type IncreasingLst 
predicate IsIncreasing(i : IntList) {
    i.Cons? ==>
     && i.head <= i.tail.head
     && 
}

*/

/* 

classes

*/
class Cell {
  var data : int
}

/*
two phase constructions

`new` keyword;

class CyclicList<X>{
    
}
*/

/*
non nul reference types
Cell? is a nullabe type
type Cell = x : Cell? | c != null

*/

/*
trai


trait Animal extends object {
    const name : string
    var age: nat
    method Print()
}

*/

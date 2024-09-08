#import "../../preamble/lemmas.typ": *
#import "../../preamble/catt.typ": *
#import "@preview/fletcher:0.5.1" as fletcher: diagram, node, edge

#exercise("1")[
  Let $T_0$ send a set $X$ to its powerset $cal(P)(X)$...
]
We show that $T=(T_0,T_1)$ is a functor by @defn-functor
#figure(table(
  columns: 2,
  align: (right, left),
  [structure], [definition],
  [domains], $T_1(f)=[A |-> {f(x) | x in A }]$,
  [identity], $T_1(1_A)= T_1(id) = id = 1_(T_0(A))$,
  [composition], $T_1(g comp f) = T_1(g) comp T_1(f)$
))
#proof(name: "composition")[$
T_1(g comp f)
&= [A |-> {g(f(x)) | x in A }] \
&= [A |-> {g(y) | y in {f(x) | x in A}}] \
&= [A |-> {g(y) | y in T_1(f)(A)}] \
&= [A |-> [B |-> {g(y) | y in B}](T_1(f)(A))] \
&= [A |-> T_1(g)(T_1(f)(A))] \
&= [A |-> (T_1(g) comp T_1(f))(A)] \
&= T_1(g) comp T_1(f)
$
$therefore T$ is a functor from $Set$ to $Set$
]

#exercise("2")[
  Define the category $bb(K)$ as follows ...
]
$bb(K)$ morphisms are left total relations for objects in $Set$. The relations are encoded as functions mapping an element of $X$ to a subset of $Y$. Thus we can show $bb(K)$ is a category by @defn-cat.
#figure(table(
  columns: 2,
  align: (right, left),
  [properties], [definition],
  [composition], $g comp f = union_(y in f(x)) g(y)$,
  [identity], $1_X = [x |-> {x}]$,
  [associativity], $h comp (g comp f) = (h comp g) comp f$,
  [unital], $1_T(Y) comp f comp 1_X = f$,
))
#grid(columns: (1fr, 1fr), align: (left, left),
proof(name: "associativity")[$
h comp (g comp f)
&= [x |-> union_(z in (g comp f)(x)) h(z)] \
&= [x |-> union_(z in union_(y in f(x)) g(y)) h(z)] \
&= [x |-> union_(y in f(x)) union_(z in g(y)) h(z)] \
&= [ x |-> union_(y in f(x)) (h comp g)(y)] \
&= [x |-> ((h comp g) comp f)(x)] \
&= (h comp g) comp f
$],
proof(name: "unital")[$
1_(T(Y)) comp f comp 1_X
&= [x |-> union_(x' in 1_X(x)) union_(y in f(x')) 1_(T(Y))(y)] \
&= [x |-> union_(x' in {x}) union_(y in f(x')) [y |-> {y}](y)] \
&= [x |-> union_(x' in {x}) union_(y in f(x')) {y}] \
&= [x |-> union_(x' in 1_X(x)) f(x')] \
&= [x|-> union_(x' in {x}) f(x')] \
&= [x |-> f(x)] = f
$])

Let $F,G$ be an isomorphism by @defn-isomorphism
#grid(columns: (1fr, 1fr), align: (left, left),
[
$
arr(F,bb(K),Rel)
$
$
F(X) &= X \
F(arr(f,X,T(Y))) &= {(x,y) | y in f(x)}
$
],[
$
arr(G, Rel, bb(K))
$
$
G(X) &= X \
G(R) &= [x |-> {y | (x,y) in R}]
$
])

#grid(columns: (1fr, 1fr), align: (left, left),
proof(name: $G comp F = 1_bb(K)$)[$
&(G comp F)(f)\
&= G({(x,y) | y in f(x)}) \
&= [x |-> {y | (x,y) in {(x,y) | y in f(x)}}] \
&= [x |-> {y | y in f(x)}] \
&= [x |-> f(x)] = f
$],
proof(name: $F comp G = 1_Rel$)[$
&(F comp G)(R) \
&= F([x |-> {y | (x,y) in R}]) \
&= {(x,y) | y in [x |-> {y | (x,y) in R}](x)} \
&= {(x,y) | y in {y | (x,y) in R}} \
&= {(x,y) |(x,y) in R)} = R
$]
)
$therefore bb(K)$ is a category that is isomorphic to $Rel$ via $F,G$.

#exercise("3")[
Let $bb(C)$ be a category with binary products ...
]
_Remark_: epi, mono, showing uniqueness of morphism is not explored in SA chapter 1, we will revisit this exercise in the future.

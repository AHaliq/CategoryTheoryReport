#import "../../preamble/lemmas.typ": *
#import "../../preamble/catt.typ": *
#import "@preview/fletcher:0.5.1" as fletcher: diagram, node, edge

#exercise("3 From Wk1")[Let $bb(C)$ be a category with binary products]

#proof(name: [is the projection $pi_X : X times Y -> X$ an epimorphism in general? Is it a monomorphism?])[
It is a monomorphism since there is a unique $u$ into $X times Y$ by UMP of product. It is not necessarily an epimorphism as there can be more than one distinct morphism out of $X$
]

#grid(columns: (1fr, 1fr), align: (left, left), 
proof(name: [show $(f,g) comp h = (f comp h, g comp h)$])[
#figure(diagram(cell-size: 10mm, $
& W
  edge("ddl", f comp h, ->)
  edge("ddr", g comp h, ->)
  edge("d",h,->)
  edge("dd", (f comp h, g comp h), "-->", bend: #20deg) \
& Z edge("d", (f,g), "-->") \ 
X edge("ur", f, <-) &
X times Y 
  edge("l", pi_X, ->)
  edge("r", pi_Y, ->) &
Y edge("ul", g, <-)
$))
$
"UMP"(f comp h, g comp h) = (f,g) comp h
$],
proof(name: [Let $arr(f,Z,X)$ and $arr(g,W,Y)$ be ...])[
#figure(diagram(cell-size: 10mm, $
&
A
  edge("dl", h_Z, ->)
  edge("dr", h_W, ->) 
  edge("d", u', "-->") \
Z edge("d",f,->) &
Z times W
  edge("l",pi_Z,->) 
  edge("r",pi_W,->) 
  edge("d",u,"-->") &
W edge("d",g,->) \
X &
X times Y
  edge("l",pi_X,->)
  edge("r",pi_Y,->) &
Y
$))
$
"UMP"(h_Z,h_W) &= u' \
"UMP"(f comp h_Z, g comp h_W) &= u comp u'
$
by uniqueness of $u'$ and $u comp u'$, $u$ too is unique
]
)
#proof(name: [Show  $(f times g) comp (h times k) = (f comp h) times (g comp k)$])[
#figure(diagram(cell-size: 10mm, $
& T
  edge("d", u, "-->")
  edge("dl", u_A, ->)
  edge("dr", u_B, ->)
& \
A 
  edge("d", h, ->) &
A times B
  edge("l", pi_A, ->)
  edge("r", pi_B, ->)
  edge("d", (h,k), "-->") &
B
  edge("d", k, ->) \
Z edge("d", f, ->) &
Z times W 
  edge("l", pi_Z, ->)
  edge("r", pi_W, ->)
  edge("d", (f,g), "-->") &
W
  edge("d",g,->) \
X &
X times Y
  edge("l",pi_X,->) 
  edge("r",pi_Y,->) &
Y
$))
$
"UMP"(u_A, u_B) &= u \
"UMP"(h comp u_A, k comp u_B) &= (h,k) comp u \
"UMP"(f comp h comp u_A, g comp k comp u_B) &= (f,g) comp (h,k) comp u \
(f comp h comp u_A) times (g comp k comp u_B) &= (f,g) comp (h,k) comp u \
((f comp h) times (g comp k)) comp u &= (f,g) comp (h,k) comp u \
(f comp h) times (g comp k) &= (f times g) comp (h times k) \
$
]


#exercise("1")[Show that every poset considered as a catgory has equalizers and coequalizers of all pairs of morphisms]

_Remark_: SA Chapter 2 did not cover equalizers and coequalizers, we will revisit the question in the future.

#exercise("2")[Let the functor $arr(F,bb(C),bb(D))$ be an isomorphism of categories. Show the following.]

#proof(name: [if $bb(C)$ has binary products so does $bb(D)$ and $F$ preserves them])[
A product is a $"UMP"(arr(f,X,A),arr(g,X,B))= arr(u,X,A times B)$
#figure(table(columns: 2, align: (right, left),
[Product UMP], [definition],
[existence], $arr(F(f),F(X),F(A)),arr(F(g),F(X),F(B)), exists arr(F(u),F(X),F(A times B))$,
[uniqueness], $exists u', F(u). F^(-1)(u') = F^(-1)(F(u)) => u' = F(u)$
))
since $u$ is unique by definition of product, and $F$ is an isomorphism, if there exists another $arr(u',F(X),F(A times B))$ it too maps to unique $u$ bijectively, making $u' = F(u)$
]

#proof(name: [if $bb(C)$ has binary coproducts so does $bb(D)$ and $F$ preserves them])[
same argument as above
]

_Remark_: skipping the equalizers and coequalizers for now

#exercise("3")[Let $bb(C)$ be a category and $X$ an object of $bb(C)$. Show the following]

#proof(name: [The slice category $slice(bb(C),X)$ always has a terminal object])[
recall the objects are morphisms $arr(f,\_,X)$ and morphisms are morphisms between the domain objects. All objects; $arr(f,\_,X)$ thus have morphisms to object $arr(id_X,X,X)$, making it a terminal object

#figure(diagram(cell-size: 10mm, $
Y 
  edge("d", f, ->)
  edge("r", f, ->) &
X edge("dl", id_X,->)\
X
$))
]

#proof(name: [If $bb(C)$ has an initial object then so does $slice(bb(C),X)$])[
if $0$ is the initial object of $bb(C)$ then $arr(0_X,0,X)$ is the initial object. If $arr(f,Y,X)$ is an object of $slice(bb(C),X)$ then $arr(0_Y,0,Y)$ is the morphism from the initial object of $slice(bb(C),X)$

#figure(diagram(cell-size: 10mm, $
0 
  edge("r", 0_Y, ->)
  edge("d", 0_X, ->) &
Y 
  edge("dl", f, ->) \
X
$))
]

_Remark_: skipping the equalizers question for now
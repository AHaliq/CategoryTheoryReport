#import "../../preamble/lemmas.typ": *
#import "../../preamble/catt.typ": *
#import "@preview/fletcher:0.5.1" as fletcher: diagram, node, edge

#exercise("1")[Show that a function between sets is an epimorphism if and only if it is surjective. Conclude that isos in $Set$ are exactly the epi-monos.]

#proof(name: "surjective implies epimorphism")[

We can define surjective functions as follows and derive the property of epimorphisms
$
&forall y in Y. exists x. f(x) = y \
&= forall x. f(x) = y and (g(y) "is well defined") \
&= forall x. f(x) = y and (g(y) = h(y) => g(y) = h(y)) \
&= forall x. g(f(x)) = h(f(x)) => g = h \
&= g comp f = h comp f => g = h \
&= "isEpi"(f)
$
]

#proof(name: "epimorphism implies surjective")[
#grid(columns: (1fr, 1fr), align: (left, left),
[
if $f$ is not surjective then $"im"(f)$ is a subset of $Y$

#figure(diagram(cell-size: 10mm, $
X
  edge("r", f, ->) &
#node($Y$, name:<Y>)
  #edge(<Y>,<Y>, $id_Y$, "->", bend: 130deg)
  edge("r", pi, ->, bend: #30deg) &
"im"(f)
  edge("l", i, "hook->", bend: #30deg)
$))
],
[
if we let $g = id_Y$ and $h= i comp pi$ we can see
$
"isEpi"(f) &= id_Y comp f = i comp pi comp f => id_Y = i comp pi \
&= Y = "im"(f) \
&= "surjective"(f)
$
])
]

#proof(name: "isos are epi-monos")[
Isomorphisms are bijective functions, and thus are both surjective and injective. Thus We just have to show injective functions are exactly monomorphisms.

we can define injectivity as follows and derive the property of monomorphisms
$
&forall w_1, w_2. w_1 != w_2 => f(w_1) != f(w_2) \
&=forall w_1, w_2. f(w_1) = f(w_2) => w_1 = w_2 \
&=forall w.  f(g(w)) = f(h(w)) => g(w) = h(w) \
&=f comp g = f comp h => g = h \
&= "isMono"(f)
$

#grid(columns: (1fr, 1fr), align: (left, left),
[
if $f$ is not injective then $"preim"(f)$ is a strict subset of $X$ as there can be more than two pre-images for a single element in the codomain.

#figure(diagram(cell-size: 10mm, $
"preim"(f)
  edge("r", i, "hook->", bend: #30deg) &
#node($X$, name: <X>)
  #edge(<X>, <X>, $id_X$, "->", bend: 130deg)
  edge("l", pi, ->, bend: #30deg)
  edge("r", f, ->) &
Y
$))
],
[
if we let $g = i comp pi$ and $h = id_X$ we can see
$
"isMono"(f)
&= f comp id_X = i comp pi comp f => id_X = i comp pi \
&= X = "preim"(f) \
&= "injective"(f)
$
])
]

#exercise("2")[Show that in a poset category, all arrows are both monic and epic.]
Recall a poset category has elements of the poset as objects and morphisms as witness the $<=$ relation holds for the two objects. Since all arrows between any two objects are unique, $g = h$ regardless if they are post-composites of an epi or pre-composites of a mono. Thus all arrows are monic and epic.

#exercise("3")[(Inverses are unique.) If an arrow $arr(f,A,B)$ has inverses $g,arr(g',B,A)$ (i.e. $g comp f = 1_A$ and $f comp g = 1_B$ and similarly for $g'$), then $g=g'$.
]

$g comp f = 1_A$ makes $f$ a split mono of epic $g$ and $g'$ by @defn-splitepimono. Since $g$ and $g'$ are inverses of $f$, thus $f comp g = f comp g' = 1_B$. Moreover since $f$ is a monomorphism, 

$
"isMono"(f) = f comp g = f comp g' => g = g'
$

#exercise("4")[With regard to a commutative triangle... in any category $upright(bold(C))$, show]

#proof(name: [if $f$ and $g$ are isos (resp. monos, resp. epis), so is $h$])[
we know by the commutative triangle $h = g comp f$

since $f,g$ are isos we also know there exists unique $f^(-1),g^(-1)$ such that

#grid(columns: (1fr, 1fr), align: (left, left),
$
1_A &= f^(-1) comp g^(-1) comp g comp f \
&= f^(-1) comp g^(-1) comp h
$,
$
1_B &= g comp f comp f^(-1) comp g^(-1) \
&= h comp f^(-1) comp g^(-1)
$
)
$
therefore h^(-1) &= f^(-1) comp g^(-1) => "isIso"(h)
$
]

#proof(name: [if $h$ is monic, so is $f$])[
if $f$ is not monic, there exists $i != j$ where $f comp i = f comp j => i != j$

now that we know $i$ and $j$ are distinct, we can see $h$ is also not monic as $h comp i = h comp j cancel(=>) i = j$

thus proven by contrapositive
]

#proof(name: [if $h$ is epic, so is $g$])[
similar argument as monic
]

#proof(name: [if $h$ is monic, $g$ need not be.])[

#figure(diagram(cell-size: 10mm, $
E
  edge("r", i_c, ->, bend: #30deg)
  edge("r", j_c, ->, bend: #{-30deg}) &
A
  edge("r", f, ->)
  edge("dr", h, ->) &
B
  edge("d", g, ->) &
D
  edge("l", i_b, ->, bend: #30deg)
  edge("l", j_b, ->, bend: #{-30deg}) \ & &
C
$))
it is very well possible $i_c = j_c$ and $i_b != j_b$
]

#exercise("5")[Show that the following are equivalent for an arrow $arr(f,A,B)$ in any category]

#grid(columns: (1fr, 1fr), align: (left, left),
[
- $f$ is an isomorphism
- $f$ is both a mono and a split epi
- $f$ is both a split mono and an epi
- $f$ is both a split mono and a split epi

#figure(diagram(cell-size: 10mm, $
A
  edge("r", f, ->)
  edge("dr", 1_A, ->) 
  #edge("dr", $g comp f$, "->", label-side: right, bend: -30deg) &
B
  #edge("dr", $1_B$, "->", label-side: right)
  #edge("d", $g$, "->", label-side: left)
  edge("dr", f comp g, ->, bend: #30deg)\
& A
  #edge("r", $f$, "->", label-side: right) &
B
$))]
,
$
"isIso"(f) &= g comp f = 1_A and f comp g = 1_B \
&= (f comp g comp f = f comp 1_A) and (f comp g = 1_B) \
&= "isMono"(f) and "isSplitEpi"(f) \
&= g comp f = 1_A and f comp g = 1_B \
&= (g comp f = 1_A) and (f comp g comp f = 1_B comp f) \
&= "isSplitMono"(f) and "isEpi"(f) \
&= (g comp f = 1_A) and (f comp g = 1_B) \
&= "isSplitMono"(f) and "isSplitEpi"(f)
$)

#exercise("13")[In any category with binary products, show directly that $A times (B times C) iso (A times B) times C$]

#figure(diagram(cell-size: 12mm, $
B &
A times B
  edge("l", pi_B, ->)
  edge("d", pi_A, ->) &
(A times B) times C
  edge("l", pi_(A,B), ->)
  edge("r", pi_C, ->)
  edge("dl", ->)
  edge("dr", ->) &
C &
X
  edge("l", h, ->)
  edge("d", g, ->)
  edge("dl", "-->") \
X
  edge("u", g, ->)
  edge("ur", "-->")
  edge("r", f, ->) &
A &
A times (B times C)
  edge("l", pi_A, ->)
  edge("r", pi_(B,C), ->)
  edge("ul", ->)
  edge("ur", ->)
  edge("u", upright("assoc"), "<-->") &
B times C
  edge("r", pi_B, ->)
  edge("u", pi_C, ->) &
B
$))

$
"UMP"(pi_(A,B),pi_C) &= upright("assoc") \
"UMP"(pi_A,pi_(B,C)) &= upright("assoc")^(-1) \
(A times B) times C iso A times (B times C) &= "isIso"(upright("assoc"))
$
_Note_: there is some abuse of notation where different projection morphisms are notated with the same name. But the UMPs holds nonetheless.

#exercise("14")[For any index set $I$, define the ...]

#proof(name: [For any index set $I$, define the prouct $Pi_(i in I) X_i$ of an $I$-indexed family of objects $(X_i)_(i in I)$ in a category, by giving a UMP generalizing that for binary products (the case $I=2$)])[
$
"UMP"_I (arrow(f)) &= cases(
  "UMP"_(I-1) (arrow(f) slash {f_1, f_2} union {"UMP"(f_1,f_2)}) & #h(1em) I > 1,
  f_1
)
$
this is left associative e.g.
$
"UMP"_3 ({f,g,h}) 
&= "UMP"_2 ({f times g, h}) \
&= "UMPI"_1 ({(f times g) times h)}) \
&= (f times g) times h
$
we can define $"UMP"_I$ via right associativity by popping the last two elements instead.
]

#proof(name: [Show that in $Set$, for any set $X$ the set $X^I$ of all functions $arr(f,I,X)$ has this UMP, with respect to the "constant family" where $X_i = X$ for all $i in I$, and thus $X^I iso Pi_(i in I) X$])[
$
"UMP"_I (X^I)
&= "UMP"_I ({f_1,f_2,f_3 ...}) \
&= "UMP"_(I-1) ({f_1 times f_2, f_3, ...}) \
&= "UMP"_1({f_1 times f_2 times f_3 ...}) \
&= f_1 times f_2 times f_3 ...
$
]

#exercise("15")[Given a category $upright(bold(C))$ with objects $A$ and $B$, define the category $upright(bold(C))_(A,B)$...]

#figure(diagram(cell-size: 10mm, $
& X
  edge("dl", x_1, ->)
  edge("dr", x_2, ->)
  edge("d", u, "-->") \
A &
1 
  edge("l", pi_A, ->)
  edge("r", pi_B, ->) &
B
$))

$
forall X. "UMP"(x_1,x_2) &= u \
1_X &: (X,x_1,x_2) -> (1, pi_A, pi_B)
$

#exercise("17")[In any category $upright(bold(C))$ with products, define the graph ...]

we can deduce the following if $f$ is monic
$
"isMonic"(1_A times f)
&= (1_A times f) comp g = (1_A times f) comp h => g = h \
&= (1_A comp g times f comp g) = (1_A comp h times f comp h) => g = h \
&= 1_A comp g = 1_A comp h and f comp g = f comp h => g = h \
&= g = h and f comp g = f comp h => g = h \
&= f comp g = f comp h => g = h
$

thus $f$ must be monic by the contrapositive
$
g != h => f comp g != f comp h
$

then we have the functor
$
Gamma(A) &= A \
Gamma(f) &= "im"(1_A times f)
$
that preserves the structure
#figure(table(columns: 2, align: (left, left), 
[structure], [definition],
[domain], $arr(Gamma(f),Gamma(A), Gamma(B))$,
[identity], $Gamma(1_A) = "im"(1_A times 1_A) = 1_(Gamma(A))$,
[composition], $Gamma(g comp f) = Gamma(g) comp Gamma(f)$,
))

#proof(name: "composition")[
$
Gamma(g comp f)
&= "im"(1_A times g comp f) \
&= "im"((1_A times g) comp (1_A times f)) \
&= "im"(1_A times g) comp "im"(1_A times f) \
&= Gamma(g) comp Gamma(f)
$
]

#exercise("18")[Show that the forgetful functor $arr(U, Mon,Set)$ from ...]

A representable functor is one that 
#import "../../preamble/lemmas.typ": *
#import "../../preamble/catt.typ": *
#import "@preview/fletcher:0.5.1" as fletcher: diagram, node, edge

#exercise("1")[The objects of $Rel$ are sets ...]

We show $Rel$ is a category by @defn-cat
#figure(
  table(
    columns: 2,
    align: (right, left),
    [properties], [definition],
    [composition], $(S comp R)={(a,c)|exists b.(a,b) in R and (b,c) in S}$,
    [identity], $1_A={(a,a)|a in A}$,
    [associativity], $(S comp R) comp Q = S comp (R comp Q)$,
    [unital], $1_B comp S comp 1_A = S$,
  ),
)

#proof(name: "associativity")[$
    (S comp R) comp Q
    &= {(b,d)|exists c. (b,c) in R and (c,d) in S} comp Q \
    &= {
      (a,d)|exists b. (a,b) in Q and (b,d) in {
        (b,c)|exists c. (b,c) in R and (c,d) in S
      }
    } \
    &= {(a,d)|exists b.(a,b) in Q and exists c.(b,c) in R and (c,d) in S} \
    &= {
      (a,d)|exists c. (a,c) in {(a,c)|exists b.(a,b) in Q and (b,c) in R} and (
        c,d
      ) in S
    } \
    &= {(a,d)|exists c. (a,c) in (R comp Q) and (c,d) in S} \
    &= S comp (R comp Q)
  $]

#proof(name: "unital")[$
    1_B comp S comp 1_A
    &= 1_B comp {(a,b)| exists a.(a,a) in 1_A and (a,b) in S} \
    &= 1_B comp {(a,b)| exists a. (a,b) in S} \
    &= 1_B comp S \
    &= {(a,b)|exists b.(a,b) in S and (b,b) in 1_B} \
    &= {(a,b)|exists b. (a,b) in S} \
    &= S
  $]

$therefore Rel$ is a category

Let $G$ be a functor such that @defn-functor holds.

#figure(
  table(
    columns: 2,
    align: (right, left),
    [structure], [definition],
    [domains], $G(f) = {(a,f(a))|a in A}$,
    [identity], $G(1_A) = {(a,1_A (a))|a in A} = 1_G(A)$,
    [composition], $G(g comp f) = G(g) comp G(f)$,
  ),
)

#proof(name: "composition")[$
    G(g comp f)
    &= {(a,(g comp f)(a)) | a in A} \
    &= {(a,g(b)) | f(a) = b and a in A} \
    &= {(a,c)|f(a) = b and g(b) = c and a in A} \
    &= {(a,c)|(a,b) in {(a,f(a))|a in A} and (b,c) in {(b,g(b))|b in B}} \
    &= {(a,c)| (a,b) in G(f) and (b,c) in G(g)} \
    &= G(g) comp G(f)
  $
  $therefore arr(G,Set,Rel)$
]

Let $C$ be a functor as @defn-functor holds.

#figure(
  table(
    columns: 2,
    align: (right, left),
    [structure], [definition],
    [domains], $C(S) = {(b,a)|(a,b) in S}$,
    [identity], $C(1_A) = {(a,a)|(a,a) in 1_A} = 1_C(A)$,
    [composition], $C(S comp R) = C(S) comp C(R)$,
  ),
)

#proof(name: "composition")[$
    C(S comp R)
    &= {(c,a)|(a,c) in S comp R} \
    &= {(c,a)|exists b.(a,b) in R and (b,c) in S} \
    &={(c,a)|exists b.(c,b) in C and (b,a) in C(R)} \
    &= C(S) comp C(R)
  $
  $therefore arr(C,op(Rel),Rel)$
]

#exercise("2")[Consider the following isomorphisms of categories and determine which hold.]

#figure(
  table(
    columns: 2,
    align: (right, left),
    [isomorphism], [holds],
    $Rel iso op(Rel)$, [yes by $C comp C = 1_op(Rel) = 1_Rel$],
    $Set iso op(Set)$, [no since not all functions are bijective; has inverses],
    $op(P(X)) iso P(X)$,
    [yes as $P(X)$ is a subcategory of $Rel$ thus $C$ is proof],
  ),
)

#exercise("3")[Show that...]

#proof(name: [isomorphisms in $Set$ are bijections])[$
    A iso B
    &<-> exists f,g. g comp f = 1_A and f comp g = 1_B \
    &<-> exists f,g.forall x,y. g(f(x)) = x and f(g(y)) = y \
    &<-> "isBijective"(f)
  $]

#proof(name: [isomorphisms in $Mon$ are bijective homomorphisms])[$
    A iso B
    &<-> exists f,g. g comp f = 1_A and f comp g = 1_B \
    &<-> exists f,g. forall a_0, a_1, b_0, b_1. \
    & g(f(a_0 times_A a_1)) = g(f(a_0) times_B f(a_1)) = g(f(a_0)) times_A g(
      f(a_1)
    ) = a_0 times_A a_1 \
    &and f(g(b_0 times_B b_1)) = f(g(b_0) times_A g(b_1)) = f(g(b_0)) times_B f(
      g(b_1)
    ) = b_0 times_B b_1 \
    &<-> "isBijectiveHomomorphism"(f)
  $]

#proof(name: [isomorphisms in $Pos$ are not bijective homomorphisms])[

  Let $a_0,a_1 in A$ be a poset where $a_0 <= a_1$.

  Let $b_0,b_1 in B$ be a poset where there is no ordering between $b_0$ and $b_1$.

  Even though we can define a homomorphism / bijective function from $[a_i |-> b_i]$,

  there are no monotone functions / bijective homomorphisms $f$ such that $f(a_0) <= f(a_1)$
]

#exercise("5")[For any category $bold(C)$, define a functor $U$...]
Let $U$ be a functor such that @defn-functor holds.
#figure(
  table(
    columns: 2,
    align: (right, left),
    [structure], [definition],
    [domains],
    $U(arr(f,X,C)) &= X \ U(f in Hom(slice(bold(C),C),s:X,t:Y)) &= f$,

    [identity], $U(1_X) = 1_X = 1_U(X)$,
    [composition], $U(g comp f) = g comp f = U(f) comp U(g)$,
  ),
)
We then define the functor $F$ as follows:
#figure(
  table(
    columns: 2,
    align: (right, left),
    [structure], [definition],
    [domains],
    $F(arr(f,X,C)) = f \ F(g in Hom(slice(bold(C),C),s:f,t:f')) = (g,1_C)$,

    [identity], $F(1_arr(f,X,C)) = (1_X,1_C)$,
    [composition], $F(g_2 comp g_1) = F(g_2) comp F(g_1)$,
  ),
)
#proof(name: "composition")[$
    F(g_2 comp g_1)
    &= (g_2 comp g_1, 1_C) \
    &= (g_2 comp g_1, 1_C comp 1_C) \
    &= (g_2,1_C) comp (g_1,1_C)
    &= F(g_2) comp F(g_1)
  $
  #figure(
    diagram(
      cell-size: 10mm,
      $
        X edge("r", g_1, ->) edge("d", f, ->) &
        Y edge("d", f', ->) edge("r", g_2, ->) &
        Z edge("d", f'', ->) \
        C edge("r", 1_C, ->) &
        C edge("r", 1_C, ->) & C
      $,
    ),
  )
]
#proof(name: $dom comp F = U$)[
  $
    (dom comp F)(f) = dom(f) = X = U(f) \
    (dom comp F)(g) = dom(g,1_C) = g = U(g)
  $
]

#exercise("6")[Construct the 'coslice category'...]
We define the co-slice category as before in @defn-constructions.

#{
  let cat = $bold(C)$
  let cs = $slice(bold(C), C)$
  let cc = $coslice(bold(C),C)$
  [
    $
      Ob(cc) = {X|Hom(cat,s:C,t:X) != emptyset} \
      Hom(cc,s:arr(f,C,X),t:arr(g,C,Y)) = Hom(cat,s:X,t:Y)
    $
    with the dual operator on slice categories as
    $
      &op((Ob(cs), Hom(cs))) \
      &= ({arr(f^(-1),C,X)|arr(f,X,C) in Ob(cs)}, Hom(cs)) \
      &= (Ob(cc), Hom(cc))
    $
  ]
}

#exercise("7")[Let $2={a,b}$ be any set with exactly two elements...]
Given
$
  F(arr(f,X,2)) = (f^(-1)(a),f^(-1)(b))
$
we can define its inverse as
$
  F^(-1)(x_0,x_1) = [x_0 |-> a, x_1 |-> b]
$
such that
#proof(name: "inverse")[
  #grid(
    columns: (1fr, 1fr),
    align: (center + horizon, center + horizon),
    $
      (F^(-1) comp F)(f)
      &= F^(-1)(f^(-1)(a),f^(-1)(b)) \
      &= [f^(-1)(a) |-> a, f^(-1)(b) |-> b] \
      &= f
    $,
    $
      (F comp F^(-1))(x_0,x_1)
      &= F([x_0 |-> a, x_1 |-> b]) \
      &= (x_0,x_1)
    $,
  )
  $therefore Set slash 2 iso Set times Set$
]
moreover if we have $1={star}$
$
  F(x) &=[x |-> star] \
  F(arr(f,X,1))&=f^(-1)(star)
$
similarly we have
#proof(name: "inverse")[
  #grid(
    columns: (1fr, 1fr),
    align: (center + horizon, center + horizon),
    $
      (F^(-1) comp F)(f)
      &= F^(-1)(f^(-1)(star)) \
      &= f
    $,
    $
      (F comp F^(-1))([x |-> star])
      &= F(x) \
      &= [x |-> star]
    $,
  )
  $therefore Set slash 1 iso Set$
]

#exercise("11")[Show that the free monoid functor...]
#proof(name: "from effect")[
  the functor $M$ holds @defn-functor as follows

  #figure(
    table(
      columns: 2,
      align: (right, left),
      [structure], [definition],
      [domains], $M(f) = [x_0... |-> f(x_0)...]$,
      [identity], $M(1_A) = M(id_Set) = id_Mon = 1_M(A)$,
      [composition], $M(g comp f) = M(g) comp M(f)$,
    ),
  )
  $
    M(g comp f)
    &= [x_0... |-> g(f(x_0))...] \
    &= [y_0... |-> g(y_0)...] comp [x_0... |-> f(x_0)...] \
    &= M(g) comp M(f)
  $
]


#proof(name: "from UMP")[
  Let $"UMP" : (X -> |M(X)|) -> (X -> |M(Y)|) -> (M(X) -> M(Y))$, then
  $
    M(arr(f,X,Y)) = "UMP"(i_X,i_Y comp f) = overline(f)
  $
  #grid(
    columns: (1fr, 1fr),
    align: (center + horizon, center + horizon),
    figure(
      diagram(
        cell-size: 10mm,
        $
          #node($M(X)$, name: <MX>)
  edge("r",overline(f),"-->")
  edge("rr", "-->", overline(g comp f), bend: #(30deg))
  edge("d",stroke: sstroke,=>) &
#node($M(Y)$, name: <MY>)
  edge("r",overline(g),"-->")
  edge("d",stroke: sstroke,=>) &
#node($M(Z)$, name: <MZ>)
  edge("d",stroke: sstroke,=>) \
#node(
align(bottom + right,text(silver)[$Mon$]),
corner-radius: 5pt,
stroke: silver,
enclose: (<MX>, <MY>, <MZ>),
)
#node($|M(X)|$, name: <MBX>)
  edge("r",|overline(f)|,->) &
#node($|M(Y)|$, name: <MBY>)
  edge("r",|overline(g)|,->) &
#node($|M(Z)|$, name: <MBZ>) \
#node($X$, name: <X>)
  edge("u",i_X,"hook->")
  edge("r",f,->)
  edge("ru",
  stroke: sstroke,
  marks: ->
  ) &
#node($Y$, name: <Y>)
  edge("u",i_Y,"hook->")
  edge("r",g,->)
  edge("ru",
  stroke: sstroke,
  marks: ->
  ) &
#node($Z$, name: <Z>)
  edge("u",i_Z,"hook->")
#node(
align(bottom + right,text(silver)[$Set$]),
corner-radius: 5pt,
stroke: silver,
enclose: (<MBX>, <MBY>, <MBZ>, <X>, <Y>, <Z>),
)
        $,
      ),
    ),
    $
      M(g comp f)
      &= "UMP"(i_X,i_Z comp g comp f) \
      &= overline(g comp f) \
      "(by uniqueness)"&= overline(g) comp overline(f) \
      &= M(g) comp M(f)
    $,
  )]

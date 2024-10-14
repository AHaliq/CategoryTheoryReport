#import "../../preamble/lemmas.typ": *
#import "../../preamble/catt.typ": *
#import "@preview/fletcher:0.5.1" as fletcher: diagram, node, edge

#exercise("1")[In any category $bold(C)$, show that ... is a coproduct diagram just if for...]

For products we have the following as given
$
  "UMP"(c_1^(-1) comp f^(-1), c_2^(-1) comp f^(-1)) &= f^(-1) \
  Hom(op(bold(C)),s:Z,t:C) &iso Hom(op(bold(C)),s:C,t:A) times Hom(op(bold(C)),s:C,t:B) \
  f^(-1) &iso (c_1^(-1) comp f^(-1), c_2^(-1) comp f^(-1))
$
taking its dual we derive
$
  f &iso (f comp c_1, f comp c_2) \
  Hom(bold(C),s:C,t:Z) &iso Hom(bold(C),s:A,t:C) times Hom(bold(C),s:B,t:C)
$

#exercise("2")[Show in detail that the free monoid functor $M$ preserves coproducts for any sets $A,B$ ...]

#figure(
  diagram(
    cell-size: 10mm,
    $
      & M(X)
  edge("dl", M(a), <-)
  edge("dr", M(b), <-) \
M(A)
  edge("d", 1_(M(A)), <-) &
M(A + B)
  edge("l", M(q_a), <-)
  edge("r", M(q_b), <-)
  edge("u", M(u), "-->")
  edge("dl", M(q_a), <-)
  edge("dr", M(q_b), <-)
  edge("d", u', "<--")
  &
M(B)
  #edge("d", $1_(M(B))$, "->", label-anchor: "west", label-sep: 0em) \
M(A) &
M(A) + M(B)
  edge("l", <-)
  edge("r", <-) &
M(B)
    $,
  ),
)
$
  "UMP"(a,b) &= u \
  "UMP"(M(a), M(b)) &= M(u) \
  "UMP"(M(a), M(b)) &= M(u) comp u' \
$
by uniqueness property of UMP
$
  M(u) &= u' comp M(u) \
  1_(M(A+B)) &= u' \
  M(A+B) &= M(A) + M(B)
$

#exercise("3")[Verify that the construction given in the text of the coproduct of monoids $A+B$ as a quotient of the free monoid $M(|A|+|B|)$ really is a coproduct in the category of monoids.]

#figure(
  diagram(
    cell-size: 10mm,
    $
      C
  #edge("r", $c_1$, "->", shift: 3pt)
  #edge("r", $c_2$, "->", shift: -3pt, label-anchor: "north", label-sep: 0em) &
M(|A|+|B|)
  #edge("rr", $q$, ">->", bend: 30deg)
  #edge("drr", $[f,g]'$, "->", bend: -30deg) &
A
  edge("r", i_A, ->)
  edge("dr", f, ->) &
M(|A|+|B|) slash ~
  edge("d", [f,g], "-->") &
B
  edge("l", i_B, ->)
  edge("dl", g, ->) \
& & & M
    $,
  ),
)
1. $arr([f,g],M(|A|+|B|) slash ~, M)$ is defined as follows
$
  [f,g]([a] dot "rest") &= f(a) dot_M [f,g]("rest") \
  [f,g]([b] dot "rest") &= g(b) dot_M [f,g]("rest")
$
2. $q$ is defined as a quotient of $M(|A|+|B|)$ such that
$
  [f,g]' comp c_1 = [f,g]' comp c_2 => [f,g] comp q = [f,g]'
$
3. thus a coequalizer by $"UMP"(c_1,c_2,q) = [f,g]$
4. thus $[f,g]$ is unique by $q$ being a coequalizer
5. thus the coproduct $A+B$ holds for $"UMP"(f,g)=[f,g]$
6. therefore, we have $M(|A|+|B|) slash ~ = A + B$


#exercise("4")[Show that the product of two powerset boolean algebras $cal(P)(A)$ and $cal(P)(B)$ is also a powerset, ...]

#figure(
  diagram(
    cell-size: 10mm,
    $
      & X
      edge("dl", a, ->)
      edge("dr", b, ->)
      edge("d", u, "-->") \
      cal(P)(A)
      edge("r", pi_1, <-) &
      cal(P)(A + B) &
      cal(P)(B)
      edge("l", pi_2, <-)
    $,
  ),
)

$
  pi_1 &= [S |-> S sect A}] \
  pi_2 &= [S |-> S sect B] \
  a &= [x |-> u(x) sect A}] \
  &= [S |-> S sect A] comp [x |-> u(x)]\
  &= pi_1 comp u \
  b &= pi_2 comp u \
  "UMP"(a,b) &= u
$

#exercise("6")[Verify that the category of monoids has all equalizers and finite products.]

#figure(
  diagram(
    cell-size: 10mm,
    $
    A_2 &
      A_0
  edge("l", i', "hook->")
  edge("r", i, "hook->") &
A_1
  #edge("r", $f$, "->", shift: 3pt)
  #edge("r", $g$, "->", shift: -3pt, label-anchor: "north", label-sep: 0em) &
B \
& Z
  edge("u", h, "-->")
  edge("ur", z, ->)
  edge("ul", z', ->)
    $,
  ),
)

1. let $A_0 = {a | a in A_1 and f(a) = g(a)}$ making $A_0 subset.eq A_1$ and $i$ its inclusion
2. moreover $forall x. h(x)= z(x)$ making $h$ uniquely determined from $z$
3. thus equalizer UMP $f comp z = g comp z => i comp h = z$ holds
4. let $A_0 subset.eq A_2$ with $i'$ its inclusion
5. thus $forall x. h(x)=z'(x)$ as well satisfying the UMP for product
6. therefore $A_0 = A_1 times A_2 subset.eq A_1 sect A_2$

#exercise("10")[In the proof of proposition 3.24 in the text it is shown that any monoid $M$ has a specific presentation $T^2 M arrows.rr T M -> M$ as a coequalizer of free monoids. Show that coequalizers of this particular form are preserved by the forgetful functor $Mon -> Set$]

#figure(
  diagram(
    cell-size: 10mm,
    $
    |T^2 M|
      #edge("r", $|epsilon|$, "->", shift: 3pt)
      #edge("r", $|mu|$, "->", shift: -3pt, label-anchor: "north", label-sep: 0em) &
    |T M|
      #edge("r", $|pi|$, "->") 
      edge("dr", z, ->) & 
    |M| 
      edge("d", u, "-->") \
    & & Z
  $
  )
)
1. recall $|q| = [a |-> q(a)]$ from $q$ with arguments as single alphabets
2. since $pi (x_1, ..., x_n) = x_1 dot ... dot x_n$, then $|pi|(x) = x$, thus $|pi| = 1_(|T M|)$ and $u=z$
5. therefore $z comp |epsilon| = z comp |mu| => u comp |pi|$, making preserving the coequalizer

#exercise("11")[Prove that $Set$ has all coequalizers by constructing the coequalizer of a parallel pair of functions $A arrows.rr^f_g B -> Q = B slash (f=g)$ by quotienting $B$ by a suitable equivalence relation $R$ on $B$, generated by the pairs $(f(x),g(x))$ for all $x in A$. Define $R$ to be the intersection of all equivalence relations on $B$ containing all such pairs.]
#figure(
  diagram(
    cell-size: 10mm,
    $
    A
      #edge("r", $f$, "->", shift: 3pt)
      #edge("r", $g$, "->", shift: -3pt, label-anchor: "north", label-sep: 0em) &
    B
      #edge("r", $q$, "->") 
      edge("dr", mu, ->) & 
    Q
      edge("d", mu, "-->") \
    & & B times B
  $
  )
)
1. we know $R(b_1,b_2) = R(f(x),g(x))$
2. let $q(b) = {b | R(b,b)}$ and $mu(b) = (b,b)$
2. thus $mu comp f = mu comp g => mu comp q = mu$
$
  (mu comp f)(x) = (mu comp g)(x) &=> (mu comp q)(b) = mu(b)\
  mu(f(x)) = mu(g(x)) &=> { mu(b) | R(b,b) } = mu(b)\
  (f(x),f(x)) = (g(x),g(x)) &=> { mu(b) | R(b,b) } = mu(b)\
  R(f(x),g(x)) &=> { mu(b) | R(b,b) } = mu(b)\
  R(b,b) &=> { mu(b) | R(b,b) } = mu(b)\
  R(b,b) &=> mu(b) = mu(b)\
  R(b,b) &=> top \
$
4. therefore the UMP holds for coequalizer

#exercise("12")[Verify the coproduct-coequalizer construction mentioned in the text for coproduct of rooted posets, that is, posets with a least element 0 and monotone maps preserving 0. Specifically, show that the coproduct $P +_0 Q$ of two such posets can be constructed as a coequalizer in posets, $1 arrows.rr^(0_p)_(0_Q) P+Q -> P +_0 Q$. You may assume as given the fact that the category of posets has all coequalizers.]
#figure(
  diagram(
    cell-size: 10mm,
    $
    1
      #edge("r", $0_P$, "->", shift: 3pt)
      #edge("r", $0_Q$, "->", shift: -3pt, label-anchor: "north", label-sep: 0em) &
    P+Q
      #edge("r", $q$, "->") 
      edge("dr", f, ->) & 
    P +_0 Q
      edge("d", f, "-->") \
    & & R
  $
  )
)
1. $0_P, 0_Q$ is the representation of the least element in $P, Q$ respectively
2. $q$ quotients the least elements of $P, Q$ i.e. $0_P = 0_Q$
3. thus $f comp 0_P = f comp 0_Q => f comp q$ making $q$ the coequalizer

#exercise("13")[Show that the category of monoids has all coequalizers as follows
#exercise("1")[Given any pair of monoid homomorphisms $f,g:M->N$, show that the following equivalence relation on $N$ agree:
#exercise("a")[$n ~ n' <=>$ for all monoids $X$ and homomorphisms $h:N->X$, one has $h f = h g$ implies $h n= h n'$]
1. let $m$ be such that $f(m) = n, g(m) = n'$
2. thus
$
  n &~ n' \
  f(m) &~ g(m) \
  (h comp f)(m) &~ (h comp g)(m) \
  h(n) &~ h(n')
$
#exercise("b")[the intersection of all equivalence relations $~$ on $N$ satisfying $f m ~ g m$ for all $m in M$ as well as $n ~ n' and m ~ m' => n dot m ~ n' dot m'$]
1. ??
]
#exercise("2")[Taking $~$ to be the equivalence relation defined in (1), show that the quotient set $N slash ~$ is a monoid under $[n] dot [m] = [n dot m]$, and the projection $N -> N slash ~$ is the coequalizer of $f$ and $g$.]
?? whats $[n]$ again?
]



#exercise("14")[Consider the following category of sets:

#exercise("a")[Given a function $arr(f,A,B)$ describe the equalizer of the function $f comp p_1, f comp p_2 : A times A -> B$ as a binary relation on $A$ and show that it is an equivalence relation called the kernel of $f$]
?? what is a kernel?

#exercise("b")[Show that the kernel of the quotient $A -> A slash R$ by an equivalence relation $R$ is $R$ itself]

?? i need to learn more algebra about kernels

#exercise("c")[Given any binary relation $R subset.eq A times A$, let $[R]$ be the equivalence relation on $A$ generated by $R$. Show that the quotient $A -> A slash [R]$ is the coequalizer of the two projections]

#exercise("d")[Using the foregoing, show that for any binary relation $R$ on a set $A$ one can characterize the equivalence relation $[R]$ generated by $R$ as the kernel of the coequalizer of the two projections of $R$.]
]

*notes* in commutative diagram below eqn 3.8 in 3.24, it should be $T^2 M$ and not just $T^2$ right?
#import "../../preamble/lemmas.typ": *
#import "../../preamble/catt.typ": *
#import "@preview/fletcher:0.5.1" as fletcher: diagram, node, edge

#definition(name: "Monomorphisms and Epimorphisms")[
  @sa[definition 2.1]

  _monomorphisms_ have unique pre-composites from the same object.
  $
    "isMono"(mono(f,A,B)) = f comp g = f comp h => g = h
  $
  _epimorphisms_ have unique post-composites to the same object
  $
    "isEpi"(epi(f,A,B)) = g comp f = h comp f => g = h
  $
]<defn-epimono>

#definition(name: "split mono and epi")[
  @sa[definition 2.7]

  #grid(
    columns: (1fr, 1fr),
    align: (left, left),
    [Let $epi(e,X,A)$, then if
      $
        e comp s = 1_A
      $
      - $s$ is a *section* / *splitting* of $e$, and is monic
      - $e$ is a *retraction* of $s$, and is epic
      - $A$ is a *retract* of $X$
    ],
    [
      Let $mono(m,A,X)$, then if
      $
        s comp m = 1_A
      $
      - $s$ is a *section* / *splitting* of $m$, and is epic
      - $m$ is a *retraction* of $s$, and is monic
      - $A$ is a *retract* of $X$
    ],
  )
  - if $f$ is a right inverse of $g$ / $g$ is a left inverse of $f$, then $g comp f = 1$, then $f$ is a split mono of epic $g$
  - if isomorphic then $f,g$ are both split epi and mono of each other
]<defn-splitepimono>

#theorem(name: "Interpretation of split epis (optional)")[
  @sa[example 2.8]
  - an object $P$ is _projective_ if for any $e,f$ there is an $overline(f)$ as follows. $"Proj"(e,f)= overline(f)$
  $
    "isProjective"(
      P
    ) = forall epi(e,E,X), arr(f,P,X). exists arr(overline(f),P,E). e comp overline(f) = f
  $
  #figure(
    diagram(
      cell-size: 10mm,
      $
        & E
        edge("d", e, "->>") \
        P
        edge("ur", overline(f), "->")
        edge("r", f, "->") &
        X
      $,
    ),
  )
  - intuitively $e$ has _lifts_ of $f$; permitting _"more"_ arrows; a _"free"_ structure
  - split epis $epi(e,E,X)$ are categorical choice functions by using fibers $e^(-1)(x)$
  - axiom of choice implies all sets are projective
]

#definition(name: "Initial and Terminal Objects and Duality")[
  @sa[definition 2.9, 2.10]
  a category is initial / terminal if it has initial / terminal objects $0$ / $1$

  $
    "UMP"_"terminal" (0) = forall X. exists! 0. 0_X in Hom("",s:0,t:X) \
    "UMP"_"initial" (1) = forall X. exists! 1. 1_X in Hom("",s:X,t:1)
  $

  - $op(0) = 1$, initial and terminal objects are duals
  - $op(mono(f,A,B)) = epi(f',B,A)$, monomorphisms and epimorphisms are duals
]

#theorem(name: "Generalized elements from initial and terminal objects")[
  @sa[section 2.3]

  In $Set$
  - $1 = { star }$, thus morphisms $arr(overline(x),1,X)$ represent $x in X$; meaning $X iso Hom(Set,s:1,t:X)$
  - $overline(x)$ are _generalized elements_ / _global elements_ / _points_ / _constants_ of $X$
  - if $overline(x)$ is an epimorphism, then $X$ has a unique inhabitant since $f comp overline(x) = g comp overline(x) => f = g$
  - instead of $1$ we can also use $T$ to _"probe"_ the internal structure of $X$
]

#definition(name: "Products")[
  @sa[definition 2.15] $P$ is a product of $A$ and $B$ under $p_1,p_2$ if there exists a unique $u$; $P,A,B,p_1,p_2$ is called a diagram of the limit. $"UMP"(x_1,x_2) = u$
  $
    "UMP"_"product" (x_1,x_2,u,p_1,p_2) = forall x_1, x_2. exists! u. x_1 = p_1 comp u and x_2 = p_2 comp u
  $
  #figure(
    diagram(
      cell-size: 10mm,
      $
        & #node($X$, name: <X>)
  edge("dl", x_1, ->)
  edge("d", u, "-->")
  edge("dr", x_2, ->) \
#node($A$, name: <A>) &
#node($P$, name: <P>)
  edge("l", p_1, ->)
  edge("r", p_2, ->) &
#node($B$, name: <B>)
      $,
    ),
  )
  note that there can be more than one product of $A,B$ i.e. $p_1',p_2'$ can be distinct from $p_1,p_2$
]

#definition(name: "Categories with Products for every pair of objects")[
  @sa[section 2.6]

  Let $times$ be a functor
  $
    times &: C times C -> C \
    times(A,A') &= A times A' \
    times(arr(f,A,B),arr(f',A',B')) &= arr(f times f',A times A',B times B')
  $
  - this implies $A times(B times C) iso (A times B) times C$, by UMP uniqueness they are isomorphic; associative
  - terminal objects behave as nullary products; an identity for products
  - single objects behave as unary products

  #figure(
    grid(
      columns: (1fr, 1fr),
      align: (center + horizon, center + horizon),
      diagram(
        cell-size: 10mm,
        $
          X edge("d", !, "-->") \ 1
        $,
      ),
      diagram(
        cell-size: 10mm,
        $
          & X
          edge("d", overline(p), "-->")
          edge("dr",overline(p), "-->")
          edge("dl",overline(p), "-->") \
          P
          edge("r", id, <-) &
          P
          edge("r", id, ->) &
          P
        $,
      ),
    ),
  )
  - thus a category $C$ has all finite products if it has $times$ and $1$
  - a category $C$ has all small products if every set of objects has a product object
]

#definition(name: "Products as Hom-sets")[
  @sa[section 2.7]

  $Hom(C,s:X,t:-) : C -> Set$ is called the covariant representable functor of $X$, where notationally:
  $
    Hom(C,s:X,t:g) = g_* = [f |-> g comp f]
  $
  iff for every object $X$, the canonical function is an isomorphism
  $
    theta.alt_X : Hom(,s:X,t:P) iso Hom(,s:X,t:A) times Hom(,s:X,t:B)
  $
  such that
  $
    theta.alt_X (u)&= (p_(1*)(u), p_(2*)(u)) \
    theta.alt_X (u) &= (x_1, x_2)
  $
  then the $C$ has all finite products

  moreover a functor $F$ preserves products iff $F(A times B) iso F(A) times F(B)$

  thus, the covariant representable functor of $X$ preserves products
]
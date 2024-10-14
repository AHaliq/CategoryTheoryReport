#import "../../preamble/lemmas.typ": *
#import "../../preamble/catt.typ": *
#import "@preview/fletcher:0.5.1" as fletcher: diagram, node, edge

#exercise("1 from wk2")[Show that every poset considered as a category has equalizers and coequalizers of all pairs of morphisms]
A poset as a category, has objects as elements of the poset and morphisms as witness of the ordering relation. Thus for any two morphisms $f,g: A -> B$ in the poset

#grid(
  columns: (1fr, 1fr),
  align: (left, left),
  [
    #figure(
      diagram(
        cell-size: 10mm,
        $
          E
  edge("r", e, >->) &
A
  #edge("r", $f$, "->", shift: 3pt)
  #edge("r", $g$, "->", shift: -3pt, label-anchor: "north", label-sep: 0em) &
B \
Z
  edge("u", u, "-->")
  edge("ur", z, ->)
        $,
      ),
    )

    $e$ is an equzlier when $E = A and B$ greatest lower bound since for any other $Z$ it will then unqiuely be $Z <= E$ such that $arr(u,Z,E)$
  ],
  [
    #figure(
      diagram(
        cell-size: 10mm,
        $
          A
  #edge("r", $f$, "->", shift: 3pt)
  #edge("r", $g$, "->", shift: -3pt, label-anchor: "north", label-sep: 0em) &
B
  edge("r", q, ->>)
  edge("dr", z, ->) &
Q
  edge("d", u, "-->") \
& & Z
        $,
      ),
    )

    $q$ is a coequalizer when $Q = A or B$ least upper bound since for any other $Z$ it will then unqiuely be $Z >= Q$ such that $arr(u,Q,Z)$
  ],
)
Moreover from the definition of the morphisms in the category we know that if there are parallel morphisms they have to be equal.

#exercise("2 from wk2")[Let the functor $arr(cal(F), bb(C), bb(D))$ be an isomorphism of categories. Show the following.]

#proof(name: [if $bb(C)$ has equalizers so does $bb(D)$ and $cal(F)$ preserves them.])[

  an equalizer has the following UMP
  $
    "UMP"(f,g,z) = u
  $
  thus, we know $F(u)$ is unique by the composition preserving property of functors
  $
    "UMP"(F(f), F(g), F(z)) &= F(u)
  $
]

#proof(name: [if $bb(C)$ has coequalizers so does $bb(D)$ and $cal(F)$ preserves them.])[
  by duality of the above argument, so does coequalizers.
]

#exercise("3 from wk2")[Let $bb(C)$ be a category and $X$ and object of $bb(C)$. Show the following. If $bb(C)$ has equalizers so does $slice(bb(C),X)$]

#figure(
  diagram(
    cell-size: 10mm,
    $
      & X
  edge("dl", x_Z, ->)
  edge("d", x_A, ->)
  edge("dr", x_B, ->) \
E
  edge("r", e, >->) &
A
  #edge("r", $f$, "->", shift: 3pt)
  #edge("r", $g$, "->", shift: -3pt, label-anchor: "north", label-sep: 0em) &
B \
Z
  edge("u", u, "-->")
  edge("ur", z, ->)
    $,
  ),
)
$
  "UMP"(f,g,z) &= u
$
since the morphisms of the slice categories are also the morphisms in the underlying category, the equalizer in the slice category is the same as the equalizer in the underlying category. This is only true if $X$ has a morphism to all objects of the equalizer.

*Note*: we will move mandatory assignment for week 3 to week 4 since most of them are on pullbacks which is the next chapter.
#import "../../preamble/lemmas.typ": *
#import "../../preamble/catt.typ": *
#import "@preview/fletcher:0.5.1" as fletcher: diagram, node, edge

#definition(name: "Duality")[@sa[Proposition 3.1, 3.2]

  / Formal Duality: if $Sigma$ follows from the axioms of categories, then so does its dual $Sigma^*$
  $
    ("CT" => Sigma) => ("CT" => Sigma^*)
  $
  specifically, if for a category $bold(C)$ that $Sigma$ holds, then in its dual $op(bold(C))$ the interpretation $Sigma^*$ holds.
  $
    (bold(C) => Sigma) => (op(bold(C)) => Sigma^*)
  $
  / Conceptual Duality: moreover if $Sigma$ holds for all categories $bold(C)$, then it also holds in all $op(bold(C))$. Thus
  $
    forall bold(C). (bold(C) => Sigma) => (op(bold(C)) => Sigma)
  $
  with both we can conclude that
  $
    => (op((op(bold(C)))) => Sigma^*) => (bold(C) => Sigma^*)
  $
]<defn-duality>

#definition(name: "Coproducts")[@sa[Definition 3.3]

  $
    "UMP"_"coproduct" (x_1,x_2,u,q_1,q_2) = forall x_1, x_2. exists! u. x_1 = u comp q_1 and x_2 = u comp q_2
  $
  #figure(
    diagram(
      cell-size: 10mm,
      $
        & #node($X$, name: <X>)
  edge("dl", x_1, <-)
  edge("d", u, "<--")
  edge("dr", x_2, <-) \
#node($A$, name: <A>) &
#node($P$, name: <P>)
  edge("l", q_1, <-)
  edge("r", q_2, <-) &
#node($B$, name: <B>)
      $,
    ),
  )

  notice the UMP is dual to products; flipped arrows and composition

  Examples of Coproducts:

  #figure(
    table(
      columns: 4,
      align: (right, left, left, left),
      [category], [equation], [description], [example of],
      $Set$, $A + B = A times 1 union B times 2$, [disjoint union of sets], [from definition],
      [*Monoids*], $M(A+B) iso M(A) + M(B)$, [monoid of $A+B$], [preserves coproducts],
      [*Top/Powerset*],
      $cal(P)(X + Y) iso cal(P)(X) times cal(P)(Y)$,
      [$2^(X+Y) iso 2^X times 2^Y$],
      [dual in underlying],

      [*Posets*], $p + q = p or q$, [least upper bound], [from definition],
      [*Proofs*], $phi + psi = phi or psi$, [disjunction], [from definition],
      [*Free Monoids*], $A + B iso M(|A| + |B|) slash ~$, [quotient unit & mul], [underlying quotient],
      [*Abelian Groups*], $A + B iso A times B$, [commutative], [self dual],
    ),
  )
]<defn-coproducts>


#grid(
  columns: (1fr, 1fr),
  align: (left + horizon, left + horizon),
  definition(name: "Equalizers")[@sa[Definition 3.13, 3.16] $"UMP"(f,g,z) = u$, notice $e$ is monic by uniqueness of $u$
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
    equalizers as subsets as two outgoing morphisms $f,g$ are equalized to one $e$
  ],
  definition(name: "Coequalizers")[@sa[Definition 3.18, 3.19] $"UMP"(f,g,z)=u$, notice $q$ is epic by unqiueness of $u$

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

    coequalizers as quotients as two incoming morphisms $f,g$ are coequalized to one $q$
  ],
)
$
  "UMP"_"equalizer" (e,f,g) = forall z. exists! u. f comp z = g comp z => e comp u = z \
  "UMP"_"coequalizer" (q,f,g) = forall z. exists! u. z comp f = z comp g => u comp q = z
$
#figure(
  table(
    columns: 3,
    align: (right, left, left),
    [UMP], [existence], [uniqueness],
    [equalizer], $forall f, g. exists e. f comp e = g comp e$, $forall z. exists! u. e comp u = z$,
    [coequalizer], $forall f, g. exists q. q comp f = q comp g$, $forall z. exists! u. u comp q = z$,
  ),
)<defn-co-equalizer>

#definition(name: "Presentation of Algebras")[@sa[Definition 3.24]
  - Given a finite set, let it be the *generators* of the *free algebra*
    - $F(3) = F(x,y,z)$ where $x,y,z$ are generators.
  - the relations it must hold are defined by coequalizers
    - $x y = z$ is quotiented by $q$ if $"UMP"(x y, z, q) = id_q$
    - more generally the morphisms can be the relations themselves; $r_1 |-> x y = z, r_2 |-> y^2 = 1$
  - this is called a *presentation* of the algebra; they are not unique
]
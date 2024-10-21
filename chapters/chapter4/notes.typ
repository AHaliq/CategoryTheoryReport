#import "../../preamble/lemmas.typ": *
#import "../../preamble/catt.typ": *
#import "@preview/fletcher:0.5.1" as fletcher: diagram, node, edge

#definition(name: "Subobjects")[@sa[Definition 5.1, Remark 5.2, Example 5.3]
  - A subobject of an object $X$ is a monomorphism $mono(m, M, X)$ in $bold(C)$
  - $"Sub"_bold(C)(X)$ is a category of subobjects of $X$ with morphisms arrows in $slice(bold(C), X)$
    - the morphisms between any two objects in $"Sub"_bold(C)(X)$ are unique (by mono $m$)
    - thus $"Sub"_bold(C)(X)$ is a *preorder category*
    - thus if theres a morphism both ways, it is an isomorphism modelling $equiv$
  - if we quotient the isomorphic objects into equivalence classes, we get a *poset category*
    - in this interpretation $"Sub"_Set(X) iso P(X)$; powerset; objects are subsets
    - thus morphisms $mono(f, M, M')$ is also monic since composites of monos are also monos
    - thus we have a functor $"Sub"(M') -> "Sub"(X) = [f |-> m' comp f]$
    - _local set membership_ $m in_X M' <=> exists f. m = m' comp f$
  #figure(
    table(
      columns: 2,
      align: (center + horizon, center + horizon),
      [preorder], [poset],
      figure(
        diagram(
          cell-size: 10mm,
          $
            M
            edge("r", f, "-->")
            #edge("dr", $m$, ">->", label-anchor: "east", label-sep: 0em) &
          M'
            #edge("d", $m'$, ">->", label-anchor: "west", label-sep: 0em) \
          &X
          $,
        ),
      ),
      figure(
        diagram(
          cell-size: 10mm,
          $
            M'
            edge("r", m', >->) &
          X
            #edge("r", $g$, "->", shift: 3pt)
            #edge("r", $h$, "->", shift: -3pt, label-anchor: "north", label-sep: 0em) &
          Y \
          M
            edge("u", f, "-->")
            edge("ur", m, >->)
          $,
        ),
      ),
    ),
  )
  - since equalizers are monos they are subobjects too $m in_X M' <=> g(m) = g(h)$
    - we can then regard $M'$ as the subobject of generalized elements $m$ such that $g(m) = h(m)$
]<defn-subobject>

#definition(name: "Pullbacks")[@sa[Definition 5.4, Proposition 5.5, Corollary 5.6]
  #figure(
    grid(
      columns: (auto, 1fr),
      align: (left, left),
      figure(
        diagram(
          cell-size: 5mm,
          $
            Z
          edge("dddr", z_1, ->)
          #edge("dr", $u$, "-->")
          edge("drrr", z_2, ->) \
        & P
          edge("rr", pi_2, ->)
          edge("dd", pi_1, ->) &&
        B
          edge("dd", g, ->) \ \
        & A
          edge("rr", f, ->) &&
        C
          $,
        ),
      ),
      [
        - a pullback is a $"UMP"(f,g)=angle.l p_1,p_2 angle.r = u$
          - $P = A times_C B = {angle.l z_1,z_2 angle.r in A times B | f comp z_1 = g comp z_2}$
          - $P$ is a subobject of $Z$ that makes it commute in the square
          - or determined as an equalizer of $f comp pi_1$ and $g comp pi_2$
          - if $pi_1$ is monic, $g$ is monic too
        #figure(
          table(
            columns: 2,
            align: (right, left),
            [UMP], [definition],
            [existence], $forall f, g. exists! u. f comp pi_1 comp u = g comp pi_2 comp u$,
            [uniqueness], $pi_1 comp u = pi_1' comp u' = z_1$,
          ),
        )
      ],
    ),
  )
  - in $Set$ the square made by $arr(f, A, B)$ and $arr(overline(f), f^(-1)(V), V)$; its inverse images to images with inverses, form a pullback, generalizing inverses
  - horizontally composed squares $arrow.b arrows.rr arrow.b arrows.rr arrow.b$
    - if the two squares are pullbacks, so is the outer rectangle
    - if the right square and outer rectangle are pullbacks, so is the left square
  - the pullback of a commutative triangle is a commutative triangle; prism diagram
  - a pullback is a functor, fix $arr(g, B, C)$, the functor is $arr(g^*, slice(bold(C),C), slice(bold(C),C')) = [f |-> pi_2]$
  - for $arr(f,A,B)$ the $arr(f^(-1), "Sub"(B), "Sub"(A))$ and $arr(f^*, slice(bold(C), B), slice(bold(C),A))$ form a pullback too
]<defn-pullback>

#definition(name: "Diagram")[@sa[Definition 5.15]
  - a diagram is a functor $arr(D, bold(J), bold(C))$ where $bold(J)$ is an index category
  - a cone is an object $C$ and family of arrows $arr(c_j, C, D_j)$
    - any arrows $arr(alpha,i,j)$ makes the triangle $arr(D_alpha, D_i, D_j), c_i, c_j$ commute
  - a cone morphisms $arr(theta.alt, (C,c_j), (C',c_j'))$, maps the object and family of arrows to another
    - the triagle $theta.alt, c_j, c_j'$ also commutes
    - this forms a category $Cone(D)$
]<defn-diagram>

#definition(name: "Limits")[@sa[5.16-5.25]
  - a limit of a diagram $D$ is a terminal object in $Cone(D)$ with $"UMP"(C, c_j, D) = u$
    - the limit is notated as $arr(p_i, lim(j) D_j, D_i)$; the arrrows from the limit cone object to the diagram
    - a limit exists if for all cones, there exists a unique morphism to the limit cone
  #figure(
    grid(
      columns: (1fr, auto),
      align: (center + horizon, center + horizon),
      figure(
        table(
          columns: 2,
          align: (right, left),
          [UMP], [definition],
          [existence], $forall (C,c_j), D. exists! (arr(u, C, lim(j) D_j)). forall j. p_j comp u = c_j$,
          [uniqueness], [if there are two there will be an iso],
        ),
      ),
      figure(
        diagram(
          cell-size: 5mm,
          $
            & C
      edge("d", u, "-->")
      #edge("ddl", $c_i$, "->", bend: -30deg)
      #edge("ddr", $c_j$, "->", bend: 30deg) \
    & lim(j)D_j
      edge("dl", p_i, ->)
      edge("dr", p_j, ->) \
    D_i
      edge("rr", D_alpha, ->) & &
    D_j
          $,
        ),
      ),
    ),
  )
  #figure(
    table(
      columns: 3,
      align: (center + horizon, center + horizon, center + horizon),
      [diagram; $bold(J)$], [limit], [diagram],
      $circle.filled.small circle.filled.small$,
      [product],
      figure(
        diagram(
          cell-size: 10mm,
          $
            D_1 &
            lim(j) D_j
            edge("l", p_1, ->)
            edge("r", p_2, ->) &
            D_2
          $,
        ),
      ),

      $circle.filled.small arrows.rr circle.filled.small$,
      [equalizer],
      figure(
        diagram(
          cell-size: 10mm,
          $
            lim(j) D_j
      edge("r", c_1, ->)
      #edge("rr", $c_2$, "->", bend: -40deg, label-anchor: "south", label-sep: -0.5em) &
    D_1
      #edge("r", $D_alpha$, "->", shift: 3pt)
      #edge("r", $D_beta$, "->", shift: -3pt, label-anchor: "north", label-sep: 0em) &
    D_2
          $,
        ),
      ),

      $emptyset$, [terminal object], $lim(j) D_j$,
      $circle.filled.small -> circle.filled.small <- circle.filled.small$,
      [pullback],
      figure(
        diagram(
          cell-size: 10mm,
          $
            lim(j) D_j
            edge("r", pi_2, ->)
            edge("d", pi_1, ->) &
            D_2
            edge("d", g, ->) \
            D_1
            edge("r", f, ->) &
            C
          $,
        ),
      ),
    ),
  )
  #figure(
    caption: "lhs iff rhs",
    table(
      columns: 2,
      align: (right, left),
      [lhs], [rhs],
      [binary products, equalizers], [pullbacks],
      [finite products, equalizers], [pullbacks, terminal object],
      [finite products, equalizers], [finite limits],
      [finite products and equalizers of a cardinality], [finite limits of the cardinality],
    ),
  )
]<defn-limit>




#definition(name: "Contravariant Functors")[@sa[Definition 5.26]
  a functor of the form $arr(F, op(bold(C)), bold(D))$
]<defn-contravariant-functor>

#definition(name: "Functor preserving Limits")[@sa[Definition 5.24-5.25]
  - a functor $arr(F, bold(C), bold(D))$ preserves limits of type $bold(J)$ if $arr(p_j, L, D_j)$ is a limit, then the cone $arr(F p_j, F L, F D_j)$ is a limit for the diagram $arr(F D, bold(J), bold(D))$
  - a functor preserving limits is said to be *continuous*
  $
    F(lim("") D_j) iso lim("") F (D_j)
  $
  - representable functor $Hom(,s: C, t: -)$ preserves all limits
  - contravariant representable functors i.e. $Hom(,s: -, t: C)$, map colimits to limits
]<defn-functor-limit>

#definition(name: "Pushouts")[@sa[Definition 5.6] dual of a pullback; where the pushout quotients $forall a. f(a) ~ g(a)$
]<defn-pushout>

#definition(name: "Colimits")[@sa[Definition 5.6] dual of a limit
]<defn-colimits>

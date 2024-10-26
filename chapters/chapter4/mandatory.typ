#import "../../preamble/lemmas.typ": *
#import "../../preamble/catt.typ": *
#import "@preview/fletcher:0.5.1" as fletcher: diagram, node, edge

#exercise("1")[Suppose the square below is a pullback. Show the following

#exercise("1.1")[If $g$ is a split epimorphism then $k$ is]
#figure(diagram(cell-size: 5mm,
$
A
  edge("r", h, ->)
  #edge("d", $k$, "->", label-anchor: "west", label-sep: 0em)
  #corner("dr") &
B
  edge("d", g, "->>") \
C
  edge("r", f, "->")
  #edge("u", $s'$, ">->", bend: 30deg) &
D
  #edge("u", $s$, ">->", bend: -30deg)
$))
1. By definition of a pullback we know $A = C times_D B = {(c,b) | f(c) = g(b)}$
2. since $g$ is a split epi $exists s . g comp s = 1_D$ where $s' = [c |-> (c, (s comp f)(c)]$
$
k comp s' &= [c |-> k(c,(s comp f)(c))] \
&= [c |-> c] \
&= 1_C
$
3. thus $s'$ is a section of $k$
5. $k$ is also an epimorphism
$
m comp k = n comp k
<=> &m comp k comp s' = n comp k comp s' \
<=> &m comp 1_C = n comp 1_C \
<=> &m = n
$
6. therefore $k$ is a split epi

#exercise("1.2")[If $g$ is an isomorphism then $k$ is]

$
s' comp k
&= [(c,b) |-> (s' comp k)(c,b)] \
&= [(c,b) |-> s'(c)] \
&= [(c,b) |-> (c,s comp f(c))] \
&= [(c,b) |-> (c,s comp g(b))] && "by UMP of pullback" \
&= [(c,b) |-> (c,b)] && "by isomorphism of "g,s \
&= 1_A
$
therefore the section $s'$ is also a left inverse making $k$ an isomorphism

#exercise("1.3")[If $g$ is a split monomorphism then $k$ is not necessarily a split monomorphism]

1. a counter example is if $A = {(1,1), (1,2)}$
2. then $forall p. k(p) = 1$
3. therefore $cancel(exists) s'. s' comp k = 1_A$
]

#exercise("2")[Recall that the two-pullback lemma, or the pullback pasting lemma, show that if the left square and the outer rectangle are pullbacks then the right square can fail to be a pullback]
#figure(diagram(cell-size: 5mm,
$
{star}
  edge("r", [star |-> star], ->)
  edge("d", 1, ->)
  #corner("dr") &
{star, star'}
  edge("d", [x |-> star], "->") 
  edge("r", f, ->)
  #corner("dr") &
{star, star'}
  #edge("d", $[x |-> star]$, "->", label-anchor: "west", label-sep: 0em) \
{star}
  edge("r", 1, "->") &
{star}
  edge("r", 1, ->) &
{star}
$))

1. the left square is a pullback since $exists !u. 1 comp 1 comp u = [x |-> star] comp [star |-> star] comp u$
  - where $u=[x |-> star]$
2. the outer rectangle is a pullback since $exists !u. 1 comp 1 comp 1 comp u = [x |-> star] comp f comp [star |-> star] comp u$
  - where $u=[x |-> star]$
3. the right rectangle is not a pullback since $u$ is not unique in $1 comp [x |-> star] comp u = [x |-> star] comp f comp u$
  - where $u=[x |-> star]$ or $u=[x |-> star']$ both satisfies

#exercise("3")[A regular monomorphism is an arrow $mono(e,E,A)$ which is an equalizer of some pair of arrows $f,g: A -> B$. Recall that by Proposition 3.16 of SA $e$ is in particular a monomorphism. Show that in a pullback square below, if $e$ is a regular monomorphism then so is $e'$ for any object $C$ and any arrow $h$. This property is often called "regular monos are stable under pullback".]

#figure(grid(columns: (auto, 1fr), align: (center + horizon, horizon + left), gutter: 2em, 
figure(diagram(cell-size: 5mm,
$
E'
  #corner("dr")
  edge("r", h', ->)
  edge("d",  e', ->) &
E
  edge("d", e, ->) \
C
  edge("r", h, ->) &
A
$)),
[
  Given
  1. $C <-^e' E' ->^h' E$ are a pullback of $C ->^h A <-^e E$
  2. $arr(e,E,A)$ is a regular monomorphism
],
grid.cell(colspan: 2, align: left, [
  We prove that $e'$ is a regular monomorphism by showing
  - $e'$ is a monomorphism by (4)
  - $e'$ is an equalizer for any $C$ and $h$ by (5) and (6)
])))
#figure(grid(columns: (auto, 1fr), align: (center + horizon, horizon + left), gutter: 2em,
figure(diagram(cell-size: 5mm,
$
X
  #edge("rr", $f$, "->", bend: 30deg) 
  #edge("dr", $g$, "->", bend: -30deg)
  edge("r", u, "-->") &
E'
  #corner("dr")
  edge("r", h', ->)
  edge("d",  e', ->) &
E
  edge("d", e, >->) \
& C
  edge("r", h, ->) &
A
$)),
[
  3. Given by (1) and @defn-pullback, for any $X$
    1. $(h comp e' = e comp h') and $
    2. $forall X, (arr(f,X,E)), (arr(g,X,C)), exists! (arr(u,X,E')).$
    3. $#h(1em) (e' comp u = g) and$
    4. $#h(1em) (h' comp u = f)$
],
grid.cell(colspan: 2, align: left, [
  *Explanation*: Given the pullback, for any $X$ and morphisms $arr(f,X,E),arr(g,X,C)$, there exists a unique $u$ such that the square commutes even with $u$ precomposed and that the triangles $X,E',C$ and $X,E',E$ commutes as well.
])))
#figure(grid(columns: (auto, 1fr), align: (center + horizon, horizon + left), gutter: 1em,
figure(diagram(cell-size: 5mm,
$
X
  #edge("r", $u_1$, "->", shift: 3pt) 
  #edge("r", $u_2$, "->", shift: -3pt, label-anchor: "north", label-sep: 0em) &
E'
  #corner("dr")
  edge("r", h', ->)
  edge("d",  e', >->) &
E
  edge("d", e, >->) \
& C
  edge("r", h, ->) &
A
$)),
[
  Let $forall (u_1, u_2 : X -> E').$ be the scope of the following formulas
  4. By (3.1) where $h comp e' = e comp h'$ we know the following
  $#h(1em) ((e comp h') comp u_1 = (h comp e') comp u_1) and ((e comp h') comp u_2 = (h comp e') comp u_2)$
  5. Supposing $e' comp u_1 = e' comp u_2$ we derive from (4) that
  $#h(1em) e' comp u_1 = e' comp u_2 =>\
  #h(1em) e comp h' comp u_1 = h comp e' comp u_1 = h comp e' comp u_2 = e comp h' comp u_2$
  6. Given (2) where $e$ is a monomorphism we know
  $#h(1em) e comp h' comp u_1 = e comp h' comp u_2 => h' comp u_1 = h' comp u_2$
  7. The consequent of (5) satisfies the antecedent of (6), thus by transitivity we have
  $#h(1em) e' comp u_1 = e' comp u_2 => h' comp u_1 = h' comp u_2$
  8. Given (1) and (3), there must exist a unique $v:X -> E'$, since both $u_1, u_2$ satisfies $v$, they must be equal
  $#h(1em) h' comp u_1 = h' comp v and e' comp u_1 = e' comp v and \
  #h(1em) h' comp u_2 = h' comp v and e' comp u_2 = e' comp v =>
  u_1 = u_2$
  9. (7) satisfies the antecedent of (8), thus by transitivity we have that $e'$ is a monomorphism
  $#h(1em) e' comp u_1 = e' comp u_2 => u_1 = u_2$

],
grid.cell(colspan: 2, align: left, [
*Explanation*: The square commutes (4), additionally with $e' comp u_1 = e' comp u_2$ as the premise for $e'$ to be a monomorphism, we have that $e comp h' comp u_1 = e comp h' comp u_2$ in (5). This satisfies the premise for $e$ to be a monomorphism in (6). Thus we get the consequent $h' comp u_1 = h' comp u_2$ in (7). Moreover, since morphisms $X -> E'$ have to be unique by UMP of the pullback, they must be equal (8). Therefore $e'$ is a monomorphism (9).
])))
#figure(grid(columns: (auto, 1fr), align: (center + horizon, horizon + left), gutter: 1em,
figure(diagram(cell-size: 5mm,
$
X
  #edge("dr", $x_C$, "->")
  edge("r", u, "-->") &
E'
  #corner("dr")
  edge("r", h', ->)
  edge("d",  e', >->) &
E
  edge("d", e, >->) \
& C
  edge("r", h, ->) &
A
  #edge("d", $a$, "->", shift: 3pt, label-anchor: "west", label-sep: 0em) 
  #edge("d", $a'$, "->", shift: -3pt, label-anchor: "east", label-sep: 0em) \
& & B
$)),
[
  Let $forall (a,a': A -> B).$ be the scope of the following formulas
  10. By (2) where $e$ is an equalizer
  $#h(1em) a comp e = a' comp e$
  11. By (3.1); $h comp e' = e comp h'$, and (10), $e'$ equalizes $a comp h$ and $a' comp h$
  $#h(1em) (a comp e) comp h' = (a' comp e) comp h' = \
  #h(1em) (a comp h) comp e' = (a' comp h) comp e'$
  12. Given (1) and (3), there must exist a unique $arr(u,X,E')$ for any $X$ and $arr(x_C,X,C)$ such that $e' comp u = x_C$ in (3.3).
  $#h(1em) a comp h comp e' comp u = a comp h comp x_C  and\
  #h(1em) a' comp h comp e' comp u = a' comp h comp x_C$
  13. Since $e'$ is universal (12), equalizes on $h$ (11) and is a monomorphism (9), $e'$ must be a regular monomorphism.
],
grid.cell(colspan: 2, align: left, [
*Explanation*: It is given $e$ is an equalizer for $a,a'$ in (10) if we precompose it by $h'$ in (11) it will still hold. Since the square commutes the identity holds for $a,a'$ composed with $h comp e'$ as well. Moreover $e'$ is universal by the the uniqueness of $u$ induced by the pullback. Therefore $e'$ is an equalizer for $h comp a$ and $h comp a'$. Making it both a monomorphism and an equalizer and thus a regular monomorphism $square.filled$ 
]),
))

second attempt:
$
&"UMP"_"pullback" (e',h',h,e) and "UMP"_"equalizer" (e,a,a') and "isMono"(e) \
=& ((h e' = e h') and (forall f,g. exists! u. f = e' u and g = h' u)) and \
&(forall v_1. a v_1 = a' v_1 and exists! u_1. e u_1 = v_1) and \
&(forall v_2, v_3. e v_2 = e v_3 => v_2 = v_3) \ \
&"let " v_1 = h f, u_1 = h' u, v_2 = h' u_1, v_3 = h' u_2 \ \
=& (h e' = e h') and (forall f,g. exists! u. (f = e' u and g = h' u) and \
&(a (h f) = a' (h f) and e (h' u) = (h f)) and \
&(forall u_1, u_2. e h' u_1 = e h' u_2 => h' u_1 = h' u_2)) \


=& ... \
=& (forall f. h a f = h a' f and exists! u. e' u = f) and \
& (forall u_1, u_2. e' u_1 = e' u_2 => u_1 = u_2) and ... \
=& "UMP"_"equalizer" (e',h comp a, h comp a') and "isMono"(e') and ... \
$

#pagebreak()

#exercise("4")[Let $mono(e,A,B)$ be a regular monomorphism. Show that if the square is a pushout then $e$ is the equalizer of $x$ and $y$]


#figure(grid(columns: (auto, 1fr), align: (center + horizon, horizon + left), gutter: 1em, 
figure(diagram(cell-size: 5mm,
$
A
  edge("r", e, >->)
  edge("d", e, >->) &
B
  edge("d", y, >->) \
B
  edge("r", x, ->) &
Q
  #corner("ul")
$)),
[
  1. we have the following pushout with $e$ as a regular monomorphism
],
figure(diagram(cell-size: 5mm,
$
A
  edge("r", e, >->)
  edge("d", e, >->) &
B
  edge("d", y, >->)
  edge("dr", x_B, ->) \
B
  edge("r", x, ->)
  #edge("rr", $x_B$, "->", bend: -30deg) &
Q
  #corner("ul")
  edge("r", u, "-->") &
X
$)),
[
  2. let $arr(u,Q,X)$ be a pushout for any $X$
  3. thus $e comp x comp u = e comp y comp u$
  4. thus $e comp x = e comp y => x = y$, satisfies the existence equalizer UMP
],
figure(diagram(cell-size: 5mm,
$
Y
  edge("r", v, "-->")
  #edge("dr",  $y_B$, "->", label-anchor: "north", label-sep: 0em)
  #edge("rr", $y_B$, "->", bend: 30deg) &
A
  edge("r", e, >->)
  edge("d", e, >->) &
B
  edge("d", y, >->)
  edge("dr", x_B, ->) \
& B
  edge("r", x, ->)
  #edge("rr", $x_B$, "->", bend: -30deg) &
Q
  #corner("ul")
  edge("r", u, "-->") &
X
$)),
[
  5. for any $Y$, $arr(v,Y,A)$ must be unique by $e$ being a mono
  6. thus $v comp e = y_B$, satisfies the uniqueness equalizer UMP
  7. therefore by (4) and (6) $e$ is the equalizer of $x$ and $y$
],
))

#exercise("5")[Let $arr(F, bb(C), bb(D))$ be a finite limit preserving functor. Show that for any monomorphism $mono(m,A,B)$ the morphism $arr(F(m), F(A), F(B))$ is also a monomorphism, i.e. F preserves monomorphisms. Dualizing, show that if $arr(F,bb(C),bb(D))$ preserves finite colimits then it preserves epimorphisms.]

#exercise("6")[Give an example of each of a functor $Set -> Set$ that:

#exercise("6.1")[Both preserves and creates terminal objects;]

#exercise("6.2")[Preserves, but does not create, terminal objects]

#exercise("6.3")[Neither preserves nor creates terminal objects]

#exercise("6.4")[Finally show that any functor $Set -> Set$ which creates terminal objects also preserves them.]
]
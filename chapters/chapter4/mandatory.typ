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

#figure(diagram(cell-size: 5mm,
$
E'
  #corner("dr")
  edge("r", ->)
  edge("d",  e', ->) &
E
  edge("d", e, ->) \
C
  edge("r", h, ->) &
A
$))

1. Let $u = angle.l arr(f,X,E), arr(g,X,C) angle.r$ be the pullback
2. since $e$ is mono, $g$ is unique
3. since $u$ and $g$ are unique, $f$ is unique
4. since $f$ and $u$ are unique, $e'$ is unique
5. thus any precomposition of $e'$ from the same object is unique too
4. by pullback $g comp e = h comp e' comp u$, since $g,u$ are unique, for specific $e,e'$, then $h$ is unique

not sure

#exercise("4")[Let $mono(e,A,B)$ be a regular monomorphism. Show that if the square is a pushout then $e$ is the equalizer of $x$ and $y$]

by pushout $"UMP"(e,e) = u$

$
u comp x comp e &= u comp y comp e \
x comp e &= y comp e
$

by equalizer $"UMP"(x,y,z) = arr(u',Z,A)$

not sure

#exercise("5")[Let $arr(F, bb(C), bb(D))$ be a finite limit preserving functor. Show that for any monomorphism $mono(m,A,B)$ the morphism $arr(F(m), F(A), F(B))$ is also a monomorphism, i.e. F preserves monomorphisms. Dualizing, show that if $arr(F,bb(C),bb(D))$ preserves finite colimits then it preserves epimorphisms.]

#exercise("6")[Give an example of each of a functor $Set -> Set$ that:

#exercise("6.1")[Both preserves and creates terminal objects;]

#exercise("6.2")[Preserves, but does not create, terminal objects]

#exercise("6.3")[Neither preserves nor creates terminal objects]

#exercise("6.4")[Finally show that any functor $Set -> Set$ which creates terminal objects also preserves them.]
]
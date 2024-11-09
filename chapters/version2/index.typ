#import "../../preamble/lemmas.typ": *
#import "../../preamble/catt.typ": *
#import "../../preamble/dtt.typ": *
#import "@preview/fletcher:0.5.1" as fletcher: diagram, node, edge
#import "@preview/curryst:0.3.0": rule, proof-tree
#import "@preview/equate:0.2.1": equate

#show: equate.with(breakable: true, sub-numbering: true)

= Version2

This section onwards departs from the previous due to new understanding of proof writing in category theory, particularly with UMPs.

#exercise("3, chapter 4")[regular mono stable under pullback]
#figure(diagram(cell-size: 5mm,
$
X
  #edge("rr", "->", bend: 40deg) 
  #edge("dr", "->")
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
  #edge("r", $a'$, "->", shift: 3pt, label-anchor: "south", label-sep: 0em) 
  #edge("r", $a$, "->", shift: -3pt, label-anchor: "north", label-sep: 0em)
& B
$))
#set math.equation(numbering: "(1.1)")

Given $h',e'$ is a pullback of $h,e$
$
  "Pullback"_(h,e)(e',h') <=>
  & h e' = e h' and #<pb-diagram> \
  &forall f, g. h f = e g => #<pb-unique-cond> \
  &exists! u. h' u = g and e' u = f#<pb-unique-cons>
$

Given $e$ is a monomorphism
$
  "isMono"(e) <=>
  &forall g,h. e g = e h => #<e-mono-cond> \
  &g = h #<e-mono-cons>
$

We show $e'$ is a monomorphism
$
  "isMono"(e') <=>
  &forall u_1,u_2. e' u_1 = e' u_2 => #<ep-mono-cond> \
  &u_1 = u_2 #<ep-mono-cons>
$
#set math.equation(numbering: none)
By @pb-diagram and @ep-mono-cond as assumption, we have
$
  (e h') u_1 = h (e' u_1) = h (e' u_2) = e h' u_2
$
This satisfies @e-mono-cond by $g=h' u_1, h=h' u_2$ thus quotienting them as in @e-mono-cons
$
h' u_1 = h' u_2
$
We have by assumption @ep-mono-cond
$
e' u_1 = e' u_2
$
Both $u_1,u_2$ now satisfies @pb-unique-cons and by uniqueness we get @ep-mono-cons
$
u_1 = u_2
$
$therefore e'$ is a mono. $square$

#set math.equation(numbering: "(1.1)")
Given $e$ is an equalizer; we assume for some $a,a'$
$
  "Equalizer"_(a,a')(e) <=>
  &a e = a' e and #<e-diagram> \
  &forall z. a z = a' z => #<e-unique-cond> \
  &exists! u. e u = z #<e-unique-cons>
$
We show equalizers are stable under pullback; $e'$ is an equalizer on $a h$ and $a' h$.
$
  "Equalizer"_(a h, a' h)(e') <=>
  &a h e' = a' h e' and #<ep-diagram> \
  &forall z.  a h z = a' h z => #<ep-unique-cond> \
  &exists! u. e' u = z #<ep-unique-cons>
$
#set math.equation(numbering: none)

@ep-diagram derived by @pb-diagram and @e-diagram
$
  a (h e') = (a e) h' = a' (e h') = a' h e'
$

Supposing @ep-unique-cond for $z=f$
$
  forall f. a h f = a' h f
$
this satisfies @e-unique-cons giving us some unique $g$ by @e-unique-cons
$
  exists! g. e g = h f
$
this satisfies @pb-unique-cons giving us some unique $u_1$ by @pb-unique-cons
$
  exists! u_1. h' u_1 = g and e' u_1 = f
$
this satisfies 3.3 but stronger, thus not necessarily unique, assuming another morphism $u_2$ exists
$
  forall u_2. e' u_2 = f
$

both $u_1, u_2$ satisfies @ep-mono-cons thus quotienting them, specifically:
$
  e' u_1 = e' u_2 => u_1 = u_2
$
Thus the consequent of @ep-unique-cons holds
$
  exists! u. e' u = f
$

$therefore e'$ is an equalizer on $a h$ and $a' h$. $square.filled$

#figure(proof-tree(
  rule(
    $"isMono"(e')$,
    rule(
      $3.1_(u_1,u_2) => 3.2$,
      rule($3.1_(u_1,u_2)$),
      rule(
        $1.1$,
        $"Pullback"_(h,e)(e',h')$
      ),
      rule(
        $2.1_(h' u_1, h' u_2)$,
        $"isMono"(e)$
      ),
      rule(
        $1.3$,
        $"Pullback"_(h,e)(e',h')$
      )
    )
  )
))
#figure(proof-tree(
rule(
  $"Equalizer"_(a h,a' h)(e')$,
  rule(
    $5.1$,
    rule($1.1$,$"Pullback"_(h,e)(e',h')$),
    rule($2.1$,$"Equalizer"_(a,a')(e)$)
  ),
  rule(
    $5.2_f => 5.3_u$,
    rule(
      $1.2_(f,g) => 1.3_(u_1)$,
      rule(
        $4.2_(h f) => 4.3_g$,
        $"Equalizer"_(a,a')(e)$,
        rule(
          $5.2_f$
        )
      ),
      $"Pullback"_(h,e)(e',h')$,
    ),
    rule(
      $u_2$
    ),
    rule(
      $3.1_(u_1,u_2) => 3.2$,
      $"isMono"(e')$
    )
  )
)
))

#pagebreak()

#exercise("Assignment 4: 1")[Let $bb(C)$ be a cartesian closed category. Show the following properities
#exercise("a")[
Let $arr(f, A times B, C)$ and $arr(g, C, D)$ be morphisms. Recall that using exponential transposes and evaluation we can define the morphism $arr(g^B, C^B, D^B)$. Show $g^B comp tilde(f) = tilde(g comp f)$ as a morphism $A -> D^B$
]
#figure(diagram(cell-size: 10mm,
$
  D^B &
  D^B times B
    edge("r", epsilon, ->) &
  D \
  C^B
    #edge("u", $g^B$, "->", label-anchor: "east", label-sep: 0em) &
  C^B times B
    #edge("u", $g^B times 1_B$, "->", label-anchor: "east", label-sep: 0em)
    edge("r", epsilon, ->)
    edge("ru", dash(g^B), ->) &
  C
    edge("u", g, ->) \
  A
        #edge("u", $tilde(f)$, "->", label-anchor: "east", label-sep: 0em) &
  A times B
    #edge("u", $tilde(f) times 1_B$, "->", label-anchor: "east", label-sep: 0em)
    edge("ru", f, ->)
$))
#exercise("b")[Show that for any $arr(f,A times B, C)$ and any $arr(h, A', A)$ we have $tilde(f) comp h = tilde(f comp (h times id))$]
#figure(diagram(cell-size: 10mm,
$
  C^B &
  C^B times B
    edge("r", epsilon, ->) &
  C \
  A
    #edge("u", $tilde(f)$, "->", label-anchor: "east", label-sep: 0em) &
  A times B
    #edge("u", $tilde(f) times 1_B$, "->", label-anchor: "east", label-sep: 0em)
    edge("r", , "=") &
  A times B
    edge("u", f, ->) \
  A'
        #edge("u", $h$, "->", label-anchor: "east", label-sep: 0em) &
  A' times B
    #edge("u", $h times id$, "->", label-anchor: "east", label-sep: 0em)
    #edge("ru", $h times id$, "->", label-anchor: "west", label-sep: -0.5em)
$))
#align(center)[where $id = 1_B$]
]


#include "appendix.typ"
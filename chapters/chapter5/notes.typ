#import "../../preamble/lemmas.typ": *
#import "../../preamble/catt.typ": *
#import "@preview/fletcher:0.5.1" as fletcher: diagram, node, edge

#definition(name: "Exponentials")[@sa[Definition 6.1]
$
"isExponential"(C^B, epsilon) =&
  forall A, (arr(f,A times B, C)). exists! (arr(tilde(f),A,C^B)). epsilon comp (tilde(f) times 1_B) = dash(tilde(f))=f 
$
]

#definition(name: "Cartesian Closed Category (CCC)")[@sa[Definition 6.2]
$
"isCCC"(Ob(""), Hom("")) =&
  "isCategory"(Ob(""), Hom("")) \
  &and forall A,B. exists! A times B. "UMP"_"product" (arr(p_1,A times B, A), arr(p_2,A times B, B)) \
  &and forall B,C. "isExponential"(C^B, epsilon)
$
]

todo:
categorical logic
- Heyting Algebra $~$ Intuitionistic Propositional Calculus
- CCC $~$ $lambda$-calculus
- Kripke models of logic; variable sets
- theory: a set of basic types and terms and equations between them (generators; recall the section on coequalizer)
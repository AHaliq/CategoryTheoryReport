#import "../../preamble/lemmas.typ": *
#import "../../preamble/catt.typ": *
#import "@preview/fletcher:0.5.1" as fletcher: diagram, node, edge

#definition(name: "Category")[
@sa[definition 1.1]
A category is a collection of objects and morphisms between them satisfying some properties.
$
C = (Ob(C), Hom(C)) \
$
#grid(columns: (1fr, 1fr), align: (center, center),
$A, B, C, ... in Ob(C)$,
$vec(delim: #none, arr(f,A,B), arr(g,B,C), dots.v) in Hom(C)$
)
#figure(table(
  columns: 2,
  align: (right, left),
  [properties], [definition],
  [composition],
  $forall arr(f,A,B), arr(g,B,C). exists arr(g comp f, A, C)$,
  [identity],
  $exists! arr(1_A,A,A)$, 
  [associativity],
  $ h comp (g comp f) = (h comp g) comp f$,
  [unital],
  $f comp 1_A = f = 1_B comp f$,
))
]<defn-cat>

#definition(name: "Functor")[
@sa[definition 1.2]
A functor is a structure preserving map from one category to another.
$
arr(F,C,D)
$
#figure(table(
  columns: 2,
  align: (right, left),
  [structure], [definition],
  [domains], $arr(F(f),F(A),F(B))$,
  [identity], $F(1_A)=1_F(A)$,
  [composition], $F(g comp f) = F(g) comp F(f)$,
))
]<defn-functor>

#definition(name: "Isomorphism")[
@sa[definition 1.3]
An isomorphism is a morphism that has an inverse. The objects on them are isomorphic.
$
"isIso"(f) &= exists! g. g comp f = 1_A and f comp g = 1_B \
A iso B &= exists arr(f,A,B). "isIso"(f)
$
]<defn-isomorphism>

#definition(name: "Constructions on Categories")[
@sa[definition 1.6]
Here are categories that are constructed out of prior categories.
#figure(table(
  columns: 3,
  align: (right, center, center),
  [category], [objects], [morphisms],
  [product $A times B$], $Ob(C) times Ob(B)$, $Hom(C) times Hom(B)$,
  [dual $op(C)$], $Ob(C)$, $A,B |-> Hom(C,s:B,t:A)$,
  [arrow $C^(->)$], $Hom(C)$, $f,f' |-> {(g,g') | g' comp f = f' comp g}$,
  [slice $slice(C,A)$], ${X | Hom(C,s:X,t:A) != emptyset}$, $Hom(C)$,
  [co-slice $coslice(C,A)$], ${X | Hom(C,s:A,t:X) != emptyset}$, $Hom(C)$,
))
]<defn-constructions>

#definition(name: "Universal Mapping Property: Free Monoids and Categories")[
@sa[definition 1.7,1.9,1.10]
- Alphabet: $A={a_0,a_1,a_2,...}$
- Words: concatenations of $a_i$ form words. along with $-$; an empty word, forms a monoid
- Free Monoid: elements of $A$ freely generate the monoid $M(A)$
- Forgetful Functor: $arr(|-|,"Monoids","Sets")$, gives an underlying alphabet of a monoid
#grid(columns: (1fr, 1fr), align: (center + horizon, center + horizon),
figure(table(
  columns: 2,
  align: (right, left),
  [UMP], [definition],
  [existence], $forall i, f. exists! overline(f). |overline(f)| comp i = f$,
  [uniqueness], $|overline(f_a)| comp i &= f and \ |overline(f_b)| comp i &= f -> \ overline(f_a) &= overline(f_b)$,
)),
figure(diagram(cell-size: 10mm, $
#node($M(A)$, name: <MA>)
  edge("d", "=>", stroke: sstroke)
  edge("r", overline(f), "-->") &
#node($N$, name: <N>)
  edge("d", "=>", stroke: sstroke) \
#node($|M(A)|$, name: <MBA>)
  edge("r", |overline(f)|, ->) &
#node($|N|$, name: <BN>) \
#node($A$, name: <A>)
  edge("u", i, ->)
  edge("ur", f, ->)
#node(
align(bottom + right,text(silver)[$Mon$]),
corner-radius: 5pt,
stroke: silver,
enclose: (<MA>, <N>),
)
#node(
align(bottom + right,text(silver)[$Set$]),
corner-radius: 5pt,
stroke: silver,
enclose: (<MBA>, <BN>, <A>),
)
$))
)
- No Junk: all words are concatenations of $A$; implied by uniqueness
- No Noise: equality of words by equality of alphabets; implied by existence
- Free Category: if $A$ are the set of edges of a directed graph, the words are morphisms of a category excluding identity morphisms
]<defn-freemonoid>

#definition(name: "Category Size")[
@sa[definition 1.11,1.12]
A size of a category depends of its consituents are sets
#figure(table(
  columns: 2,
  align: (right, left),
  [size], [definition],
  [small], [$Ob(C), Hom(C)$ are sets],
  [locally small], [$Hom(C,s:A,t:B)$ are sets],
  [large], [otherwise]
))
]

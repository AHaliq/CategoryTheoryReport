#import "../../preamble/lemmas.typ": *
#import "../../preamble/catt.typ": *
#import "../../preamble/dtt.typ": *
#import "@preview/fletcher:0.5.1" as fletcher: diagram, node, edge
#import "@preview/curryst:0.3.0": rule, proof-tree

#pagebreak()

= Appendix

$
&"isCategory"(cal(C)) =&
  &forall A,B,C in Ob(cal(C)), f in Hom(cal(C),s:A,t:B), g in Hom(cal(C),s:B,t:C).g comp f in Hom(cal(C),s:A,t:C) \
  &&and& forall X in Ob(cal(C)). exists! 1_X in Hom("",s:X,t:X) \
  &&and& forall h,g,f. h comp (g comp f) = (h comp g) comp f \
  &&and& forall A,B in Ob(cal(C)), f in Hom(cal(C),s:A,t:B). f comp 1_A = f = 1_B comp f \

&"isFunctor"(arr(F,C,D)) =&
  &forall f in Hom(C,s:A,t:B). F(f) in Hom(D,s:F(A),t:F(B)) \
  &&and& forall 1_X in Hom(C,s:X,t:X). F(1_X) = 1_(F(X)) \
  &&and& forall g,f in Hom(C). F(g comp f) = F(g) comp F(f) \

&"isIso"(arr(f,A,B)) =&
  &exists! g. g comp f = 1_A and f comp g = 1_B \

& A iso B = &
  &exists (arr(f,A,B)). "isIso"(f) \

& C times D = &
  &(Ob(C) times Ob(D), [(C_1,D_1), (C_2,D_2) |-> Hom(C,s:C_1,t:C_2) times Hom(D,s:D_1,t:D_2)]) \

& op(C) = &
  &(Ob(C), [A,B |-> {arr(op(f),A,B) | f in Hom(C,s:B,t:A) }]) \

& C^(->) = &
  &(Hom(C), [f,f' |-> {(g,g') | g' comp f = f' comp g}]) \

& slice(C,A) = &
  &({f | f in Hom(C,s:X,t:A)}, [f,f' |-> Hom(C, s:dom(f), t:dom(f'))]) \

& coslice(C,A) = &
  &({f | f in Hom(C,s:A,t:X)}, [f,f' |-> Hom(C, s:cod(f), t:cod(f'))]) \

& "isMono"(f) =&
  &forall g,h. f comp g = f comp h => g = h \

& "isEpi"(f) =&
  &forall g,h. g comp f = h comp f => g = h \

& "isSplitMono"(m,s) =&
  &s comp m = 1_dom(m) \

& "isSplitEpi"(e,s) =&
  &e comp s = 1_cod(e) \

& "areIso"(f,g) =&
  &"isSplitEpi"(f,g) and "isSplitMono"(f,g) \

& "isProjective"(P) =&
  &forall epi(e,E,X), arr(f,P,X). exists arr(overline(f),P,E). e comp overline(f) = f \ \

& "UMP"_"freemonoid" (|overline(f)|) =&
  &forall i,f. exists! overline(f). |overline(f)| comp i = f \

&"UMP"_"terminal" (0_X) =&
  &forall X. exists! 0. 0_X in Hom("",s:0,t:X) \

&"UMP"_"initial" (1_X) =&
  &forall X. exists! 1. 1_X in Hom("",s:X,t:1) \

&"UMP"_"product" (p_1,p_2) =&
  &forall x_1, x_2. exists! u. x_1 = p_1 comp u and x_2 = p_2 comp u \

&"UMP"_"coproduct" (q_1,q_2) =&
  &forall x_1, x_2. exists! u. x_1 = u comp q_1 and x_2 = u comp q_2 \

&"UMP"_"equalizer" (e,f,g) =&
  &forall z. (f comp z = g comp z) and exists! u. e comp u = z \

&"UMP"_"coequalizer" (q,f,g) =&
  &forall z. (z comp f = z comp g) and exists! u. u comp q = z \

&"UMP"_"pullback" (p_1,p_2,f,g) =&
  & (f comp p_1 = g comp p_2) \
  &&and& forall z_1, z_2. exists! u. z_1 = p_1 comp u and z_2 = p_2 comp u \

&"UMP"_"limit" ({p_i}, D) =&
  &forall {c_j}. exists! u. forall j. p_j comp u = c_j \

&"isExponential"(C^B, epsilon) =&
  &forall A, (arr(f,A times B, C)). exists! (arr(tilde(f),A,C^B)). epsilon comp (tilde(f) times 1_B) = dash(tilde(f))=f \

&"isCCC"(Ob(""), Hom("")) =&
  &"isCategory"(Ob(""), Hom("")) \
  &&and& forall A,B. exists! A times B. "UMP"_"product" (arr(p_1,A times B, A), arr(p_2,A times B, B)) \
  &&and& forall B,C. "isExponential"(C^B, epsilon) \
$

TODO LIST:

list of functors: $|-|, (-)^A, op((-)), Hom("",s:A,t:-), Hom("",s:-,t:A)$

todo in chapter4 notes
- $(f)^A = tilde(f comp epsilon)$
- define Sub and Cone category

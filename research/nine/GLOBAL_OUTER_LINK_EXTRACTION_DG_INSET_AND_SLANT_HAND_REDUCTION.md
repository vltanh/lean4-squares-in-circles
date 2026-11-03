# D/G inset clearance and a single-line reduction of the lower-right region

November 2, 2026. The D/G clearance lemma and the implication from the
stated slanted halfplane are complete hand arguments. Establishing that
halfplane for the entire original caller is a separate finite-table task;
this file does not assume its completion. No Lean, Lake, or CI.

Put `Q=1105/256`, `rho=91/60`, `h_S` for the original coordinate halfwidth,
and `g_S=1/(4h_S)` for the halfwidth of the aligned square contained in the
same physical original. All original interiors remain disjoint.

## 1. A stronger original D/G vertical comparison

In the normalized `001/00` domain with `v=y_D-y_C>=7/30`, the completed
endpoint-order theorem proves `y_G>y_D`. The original localization and
left endpoint cap give

    x_G-h_G>101/432,      x_D>4/3,
    x_D+h_D<133/64,       x_G<91/60.

These are established in
`WEAK_OUTER_LARGE_GAP_SHORT_ENDPOINT_ORDER_HAND_TABLE.md` and the
explicit derivation in `WEAK_OUTER_NUMERIC_AFFINE_DG_CLEARANCE.md`.
Set `S=h_D+h_G` and `K=3187/1728`. Then

\[
 x_D-x_G<K-S,
 \qquad x_G-x_D<11/60.                              \tag{1}
\]

For every physical square,

\[
 h+g-1=h+\frac1{4h}-1=\frac{(2h-1)^2}{4h}\ge0.
\]

Consequently

\[
 g_D+g_G\ge2-S>K-S,
\]

where the strict reserve `2-K=269/1728` is positive. The reverse
horizontal gap in (1) is also strictly below the inset sum, since

\[
 11/60<1/\sqrt2\le g_D+g_G.
\]

Thus the open horizontal projections of the two contained aligned
squares overlap. Those insets are subsets of the unchanged physical
D,G, so their open interiors are disjoint. They must therefore separate
vertically. The already proved height order fixes the sign, yielding

\[
                 \boxed{y_G-y_D\ge g_D+g_G.}          \tag{2}
\]

This preserves both physical chiralities and every possible owned
separator. It does not posit actual separation of the two full physical
y-projections. At aligned D,G it gives clearance one. For larger widths,
the previously proved affine clearance can be stronger; both remain
available simultaneously.

For a closed angle box, a necessary interval row uses
`g_D^-=1/(4h_D^+)`, `g_G^-=1/(4h_G^+)`. The common lower clearance may
therefore be taken to be

\[
 L=\max\left\{g_D^-+g_G^-,\;
 \frac78(h_D^-+h_G^-)-\frac{41}{120}\right\}.           \tag{3}
\]

This can safely tighten the original D/G height difference, the C/G
height difference by adding the original 5/8 C/D gap, and the propagated
coordinate intervals. All these uses concern the same original centers.

## 2. One slanted halfplane suffices for the C-bottom conclusion

In the large-gap caller `v>=5/8`, the inherited horizontal localization
supplies

\[
                       29/60<x_C<4/5.                 \tag{4}
\]

The upper endpoint follows from `x_C<h_C+5/64` and
`(4/5-5/64)^2-1/2=2161/102400>0`.

Suppose a separate proof supplies

\[
                 y_C+\frac78x_C\le-\frac7{32}.        \tag{5}
\]

Write p=x_C and w=rho+y_C. The original center bound gives w>=0.
Equations (4)--(5) imply

\[
 y_C\le-\frac7{32}-\frac78\frac{29}{60}
       =-\frac{77}{120}<-\frac58,
\]

with strict reserve 1/60. They also give

\[
 0\le w\le\frac{623}{480}-\frac78p.
\]

The right side is positive throughout `[29/60,4/5]`. The function

\[
 f(p)=p^2+\left(\frac{623}{480}-\frac78p\right)^2
\]

is convex. Its maximum on the interval is therefore at an endpoint.
The endpoint values leave the exact positive reserves

\[
 1-f(29/60)=\frac{11}{14400},\qquad
 1-f(4/5)=\frac{23}{9216}.                            \tag{6}
\]

In the first evaluation the upper bound for w is 7/8; in the second it
is 287/480. Hence (5) implies the complete strict C-bottom conclusion

\[
              y_C<-5/8,\qquad x_C^2+(\rho+y_C)^2<1.   \tag{7}
\]

The exact constant in (5) is deliberately weaker than the value
`-1/4` of its left side at the aligned limiting triple
`C=(1/2,-11/16)`, `D=(3/2,-1/16)`, `G=(1,15/16)`.
That observation guided discovery; it is not a proof of (5).

## 3. Eliminating a further original from the lower-right region

Assume (7), and suppose another original H satisfies
`x_H>=0`, `y_H<=y_C`. Write

    C=(p,-q), H=(u,-w),
    p>=29/60, q>=5/8, u>=0, w>=q, u^2+w^2<=rho^2.

If u<=p, then

\[
 |H-C|^2\le p^2+(\rho-q)^2<1,
\]

contradicting the disjoint radius-1/2 open disks contained in C and H.
If u>=p, put `z=u-p>=0`, `t=w-q>=0`. Physical center separation gives
`z^2+t^2>=1` and hence `z+t>=1`. As both p,q are at least 29/60,

\[
\begin{aligned}
 |H|^2
 &=p^2+q^2+z^2+t^2+2pz+2qt\\
 &\ge(29/60)^2+(5/8)^2+1+2(29/60)\\
 &=(89/60)^2+(5/8)^2
   =\rho^2+93/320>\rho^2,
\end{aligned}
\]

another contradiction. This exhausts H's original placement and
orientation without introducing an H angle or separator variable.

## 4. Exact arithmetic and acceptance boundary

`computer_assisted/extraction_search_inset_slant_arithmetic.py` checks
all rational constants in (1)--(7) and the two-case elimination. It uses
only exact fractions.

The D/G comparison (2) is established unconditionally in its stated
caller. Sections 2--3 prove a complete implication from (5). The current
numerical evidence for (5) is not promoted to a theorem here: a separate
complete original C,D,G proof, with all orientation and physical-owner
branches retained, must establish it before applying this reduction.
Neither this file nor the local right-lower exclusion by itself closes
a whole marked mask or the remaining original-nine placement problem.

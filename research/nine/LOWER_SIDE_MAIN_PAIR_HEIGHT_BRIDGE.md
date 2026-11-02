# A lower side original narrows its main frame and raises its height

November 2, 2026. Complete physical reduction and a finite exact table.
No Lean, Lake or CI. This theorem is an input for the lower-side exclusion;
it does not claim that exclusion or the full `010/11` mask closed.

## 1. Original-square statement

Keep the complete original `010/11` domain, with original main squares
A,B,C,D, selected short triple L,P,R and the other two original squares.
The outer main links are actual; the middle main link and both short
links are weak horizontal center-cone comparisons. Reflect vertically
so P is above both inner mains. Suppose its whole floor is at most 1/10.
The independently completed quarter-height theorem gives

    yB,yC < -1/4.

Suppose an original outsider S belongs to either closed side strip and
lies below its assigned inner main M. Write h for the original M's
coordinate halfwidth. Then

    h < 31/50.                                           (T1)

Furthermore, if h >= 57/100, then

    yM > 3h - 211/100.                                   (T2)

The original signed lower-side profile may therefore be strengthened to

    yM > max(f(h), 3h-211/100)   when 57/100 <= h < 31/50,

with its previous f(h) unchanged on 1/2 <= h <= 57/100. Here

    f(h)=-(2/3)h + max(0,min((h-1/2)/6,(27/50-h)/3)) + 1/400.

All original main and outsider frames remain independent. The theorem
uses the original other inner main N, not an artificial copy or an
extra chain relation. The accepted lower-side pair theorem supplies
f(h) from the actual M/S physical pair.

## 2. M must be the higher inner main once h >= 57/100

Let K be N's coordinate halfwidth and set

    g=1/(4h), G=1/(4K), eta=h+g-1, theta=K+G-1,
    V=eta+theta < 1/30.

The original endpoint theorem gives h,K < 13/20. The accepted f implies

    yM > -(2/3)(13/20)+1/400 = -517/1200.

The original main-center bands and weak middle bit give

    0 < xC-xB < d := min(61/30-h-K, h+K).

For h >= 57/100 and K >= 1/2, this is at most 289/300. If M were
not higher than N, the quarter-height theorem would give

    0 <= yN-yM < 217/1200.

But the two original contained half-unit disks require their centers to
be at distance at least one, whereas

    1 - (289/300)^2 - (217/1200)^2 = 2263/57600 > 0.

This is impossible. Consequently yM > yN. Equal heights are included
in the excluded alternative. The height order has been proved before
using any upward original separator.

## 3. Retain the other main's full endpoint-height budget

The original outer cone of N, the corresponding endpoint center band,
and the endpoint height reserve give the strict lower bound

    yN > m(h,K) := G + eta - 199/120 + (32/9)(eta+theta).   (1)

For example, if N is C, use yC >= yD-(xD-xC),
yD >= -1/8+(32/9)V, xD < 91/60 and
xC > G+eta-1/60. The left case is its horizontal reflection.
The eta contribution of the other original main has not been dropped.

Every genuine owned axis separating the original M,N pair has support
sum at least

    sigma=1+|h-K|.

Let

    k=sqrt(1/2-h^2), a=h+k, b=h-k,
    kN=sqrt(1/2-K^2), A=K+kN, B=K-kN.

Since the true horizontal gap is below d<1 and M is higher than N,
a separating normal with nonpositive vertical component cannot reach
support sigma. Maximizing the horizontal projection over the true gap
and retaining all four possible owned axes therefore gives

    yM-yN >= F(h,K),
    F=min((sigma-a*d)/max(b,1/40),
          (sigma-b*d)/a,
          (sigma-A*d)/max(B,1/40),
          (sigma-B*d)/A).                            (2)

All numerators are positive: d<=289/300 and sigma>=1. Clipping a
positive denominator upward weakens the candidate lower bound. When
b or B is zero its horizontal axis is impossible; adding the clipped
finite candidate to the minimum only weakens the result. Thus no
aligned boundary is omitted.

The same support sum and the original center distance also give

    yM-yN >= sqrt(max(0,sigma^2-d^2)).

Put J(h,K) equal to the maximum of this radical and F. Equations
(1)--(2) prove

    yM > m(h,K)+J(h,K).                              (3)

The use of d relaxes the original physical pair; it does not create
an actual horizontal separation between B,C.

## 4. Complete two-variable finite table

The table proves the following scalar consequences, including the
closed faces of both rectangles:

| h interval | K interval | Budget-or-height conclusion | Leaves |
|---|---|---|---:|
| [57/100,31/50] | [1/2,13/20] | V>1/30 or m+J>3h-211/100 | 1,584 |
| [31/50,13/20] | [1/2,13/20] | V>1/30 or m+J>-1/4 | 155 |

The complete certificate `lower_side_height_bridge.json` consists of
binary rational midpoint covers of these two specified roots. There
are 1,739 strict leaves and 3,476 nodes, with maximum depth 13 and no
frontier. Every leaf proves a strictly negative upper bound on either
`1/30-V` or `target-m-J`, using the target printed in the table.
All shared subdivision boundaries are retained in both children.

The independent `verify_lower_side_height_bridge.py` imports no producer.
It reconstructs both rational roots, all exact bisections, the complete
physical formulas above and each strict leaf. Its interval endpoints
are exact Fractions; radicals use independently checked integer-square
root enclosures at 90 binary places. The frame components and eta are
bounded by their endpoint monotonicity. Every leaf passed a complete
replay, recorded in `lower_side_height_bridge_independent_replay.json`.
The replay also reconstructs the positive rational reserve of Section 2.

The first row and (3) prove (T2). The second row contradicts the
independently established strict bound yM<-1/4, proving (T1). No
numerical optimizer output enters either conclusion.

## 5. Dependency and scope

The dependency order is: outer-actual endpoint bounds and the physical
lower-side pair envelope; the independently proved quarter-height
result; the original height-order argument of Section 2; the present
finite two-main table. No lower-side exclusion is assumed in proving
this bridge. An original S remains a necessary premise for f(h).

The other main's full frame interval up to 13/20 is retained in the
scalar table. This theorem narrows the assigned main only; it does not
assert that the other main's halfwidth is also below 31/50. The original
lower-side-extra target and complete fixed mask remain separate tasks.

# A central selected left square and an upper left-side extra

November 2, 2026. Complete hand reductions, including a three-row
rational center-distance table. The low-side/lower-central caller uses
the separately verified theorem identified in Section 4. No Lean or CI.

## 1. The original selected central L is high

Use the original low-P-floor 010/11 configuration, upward routing, and
xP>=0. Suppose the selected L is central and an unselected original S
is in the left side strip above B. Put

    ell=29/60, u=13/12, beta=124/375, rho=91/60.

The original selected cone comparisons give

    beta < Z=-xL < ell,      0<=xP<1129/3000.

Central routing makes L above both mains. The completed ordering theorem
applies to this actual L, giving yL>yP. The central corollary in
`LOW_OPPOSITE_ORIGINAL_LIES_BELOW_SELECTED_MIDDLE.md` then gives
yL>3/5. Unlike the distinct-extra floor theorem, this ordering argument
is valid when its central original is the selected L itself.

The original right shoulder R is high and has positive x. All original
identities and physical pairs are retained.

## 2. A high S forces L's whole floor above 1/10

Suppose yS>=3/5, and contrary to the claim yL-hL<=1/10. Since
hL<=1/sqrt(2)<71/100, we have 3/5<yL<81/100. Put X=-xS; then
ell<=X<u and the universal center bound gives yS<sqrt(rho^2-X^2).

The following table bounds both center heights by Y and their horizontal
gap by Xmax-beta. Every bound is a rational inequality.

| X interval | Y | Y^2+Xmin^2-rho^2 | 1-(Xmax-beta)^2-(Y-3/5)^2 |
|---|---:|---:|---:|
| [29/60,4/5] | 36/25 | 13/1875 | 10424/140625 |
| [4/5,19/20] | 129/100 | 43/11250 | 157867/1125000 |
| [19/20,13/12] | 119/100 | 1649/90000 | 96067/1125000 |

The third column proves yS<Y. In every row Y>81/100, so L too has
center height in [3/5,Y]. Also X>=ell>Z, hence |xS-xL|=X-Z is
strictly less than Xmax-beta. The positive last column proves
|cS-cL|^2<1. Their original contained open half-unit disks would overlap,
contradicting physical nonoverlap. Therefore L has good whole floor.

The five distinct originals A,S,L,R,D now satisfy the widened cap:
S and R are opposite high shoulders and L is a good central original.
It gives Dmain<=2, contradicting Dmain>=2+V>2. Thus the entire high-S
branch is impossible, irrespective of the location of the other extra.

## 3. A low S lies below P by the original L/P cone

Suppose instead yS<3/5. Since S>B, the original wide-main clearance
and yB>-6/5 give yS>-9/20. The endpoint-inset disk localization proves

    ell<=X=-xS<121/200.

Since L is central with Z>beta,

    |xS-xL|=X-Z <121/200-beta=823/3000<7/25.

We have yL>3/5>yS. The original L/S center disks therefore imply
yL-yS>24/25, using (7/25)^2+(24/25)^2=1. If yS>=yP, this would give
yL-yP>24/25. But the original selected L/P cone gives

    yL-yP <= xP+Z <1129/3000+29/60=2579/3000<24/25.

This is a contradiction. Thus the original low side extra satisfies

    yB<yS<yP,               yS<3/5.                (1)

No new S/P cone has been inferred. The actual L/P cone and the actual
L/S physical pair suffice for the height order.

## 4. Consequence when the other extra is lower central

If the remaining original extra is lower central,
`LOW_OPPOSITE_SIDE_BELOW_P_WITH_LOWER_CENTRAL_HAND_TABLE.md` excludes exactly the original order
(1), with the full bound yS<3/5. Hence its accepted 40,779-leaf table
and Sections 1-3 close the full mixed case with central selected L,
one upper left-side extra and one lower central extra.

This caller uses that finite theorem only after its complete independent
replay and physical audit have passed. The three-row exclusion and the
low-side ordering of Sections 2-3 are unconditional hand consequences of
their stated original hypotheses. They do not rely on an unproved
general no-lower-side theorem.

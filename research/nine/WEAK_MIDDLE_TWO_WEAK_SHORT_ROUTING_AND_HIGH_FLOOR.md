# Uniform 010/11 routing and complete exclusion of its high selected floor

November 2, 2026. Complete physical hand caller, using the preserved
independently replayed 6,302-leaf position theorem and the accepted
widened cap. The low-floor complement remains open here. No Lean,
Lake, or CI.

The accepted baseline sources below are pinned at
ddadfdd3bd2ef39a2e698680f9a2f3b7d73876ab. Write A,B,C,D for the
original main four-chain, L,P,R for the original selected short chain,
and F,G for the two other originals. All nine independent frames,
36 corner bounds and 36 original physical pairs remain present.

The main outer links are actual, the middle main link is weak, and all
five designated center comparisons are horizontal cone comparisons.
Both selected short links are weak. Only the physical cone part of the
short-chain hypotheses is needed for the deductions below.

Put

    Q=1105/256, l=29/60, u=13/12,
    alpha=707/1000,
    m=u-alpha=1129/3000,
    beta=2alpha-u=124/375.

## 1. Endpoint reserves and all original inner widths

For either inner main set g=1/(4h), eta=h+g-1. The accepted outer-link
reserve theorem gives, with V=eta_B+eta_C,

    0<=V<1/30,  1/2<=h_B,h_C<13/20,
    h_B-61/60<x_B<1/60-g_B-eta_C,
    g_C+eta_B-1/60<x_C<61/60-h_C,
    |y_C-y_B|<31/30,
    Dmain=x_D-x_A-h_A-h_D>=2+V.

Both endpoint frames have h_E<8/15, their center coordinates lie in
the inherited bands +/-[89/60,91/60], and |y_E|<=1/8. Every original
outsider has |x|<u. The endpoint inset margins satisfy

    g_E-|y_E|>221/600.

Because the middle main link is weak, V>0: otherwise both h_B,h_C
equal 1/2, and two aligned units with dx<1 and |dy|<=dx<1 have
overlapping interiors. In particular

    Dmain>2.                                         (1)

Every displayed input is valid at closed Q. No actual middle edge or
31/60 inner-width bound is assumed.

## 2. Complete horizontal bounds for the selected cone triple

Every original physical unit contains its centered half-unit disk.
For a cone pair, dx>=|dy| and center distance at least one imply
dx>=1/sqrt(2)>alpha. The latter strict rational comparison has reserve

    1/2-alpha^2=151/1000000>0.

Applying both selected comparisons and the outsider strip yields

    -u<x_L<-beta<0<beta<x_R<u,
    -m<x_P<m<l.                                     (2)

Thus the selected middle P is central even though neither selected
short link is actual. The shoulders are not assumed to lie in the
outer side bands; that would require a separate argument.

## 3. The original P is above both mains after reflection

The 12-row physical lemma in
`WEAK_MIDDLE_ROUTING_AND_HIGH_FLOOR.md`, Section 1, states

    1/2<=h_M<=13/20,
    |x_S-x_M|<=7/5-h_M
       ==> |y_S-y_M|>3/4.                         (3)

It is independent of the actual/weak bits of the selected short chain.
We check its full caller rather than importing that source's 010/01
routing bounds.

For P and B, the two directed horizontal gaps are bounded by

    x_P-x_B < m+61/60-h_B =1393/1000-h_B <7/5-h_B,
    x_B-x_P < m+1/60-g_B-eta_C <7/5-h_B.

The last comparison is very loose: h_B-g_B<69/260<3/10,
and m+1/60+3/10<7/5. The C calculation is its horizontal
reflection. Thus P has vertical gap greater than 3/4 from each main.
It cannot lie between them because 31/30<3/2. Reflect vertically so

    y_P>max(y_B,y_C).                              (4)

For L and B, the two horizontal directions obey

    x_B-x_L <11/10-g_B-eta_C <7/5-h_B,
    x_L-x_B <61/60-beta-h_B <7/5-h_B.

Here the first comparison again uses h_B-g_B<69/260<3/10.
Thus (3) applies to L and its own main B; similarly it applies to R
and C. If L were below B, (3)-(4) would give y_P-y_L>3/2, whereas
the retained cone edge and (2) give

    y_P-y_L<=x_P-x_L<u+m=4379/3000<3/2.

This is impossible. The right argument is reflected. Consequently

    y_L>y_B, y_R>y_C,
    y_L-y_B>3/4, y_R-y_C>3/4.                    (5)

The independent outer-cone calculation in Section 2 of
`WEAK_MIDDLE_CENTRAL_ROUTING_AND_LOWER_COUNT.md` proves y_B,y_C>-6/5.
It uses only the original endpoint reserve and the actual outer links,
not that source's later low-floor main-height theorem. For example

    y_B>g_B-199/120+(32/9)eta_B,
    g_B+(32/9)eta_B>=4sqrt(82)/9-32/9>11/24.

Hence (5) gives the useful uniform bounds

    y_L,y_R>-9/20.                                 (6)

No assertion that L is above the opposite main, or R above its opposite
main, is needed for this routing or the high-floor caller.

## 4. At least one shoulder is high

Call a selected shoulder high when its center height is at least 3/5.
By (6), any shoulder that is not high has |y|<3/5. Reflecting the
horizontal coordinate, its own original endpoint inset has

    x_E-g_E<503/480, g_E-|y_E|>221/600.

The shoulder's half-unit disk avoids that inset. Its vertical distance
from the inset is less than e=139/600. Its horizontal distance is
therefore greater than sqrt(1/4-e^2). It follows that every low selected
shoulder S satisfies

    |x_S|<503/480-sqrt(1/4-(139/600)^2)<121/200.     (7)

The final comparison is exact:

    503/480-121/200=1063/2400>0,
    1/4-(139/600)^2-(1063/2400)^2=179/1152000>0.

If both selected shoulders were low, their total horizontal span would
be less than 121/100. But the two original cone comparisons require a
span at least sqrt(2)>2alpha=707/500>121/100. Thus at least one of L,R
is high, including every boundary height at 3/5 in the high case.

## 5. The high selected whole-floor branch is impossible

Suppose y_P-h_P>=1/10. If both shoulders are high, the five distinct
original units A,L,P,R,D satisfy the direct statement of
`WIDENED_JOINT_FIVE_SQUARE_CAP.md`. Equations (2) supply the needed
signs and central band; Section 1 supplies all endpoint hypotheses.
The cap gives Dmain<=2, contrary to (1).

Otherwise exactly one shoulder is low. Reflect horizontally and reverse
the original labels so L is high and R is low. Equations (7) and the
two original cone gaps give

    x_L<x_R-2alpha<121/200-707/500=-809/1000<-l,
    x_P<x_R-alpha<121/200-707/1000=-51/500<-1/10.

Thus L is now proved to be in the left outer side band, and y_L>=3/5.
P is central by (2), has the assumed good whole floor, and follows L
in the original cone comparison. The original left endpoint contains
the fixed rectangle used by the completed 6,302-leaf position theorem.
The physical transfer is proved in
`ENDPOINT_RECTANGLE_POSITION_LEMMA_TRANSFER_AUDIT.md`: the position
table uses this endpoint rectangle, the original L/P frames and pair,
and their cone comparison, and no inner-main width or middle actual
edge. Its unchanged exact conclusion is x_P>-1/10, a contradiction.

Therefore the complete high-floor branch of 010/11 is excluded even at
closed Q. Every surviving original configuration must satisfy

    y_P-h_P<1/10,                                  (8)

after the vertical reflection in (4). The complementary low-floor branch
is not excluded by this manuscript. In particular, the two unselected
original squares F,G remain essential available resources in the full
problem; no premise restricting their positions has been introduced.

## 6. Numerical discovery does not replace the remaining proof

The exact original-seven control in
`selected_seven_exact_control.json` fits q=213/50<Q and has precisely
the selected 010/11 comparisons. Its independent Fraction checker
reconstructs all 28 corners, all 21 original pairs, and all five marked
edges. Its selected P has bad floor, as required by (8).

This demonstrates that the selected-seven subsystem cannot close the
remaining low-floor problem by itself. It is not a counterexample to the
nine-square assertion: the other two original units are absent. The
full 010/11 low-floor complement requires the extra originals. That
complement is closed separately by `A2_010_11_WHOLE_DOMAIN_ASSEMBLY.md`,
which retains them and proves every remaining domain.

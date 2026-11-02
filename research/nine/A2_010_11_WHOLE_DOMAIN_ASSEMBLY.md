# Original-nine assembly for the fixed 010/11 mask

November 2, 2026. **Complete strict-radius closure of the entire original-nine
010/11 mask.** Every finite input has a complete independent exact replay;
the physical/code reviews, saved-source bindings, and independent
original-nine assembly review have passed. The exact evidence is recorded
in `A2_010_11_VERIFIED_CLOSURE_2026_11_02.md` and its immutable manifest.
No Lean, Lake or CI. No closed-Q exclusion is claimed.

## 1. Exact domain and one permissible normalization

Assume the full original-nine 010/11 predicate in a disk with squared
radius q<Q=1105/256. Retain the actual unit squares A,B,C,D,L,P,R,F,G,
their nine independent frames, all 36 original corner conditions, all
36 original physical pair conditions, and all five designated horizontal
center-cone comparisons. The outer main links A/B and C/D are actual
horizontal projection separations. The middle main link B/C and both
selected short links L/P and P/R are strictly weak projection gaps.

Apply `SMALL_CENTER_EXPANSION_PRESERVES_FIXED_MASKS.md` once, before
classifying outsiders: multiply every original center by a sufficiently
small common factor greater than one, leaving each original frame
unchanged. The finite strict corner margin keeps all corners inside Q;
all three strict weak bits remain weak; actual links and all cone
comparisons remain valid. Every true pair separator becomes strict, so
the expanded closed original squares are pairwise disjoint. We prove
the contradiction for these expanded original squares. No later
argument needs to preserve a classification from before the expansion.

Write hS for an original square's coordinate halfwidth and, for the
inner mains, gS=1/(4hS), etaS=hS+gS-1 and V=etaB+etaC. The endpoint
reserve theorem `OUTER_ACTUAL_LINK_ENDPOINT_RESERVE_HAND_PROOF.md`,
Sections 4-5, for actual outer links gives

    1/2<=hB,hC<13/20, 0<=V<1/30,
    Dmain=xD-xA-hA-hD>=2+V,
    |xS|<u=13/12 for every original outsider S.

The genuine weak B/C bit forces V>0: at V=0 both inner mains are
aligned unit squares and their weak horizontal gap and original cone
comparison would give overlap. Consequently Dmain>2.

The complete routing argument in
`WEAK_MIDDLE_TWO_WEAK_SHORT_ROUTING_AND_HIGH_FLOOR.md` permits a vertical
reflection so P is above both inner mains and L>B, R>C. A horizontal
reflection with reversal of both selected chains permits xP>=0 and
preserves the exact mask 010/11. Put ell=29/60 and beta=124/375. Then

    0<=xP<1129/3000<ell,
    -u<xL<-beta<0, 707/1000<xR<u,
    yR>=3/5.

The last assertion follows because a routed shoulder below 3/5 has
absolute abscissa less than 121/200, inconsistent with xR>707/1000.
No cone involving F, G, or any replacement cap witness is introduced.

## 2. Selected-floor split and lower-central count

The same complete routing manuscript excludes the entire branch
yP-hP>=1/10. When both selected shoulders are high it applies the
widened five-square cap. When one is low it uses the complete
6,302-leaf original endpoint/shoulder position theorem, with its transfer
to the actual-outer domain audited in
`ENDPOINT_RECTANGLE_POSITION_LEMMA_TRANSFER_AUDIT.md`.

Thus any surviving configuration has yP-hP<1/10. The complete
9,688,640-leaf theorem
`WEAK_MIDDLE_TWO_WEAK_SHORT_MAINHEIGHT_QUARTER.md` then proves

    yB,yC<-1/4.

`WEAK_MIDDLE_UNCONDITIONAL_CENTRAL_ROUTING.md` applies to every original
outsider whose center satisfies |x|<=ell: it is above both mains or
below both. Its original own-half clearance exceeds 909/1000. Therefore
every lower central original has whole ceiling below -9/20. The
reflected two-square central-strip cap proves that at most one central
outsider is lower. This count uses the actual originals and includes
all zero-coordinate and strip-boundary faces.

The completed ordering theorem
`WEAK_MIDDLE_UPPER_EXTRA_ORDER_BY_FOUR_RADICALS.md` says that every
upper central original distinct from P lies above P in this low-floor
domain. It applies also to a selected central L. For an unselected
upper central original U, distinct from L,P,R and the mains,
`WEAK_MIDDLE_DISTINCT_UPPER_EXTRA_GOOD_FLOOR.md` then proves

    yU-hU>1/10, hence yU>3/5.

The distinctness requirement is essential: the latter finite theorem
is never used with U=L or U=R.

## 3. Classify the two extra originals only after side exclusion

`WEAK_MIDDLE_NO_LOWER_SIDE_EXTRA_HAND_TABLE.md`, with all 128 roots and
27,552,502 leaves independently replayed, excludes every original outsider
in a closed side strip below
its assigned inner main. The existing uniform physical clearance also
excludes equality with that main. The complete own-half upper-side
theorem `WEAK_MIDDLE_OWN_HALF_ABOVE_SIDE_EXTRA.md` excludes an extra
original in the right side strip above C: the high original R forces
that extra below 9/16, and the accepted low-side floor theorem would
make P's floor exceed 1/10.

It follows that each of the two actual extras F,G belongs to exactly
one of these disjoint classes:

| Class | Original location and order |
|---|---|
| C | -ell<x<ell; above both inner mains or below both |
| S | -u<x<=-ell; above B |

A center on either closed side boundary is classified as a side center;
the central input theorems allow closed central boundaries and therefore
apply to this open central subdomain. The original outsider bound
exhausts all horizontal locations. Hence the unordered extra patterns
are exactly C/C, S/C, and S/S.

Two further complete local results are used below. The below-P and
at-or-above-P low-side/lower-central theorems together exclude an
original left-side S with B<S and yS<=3/5 whenever a distinct original
lower central V exists. S may be the selected L or an extra. Their
height-order split is exhaustive, including yS=yP in the latter
case; it adds no S/P cone. Also, the independent hand proof
`WEAK_MIDDLE_CENTRAL_SELECTED_LEFT_WITH_SIDE_EXTRA.md` closes the whole
case with selected central L, an upper left-side extra and a lower
central extra, using only the below-P finite theorem.

## 4. Two central extras: C/C

At most one extra is lower, so an upper central extra U exists and has
good whole floor by Section 2. If yL>=3/5, the five distinct originals
A,L,U,R,D satisfy the widened cap, giving Dmain<=2, a contradiction.

Suppose yL<3/5. If L were central, its existing L>B order and central
routing would make it upper. The ordering theorem would give L>P.
But the central opposite-half corollary in
`LOW_OPPOSITE_ORIGINAL_LIES_BELOW_SELECTED_MIDDLE.md` forces every such
central original of height at most 3/5 below P. Thus L is a true left-side
original, still above B and low.

If one extra is lower central, the complete low-side/lower-central
exclusion applies with S=L and gives a contradiction. If both extras
are upper, they both have good whole floors. The accepted upper-column
separation theorem forbids two good original central units with
horizontal gap at most ell. Therefore the two extra centers have
strict opposite signs: a zero or a common closed half-plane would give
gap at most ell. Name the negative one Uminus and the positive one Uplus.
The five distinct originals A,Uminus,Uplus,R,D satisfy the widened cap:
Uminus and R are high opposite shoulders, Uplus is good and central.
Again Dmain<=2 contradicts Dmain>2. This exhausts C/C.

## 5. One side and one central extra: S/C

Call the side extra S and the central extra U. If U is upper, it has
good whole floor. The complete hand resource
`WEAK_MIDDLE_OPPOSITE_SIDE_SUPPLIES_HIGH_SHOULDER.md` proves that at least
one of the two distinct originals L,S is high. Its proof includes
selected central L. Choose that high negative-x original H. The five
distinct originals A,H,U,R,D satisfy the widened cap and contradict
Dmain>2. In particular U is not reused as either shoulder.

Now suppose U is lower. If L is central,
`WEAK_MIDDLE_CENTRAL_SELECTED_LEFT_WITH_SIDE_EXTRA.md` supplies the
complete contradiction. Its high-S branch proves that the actual L has
good whole floor by a three-row rational center-distance argument and
uses A,S,L,R,D in the cap. Its low-S branch proves B<S<P from the actual
L/P cone and actual L/S pair, then uses the complete below-P/lower-central
theorem. The two branches meet without a missing equality face.

If L is instead a true left-side original, L and S are distinct originals
in the same side strip, both above B. The two-square side-center cap
forbids both center heights from being at least 9/16. Thus one of L,S
has height below 9/16<3/5. The complete low-side/lower-central exclusion
applies to that actual low original and the actual lower central U,
regardless of which one is selected. This exhausts S/C.

## 6. Two side extras: S/S

Both actual extras lie above B in the left side strip. The complete
strict-radius caller is
`TWO_OPPOSITE_UPPER_SIDE_EXTRAS_CLOSED_HAND_PROOF.md`. For clarity, its
entire occupancy argument is as follows.

The outer-actual side-marker capacity in
`OUTER_ACTUAL_LINK_ENDPOINT_RESERVE_HAND_PROOF.md`, Sections 4-5, applies because the expanded
closed original squares are pairwise disjoint. It allows at most two
outsiders in a closed side strip. Therefore the selected L is central,
since otherwise L and the two extras would be three left-side outsiders.
Its existing L>B order and central routing make L upper central.

The two side extras cannot both be below 3/5: endpoint-inset localization
would put their abscissas in a strip of width 73/600, and their original
main clearances would put their heights in an interval of length 83/100,
contradicting their half-unit center disks. Thus one extra H is high.
The same-side center cap puts the other extra K below 9/16. Since K is
above B, the accepted wide-main low-side floor theorem applied to the
same-half upper central original L gives yL-hL>1/10.

The cap now uses the five distinct originals A,H,L,R,D and gives the
required contradiction. This closes all S/S height orders and frames.

## 7. Scope and finite dependency assembly

Every high-floor and low-floor case of the full fixed 010/11 predicate
has a complete contradiction, with all local inputs accepted. Every terminal cap
uses the original endpoints, two distinct high original shoulders of
opposite horizontal signs, and a further distinct original central unit
with whole floor at least 1/10. The cap does not require new comparisons
between those witnesses. The other originals remain present and physical.

The proof dependencies proceed in this order: outer-actual endpoint and
pair facts; uniform routing and high-floor exclusion; quarter-main-height
and upper-original ordering; local side-height inputs and lower-central
frame bounds; the no-lower-side and low-side/lower-central finite
exclusions; distinct-extra good-floor and original high-shoulder inputs;
the three exhaustive extra patterns above. None of the local finite
exclusions uses this occupancy conclusion or assumes its own later cap
witnesses. The final manifest records the precise reusable dependencies.

The conclusion is a **strict-radius** exclusion of the whole 010/11
mask. This assembly makes no closed-Q
exclusion claim because it uses the permitted small center expansion
for the side-marker capacity. It makes no assertion about the remaining
fixed masks, historical positional roots, unrestricted equality, or the
global lower bound. Those are separate fixed obligations.

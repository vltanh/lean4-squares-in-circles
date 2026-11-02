# Complete-domain assembly for the weak-middle mixed short chain

## Accepted status

This assembly covers and excludes the unchanged full physical `010/01`
predicate and its horizontal reversal `010/10`, at closed
`Q=1105/256`. Every stated finite-table dependency has now passed its
independent exact replay. The root proof agent independently audited the
geometric reductions and this complete, acyclic assembly. There are no
pending arithmetic dependencies.

The global fixed coverage ledger is not edited by this note. None of the
intermediate complete consequences is an additional global case label.
No Lean, Lake, or CI is used.

## 1. Keep all nine original physical squares

Name the original main chain `A,B,C,D`, the original selected short
chain `L,P,R`, and the two remaining original squares F,G. All corners
lie in the closed Q-disk, frames remain independent, and all original
physical pairs have disjoint interiors. The actual comparisons are the
outer main links and `L--P`; `B--C` and `P--R` are the original weak
horizontal-cone comparisons.

Write `h_S` for physical coordinate halfwidth,
`g_S=1/(4h_S)`, `eta_S=h_S+g_S-1`, and `V=eta_B+eta_C`.
The outer-link reserve theorem proves

    0<=V<1/30,
    Dmain:=x_D-x_A-h_A-h_D >=2+V,

along with the inherited endpoint frames/center bands and the complete
outsider strip `|x|<13/12`. The uniform weak-middle routing theorem
reflects vertically, if necessary, so that P is above both inner mains
and the original shoulders satisfy

    x_L<-23/30, x_R>23/30,
    25/32<y_L,y_R<21/16,
    -1/12<x_P<23/60.

These statements allow the entire inner range `h_B,h_C<13/20`. The
stronger old actual-four bound31/60 is not used.

The quantity V is strictly positive. Indeed `eta_S>=0`, with equality
only at `h_S=1/2`. If V were zero, both B and C would be axis aligned.
Their weak x-comparison would have `x_C-x_B<1`, while their original
horizontal cone would give `|y_C-y_B|<=x_C-x_B<1`. The aligned physical
squares would then overlap in both coordinate projections, contradicting
disjoint interiors. Consequently

    Dmain>2.                                       (1)

## 2. The high-floor branch of the original P is already impossible

If `y_P-h_P>=1/10`, the five original physical squares `A,L,P,R,D`
satisfy the completed unrestricted joint five-square cap. Their retained
endpoint/shoulder bands, P's central strip, and its whole floor are
exactly that theorem's caller. It gives, even at closed Q,

    46*Dmain+27/2 <=211/2.

Equation (1) makes the left side strictly greater than211/2. Thus the
whole high-floor branch is excluded, including its equality face.

It remains to assume `y_P-h_P<1/10`. The following complete consequences
use the slightly larger closed branch `y_P-h_P<=1/10`.

## 3. Both original extras are central

The complete main-height table proves

    y_B,y_C<-3/10.

For either original extra S, the complete above-side theorem excludes
S above its assigned main in either closed side strip. The complete
below-side transfer excludes it below that assigned main. Equal heights
are already impossible by the uniform3/4 physical clearance lemma.
Hence no original extra occupies either closed side strip, and

    |x_F|<29/60,             |x_G|<29/60.            (2)

No side capacity or choice of replacement square is needed for this
step; both original physical extras have been treated.

## 4. There is an original upper central extra above P

The original outer-cone/endpoint reserve gives both main heights above
`-6/5`. Together with the complete `-3/10` upper bound, their height
spread is less than9/10. The exact twelve-row central-clearance lemma
then gives the exhaustive routing: each original square satisfying (2)
is either above both mains or below both.

A lower central extra has center below`-6/5` and whole upper edge below
`-6/5+1/sqrt(2)<-9/20`. The reflected central-strip two-square theorem
forbids two such original lower extras. Therefore at least one of F,G,
call it U, is above both mains.

The complete central-order table proves that every such original U is
above P. The complete upper-central whole-floor theorem then proves

    y_U-h_U>1/10.                                  (3)

Its hypotheses retain the original P and U frames, their original
physical separator, the same-half original main, and the original left
shoulder. No new horizontal-cone relation is imposed on L,U,R.

## 5. The original five-square joint cap gives the final contradiction

The original physical squares `A,L,U,R,D` satisfy the unrestricted joint
five-square theorem: (2) places U in its allowed central band, (3) gives
its whole floor, and the original endpoints and shoulders retain their
already proved bands. The theorem's full owner and normal-sign cover
requires no selected cone or actual comparison for either new central
pair L/U or U/R.

The closed-Q cap again gives

    46*Dmain+27/2 <=211/2,

contradicting (1). This excludes the entire low-floor complement. Along
with Section2, the unchanged full moving `010/01` predicate has no
closed-Q witness with all exact acceptance records now completed.
Horizontal reversal gives the corresponding complete exclusion for
`010/10`.

## Dependency records

The mathematical dependencies, with their complete scopes, are:

- `OUTER_ACTUAL_LINK_ENDPOINT_RESERVE_HAND_PROOF.md`;
- `WEAK_MIDDLE_ROUTING_AND_HIGH_FLOOR.md` and its12-row3/4-clearance table;
- `WEAK_MIDDLE_LOW_FLOOR_MAINHEIGHT_THREE_TENTHS.md`,51,817 leaves;
- `WEAK_MIDDLE_ABOVE_SIDE_EXTRA_EXCLUSION.md`,161,236 leaves;
- the original below-side pair envelope,3,387 leaves, followed by
  `WEAK_MIDDLE_BELOW_SIDE_EXTRA_EXCLUSION.md`,368,125-leaf transfer;
- `WEAK_MIDDLE_CENTRAL_ROUTING_AND_LOWER_COUNT.md`,12-row9/10 clearance;
- `WEAK_MIDDLE_UPPER_CENTRAL_EXTRA_ABOVE_P.md`,155,395 leaves;
- `WEAK_MIDDLE_UPPER_CENTRAL_WHOLE_FLOOR.md`,71,126 leaves;
- the closed-Q `TWO_SQUARE_CENTRAL_STRIP_CAP_HAND_PROOF.md` and completed
  `UNRESTRICTED_JOINT_FIVE_SQUARE_HIGH_FLOOR_CAP.md`.

All original callers and both floor alternatives are covered. The accompanying exact acceptance records certify all finite arithmetic
dependencies of this complete-domain closure.

## Independent assembly audit

The root proof agent independently audited this assembly and the central
routing/lower-count argument. It found the coverage complete and the
dependencies acyclic. The final below-side replay subsequently passed.
The strict surplus V>0 is applied only to the unchanged original weak
middle comparison. This manuscript records the proved coverage; the fixed ledger is managed
separately by the root proof integration.

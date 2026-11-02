# Independent review of the final fixed-mask 000/11 assembly

November 2, 2026. Agent review of the complete physical and finite-case
assembly. No Lean or CI. This review does not claim a human review or a
formal-kernel proof.

## Reviewed frozen sources

The principal source is
`pr11/research/nine/A2_000_11_WHOLE_DOMAIN_ASSEMBLY.md`, SHA-256
`f8a8d16639a273f4c94bd84b5fd39bb71d4344d24f22e87249bb8161ae965ae9`.

Its normalization source is
`pr11/research/nine/SMALL_CENTER_EXPANSION_PRESERVES_FIXED_MASKS.md`,
SHA-256
`dc5d72e4554296c98bc2a0dc0c45003e495de54c1c60af0a6e3a31f2d06de8c4`.

I read the entire final parent assembly and normalization. I also checked
the complete full-side-middle, full-side-bottom/top, and (2,3,0) callers
against this new normalization, and checked the two-upper (1,3,1) source's
final low-side extraction. The remaining inputs have the earlier
independent reviews and exact replay records cited by the assembly.

**Result: PASS. No missing occupancy, height order, reflection case,
distinctness condition, or normalization premise was found. The conclusion
has strict-radius scope C only.**

## 1. Small expansion preserves the exact predicate

For a strict counterexample, all 36 corner inequalities have a positive
continuity margin. The two selected weak gaps satisfy d<H with d>0, so
the finite bounds lambda<H/d leave an interval lambda>1. The same
multiplier strictly improves each original physical separator, preserves
all cone comparisons and actual links, and preserves both strict weak
bits. It leaves every original frame unchanged. Choosing the extra finite
central-coordinate bounds also preserves all columns, although the new
assembly may simply classify after expansion.

The identity

`Dlambda=lambda D0+(lambda-1)(h0+h3)>2`

uses D0>=2 and h0+h3>0. It does not require expansion to a Q-contact.
Every subsequent geometric inequality uses only closed-Q containment,
closed-square disjointness, the retained comparisons, and this strict
endpoint span. Historical source wording that expands all the way to Q
therefore adds no necessary premise to those geometric arguments.

In particular, the new fixed-mask assembly does not need to reclassify
the short bits or invoke another mask during its normalization.

## 2. Count and common-routing coverage

At most two outsiders occur in each closed side column. Five outsiders
therefore give exactly the nine ordered counts represented by

`(2,1,2), (2,2,1), (2,3,0), (1,3,1), (1,4,0), (0,5,0)`

and horizontal reflection. Their orbit sizes are 1,2,2,1,2,1, summing to
nine. The boundary x=+/-29/60 belongs to a side; no boundary is omitted.

The original cone-three routing places its middle P in the central
strip. One common vertical reflection makes every selected central
member upper and every selected side member above its own main. Every
other central original is strictly above both inner mains or strictly
below both. The selected horizontal span is at least sqrt(2)>29/30, so
all three cannot be central.

Thus (1,3,1) has at least one upper central unit. The counts (2,3,0) and
(1,4,0) have two selected upper central units; no zero-upper or one-upper
complement occurs in those families. In (2,3,0), selected L is above the
full-side main, excluding the top marker position. For (2,2,1), the
bottom/top caller does not use a selected short direction, so vertical
reflection covers top even after the common upward routing was chosen.

## 3. The final side-order and height splits are exhaustive

For (1,3,1) with exactly two upper central originals, a selected endpoint
is a side outsider, hence at least one side outsider lies above its own
main. Same-side physical clearance rules out equality. The only two
families are both above, or one above and one below. Horizontal
reflection makes the latter left-above/right-below. Its right outsider
cannot be selected, so selected R is central and selected L is precisely
the left-side original. These are exactly the hypotheses of the
opposite-side caller. There is no both-below complement.

In the both-above family, two low side outsiders contradict the selected
cone span. Both-high and exactly-one-low cases are covered. The latter
proves both upper central floors good, forces their strict horizontal
signs to be opposite, and uses negative central / positive central /
high right-side units as three distinct cap inputs. The both-high case
uses the two original side shoulders and a good original upper central.

For full-side-middle (2,2,1), the lower original left outsider gives
y1>-17/50, and the upper original left outsider has height >63/100.
If a selected endpoint is central, the two selected central originals
have opposite signs and the negative one has good floor. The sole right
outsider is high above its main, low above its main, or below its main.
Those alternatives respectively supply that outsider as the right
shoulder, give the positive central's good floor, or give the positive
central's high center through the reflected lower-side main bound.
No equality order is possible. The retained high left-side original,
negative central original, and chosen positive original are distinct.

If both selected endpoints are side outsiders, the original lower
left-side unit supplies the main-height hypothesis. The completed
low-right theorem is used first; its high-R conclusion is then consumed
by the completed low-floor theorem. The cap uses the same original
selected L,P,R, with the same frames and centers throughout.

The other counts have the stated complete height partitions: all-upper
or two-upper/one-lower for (2,3,0); two, three, or four upper for (1,4,0);
and the direct span contradiction for (0,5,0). Full-side (2,1,2) and
full-side-bottom/top (2,2,1) use their complete marker-order arguments.

## 4. Terminal, dependence, and scope

Every cap has the original two main endpoints plus three distinct
original outsiders. A central outsider may be used as a shoulder only
when its center is proved high and on the required closed horizontal
side. A good floor implies its center exceeds 3/5 because h>=1/2. All
outsiders retain |x|<13/12, so the cap's full domains are supplied.

The widened cap, universal pair tolls, pair clearance and scalar tables
are proved independently of these occupancy conclusions. The
same-side high-central disk lemma is a two-unit statement; using it in
the middle table does not use the complete (1,3,1) result. The low-right
table precedes the low-floor table. This gives the acyclic order stated
in the final assembly.

The large-table parity and complete-tree audit is recorded in
`MIDDLE_MAIN_LOW_FLOOR_CPP_INDEPENDENT_AUDIT.md`. That audit checked the
frozen mathematical evaluator, interval contractions, safe early exits,
all chirality and owner alternatives, and full tree structure against
the independent exact replay. This final assembly review does not
repeat that 2,821,264-leaf arithmetic run or claim a new one.

Every normalized case contradicts D>2. Small expansion is available for
each q<Q, however close to Q, and introduces no uniform gap assumption.
It is not asserted at q=Q. Therefore this argument discharges the entire
original strict predicate D_000/11^lt and has classification C. It does
not classify the closed-Q domain, prove global A.2, identify equality
packings, or alter any of the 7,915 positional-root IDs or 15 gate IDs.

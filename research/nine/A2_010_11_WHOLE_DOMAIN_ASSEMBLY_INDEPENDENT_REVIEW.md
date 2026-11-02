# Independent review of the original-nine 010/11 assembly

November 2, 2026. Review by the weak-outer work agent, independently of
the author of `A2_010_11_WHOLE_DOMAIN_ASSEMBLY.md`.

**Final physical and logical verdict: PASS.** The assembled geometric
argument is complete for the strict-radius original-nine 010/11 domain.
The two component arithmetic acceptances that were pending during the
initial review are now complete: the no-lower-side forest and the
at-or-above-P low-side/lower-central forest. Their final source binding,
complete counts and acceptance records were independently checked in
the addendum below. This review is separate from those exact arithmetic
replays and does not replace them.

The review covers the initial normalization, imported theorem scopes,
all three extra patterns, all cap identities, boundary cases and the
dependency order. It is an independent mathematical review, not a Lean,
Lake, CI, human-review or kernel-verification claim. No duplicate large
finite replay was run for this assembly review.

## 1. Exact input and the single initial expansion

The input is the full fixed predicate on nine original units
`A,B,C,D,L,P,R,F,G`: four main originals, three designated short-chain
originals and two further originals, all distinct. All original frames,
36 corners, 36 physical pairs, five cone comparisons, two actual outer
links and three genuinely weak links remain in force.

The strict inequality q<Q supplies a positive margin at every original
corner. The small-center-expansion lemma chooses one common multiplier
larger than one and sufficiently close to one. The three weak gaps give
three additional strict upper bounds on that multiplier. Actual
projection gaps and all five center cones persist; each original
positive pair support becomes strictly separated on the same genuine
owner axis. Thus the expanded closed original squares are pairwise
disjoint and remain in Q.

Every floor split, side classification and witness selection in the
assembly occurs after this expansion. Consequently no preservation of
the sign of a floor such as yP-hP-1/10 is needed. The horizontal and
vertical reflections preserve the exact mask: reversing the main
chain preserves 010 and reversing the selected triple preserves 11.
All subsequent arguments can use the already expanded configuration.
The S/S proof is reproduced directly on it; no second expansion or
preservation of its newly chosen cap witnesses is necessary.

The original middle weak bit forces V>0. Since eta(h)=0 only when
h=1/2, V=0 would make B,C aligned. Their horizontal gap and cone
vertical gap would both be below one, contradicting physical interior
disjointness. Therefore the accepted endpoint estimate supplies the
strict contradiction target Dmain>=2+V>2.

## 2. Common geometry and the lower-central count

The complete routing source supplies P above both inner mains, L above
B, R above C, and the simultaneous bounds

    0<=xP<1129/3000,
    -13/12<xL<-124/375,
    707/1000<xR<13/12,
    yR>=3/5.

The last fact does not assume the new side-extra exclusion: the original
P/R cone makes xR>707/1000, while a routed shoulder below 3/5 would
have |xR|<121/200. R is therefore always a genuine right-side original,
since 707/1000-29/60=671/3000>0.

The high selected-floor branch, including equality at 1/10, has its
independent complete caller in
`WEAK_MIDDLE_TWO_WEAK_SHORT_ROUTING_AND_HIGH_FLOOR.md`. Its asymmetric
low-shoulder branch uses the audited original endpoint-rectangle position
theorem; no actual L/P link or old narrow inner-main bound is inserted.
The complementary branch consequently has yP-hP<1/10 and satisfies
every weak inequality premise of the later low-floor inputs.

The 9,688,640-leaf main-height theorem proves both yB,yC<-1/4 in that
domain. The appropriate unconditional central source is
`WEAK_MIDDLE_UNCONDITIONAL_CENTRAL_ROUTING.md`, Sections 2--5. It
applies to every original with |x|<=29/60, including strip boundaries
and x=0, without using the old 010/01 main-height theorem.

Its 909/1000 clearance is a hand consequence of the accepted twelve-row
physical table: the original distance bound is strictly less than
491/1000, since

    (491/1000)^2-15007/62500=969/1000000>0.

The 1-Lipschitz distance collar adds 9/1000. For a lower central original
V, use its actual own-half main and hV<=1/sqrt(2)<709/1000. Then

    yV+hV<-1/4-909/1000+709/1000=-9/20,

where (709/1000)^2-1/2=2681/1000000>0. The reflected closed-Q
two-square central-strip cap therefore allows at most one lower central
original. Its proof does not assume any actual selected short link or
any relation between the two lower original frames.

The upper-central ordering theorem explicitly allows the actual selected
L as its U. It requires only U distinct from P; its geometric frame
minimization precedes elimination of U. In contrast, the new good-floor
theorem explicitly requires U distinct from all seven selected originals.
The assembly observes this difference at every use.

## 3. Side exhaustion and the two complete local inputs

On the closed right side, every original S has a strict vertical
clearance from C. Indeed the main bands give the forward gap

    xS-xC<11/10-gC<7/5-hC,

because 3/10-(hC-gC)>3/10-69/260=9/260. The reverse gap is still
smaller. Thus the uniform 3/4-clearance theorem excludes yS=yC;
reflection treats the left side. The new no-lower-side input excludes
the lower alternative. The own-half upper-side-extra theorem excludes
the upper right alternative for F,G in the low-P-floor domain.

These implications leave precisely

    C: -29/60<x<29/60, above both mains or below both;
    S: -13/12<x<=-29/60, above B.

The categories are disjoint and exhaustive because the original outsider
bound is |x|<13/12. A coordinate on either side boundary belongs to a
side category. Closed central theorems may be restricted to the remaining
open central interval. The unordered patterns of the two original extras
are exactly C/C, S/C, S/S.

The second component is the at-or-above-P complement to the accepted
below-P low-side/lower-central exclusion. Their precise shared caller is
an original S in the left side, above B, with yS<=3/5, and a distinct
original lower central V. The below-P theorem treats yS<yP and the
complement treats yS>=yP. S may be L or an extra in both. This union
includes yS=yP and yS=3/5 and introduces no S/P cone. S is never the
original P: equality refers only to their center heights.

The reviewed no-lower-side reduction has all 128 prescribed roots,
both original assigned-main sides, both width pieces and all five
independent signs. The reviewed at-or-above-P reduction has both possible
own-half main choices for the actual lower central original. Those root
unions have the correct scopes for this assembly. The complete saved
forests have now passed their separate exact replays, with the final
records inspected as detailed below.

## 4. C/C: both central extras

At most one extra is lower, so at least one actual extra U is upper. Its
ordering and distinctness make the good-floor theorem applicable.

If yL>=3/5, the cap witnesses `(A,L,U,R,D)` are five distinct originals.
L,R have the required opposite signs and high centers; U is central
with whole floor greater than 1/10. All endpoint frame and coordinate
hypotheses follow from the original actual-outer reserve theorem.

If yL<3/5 and L were central, unconditional central routing would make
it upper, the ordering theorem would make L>P, and Section 7 of
`LOW_OPPOSITE_ORIGINAL_LIES_BELOW_SELECTED_MIDDLE.md` would force
yL>3/5. Thus L is a true left-side original. If one extra is lower,
the complete low-side/lower-central union applies with S=L.

Otherwise both extras are upper and both have good whole floors. Their
center heights exceed 3/5. The actual upper-column theorem requires only
two such physical originals in Q; it gives horizontal separation
strictly greater than ell. If their central centers had a common closed
horizontal half-plane, including a zero coordinate, their gap would be
less than ell. Hence they have strict opposite signs. Naming them
Uminus,Uplus gives the five distinct cap witnesses
`(A,Uminus,Uplus,R,D)`. No extra is reused and no central cone is assumed.

## 5. S/C: one side and one central extra

Call them S and U. If U is upper, its good floor follows from the
distinct-extra theorem. The high-shoulder resource gives a high original
H among L,S, including when L is central. Both candidates have negative
x and are distinct from U,R,A,D. The cap `(A,H,U,R,D)` therefore has
the complete caller.

If U is lower and L central, the separate hand proof handles both
yS>=3/5 and yS<3/5. In its high branch, the three-row center-distance
argument proves the actual L has good floor; it never invokes the
distinct-extra theorem on L. Its cap is `(A,S,L,R,D)`.

In its low branch, the actual L/S center disks give yL-yS>24/25,
while the actual L/P cone gives yL-yP<2579/3000. Their difference
has positive reserve 24/25-2579/3000=301/3000. Thus S<P and the
accepted below-P/lower-central theorem applies. Equality yS=3/5 was
already assigned to the high branch.

If U is lower and L is a true left-side original, the two distinct
originals L,S are both above B in the same closed side strip. The
two-square side-center cap forces one to have height below 9/16,
hence below 3/5. The complete low-side/lower-central union applies
to that original, whether it is L or S, and the distinct actual U.
This includes both possible L/S height orders and equality with P.

## 6. S/S: both extras in the upper left side

The exact side-capacity source is
`OUTER_ACTUAL_LINK_ENDPOINT_RESERVE_HAND_PROOF.md`, Sections 4--5.
Its proof consumes a marker for each actual inner main even when its
center is central. Thus it is valid with weak B/C and does not silently
import an actual-four-chain premise. The inherited physical marker
capture uses only the actual endpoint bounds; the initial expansion
already supplies closed-square disjointness.

Therefore L cannot join the two extras in the left side. Its original
negative sign makes it central, and its L>B order makes it upper by
central routing. This conclusion is valid when xL=-ell: that equality
would still be a third side original and is excluded by capacity.

If both side extras were below 3/5, the endpoint insets would put both
absolute abscissas in [29/60,121/200), of width 73/600<13/100.
Their gaps from B are less than 6/25; the larger endpoint comparison
has exact reserve

    6/25-[121/200-(5/13-1/60)]=23/7800>0.

The center disks give both vertical gaps from B greater than 97/100,
since 1-(6/25)^2-(97/100)^2=3/2000>0. Their heights therefore belong
to (-23/100,3/5), of length 83/100. Their mutual center distance
would be below one, with conservative squared reserve

    1-(13/100)^2-(83/100)^2=1471/5000>0.

Hence one actual extra H is high. The same-side center cap makes the
other actual extra K lower than 9/16. K remains above B. The reflected
wide-main low-side-floor theorem applies to K and the same-half upper
central original L; its six original inputs are distinct and it imposes
no selected cone involving K. It gives L's good floor. Thus
`(A,H,L,R,D)` are the five distinct originals required by the cap.

## 7. Complete terminal identity table

All rows have the unchanged original endpoints A,D. Each triple in the
last column is ordered as negative high shoulder, good central original,
positive high shoulder; no new geometric chain is asserted.

| Extra pattern and branch | Terminal | Three cap originals |
|---|---|---|
| C/C; L high | Widened cap | L,U,R |
| C/C; L low; one extra lower | Low-side/lower-central exclusion | None |
| C/C; L low; both extras upper | Widened cap | Uminus,Uplus,R |
| S/C; central U upper | Widened cap | H in {L,S},U,R |
| S/C; U lower; L central; S high | Widened cap | S,L,R |
| S/C; U lower; L central; S low | Below-P/lower-central exclusion | None |
| S/C; U lower; L side | Complete low-side/lower-central exclusion | None |
| S/S | Widened cap | H,L,R |

Every cap has all five original physical pair relations available. Its
central-normal and witness-order deductions are internal to the cap,
so no missing comparison between chosen originals is presumed.

## 8. Dependency order and final scope

The accepted physical endpoint and pair inequalities precede the routing
and high-floor exclusion. The quarter-main-height and central-routing
results then supply the lower-central count. The original upper-order
theorem uses earlier main lower bounds and selected-pair resources, not
this occupancy conclusion. The distinct-extra floor theorem uses the
published upper-central height and low-side-floor inputs; its proof does
not assume no lower side or the final extra classification.

The low-side/lower-central theorems use the actual lower original, the
quarter-main-height theorem and the genuine two-inner-main width
consequence. The no-lower-side reduction uses the separately derived
signed lower-side height and main-pair bounds. None of these premises
uses the assembled C/C, S/C, S/S conclusion or future cap witnesses.
The displayed dependency graph is therefore acyclic.

There is no residual side, height-order, equality-face, frame or witness
identity branch in the assembled argument. With both complete component
acceptances, it proves the entire strict-radius 010/11 mask. It proves
no closed-Q exclusion: the closed-marker occupancy
step was justified by the initial strict-radius expansion. It changes no
other fixed mask, historical positional root or equality classification.

The author incorporated the recommended explicit unconditional-routing
and actual-outer-marker source citations. The center-height equality is
`yS=yP`; it never identifies the distinct originals S and P.

## 9. Final complete acceptance addendum

After the initial physical review, both pending arithmetic obligations
completed. I independently inspected the canonical at-or-above-P replay,
the no-lower-side immutable forest archive and manifest, all 128 raw
no-lower-side acceptance reports, their totals and their source binding.
The compact independent record is
`A2_010_11_FINAL_ACCEPTANCE_RECORDS_INDEPENDENT_CHECK.json`.

The no-lower-side package has exactly the 128 prescribed root IDs, each
once, and zero frontier. Every raw root report is PASS and complete.
Their sums are 27,552,502 strict leaves and 55,104,876 nodes, maximum
depth 63, and minimum positive reserve 3357953/2^48. All 128 compressed
root-file hashes and all 128 raw-report hashes match the immutable
manifest. The complete archive SHA-256 is

    a76663f6e8d46af76b5820197e68dacf6ed17deb75792d6cb93d5e6223cb3d90.

The manifest SHA-256 is

    e6a29e891f2ba8da58bc867c59b6a0d777cad2c79fd5d03c92b7d26f188e2426.

The complete no-lower-side checker source hash is

    5211852f38acfa94c3d80d29559042bcb346d9d1751c0c5015152fc0ecc6a424.

The saved build-binding record establishes that the fresh build of that
entire delivered source is byte-identical to the replayed executable,
whose SHA-256 is

    cd9e51c1328120fe1e45a1fd5c533eca5fa9f172a906fb883b59f0ea729593c0.

Its separate root physical/code review is
`NO_LOWER_SIDE_INDEPENDENT_PHYSICAL_CODE_REVIEW.md`. The complete
arithmetic evidence now discharges that review's explicit arithmetic
qualification; no partial-root total is used.

The at-or-above-P canonical fresh-source replay has all eight roots,
143,088 strict leaves, 286,168 nodes, depth 41, no frontier and minimum
positive reserve 136564324/2^48. Its complete restored checker source
hash is

    d4fab70e53914877a54bbaadfb37e1a413172a5078f33ac31216334c773db453.

Its certificate hash is

    53769f5264a76d8991a72f22eaebf882337f1a9fb5f7857c71ffa3652132446b.

I separately completed the full independent physical, thirteen-scalar,
parser, directed-arithmetic and saved-source-binding review in
`LOW_SIDE_AT_OR_ABOVE_P_INDEPENDENT_PHYSICAL_CODE_REVIEW.md`. The
canonical source, wrapper and certificate are byte-identical to those
reviewed files. Its new wrapper compiles an immutable temporary copy
of the complete saved source for every replay and never uses an old
executable.

These checks inspect and bind the completed exact replays; they do not
claim another full arithmetic traversal. Together with the accepted
earlier components, they remove the two qualifications present at the
start of the assembly review. The final verdict is the complete
strict-radius exclusion of the whole original-nine 010/11 predicate.

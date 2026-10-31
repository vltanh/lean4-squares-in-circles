# High middle unit and aligned adjacent section exclusion: complete review

Date: October 30, 2026 UTC.

**Verdict: PASS for both complete frozen sources. No repair requested.**

Reviewed sources:

1. `THREE_BOUNDARY_RETURNS_FORCE_A_HIGH_MIDDLE_UNIT_AND_A_UNIT_SECTION_2026_10_30.md`,
   8,086 bytes, SHA256
   `99c6d7fc3bb50cf65f8ee36ef1e041dafb344671a5a09830e691746ef1f7f528`.
2. `ALIGNED_ADJACENT_LONG_SHORT_SEVEN_CYCLE_SECTION_OVERLAP_EXCLUSION_2026_10_30.md`,
   12,063 bytes, SHA256
   `f7694cc75e45b49bd05fa106f03267c7465c622d44d6896d8090d3f09704e686`.

I read both entire sources and reconstructed their full statements,
section formulas, interval order and unchanged-certificate caller. This
review includes the complete one-unit proof, not just its later sector
corollary. The endpoint profile and wrapper inputs were already fully
reviewed in
`REVIEW_COMPLETE_UNEQUAL_FLOOR_PROFILE_AND_OBLIQUE_RETURN_WRAPPER_BLOCK_EARS_2026_10_30.md`.

Provenance: I authored the frozen adjacent normal/vertex reduction used
by the second source. The strict section-overlap argument was developed
by the root agent and independently assembled by the annular agent;
those new arguments are reviewed here. The contribution to the earlier
input is not represented as a separate independent review of my own
source.

## 1. Every above-floor unit has a full section of width at least one

The first source's Theorem 1 assumes only an actual unit contained in
D_Q and wholly in y>=3/8. Write its tilt coefficients a>=b>=0,
a^2+b^2=1, halfheight h=(a+b)/2, width sum w=a+b, center height y,
and delta=5/4-y.

Its top is at least3/8+w>=11/8>5/4. Its bottom is at most
sqrt(Q)-w<=sqrt(Q)-1<9/8<5/4. Thus the section is strictly
between its horizontal supporting lines. The actual floor gives
delta<=7/8-h. The top corner's containment gives
delta>=5/4-sqrt(Q)+h>h-7/8. Hence
|delta|<=7/8-h, including the closed floor endpoint.

For b=0 the section has length exactly one. For b>0, solving the
four actual side inequalities gives

    width = min(1/a, (h-|delta|)/(ab)).

The central band uses the opposite-side expression1/a; outside that
band the two adjacent-side intersections give the second expression.
They agree at |delta|=(a-b)/2, so no edge-change case is omitted.

The first expression exceeds one. For the second,
h-|delta|>=w-7/8, while
w-ab=w-(w^2-1)/2>=sqrt(2)-1/2>7/8. Its last inequality follows
by positive squaring from sqrt(2)>11/8. Therefore the second
expression also exceeds one. This proves the full width claim for
every nonzero tilt, with no boundary-circle or stress premise.

## 2. Full three-return count and the one-unit sector implication

The first source's count uses only the force-free support-gap-two
endpoint geometry and physical boundary-center separation. In the
stated R>=2 window, endpoint center directions are within five degrees
of the opposite horizontal axes. Every above-side boundary center is
therefore in the interval(35,145 degrees), using the existing strict
forty-degree separation. Four such centers would span more than120
degrees in an interval of width110, an impossibility. With three,
their middle direction lies strictly between75 and105 degrees.

For any single physical boundary unit whose center direction lies in
that same interval, independently of how the interval was obtained,
its center radius obeys

    31/24 < R-1/sqrt(2) <= |c| < 91/60.

The lower strict comparison uses R>=2 and1/sqrt(2)<17/24. With
sin(theta)>sin(75 degrees)>19/20, its center height exceeds589/480.
Subtracting its actual halfheight, at most1/sqrt(2)<17/24, gives
the entire square floor y>83/160. This is stronger than y>1/2 and
therefore invokes the complete width theorem above.

The same one-unit argument gives a fixed interior disk. For
P=(0,5/4), use sin(theta)>24/25 to obtain

    |c-P|^2 < r^2+25/16-(12/5)r.

The right quadratic is convex on[31/24,91/60]. Its endpoint values
are377/2880 and401/1800, so it is at most401/1800. The exact reserve
(19/40)^2-401/1800=41/14400 is positive. Thus |c-P|<19/40.
Every point of the closed radius1/40 disk about P lies at distance
strictly below1/2 from c and belongs to the actual unit's open incircle.
The stronger sine estimate follows from
sin(75 degrees)^2=(2+sqrt(3))/4>37/40>(24/25)^2.

Consequently the sector conclusion applies directly to the adjacent
cycle's C at angle88--103 degrees. A three-return count is not a
missing premise of that application. The actual entire square and
its own unrestricted frame are retained.

## 3. The general asymmetric section obstruction

The second source's first theorem is force-free once its listed
geometric premises hold. It assumes independent floors
f_A,f_B in[3/8,1/2], their sum at least7/8, x<61/60, physical
boundary C in the75--105 degree sector, an interior horizontal
section of D with c_Dx<-1/2 and
r_D>=1-sqrt(Q-(f_A+1)^2), and one original unit direction
n=(-alpha,beta) with alpha,beta>0 supplying reserve at least one
above(x,f_B).

The preceding one-unit result gives C's full section width at least
one and puts0 in its open section interval at y=5/4. The proof must
establish the actual order of D and C; it does so independently of
their center-angle order.

For every unit square, join its bottom and top support vertices.
For a nonzero tilt they are opposite vertices, with horizontal
offsets of magnitude |a-b|/2<=1/2 from the center. For an aligned
square use the supporting-side midpoints. The joining segment is
inside the unit. Every horizontal interior section therefore has
a point whose x coordinate lies in[c_x-1/2,c_x+1/2]. In D this
point is strictly negative. The two open actual section intervals
are disjoint, since each is in its square's open interior. With0
inside C's interval, D cannot lie on the right. Thus the actual
order is D on the left and C on the right, with r_D<=ell_C.
Boundary endpoint contact is allowed by this weak inequality.

For each actual C section point(X,5/4), the listed support inequality
gives

    X<=x+(beta*k-1)/alpha, k=5/4-f_B in[3/4,7/8].

Both1-beta*k and alpha sqrt(1-k^2) are positive, and the difference
of their squares is(beta-k)^2. Hence every such point obeys
X<=x-sqrt(1-k^2). This bounds r_C, not just one selected point.
The actual full width is at least one, so
ell_C<=x-sqrt(1-k^2)-1. No C orientation or intermediate-square
floor is inferred in this step.

## 4. Exact coupled-floor overlap reserve

The independent floor sum gives
f_A+1>=15/8-f_B=k+5/8. The function g(Y)=sqrt(Q-Y^2) is decreasing
throughout the relevant positive interval, so
g(f_A+1)<=g(k+5/8).

For H(k)=g(k+5/8)-sqrt(1-k^2), direct differentiation and positive
squaring show H'(k)>0 exactly when Qk^2>(k+5/8)^2. Here Q>4 and
k>=3/4>5/8 give the stronger chain Qk^2>4k^2>(k+5/8)^2.
Thus

    H(k)<=H(7/8)=23/16-sqrt(15)/8<153/160.

The radical comparison uses(77/20)^2<15. Its sign is unchanged at
either closed floor endpoint. Combining the actual D lower profile
and C left-end upper bound yields

    r_D-ell_C >= 2-x-H(k)
               > 2-61/60-153/160 =13/480>0.

This directly contradicts the actual interval order. The conclusion
is strict over the full normal, floor and section-edge domains, so
the theorem also excludes the upper-radius endpoint. The arithmetic
is independent of any guessed side ownership or common return frame.

## 5. Literal aligned adjacent cycle caller

The second theorem retains the same actual cycle
A--U--V--B--W--C--D--A, with genuine unloaded full-degree-two U,V,W,
full-degree-two A,B, physical boundary marks A,B,C,D, and compatible
physical routing/spokes. C,D can have additional positive edges.
Every completing square and original contact mean remains present.
Only A and B are assumed aligned with the actual long normal.

The frozen adjacent reduction gives R>=2 from the actual end-to-end
long normal chords, the whole above-side location of C,D, angles
theta_C in(88,103 degrees), theta_D in(129,144 degrees), the original
strict northwest short normal, and the actual B--W upper-inner vertex.
It proves that vertex without assigning a physical circle contact to W.
The full original endpoint equations and coupled endpoint heights give
the independent floor domain used in the geometric theorem. The
actual vertex is(s+1,f_B), with |s|<1/60, so x<61/60.

C lies in the required one-unit sector. D's physical boundary radius
exceeds5/4 and its angle is greater than120 degrees, so
c_Dx<-(5/4)/2=-5/8<-1/2. This is the only center-position fact
needed for its actual section order.

The complete A--D contact-locus theorem applies to the actual above-
side boundary D. Reflection of the full unequal-floor profile and
corner-wrapper theorem gives a section strictly between D's horizontal
supports and r_D>=1-g(f_A+1). If D remains above A's upper side,
the floor theorem applies; if it crosses below, the actual side
slider and original oblique normal satisfy the complete wrapper
theorem. Neither a vertical A--D force normal nor alignment of D
is assumed. Both original physical endpoint circle masks are retained.

Finally the original unloaded W force equation propagates the same
n from B to C. Its actual support-width reserve is at least one.
Since B's original exposed point is(s+1,f_B), every original point
of C has exactly the supporting lower bound needed by the force-free
section theorem. No equality of its force line with a center line,
no common frame at C, and no altered mean is used.

All geometric premises are thus supplied literally by the original
aligned branch. The13/480 overlap contradiction excludes that entire
branch even at q=Q.

## 6. Diagnostic and remaining scope

The exact six-unit diagnostic in the adjacent-normal source has no
missing boundary D with its required section and has no complete
remaining endpoint certificate. The new proof uses exactly that
additional return geometry. It is therefore consistent with the
subcritical local chain and its genuine B,U,V,W equations.

The geometric obstruction has wider reuse than one cycle, but its
current physical caller requires both long endpoints aligned. A
tilted endpoint's side cannot be replaced by a horizontal floor.
The source correctly leaves the tilted adjacent branch open and
makes no claim that all seven-cycles, larger positive blocks or the
unrestricted nine-unit target are closed.

Both complete source hashes and every listed frozen dependency were
checked against the workspace bytes. No numerical pose search,
orientation grid, source theorem alteration, certificate reselection,
discarded physical unit, original ledger edit, Lean/Lake build or CI
run entered this review.

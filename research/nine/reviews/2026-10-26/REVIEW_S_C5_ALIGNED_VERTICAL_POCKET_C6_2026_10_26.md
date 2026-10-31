# Independent review: the fixed inner-circle point and aligned vertical direct pocket

Date: October 26, 2026.

Reviewer: C6 completion agent, independent of both source authors.

**Verdict: PASS.** I read the complete
`VERTICAL_TOP_CONTACT_BOUNDARY_INNER_CIRCLE_POINT.md` and
`S_LEAF_C5_ALIGNED_VERTICAL_DIRECT_POCKET_EMPTY.md`, together
with the needed aligned-root, closed-inner-arc and physical-pocket
prerequisites. The fixed-point theorem covers every orientation
and both physical circle masks. Its original-domain join excludes
the entire stated aligned vertical-direct L-A-B pocket.

## 1. Complete physical corner and orientation cover

For an aligned top face, a positive-x circle corner must be its
right bottom corner. The norm comparison makes its horizontal
coordinate at least 1/2; the lower radius and b<1 make this strict.
The upper coordinate bound and b<k<b+1 then put the fixed point
strictly inside the aligned square. This retains every actual
top-side mean and a possible physical bottom-corner tie.

For a nonaligned square, the actual top point has the complete
chart (5). Its norm is below R. The left adjacent corner cannot
be a circle corner because the bottom corner has a strictly larger
norm. Thus the right/bottom alternative is exhaustive. If both
are circle corners, the proof explicitly uses the right case and
keeps the weak farthest-corner comparison. If the right corner
is not a circle point, the bottom is the only possibility and
inherits the hypothesis of positive x coordinate. No physical
two-corner tie or corner sign is silently discarded.

I rederived both own coordinates of the fixed point. Their squared
distance from the actual top vertex is less than one, so after
nonnegativity is proved their upper bounds below one are automatic.
This use of distance is valid even when the fixed point lies on
one of the square's closed sides.

## 2. Whole-angle fixed-point inequalities

In the right-circle case, containment of the bottom corner gives
exactly \(qs-bc\ge1/2\). Its contradiction for c>=1/2 and its
resulting s>4/5 are valid. The second own coordinate is then
nonnegative directly. A negative first coordinate would make
the actual circle corner's projection on a unit side exceed
\(1+k>R\), a contradiction. The angular inequality (10) holds
on its complete range.

For the bottom-circle first coordinate, I checked the full
positive cosine/sine combination in (13). The linear projection
coefficients are obtained with the correct strict directions
from the assumed negative own coordinate, the actual q/b bounds,
and k>8/7. Concavity on the whole interval reduces the lower
bound to its two exact endpoints; both exceed 11/4. The Cauchy
norm contradiction has the stated positive reserve.

For the second coordinate, negativity first forces q<1/2 and
therefore the additional b>13/15 premise. The c>=4/5 factorization
is correct. In the other range the two alternatives s>=c and
s<c are exhaustive and both give c+s>13/10. The positive-x
bottom-corner hypothesis is used exactly where needed in the
first alternative. Both vertical-norm contradictions are valid.
This proves the fixed point lies in the complete closed square.

I independently rebuilt all ten displayed rational identities and
the remaining elementary endpoint comparisons. Each agrees with
its stated value. No numerical orientation check was used as a
proof premise.

## 3. Actual aligned-root join and the occupied crosscut

The original vertical direct normal gives exactly the top support
line y=-b and the actual point \((q,-b)\), with q in the full
permitted interval. The accepted aligned source supplies
R^2>17/4, a<11/60 and b>49/60. The exact identities
\(as=\delta(1+c)\), \(q=\delta+ac/s\) give
\(a^2=2\delta q-\delta^2<q/30\), hence the needed implication
q<1/2 => b>13/15. Proper loaded concurrence has positive
x coordinate, so the actual circle resultant has positive
x coordinate and supplies a positive-weight physical corner
with that sign. This includes each individual radial weight
endpoint without replacing the physical mask.

Every segment of the chosen lower-right crosscut lies in an
original occupied body. The top-to-bottom norm comparison places
the chosen B circle corner strictly below its top support. The
earlier segments lie at or above that support, so the crosscut
is simple; zero-length middle segments may be omitted. Its outer
arc and every crosscut point have positive x coordinate and
height at most -1/2.

The actual C circle corners cannot lie in the lower-right outer
arc: one has negative x and the other positive y. Thus the
occupied path, its inside-body homotopy and the boundary-spoke
order place the actual L-A-B exterior free region inside the
bounded side Omega used in the proof. This containment is all
the argument needs. In a physical two-corner B mask, another
B-circle contact may cut that bounded side into smaller free
pieces; it cannot enlarge the actual pocket or invalidate the
containment. Likewise extra zero-selected-force physical
contacts can only subdivide it. The whole original means and
physical endpoints are retained by the compact-interior rule.

## 4. Complete inner-circle escape argument

A whole extra in this bounded side has center norm at least one,
so the accepted annular theorem supplies an open inner-circle
arc longer than pi/4. The exact closed L intersection is its
stated radial interval. The physical boundary unit B has center
norm greater than R-1/sqrt(2)>1, so the accepted complete
closed-intersection formulas make its entire inner-circle
intersection one interval, containing the proved fixed point.
It lies unambiguously in the lower angular half-plane.

An unblocked lower-right circle point below the angle of that
fixed point must lie below the lower endpoint of B's interval.
The decreasing-angle circle path to the negative vertical axis
therefore avoids B. It also avoids every L/A crosscut segment,
because its height is below -k<-1 whereas those segments are
above -b>-1. It avoids the outer arc by radius. The vertical
downward ray then misses the entire Jordan boundary, whose
x coordinate is positive. This is a valid escape to infinity
and contradicts membership in the bounded side.

The fixed point itself is blocked even if it lies on B's
boundary: another square's open interior cannot meet the closed
B while their open interiors are disjoint. Consequently every
extra's entire open inner arc must lie strictly between the
fixed-point angle and the lower L-arc endpoint. That interval
has length pi/2-2asin(2/5)<pi/4, a contradiction.

## 5. Accepted original scope

The complete original aligned m_x=0 direct-normal branch has
no L-A-B pocket extra. This holds for both physical B masks,
all genuine means and endpoints, all radial weight splits,
both true transmitter sliders, and all three additional
physical squares. The remaining C-U-A-L allocations are not
excluded here, and strict root-corner normal branches are not
converted into the vertical side-axis branch. No S-leaf parent
gate closure or new certificate is claimed. No Lean compilation
or CI was run.

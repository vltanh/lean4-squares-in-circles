# Independent review: the high-square barrier with a lower-route length test

Date: October 28, 2026 UTC. Reviewer: recovery_audit continuation.

## 1. Exact source and verdict

**PASS.** I read the entire frozen source
`HIGH_SQUARE_CHORD_BARRIER_WITH_LOWER_ROUTE_LENGTH.md` and independently
rederived its full geometric statement, every closed strip endpoint,
the straight-segment length argument, and both exact numerical instances.
The reviewed source is 4,873 bytes, SHA-256

`11e9eb7ba47bb8e8042aed44536046dba6c98f50961e663986935e0ea41cd9a1`,

Git blob `113de84e2c514f7048ce873d3e68d3812376ccca`.
No frozen source byte was changed. Its sole direct pin matches the
current checkout exactly:

| Input | SHA-256 | Operative use |
| --- | --- | --- |
| HIGH_SQUARE_LOW_LEFT_PORT_BARRIER_WITH_SIGNED_SMALL_SUPPORT.md | e2463dea33c2e66b97046c5727562be354e09f3f065e3dc04028e3a79a79dc58 | Complete force-free high-square barrier, with both closed horizontal endpoints and all actual B frames |

That input was completely read and independently rederived in
`REVIEW_SIGNED_SMALL_SUPPORT_HIGH_SQUARE_BARRIER_RECOVERY_AUDIT_2026_10_28.md`,
SHA-256 `4caf67fb8ff68e431eb000f3829aa26a7610cc5e0e3e08d38a114ce7b5931967`.
Its exact scope includes h<=epsilon, not merely h<=0, and includes
an upper port at H's top-left corner or anywhere on the closed strip.
Its whole-unit and actual supporting-axis proof, all endpoint cases,
and exact circle reserve remain the operative version here.

## 2. Literal force-free domain

H,A,B are the same three actual closed unit squares with pairwise
disjoint open interiors, all contained in the original circle. The
radius is R^2=(2+epsilon)^2+1/4<=1105/256, with
0<=epsilon<1/60. The actual H is

    H=[h-1,h] x [g-1,g],
    h<=epsilon, 37/50<=g<=1.

The caller supplies actual positive ell,eta satisfying ell+eta>sqrt(2),
the whole-A bounds min_A x>=h-1 and min_A y>g-1+eta, and an actual
B point P with P_x<=h-ell and P_y<7/10. The theorem forbids any
actual A-B contact. It does not require P to be a vertex, an exposed
point, a loaded port or a mean. A caller must establish the bounds on
the complete actual A, not just a convenient one of its points.

There is no force, degree, selected normal, circle-contact mask or
coefficient premise. Additional actual units in a nine-square caller
remain untouched. The result consequently applies to original shared
means and zero-weight physical contacts exactly as geometric points.

## 3. Every point of A-B in the closed H strip

Suppose V is an actual A-B contact. The whole-A hypotheses give
V_x>=h-1 and V_y>g-1+eta>g-1. Since ell>0, P_x<h.

If h-1<V_x<h and V_y<g, V lies in int H. A closed unit point in
another unit's open interior forces interior overlap, since interior
points of the first unit occur arbitrarily close to it. Thus this
case is impossible.

The exact left endpoint V_x=h-1, V_y<g is also impossible. Every
interior A point has x>h-1, by the whole-A minimum support. Choose
such points sufficiently close to V; their x remains below h and
their heights remain strictly between g-1 and g. They lie in int H.
This argument does not assume that V is a vertex or that A has an
axis parallel to H.

Therefore h-1<=V_x<h forces V_y>=g. The actual B points P,V meet
the already reviewed signed-support barrier: P is strictly left of
h and below 7/10, while V lies in the closed horizontal strip and
at least as high as H's top. That barrier excludes the case, including
V exactly at H's top-left corner.

For V_x=h and V_y>=g, the same barrier includes this right endpoint.
If instead V_x=h and g-1<V_y<g, a sufficiently short part of the
actual B segment from V toward P moves left while its height remains
strictly between H's bottom and top. It enters int H. No sign of
the vertical slope is needed, because the starting height has strict
positive distance from both horizontal sides. This exhausts the
whole closed strip, including both side endpoints.

## 4. A right contact has only a lower length violation or an upper barrier

Only V_x>h remains. The original actual segment PV crosses x=h at
a unique point E strictly between its endpoints, since P_x<h<V_x.
Convexity puts E and the entire segment in the same unchanged B.

If E_y<=g-1, the two actual collinear subsegments have the separate
component lower bounds

    |P-E|>=h-P_x>=ell,
    |E-V|>=V_y-E_y>eta.

Because E is between P and V, the lengths add exactly. Hence
|P-V|=|P-E|+|E-V|>ell+eta>sqrt(2), contradicting the diameter
of the actual unit B. This includes both E_y=g-1 and P_x=h-ell.
The argument does not incorrectly add orthogonal projections of one
unbroken vector; it adds lengths of two collinear subsegments with
different valid component lower bounds.

If g-1<E_y<g, the portion from E toward P immediately enters int H.
If E_y=g, it still enters int H because P_y<7/10<37/50<=g, so
the segment moves down and left. These are actual B points and
again force an interior overlap. The remaining possibility is E_y>g.
Now the same actual B points P,E meet the signed-support barrier at
its included right endpoint E_x=h. This is the final contradiction.

All positions of the original V have been accounted for, including
arbitrarily large V_x: no upper A-port bound is required. The auxiliary
E is only an actual point of B. It never replaces an original force
application, a normal, or a shared mean in a caller's equations.

## 5. Exact reusable instances and preservation

For ell=1 and eta=5/12, the sum is 17/12 and
(17/12)^2-2=1/144>0. For ell=6/7 and eta=679/1200,

    6/7+679/1200-17/12=53/8400>0.

Both are exact continuous bounds with positive ell,eta and require
no angle subdivision or numerical certificate. The strict whole-A
height hypothesis supplies strictness even at the allowed closed
horizontal equality P_x=h-ell or lower crossing E_y=g-1.

The statement retains every actual orientation and physical mask of
B, all possible original contact owners, all means and all zero
coefficients in any literal caller. It supplies a general geometric
export and carries no automatic original fine-family or coarse-parent
closure credit.

This independent review creates only this new file. It changes no
source, actual square, force, normal, mean, physical mask, identifier,
ledger or count. No pose sample, angle grid, Lean compilation, CI,
workflow, git commit, metadata mutation or remote write was used.

# Independent full review: three near units have no common boundary neighbor

Date: October 27, 2026.

Reviewer: global_closure, independently of author c6_side.

**Verdict: ACCEPT without correction.**

## 1. Entire fresh source and exact scope

The complete source is

    GENERAL_THREE_NEAR_UNITS_COMMON_BOUNDARY_NEIGHBOR_EXCLUSION.md
    a4efde5817af8cc06faf4ca83a401f7926dafb0ed31686d6c72e14cd2d8485d7.

I independently read every line, reconstructed the complete continuous
half-lens optimization, and checked both original two-leaf diamond
role joins. This is a full fresh audit at the new pin. It does not
restore the historical dd5847fa bytes or inherit an acceptance solely
from that missing source.

The purely geometric conclusion uses actual center separation, actual
physical contact distances, the same-nine R>2 bound, and the actual
small disk. It needs no force, contact owner, circle weight, adjacency
among the three near units, or embedding assertion.

Its two original graph callers use the complete newly reviewed origin
source

    GENERAL_TWO_PRIVATE_LEAF_DIAMOND_OPEN_ORIGIN.md
    b6f062b700518677a3cea9e9ee2fbfadbde84c0413ea76ea83352fff98cc4520,

whose separate full independent acceptance was saved immediately
before this review. No changed-parent origin premise is inferred
from the point theorem itself.

## 2. Full near-point chart, including every sign

For E,F,A in closed D_q, q=29/40, with pairwise distances at least
one, collinearity is impossible because the extreme separation would
be at least two while 2q<2.

The chosen own coordinates leave the original disk center fixed.
Relabeling and horizontal reflection give E=(s-a,t), F=(s+a,t),
s>=0, a>=1/2, and A=(s+x,t+y) with y>0. Both endpoint containment
inequalities imply the stronger one
(s+a)^2+t^2<=q^2, hence a<=q and s<=q-a.

The crucial |x|<2a bound is complete:
|x|<=q+s<=2q-a<2a because 2q<3a. Thus the nearer of the two horizontal
endpoint distances is at most a. Since both full distances are at
least one, y>=sqrt(1-a^2)=b. Actual A containment also gives t+y<=q,
so t<=q-b. The full resulting interval has b>2/3.

No H/X contact or upper restriction a<=1/sqrt(2) was introduced.
Both signs of t remain throughout the proof.

## 3. Closed half-lens and both endpoint types

For C on the same closed side of EF as A, write
C=(s+z,t+w), w>=0. The two distance upper bounds are exactly
(a+|z|)^2+w^2<=2. Replacing z by |z| can only increase its norm because
s>=0.

For v=a+|z|, fixed-v convexity in w reduces the whole closed vertical
interval to w=0 or the curved endpoint sqrt(2-v^2). The w=0 expression
increases with v and gives the stated side endpoint.

On the curved boundary,
G(v)=(s-a)^2+t^2+2+2(s-a)v+2t*sqrt(2-v^2).
Here s-a<0. If t>=0, direct differentiation gives strict decrease.
If t<0, the exact second derivative
-4t/(2-v^2)^(3/2)>0 gives convexity. Continuity includes v=sqrt(2).
Thus only the top and side endpoints remain for every sign of t.

For a<=1/sqrt(2), the side endpoint is bounded by the triangle
inequality with delta=sqrt(2)-2a>=0, giving
sqrt(S)<=q+sqrt(2)-1<49/40.
For a>=1/sqrt(2), both horizontal quantities are nonnegative and
s+sqrt(2)-a<=s+a, giving S<=q^2.
Both arguments include their common equality threshold. This checks
the previously important a>1/sqrt(2) side domain and C-on-line case.

The top endpoint uses both independent inequalities
s^2+t^2<=q^2-a^2 and t<=q-b. Its reduction to
F(b)=q^2+2b^2+2(q-b)*sqrt(1+b^2) is valid even when q-b is negative.

I independently differentiated F and obtained exactly

    F'(b)=2[q*b-(sqrt(1+b^2)-b)^2]/sqrt(1+b^2).

The entire interval has b>2/3, so the squared reciprocal term is
less than 9/25 while q*b>29/60. Thus F is strictly increasing on the
whole continuous domain. At b=sqrt(3)/2, the two stated radical
comparisons give the strict value below 2651/1600<5/3.

The point theorem therefore includes all closed disk tangencies,
a=1/2, a=q, t=0, w=0, and both half-lens endpoint types. No sampling
or pose subdivision is a premise.

## 4. Physical boundary transfer and the three-side contradiction

Every actual unit meeting closed D_epsilon has center norm strictly
below epsilon+17/24<29/40. Distinct actual centers have separation
at least one by their disjoint open incircles. Actual unit contact
gives center distance at most sqrt(2).

An actual boundary unit has a physical circle corner, with no positive
weight requirement. Its center norm is at least R-1/sqrt(2)>31/24,
whose square exceeds 5/3 by 1/576. This contradicts the point theorem
on the same closed side of any near-center line.

A boundary center touching two near units must consequently lie on
the strict opposite side of their line from the third near center.
The boundary center cannot lie on that line.

If one boundary unit touched all three, each cyclic oriented edge
of their counterclockwise triangle would have negative determinant
against that center. The sum of those three expressions is identically
det(f-e,a-e)>0. I reconstructed the cancellation directly; the three
strict negative inequalities are impossible.

This proves the complete physical theorem without an embedding,
load, degree, radial-point or pairwise-near-contact premise.

## 5. Both complete original diamond roles

The separate full two-private-leaf origin theorem gives open H and
both genuine leaf roots meeting closed D_epsilon. They are three
distinct actual near units.

When H is a hub and both private tips carry leaves, the other hub K
is untouched, truly degree three, and physically boundary by the full
unloaded-hub exclusion. Its three original neighbors are exactly H
and the two actual decorated tips. The new geometric theorem applies
to this whole role without changing either true degree-three tip.

When H is a tip and the other tip and one private hub carry leaves,
the remaining hub K is again untouched and truly degree three. Its
original neighbors are exactly H and the two decorated roots. The
same full geometric theorem applies, preserving the decorated hub's
true degree four and the decorated tip's true degree three.

Every original Q0 mask, physical leaf mask and actual circle system
is retained. The other two root/leaf roles are not supplied with a
third common contact by assertion and remain outside these callers.
No whole C2.44.b2 claim follows from this source alone.

## 6. Exact independent checks and conclusion

The twelve independently evaluated exact values were

    q^2=841/1600;
    1-q^2-4/9=431/14400;
    3/2-2q=1/20;
    (q+1/2)^2=2401/1600;
    q^2+3/2+(53/20)q-229/100=2651/1600;
    29/60-9/25=37/300;
    (53/20)^2-7=9/400;
    21-(229/50)^2=59/2500;
    5/3-2651/1600=47/4800;
    (17/24)^2-1/2=1/576;
    1/60+17/24=29/40;
    (31/24)^2-5/3=1/576.

The complete fresh geometric source and both complete original
diamond-role joins are accepted without correction. Parent root
review and publication remain separate. No shared graph label,
ledger, force certificate, remote object or workflow changed.


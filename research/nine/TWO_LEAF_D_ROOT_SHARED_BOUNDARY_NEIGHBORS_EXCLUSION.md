# A D-leaf root cannot share all its boundary neighbors with a near-origin unit

Date: October 27, 2026.

**Status: accepted complete hand proof at its full stated original scope; root and separate independent full-source/scope reviews passed.**

Accepted reviews: REVIEW_D_ROOT_SHARED_BOUNDARY_NEIGHBORS_MIXED_BLOCKS_2026_10_27.md and
REVIEW_TWO_TRIANGLE_FOUR_BRIDGES_AND_OPPOSITE_D_ROOT_ROOT_2026_10_27.md.
Source pins in those reviews precede this acceptance-only header update. No central ledger or original checkbox changes here.

Retain all nine original physical unit squares and the common compatible
selected certificate in

    79/40<=R<=sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1,
    epsilon=max(d-1,0)<1/60,
    r=R-sqrt(2),       s=1-r.

Let H have a genuine positive D leaf L. Let K be a distinct actual
unit meeting the closed disk D_epsilon. H and K need not touch.
Suppose every other original positive neighbor T_i of H is a physical
boundary unit, distinct from K, and physically touches K. There is
at least one T_i. All their original positive H contacts and actual
application means remain.

**Theorem.** This entire configuration is impossible.

H keeps its true degree, one plus the number of T_i. K and every
T_i may have arbitrary true degrees and additional forces. The K-T_i
contacts need only be physical. The theorem uses H's full actual force
and origin-moment equations and no equation at another body. All circle
masks, individual zero weights, zero-stress contacts and remaining
occupied units are retained.

## 1. The real D root has a shallow top, and no boundary contact there

The genuine D chart is

    H=[-s,r] times [a-1,a],       0<a<1,
    O belongs to int H,

with the actual D leaf pointing east and its radial inner vertex
at (r,0). If epsilon=0, the distinct K contains O and overlaps H.
Otherwise epsilon>0. The actual K point in D_epsilon lies outside
int H. Reflect the vertical axis, if necessary, to obtain

    R>sqrt(17)/2,
    129/200<r<2/3,
    1/3<s<71/200<3/8,
    0<a<=epsilon<1/60.                                 (1)

These are exactly the physical bounds of Section 1 in
TWO_LEAF_D_ROOT_NEAR_ROOT_BOUNDARY_TRIANGLE_EXCLUSION.md. Their
derivation uses only the near K point, not H-K contact.

The complete physical lemma in that source's Section 2 says that
no boundary unit distinct from H,L can contain a point of

    [-s,r] times {a},          {r} times [0,a].          (2)

For precise scope, that proof uses only the actual D leaf, (1),
and the containing-circle inequalities. A boundary unit meeting
(2) would have a circle corner at angle less than pi/9 from the
east D direction and its center within another pi/12. This violates
the physical boundary-center separation greater than pi/5. It uses
no H-K edge, no normal on that pair, and no H force equation.

Consequently every actual outward H-to-T_i unit normal m_i satisfies

    (m_i)_y<=0:                                         (3)

a positive vertical component would expose a point on the shallow
top, including either upper vertex, which (2) forbids.

## 2. The actual full H force balance makes every other normal horizontal

The D root H is physically circle-clear because it contains O
openly and has diameter sqrt(2)<R. Its complete original equation is

    lambda e_x+sum_i mu_i m_i=0,
    lambda>0,        mu_i>0.                            (4)

No other original H force is omitted under the stated complete
neighbor list. The vertical component of the leaf term is zero,
and all components in (3) are nonpositive. Therefore

    (m_i)_y=0,          m_i=e_x or m_i=-e_x             (5)

for every actual edge. Thus each real application P_i is on the
corresponding right or left H side. All its actual side means,
including endpoints, remain.

Every such actual port has strictly negative height:

    (P_i)_y<0.                                         (6)

On the right side, nonnegative heights are excluded by (2).
On the left side, a nonnegative height is at most a, so

    |P_i|^2<=s^2+a^2<r^2.

This contradicts the physical boundary-point bound for T_i.
Thus (6) holds for all original ports.

## 3. A geometric separator exists even when H and K are disjoint

The two distinct convex squares H,K have disjoint open interiors.
Their elementary separating-axis theorem provides a unit vector n
directed from H toward K such that

    H subset {x:n.x<=h_H(n)},
    K subset {x:n.x>=h_H(n)}.                           (7)

A positive gap is permitted. This is an auxiliary geometric separator
only; it is not inserted into the physical stress and changes no
selected H force or normal.

Since O is in int H and K contains an actual x_K with norm at most
epsilon,

    0<h_H(n)<=n.x_K<=epsilon.

As in the exact support calculation of the earlier source,

    n_y>4/5,              |n_x|<1/20.                  (8)

Indeed n_y<=0 would give support greater than 1/3, whereas for
n_y>0 the support is r n_x+a n_y or s|n_x|+a n_y according to
the sign of n_x. No physical H-K contact is required for this
inequality or the support formulas.

## 4. Each sign of the separator contradicts a full original H equation

First suppose n_x<=0. Write n=(-t,k) with 0<=t<1/20 and k>4/5.
Equation (7) becomes

    K subset {-t x+k y>=ts+ka}.

The full left-side return cap in Section 3 of
TWO_LEAF_D_ROOT_NEAR_ROOT_BOUNDARY_TRIANGLE_EXCLUSION.md applies
to every T_i whose actual H normal is -e_x. Its hypotheses are
only that T_i has its real rightmost support x=-s, physically
touches K in the displayed half-plane, and obeys the original
circle containment. The proof does not use H-K contact or any
triangle-normal fact. It keeps the full tilted/side-mean chart and
puts every T_i point at squared norm less than

    17/4-15911/230400<R^2.

Such a T_i cannot be physically boundary. Hence every remaining
actual m_i in (5) must be +e_x. The horizontal component of the
unchanged force equation (4) is then lambda+sum_i mu_i>0.
This is impossible.

Now suppose n_x>0. Write n=(t,k) with the same bounds, so (7)
gives

    K subset {t x+k y>=tr+ka}.

The complete right-side return obstruction in Section 4 of the
same source applies to any actual right-side H port P_i. Its
height is negative by (6). Any actual point Y in T_i intersect K
would make the segment P_i-Y enter int H or cross the relative
interior of the original D diamond's lower-left side. The proof
uses the real unit diameter and the inequality t/k<1/8. It needs
neither H-K contact, a triangle support comparison, nor any T_i
force equation.

Thus no T_i can have normal +e_x. All actual m_i in (5) equal
-e_x. Retain their original P_i and their positive magnitudes.
The D leaf's application is radial and has origin moment zero.
H's unchanged complete origin-moment equation is therefore

    0=sum_i mu_i det(P_i,-e_x)
      =sum_i mu_i (P_i)_y<0,

by (6), another contradiction. This is the actual root torque,
not a weighted mean reassigned to a different contact.

Both separator signs are exhausted. Equations (4) and the original
origin moment exclude the whole domain without requiring H,K to
touch and without changing the true force degree of any body.

## 5. Exact original opposite-root C4 consequence

Use the actual C4 order

    A-B-C-D-A,

with a genuine D leaf at A and a genuine S leaf at C. The complete
original load cover forces both private B,D positively loaded,
with their true positive degree two retained. They physically touch
the circle. The actual S root C meets D_epsilon.

Apply the theorem with H=A, K=C, and T_1=B,T_2=D. Every other
positive neighbor of the true degree-three A is exactly one of
those boundary units. Each physically touches C through its
original positive C4 edge. The theorem does not add a physical or
positive A-C contact, and none is needed.

This excludes the entire unchanged original child

    M6.B4L2.C4.OPPOSITE.LBD.SD.

Exchanging the two actual opposite roots covers its reflected S/D
placement. Every original physical mask, individual zero-weight
endpoint, side mean, leaf slider, frame and all three arbitrary
completion squares remain. The all-D opposite-root family was
already excluded and is not counted again.

The SS opposite-root sibling and adjacent-root mixed families retain
their original obligations. In particular a near-root positive edge
at H would add a force not in the complete neighbor list of this
source; it must not be dropped to apply the theorem. No whole
attachment parent or coarse cell is asserted closed here.

No physical motion, new stress normal, reduced degree, coefficient
packet, numerical pose, secondary minimizer, Lean compilation, CI
or remote action is used.


# An orientation-free interior point from the two coordinate minima of a unit square

Date: October 26, 2026.

**Status: complete elementary hand candidate, pending fresh independent
review.** This gives a single exact radius obstruction for every square
orientation and every coordinate translation. It strengthens the
missing-quadrant containment estimate without an angle cutoff or
orientation subcases. It has no force, degree, mask or radius-window
premise.

## 1. The coordinate-minimum interior point

**Theorem 1.1.** Let T be any closed Euclidean unit square. In any
fixed orthonormal coordinate frame, put
\[
                         a=\min_T x,\qquad b=\min_T y.
\]
Then
\[
                               (a+1,b+1)\in T.
 \tag{1}
\]
If T is not parallel to the coordinate axes, this point lies in
the open interior of T. If T is parallel, it is the upper-right
corner of T.

**Proof.** The axis-parallel case is immediate. Otherwise T has a
unique lowest vertex Q. Label its two inward upward unit sides as
\[
                v=(-c,s),\qquad w=(s,c),\qquad
                 c,s>0,\quad c^2+s^2=1.
\]
No ordering of c,s is imposed. The leftmost vertex is Q+v.
The actual coordinate minima therefore give
\[
                 Q=(a+c,b),\qquad
                 T=Q+[0,1]v+[0,1]w.
 \tag{2}
\]

For the proposed point P=(a+1,b+1), its own coordinates relative
to Q in this actual orthonormal side frame are
\[
 \begin{aligned}
 U&=(P-Q)\cdot v=c^2-c+s=s-c(1-c),\\
 V&=(P-Q)\cdot w=c+s-cs.
 \end{aligned}
 \tag{3}
\]
They satisfy
\[
 \begin{aligned}
 U&=s\left(1-\frac{cs}{1+c}\right)>0,\\
 1-U&=c\left(1-\frac{cs}{1+s}\right)>0,\\
 V&>0,\qquad
 1-V=(1-c)(1-s)>0.
 \end{aligned}
 \tag{4}
\]
The first two identities use 1-c=s^2/(1+c) and
1-s=c^2/(1+s). Their brackets are strictly positive since
0<c,s<1. The V signs are immediate from those same strict
component bounds.

Thus 0<U,V<1, so P lies in T's open interior. This covers the
entire tilted orientation interval; its two axis-parallel limiting
frames were already handled directly. \(\square\)

Reflection of either coordinate axis gives the corresponding point
one unit inward from any chosen pair of perpendicular extreme
support lines. The coordinate frame may also be rotated arbitrarily.

## 2. A complete radius obstruction and its equality case

**Corollary 2.1.** If T is contained in the origin-centered closed
disk D_R, then its actual coordinate minima satisfy
\[
                         (a+1)^2+(b+1)^2\le R^2.
 \tag{5}
\]
If T is tilted relative to the coordinates, the inequality is strict.

Indeed Theorem 1.1 puts the stated point in T. In the tilted case
it is a strict convex combination of T's four distinct corners.
Strict convexity of the squared Euclidean norm gives
\[
 |P|^2<\sum_j\lambda_j|z_j|^2\le R^2,
        \qquad \lambda_j>0,\quad\sum_j\lambda_j=1.
\]
This proves the strict form for all real a,b, without a sign condition.

In particular, if T satisfies exact supports
\[
                         \max_T x=A,\qquad \min_T y=B,
\]
then reflection of the first coordinate gives
\[
                         (A-1)^2+(B+1)^2\le R^2,
 \tag{6}
\]
with strict inequality for every tilted frame. Thus equality in
(6) forces
\[
                         T=[A-1,A]\times[B,B+1].
 \tag{7}
\]
There is no bound on A or B and no radius interval in this statement.

## 3. Outward orthogonal half-planes

**Corollary 3.1.** Let a_0,b_0>=0. If an arbitrary unit T is
contained in
\[
                  \{x\ge a_0,\ y\ge b_0\}\cap D_R,
\]
then
\[
                         R^2\ge(a_0+1)^2+(b_0+1)^2.
 \tag{8}
\]
If equality holds, the unit is exactly
\[
                         T=[a_0,a_0+1]\times[b_0,b_0+1].
 \tag{9}
\]

To prove it, use the actual minima a>=a_0,b>=b_0 in (5).
Both squared terms are strictly increasing in their nonnegative
minimum coordinates. Equality in (8) therefore requires
a=a_0,b=b_0 and equality in (5), which by Theorem 1.1 forces
the axis-parallel square (9).

All half-plane contact types are allowed. The unit need not
initially touch either supplied support line; no contact point
or force mean is chosen.

## 4. Exact transfer to the missing-quadrant proof

The reviewed geometric L lemma in
SS_HUB_TIP_TWO_SHARED_TIP_PORTS_FREE_CENTRAL_EXCLUSION.md
gives an actual fourth unit with
\[
                          \max_T x=0,\qquad \min_T y=t.
\]
For every real t, (6) now directly gives
\[
                              R^2\ge1+(t+1)^2,
\]
strictly for any tilted T. If the existing neighboring boundary
unit already gives equality R^2=1+(t+1)^2, the fourth unit
is exactly [-1,0]x[t,t+1].

This strengthens that source's Lemma 3.1: its sufficient restriction
t>=0 and 2t<1+1/sqrt2 is unnecessary for the stated equality
rigidity. It also replaces the separate two-tilt corner comparisons
by the single actual interior point (-1,t+1). The already frozen
source and its independent review remain valid without any change.

| Existing application source | SHA256 |
| --- | --- |
| SS_HUB_TIP_TWO_SHARED_TIP_PORTS_FREE_CENTRAL_EXCLUSION.md | ecf6da01608b625eb3b357613856cb7df035930a8dba618663aca302922aa1f6 |
| REVIEW_SS_TWO_SHARED_TIP_FREE_CENTRAL_C6_FRESH_2026_10_26.md | 8d1163bccaf49b6a4421c1f6370c322de0e545b3e0cc9f56c9107b9f9f536088 |

The present elementary theorem has no external mathematical
prerequisite beyond the definition of a Euclidean unit square and
strict convexity of squared norm. The application paragraph uses
the exact already reviewed physical L conclusion only.

No force, degree, circle mask, shared mean, chosen normal, graph ID
or original domain was modified. The result by itself supplies no
whole-gate count. No numerical pose, angle grid, scalar coefficient
certificate, Lean invocation, CI workflow or remote mutation is used.

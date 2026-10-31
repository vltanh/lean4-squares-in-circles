# Independent review: connected D-leaf boundary-wall contact

Date: October 26, 2026.
Reviewer: separate global-closure agent.
Source reviewed: ROOTED_C5_AND_D_LEAF_BOUNDARY_WALL_CONTACT.md.
Direct prerequisite read in full: D_LEAF_PARALLEL_LEFT_EXCLUSION.md.

**Verdict: accept the complete geometric wall-contact theorem and its
stated connected-wall D-leaf corollary.** Neither theorem closes the
full D-leaf fan or rooted C5 parent; their other actual interface
directions remain outside this source's hypotheses.

## 1. Independence from the old triangle force equations

I checked that the new source uses only geometric sections of the
earlier parallel-left proof. It does not import that source's torque
equations, negative/positive resultant classification, or the b=c
force-balance contradiction. The new proof obtains all circle signs
directly from the actual wall vertex and excludes b=c together with
the full closed angular domain through one scalar inequality.

The radius condition2<=R<=sqrt(1105)/16 gives
1/3<s<=sqrt(2)-1<9/20 and Y>4/3. Its actual segment I has length one
and lies in -1<=y<=1; no root force or selected support owner is used
to infer this premise in the force-free theorem.

For a unique wall vertex with y>=0, I independently checked the
negative-y corner bounds. The lower vertex is bounded by (s+1)^2,
and the left vertex by (s+sqrt(2))^2. Both are strictly below R^2.
A zero-height circle vertex is excluded by |x|<=s+sqrt(2)<R. The
axis-aligned side case gives exactly [Y-1,Y] or [-Y,1-Y], each with
one strict sign. Thus the body-by-body physical sign statement includes
every original zero individual circle weight.

## 2. Side and vertex supports cover the entire physical domain

The side-support alternative follows from an arbitrary actual
separating normal. Ordered wall points force its vertical component
negative; a horizontal separating normal is impossible for two
positive-width squares sharing their right support. Its two nonzero
horizontal signs respectively contradict the support-span bound or
the opposite wall-vertex sign. The zero-horizontal case is exactly
the earlier force-free corner-positioned-square lemma. I read that
lemma's four-vertex calculation and strict1/120 and1/3 reserves.

For two unique wall vertices, reflection and body exchange correctly
permit b<=c. The section-difference slopes show that contact requires
Delta=a+bd/c<=1; theta<=psi with b<c would instead give Delta>1.
At b=c the same equation becomes Delta=2a. Both cases give the same
closed comparison domain

    0<=psi<=min(theta/2, pi/2-theta).

The circle-corner comparisons remain strict when d=1/2, so the old
strict-angle argument extends to b=c without any force premise. The
bounds -y_C>1/4 and exclusion of B's upper circle corner use only
the actual circle equations, s<9/20 and Delta<=1. Both farthest
corners are consequently the claimed unique left vertices. Substituting
their opposite physical signs gives the exact displayed contact
equation for Y_B+Y_C.

## 3. Independent scalar reconstruction

The lower-radius comparison in Section6 is valid because

    d/dR [R^2-(1+sqrt(2)-R+w)^2]=2(1+sqrt(2)+w)>0.

The function f(w)=sqrt(4-(sqrt(2)-1+w)^2) is strictly concave on
the full interval1<=w<=sqrt(2). Its endpoint comparison with
(57-29w)/20 is exact: at sqrt(2) the squared difference is
(4906sqrt(2)-6931)/400, with squared-integer reserve98911.
Concavity therefore puts the whole function strictly above that
affine lower bound.

I independently differentiated the combined expression

    F=29a+49b+49c+9d+20bd/c.

At fixed theta, b>=2dc gives
c F_psi >=9(1-d^2-d)>0 on0<=d<=1/2. The boundary branch
psi=theta/2 has the stated expression
29-18d^2+(98d+49)sqrt(1-d^2)+9d and positive derivative:
its derivative numerator is at least49/2, while the remaining
summand is at least-9. On the other branch, psi=pi/2-theta,
the expression reduces exactly to58a+98sqrt(1-a^2), increasing
for0<=a<=1/2. The two branch maxima coincide and equal
29+49sqrt(3). The strict final comparison to114 has squared
integer reserve22. Thus the exact contact equality is impossible
throughout the entire continuous orientation domain.

These inequalities require no sampled angle, omitted endpoint,
force-selected contact normal, or numerical coefficient certificate.

## 4. Original-component corollary and limits

A physical contact edge among the specified wall-neighbor bodies
preserves the strict physical circle sign. Connectivity therefore
gives one sign for the entire supplied collection. In the genuine
D-leaf application, every other positive circle load is explicitly
required to belong to that connected wall-neighbor collection, and
the actual D leaf contributes only a horizontal circle resultant.
The full unchanged component force sum cannot cancel the common
nonzero vertical sign. The arbitrary degree at its root is retained.

The corollary explicitly supplies R>2 using the accepted same-nine
measure theorem, and does not apply that lower bound to an isolated
smaller core. It preserves the actual whole root side I and every
physical corner with zero coefficient. It does not infer the common
left wall for an arbitrary oblique A interface.

No Lean compilation, CI, optimizer, pose sampling, or new finite
sign packet was used in this review. No unrelated old certificate
is retired by this acceptance.

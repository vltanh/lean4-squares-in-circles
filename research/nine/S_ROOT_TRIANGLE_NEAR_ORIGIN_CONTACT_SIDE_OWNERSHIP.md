# A triangle S-root's contact with a near-origin neighbor has a side owner

Date: October 26, 2026.

**Status: complete uniform hand reduction, pending fresh independent full
review.** This removes the variable shared-return exception for the
near-origin contact in the existing fixed-nonleaf S-root selector.
It uses the actual physical triangle and true root degree three,
without assigning either neighbor a smaller force equation.

## 1. Exact theorem and genuine physical scope

Work in the original radius interval, with
\[
 \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16},\qquad
 d=\sqrt{R^2-\tfrac14}-1,\qquad
 \epsilon=\max(d-1,0),\qquad
                    \frac9{10}<d<\frac{61}{60}.
\tag{1}
\]
Let B be the true degree-three root of one genuine radial S leaf L.
Its other actual positive neighbors are H,K. Assume:

* H meets the closed disk of radius epsilon about the original origin;
* K physically touches the containing circle;
* H and K physically touch one another.

The actual degrees and all additional forces of H,K are arbitrary.
K may have zero total circle load. All physical units remain.

**Theorem 1.1.** In the common compatible certificate, a singleton HB
contact cannot have a free vertex/vertex normal. It has a genuine side
owner. A positive-length HB contact retains its actual shared normal
and every original mean.

There is no singleton hypothesis on BK. If both nonleaf physical
contacts are singletons, the already reviewed
S_LEAF_ROOT_FIXED_NONLEAF_CONTACT_SELECTION.md applies. Its frozen
SHA256 is
\[
\texttt{499e6d42632a811bcb7bef6596b8585c11fbb5f59f36551d02fd05c080387a43}.
\]
The new proof below excludes a free HB together with the entire
positive-length shared BK family.

The proper-port input is the purely geometric Section 2 of
END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md, from accepted ref
26d9e3042b733ff0796876a4607a7d834f4b630a, Git blob
2437407a941e6fc5c3a617f312521f3d3e8e5732. Its exact local SHA256 is
\[
\texttt{20a845eff8bee3e9c533162df0b32ea96f9dd104a3cfec41efb3b0cf92d6e9cf}.
\]
It is a physical triangle lemma and needs no circle load or degree
assumption at B. No positive radial-concurrence sign is assumed.

## 2. Both units give the small actual HB support height

The genuine S leaf gives its actual root application \(de\) and
\(h_B(e)=d\). The root B meets the closed epsilon disk.

Here is the direct full-frame verification of that last fact. If e
is a root side axis, the actual leaf midpoint lies on that side,
and the unit contains \((d-1)e\), or contains the origin if
\(d\le1\). If the root is tilted, use its inward orthonormal
axes u,v at the leaf vertex, with
\(e=-a_0u-b_0v\), \(a_0,b_0>0\), \(a_0^2+b_0^2=1\).
The nearest-point distances in these axes are
\(\max(da_0-1,0)\), \(\max(db_0-1,0)\).
Since \(d<\sqrt2\), at most one is positive; each is at most
\(\max(d-1,0)=\epsilon\). The aligned mean endpoints are
included in the same conclusion.

For any actual normal n from B to H, let
\[
                       h=h_B(n)=\min_{z\in H}n\cdot z.
\]
The small-disk points of both actual units give
\[
                            -\epsilon\le h\le\epsilon,
                              \qquad \epsilon<1/60.
\tag{2}
\]
This concerns the original support line, not a selected support point.

## 3. The complete free/shared root chart

Suppose HB is free and BK is a positive-length shared side.
Rotate so the actual B-to-K normal is \(e_y\).
The side-owned unit-triangle theorem makes the actual B-to-H
normal have nonnegative vertical component. Its strict exposure
at a B vertex makes both components nonzero. Reflect horizontally
so
\[
                       n=(-u,v),\qquad u,v>0,\quad u^2+v^2=1.
\tag{3}
\]
Its actual B point is the upper-left vertex P.

B is circle-clear by the genuine leaf reduction. Its full actual
force equation has only the S leaf and these two nonleaf contacts.
The leaf vector must point strictly right and down. Therefore its
genuine radial S application is B's opposite lower-right vertex,
which we write
\[
                 p=(A,-b),\qquad A,b>0,\qquad A^2+b^2=d^2.
\tag{4}
\]
The entire root square and actual free point are
\[
                 B=[A-1,A]\times[-b,1-b],\qquad
                 P=(A-1,1-b).
\tag{5}
\]
With actual positive scalars \(\lambda,\mu,\nu\),
\[
                      \lambda(A,-b)+\mu(-u,v)+\nu e_y=0.
\tag{6}
\]
Consequently
\[
                 \mu u=\lambda A,\qquad
                 bu-Av>0,\qquad 0<\frac vu<\frac bA.
\tag{7}
\]
No force at H or K appears in or is discarded from this genuine B3
equation.

The two nonleaf lines are nonparallel. Their concurrence q lies on
the real radial leaf line by torque about q:
\[
                              q=t(A,-b),\qquad t\in\mathbb R.
\tag{8}
\]
The actual H-B-K physical triangle gives the proper relation
\[
                                  P=q+\ell n,\qquad\ell\ge0.
\tag{9}
\]
Multiply the first coordinate of \(q=P-\ell n\) by b and the
second by A, and add. Equations (8)--(9) give
\[
                              A-b+\ell(bu-Av)=0.
\tag{10}
\]
Using (7), we conclude
\[
                                  A\le b.
\tag{11}
\]
This is the only concurrence sign information needed. In particular,
the proof has not presumed \(t>0\) or q inside B.

## 4. The whole force-angle interval forces A below one tenth

The actual HB support height in (2) is
\[
                             h=u(1-A)+v(1-b).
\tag{12}
\]
We show that \(A\ge1/10\) would make \(h>1/60\), a contradiction.

By (4),(11),
\[
 A\le d/\sqrt2<\frac{61}{60}\frac{17}{24}
                 =\frac{1037}{1440}<1.
\tag{13}
\]
Write \(u=\cos\theta,v=\sin\theta\). Equation (7) puts the
actual angle in \(0<\theta<\arctan(b/A)\). On the entire closed
comparison interval the minimum of
\[
                         (1-A)\cos\theta+(1-b)\sin\theta
\]
occurs at an endpoint. If \(b\le1\), this positive function is
concave, so its minimum is at an endpoint. If \(b>1\), its
derivative is strictly negative there, with the same conclusion.
Thus
\[
                    h\ge
                \min\left\{1-A,\frac{A+b-d^2}{d}\right\}.
\tag{14}
\]
This is a whole-interval analytic bound, not an orientation sample.

The first endpoint exceeds \(403/1440>1/60\), by (13).
For the second, put \(s=A/d\). Under \(A\ge1/10\),
\[
                  \frac6{61}<s\le\frac1{\sqrt2}.
\]
The function \(s+\sqrt{1-s^2}\) increases on this full interval.
Therefore
\[
 \frac{A+b-d^2}{d}
    =s+\sqrt{1-s^2}-d
    >\frac{6+\sqrt{3685}}{61}-\frac{61}{60}
    >\frac{66}{61}-\frac{61}{60}
     =\frac{239}{3660}>\frac1{60}.
\tag{15}
\]
Here \(\sqrt{3685}>60\), and the last exact reserve is
\(89/1830\). Both endpoint values in (14) contradict (2).

We have proved
\[
                  0<A<\frac1{10},\qquad
                  b=\sqrt{d^2-A^2}>\sqrt{\frac45}>\frac89.
\tag{16}
\]
The last positive-square reserve is \(4/405\). The upper bound
\(b<61/60\) follows from (4).

## 5. Every actual shared-return displacement is impossible

Because BK is genuinely shared, the actual K has the same frame as B,
lies above it, and has the complete tangential displacement chart
\[
             K=[A-1+s,A+s]\times[1-b,2-b],\qquad -1<s<1.
\tag{17}
\]
The whole interval is retained; the actual shared-force mean may be
anywhere on its actual overlap. We inspect all three signs of s.

### 5.1. Negative displacement

If \(-1<s<0\), the actual point P is in the relative interior
of K's bottom side. Locally K occupies the upper half-plane,
and B occupies the lower-right quadrant. A third unit H at P
could only occupy the exact lower-left quadrant. Its inward axes
would include \(-e_y\).

But P is the actual minimum-n support of H, while
\(n\cdot(-e_y)=-v<0\). A positive inward step along that H axis
would have n-projection below its asserted minimum. This contradicts
the actual strict HB normal (3).

### 5.2. Zero displacement

If \(s=0\), K and B occupy respectively the upper-right and
lower-right local quadrants at P. The entire tangent cone of H
must lie in the left half-plane. Both inward H axes therefore have
nonpositive horizontal components, and its full unit square satisfies
\[
                             \max_H x\le A-1<-9/10.
\tag{18}
\]
This is incompatible with H meeting the epsilon disk, since
\(\epsilon<1/60\). The equality displacement has not been discarded
as a limiting case.

### 5.3. Positive displacement

If \(0<s<1\), equations (16)--(17) put every K point in
\[
                            |x|<11/10,\qquad |y|<10/9.
\tag{19}
\]
For the first, its lower abscissa is greater than \(-1\), and
its upper one is below \(A+1<11/10\).
For the second, its lower height exceeds \(-1/60\), while the
upper height is below \(2-8/9=10/9\).

Thus every actual K corner has
\[
                    |z|^2<
                    \left(\frac{11}{10}\right)^2+
                    \left(\frac{10}{9}\right)^2
                     =\frac{19801}{8100}
                     <\left(\frac{79}{40}\right)^2.
\tag{20}
\]
The final exact reserve is \(37741/25920>0\).
K would be strictly circle-clear throughout the original radius
window, contradicting its actual physical circle contact.

The three signs exhaust every original shared displacement.
There is no free HB / shared BK member left.

## 6. Full theorem, compatible selection and applications

If BK is a singleton instead, the already reviewed fixed-nonleaf
S-root selector excludes the free HB before extraction. Its near-origin
H and physical boundary K premises are exactly those in Section 1;
it needs no degree or positive-circle-weight hypothesis at either
neighbor. If BK is shared, Sections 2--5 give the new whole-domain
contradiction using its original variable mean.

Hence every singleton HB has a genuine side owner, proving
Theorem 1.1. No additional selection condition is needed beyond the
previous common finite selection. The shared-return exclusion is
geometric and uses the actual original force direction throughout.

For the remaining S/S hub-tip diamond, take B to be its true-degree-three
S-leaf tip root, H its genuine S-leaf hub root, and K its boundary
hub. H meets the epsilon disk by the same genuine-root fact in
Section 2; H,K physically touch through the actual central edge.
Therefore the complete HB interface, across all original BK feature
types, has either a genuine positive-length shared side or a singleton
side owner. A free HB contact is excluded for the whole original
\[
                     \texttt{M6.B4L2.DIAMOND.HUB\_TIP.LKC.SS}
\]
domain, with H4 and K3 unchanged.

If HB is a singleton, the earlier selector also gives a side owner
on a singleton BK. A free BK with a shared HB remains outside this
new theorem. Other owner patterns and the entire original gate are
not declared closed here.

The local conclusion also applies whenever the stated triangle,
genuine S-root and near-origin-neighbor hypotheses occur at arbitrary
neighbor degrees. All original completion units, physical masks,
individual zero weights, side means and displacement endpoints
remain. No coefficient certificate, pose sample, force deletion,
post-extraction normal change, Lean compilation or CI is used.


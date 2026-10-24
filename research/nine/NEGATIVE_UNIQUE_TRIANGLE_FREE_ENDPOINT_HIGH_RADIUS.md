# A negative unique endpoint of a physical triangle has no free hub contact at high radius

**Status: complete whole-domain hand implication; root and separate independent
full hand audits passed.** Work in
\[
 \frac{\sqrt{17}}2\le R\le\frac{\sqrt{1105}}{16}.
\tag{1}
\]
Let A,H,K be three actual interior-disjoint unit squares in the fixed
origin-centered disk, pairwise physically touching. A and K physically
touch the circle. A has one physical circle corner z and exact positive
degree two, with positive edges AH and AK. Its actual circle weight
is positive. H and K may have arbitrary additional positive forces
and arbitrary physical contacts. Assume
\[
                         c_H\cdot z<0 .
\tag{2}
\]
All other physical packing squares remain arbitrary and retained.

**Theorem.** In the common compatible fixed-tip selected certificate,
the actual AH contact cannot be a free point-only vertex/vertex contact.
No extra normal selection is needed beyond the existing finite
fixed-tip preselection. All genuine shared AK means and all physical
circle masks of K are included. The theorem makes no force-balance or
degree-two assumption at H or K.

## 1. The exact point and singleton alternative

Suppose AH is free, with actual point Q and normal n pointing from
H to A. The complete geometric theorem
NEGATIVE_UNIQUE_NEIGHBOR_INNER_CONTACT.md applies to (2). It puts every
actual H/A point on the two inner faces of A, strictly less than 5/38
from its corner opposite z; both outward side coordinates of z exceed
19/20. Since the free point is an A vertex, it must be precisely
\[
                              Q=z-u-v,
\tag{3}
\]
where u,v are A's inward unit side directions at Q.

If AK is a singleton, both A applications are fixed physical points.
GENERAL_FIXED_TIP_NORMAL_SELECTION.md removes the free AH normal,
apart from its coincident radial-D exception. That exception is
impossible here: a shared point of two circle-touching units has norm
strictly greater than R-sqrt(2), whereas the coincident radial-D inner
point has exactly that norm. This is the complete local argument in
FAN_NON_HUB_OWNED_ENDPOINT_EXCLUSION.md, Section1. It uses only A's
true degree-two equation and K's physical circle contact.

We therefore keep the entire remaining case in which AK is a genuine
positive-length shared side, with its full actual mean.

## 2. Complete shared-side chart without an opposite endpoint premise

The local owned-normal triangle theorem makes the shared AK side
incident to Q. Choose an oriented orthonormal coordinate frame along
A's sides, with origin still at the true circle center, so that
\[
 \begin{split}
 A&=Q+[0,1]e_x+[0,1]e_y,\\
 K&=Q+[t,t+1]e_x+[-1,0]e_y,\qquad -1<t<1,\\
 n&=(n_x,n_y),\qquad n_x,n_y>0 .
 \end{split}
\tag{4}
\]
The reflection choosing which incident side is horizontal changes no
circle origin or physical mean. The actual AK application is
\(Q+\tau e_x\), in the actual side overlap.

The endpoint-only proof in FAN_NON_HUB_OWNED_ENDPOINT_EXCLUSION.md,
Sections2.1--2.2, applies with no other endpoint or root-degree premise.
For clarity, its entire content needed here is recalled.

If t<0, K has a half-plane tangent sector at Q, A a quadrant and H
another quadrant. Their nonoverlapping interiors force those sectors
to fill the turn, so H and A share a positive side segment. This
contradicts the free point-only premise. If t=0, the two aligned
boundary squares have equal farthest horizontal corner contribution.
Their circle equality forces Q_y=0. The actual positive A force then
gives \(Q_x+1=\sqrt{R^2-1}>1\), while torque about Q has negative left
side and nonnegative right side, again impossible.

Thus
\[
                              0<t<1,\qquad t\le\tau\le1 .
\tag{5}
\]
Write the actual unique circle force as \(F_A=kz\), \(k>0\), and
let \(\mu,\gamma>0\) be the AH and AK magnitudes. The genuine A equations
are
\[
 F_A=\mu(n_x,n_y)+\gamma e_y,\qquad
 k(z_y-z_x)=\gamma\tau.
\tag{6}
\]
Both components of its actual force are positive, so z is the corner
\(Q+e_x+e_y\). Equations (5)--(6) give
\[
 z=(b,a),\qquad a>b>\frac{19}{20},\qquad a^2+b^2=R^2,
 \qquad Q=(b-1,a-1),
\tag{7}
\]
and
\[
 \frac{n_y}{n_x}
    =\frac{a-(a-b)/\tau}{b}\le1 .
\tag{8}
\]
Every shared-side mean endpoint is retained. No equation of K or H
was used.

## 3. The real H/K contact bounds H's entire frame

H has Q as a strict support vertex for n. Since K lies strictly to
the right of Q in the x coordinate by (5), physical H/K contact
requires H to have points with x>Q_x. One inward side of H at Q
therefore has positive first coordinate. Its strict inward scalar
product with n, and orthogonality, give the full frame
\[
 H=Q+[0,1]w+[0,1]v,\qquad
 w=(c,-d),\quad v=(-d,-c),\quad
 c,d>0,\quad c^2+d^2=1 .
\tag{9}
\]
The other possible orthogonal direction would have both coordinates
positive and violate strict support. Moreover
\[
                    n_xc-n_yd<0,\qquad c<d
\tag{10}
\]
by (8). Its maximum first coordinate is exactly \(Q_x+c\).
All K points have first coordinate at least \(Q_x+t\), so the actual
H/K contact implies
\[
                                  c\ge t.
\tag{11}
\]
The contact may have any physical owner and need not carry a positive
multiplier for this step.

We now prove \(t>1/2\) on the entire domain. From (7) and the upper
radius bound,
\[
 a^2<\frac{1105}{256}-\left(\frac{19}{20}\right)^2
                      <\left(\frac{19}{10}\right)^2,
 \qquad \frac{a}{b}<2.
\tag{12}
\]
In particular \(1<a<2\). The aligned K in (4) has coordinates
\[
                   [b-1+t,b+t]\times[a-2,a-1].
\]
Its farthest horizontal coordinate is b+t, because b>19/20 and t>0.
Put
\[
                     m(a)=\max(2-a,a-1).
\]
K physically touches the circle, including any physical two-corner
case, so its exact maximum corner norm gives
\[
                  (b+t)^2+m(a)^2=R^2,\qquad
             t=\sqrt{R^2-m(a)^2}-\sqrt{R^2-a^2}.
\tag{13}
\]

At fixed R the right side increases strictly with a for
\(R/\sqrt2\le a<19/10\) in the real domain of (13). On a<=3/2,
its derivative is
\[
  \frac{2-a}{\sqrt{R^2-(2-a)^2}}
             +\frac{a}{\sqrt{R^2-a^2}}>0.
\]
On a>=3/2, the derivative is
\[
  \frac{a}{\sqrt{R^2-a^2}}
       -\frac{a-1}{\sqrt{R^2-(a-1)^2}}>0,
\]
because \(x/\sqrt{R^2-x^2}\) is strictly increasing for \(0<x<R\).
The two pieces agree at a=3/2. All intervening radicands are positive;
in particular m(a)<1 on this comparison interval.

Since \(R/\sqrt2<3/2\), (13) therefore gives
\[
 t\ge
 \sqrt{\frac{R^2}{2}+2\sqrt2R-4}-\frac{R}{\sqrt2}
                       >\frac12.
\tag{14}
\]
For the strict last comparison, both sides after moving R/sqrt(2)
are positive, and squaring reduces it exactly to
\[
                      \frac{3R}{\sqrt2}>\frac{17}{4}.
\]
At the lower endpoint (1), this is \(3\sqrt{34}>17\), whose square
is the exact inequality 306>289. It holds throughout (1).
Equations (11),(14) prove
\[
                              \frac12<c<d.
\tag{15}
\]

## 4. The actual center has strictly positive projection

The real center of the physical H in (9) is
\[
 c_H=\left(b-1+\frac{c-d}{2},
              a-1-\frac{c+d}{2}\right).
\]
Consequently
\[
 c_H\cdot z
   =R^2-a-b-\frac12\bigl((a+b)d+(a-b)c\bigr).
\tag{16}
\]

For fixed a,b satisfying (12), the bracket, as a function of c with
\(d=\sqrt{1-c^2}\), strictly decreases for c>=1/2.
Indeed its derivative is
\[
 (a-b)-(a+b)\frac{c}{\sqrt{1-c^2}}
 \le(a-b)-\frac{a+b}{\sqrt3}<0.
\]
The last comparison follows from a/b<2, since
\((a-b)/(a+b)<1/3<1/\sqrt3\).
Thus (15)--(16) imply
\[
 \begin{split}
 c_H\cdot z
 &>R^2-\frac{5+\sqrt3}{4}a-\frac{3+\sqrt3}{4}b\\
 &\ge R^2-R\sqrt{\frac52+\sqrt3}\\
 &>0 .
 \end{split}
\tag{17}
\]
The middle inequality is Cauchy--Schwarz and
\[
 \left(\frac{5+\sqrt3}{4}\right)^2+
 \left(\frac{3+\sqrt3}{4}\right)^2=\frac52+\sqrt3.
\]
The final strict comparison holds at every radius in (1), because
\[
                     \frac52+\sqrt3<\frac{17}{4}\le R^2,
 \qquad \sqrt3<\frac74.
\]
This contradicts the actual negative projection (2).

## 5. Full certificate and attachment scope

The singleton and positive-length shared alternatives exhaust AK.
The singleton case uses the existing finite fixed-tip preselection;
the shared case is a direct physical force/torque and containment
contradiction. It never changes a normal after certificate extraction
and never freezes an original mean. All possible physical assignments
were already prelisted, as required by that selection theorem.

In the triangle/diamond-hub attachment, the true negative endpoint A
has exact degree two, H has degree five and the other hub K degree
three. All three physical edges HA,AK,KH exist, and K is loaded.
Therefore this theorem excludes the **entire free HA domain for
R^2>=17/4**, for every physical K/B mask and all original weights.
The additional H/X/Y petal forces and K/B forces are retained.

Below R^2=17/4 this theorem makes no shared-interface exclusion.
Above that threshold, the remaining AH side-owner and genuine shared
AH domains remain separate. No whole diamond-hub mask, graph/load
orbit, six-body cell, or equality classification is declared closed.
Every completion square remains. No canonical motion, numerical
sample, Lean compilation or CI is used.

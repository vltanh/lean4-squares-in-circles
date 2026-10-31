# Every tilted root-axis right-circle top-vertex family has an empty leaf pocket

Date: October 26, 2026.

**Status: accepted reconstructed complete proof**, after the fresh
full-source and physical-routing review
REVIEW_S_C5_TILTED_ALL_TOP_VERTEX_LEAF_ROOT_RECOVERY_2026_10_26.md.
The earlier workspace copy was lost; this review concerns the present text.

The theorem covers both original channel forms \(t=0,t>0\), the full
original root mean, and both surviving physical right-circle masks.
No parameter subdivision or computational sign certificate is used.

## 1. Entire original chart and actual circle comparison

Keep the original component \(A-B-V-C-U-A\), genuine S leaf L at the
true degree-three root A, all nine physical units, original forces and
normals, every application mean, both transmitter sliders, and every
physical circle corner and individual weight.

Use the global leaf frame and the reflected root frame, respectively:
\[
\begin{gathered}
 L=[d,d+1]\times[-1/2,1/2],\quad p_0=(d,0),\\
 d=1+\delta,\quad0<\delta<1/60,\quad
 R^2=(d+1)^2+1/4\le1105/256,\\
 f_1=(-a,-b),\quad f_2=(-b,a),\quad a^2+b^2=1,\quad
 a>59/61,\quad0<b<16/61,\\
 D=da,\quad h=db,\quad H=1-h,\quad
 D\ge1-\delta,\quad h^2\le4\delta,\quad0<h<13/50,\\
 A=[D-1,D]\times[-H,h],\quad F=p_{AB}=(q,-H),\quad q=D-Z>0.
\end{gathered}
\tag{1}
\]
The reflected root basis is \((a,b),(b,-a)\). The original direct
normal is \(m=f_2\), and \(Z\in[0,1]\) is its actual root mean. For
\(t=0\) both linked root means remain.

The actual B and its surviving physical circle feature are
\[
 e=(k,-l),\quad w=(-l,-k),\quad k,l>0,\quad k^2+l^2=1,\qquad
 B=F+[0,1]e+[0,1]w.
\tag{2}
\]
The circle is either the unique adjacent corner \(z=F+e\), or the
radial right face containing \(F+e,F+e+w\). The complete original
feature cover is applied before using the necessary inequalities
\[
 ql-Hk\ge1/2,\qquad q>1/2,\qquad q^2+H^2\ge d^2+1/4.
\tag{3}
\]
The first and third comparisons are weak for the physical radial
face and strict for the unique mask.

## 2. One fixed point lies inside every actual B

Put
\[
 \kappa=\sqrt{21}/4,\qquad p_*=(1/2,\kappa)
\]
in global coordinates. This is on the circle of radius \(5/4\).
Its reflected root coordinates are
\[
 (A_*,-B_*),\qquad
 A_*=a/2+b\kappa,\quad B_*=a\kappa-b/2.
\tag{4}
\]
Since \(h>b/2,\ a>59/61,\ \kappa>9/8\),
\[
 B_*-H=a\kappa-b/2-1+h>
 (59/61)(9/8)-1=\frac{43}{488}>0.
\tag{5}
\]
The last inequality of (3) and \(A_*^2=1/4+(17/16)b^2+ab\kappa\)
give
\[
q^2-A_*^2\ge d^2-1+2h-h^2-\frac{17}{16}b^2-ab\kappa.
\]
Here \(d^2-1>h^2/2,\ b<h,\ a<1\). Therefore
\[
 q^2-A_*^2>
 h\left(2-\kappa-\frac{25}{16}h\right)>
 h\left(2-\kappa-\frac{29}{16}h\right)>\frac7{20}h>0.
\tag{6}
\]
For the last comparison use \(\kappa<23/20,\ h<13/50\); the remaining
rational reserve is \(23/800\). Hence \(q>A_*\).

We now prove the whole-domain comparison
\[
                             A_*k+B_*l>d.
\tag{7}
\]
First \(k<3/5\). Otherwise (3), \(q\le D<61/60\) and \(H>37/50\)
would give
\[
 ql-Hk<
 (61/60)(4/5)-(37/50)(3/5)=277/750<1/2.
\]
Throughout,
\[
 A_*>12/25,\quad B_*>19/20,\quad
 1-a=\frac{h^2}{d^2(1+a)}<\frac{61}{120}h^2,
\]
and the bound \(\kappa>8/7\) gives
\[
             B_*>\frac87\left(1-\frac{61}{120}h^2\right)-\frac h2.
\tag{8}
\]

If \(h\le1/5\), then
\[
 B_*-d>
 \frac17-\frac1{60}-\frac1{10}-\frac{61}{2625}
 =\frac{31}{10500}>0.
\]
The positive angular sum \(A_*\sin\theta+B_*\cos\theta\) is concave
for \((k,l)=(\sin\theta,\cos\theta)\). Its minimum on \(0\le k\le3/5\)
is at an endpoint. At \(k=3/5,l=4/5\), its value is greater than
\[
 (3/5)(12/25)+(4/5)(19/20)=131/125>61/60>d,
\]
whose rational gap is \(47/1500\). This proves (7) on this whole range.

If \(1/5\le h<13/50\), the actual circle equation and \(q\le D\) give
\[
 Dk+(1-h)l\ge d-\frac38+h,\qquad
 Dk\ge\delta+2h-\frac38.
\]
As \(D\le1+\delta\) and \(0<2h-3/8<1\), it follows that
\[
                              k>2h-\frac38.
\tag{9}
\]
Here \(b>12/61\), so
\[
 A_*>43/61,\qquad B_*<391/366,\qquad
 A_*-B_*/3>383/1098>1/3.
\]
The second comparison uses \(\kappa<7/6\). Positive squaring on
\(0\le k\le3/5\) gives \(l\ge1-k/3\). Consequently (8)--(9) imply
\[
 A_*k+B_*l-d>
 \frac1{840}+\frac h6-\frac{61}{105}h^2.
\tag{10}
\]
This concave quadratic has positive endpoint values
\[
        \frac{79}{7000}\quad(h=1/5),\qquad
        \frac{919}{175000}\quad(h=13/50).
\]
Thus (7) is proved on the entire domain.

The two own coordinates of \(p_*-F\) are
\[
 \xi=k(A_*-q)+l(B_*-H),\qquad
 \eta=l(q-A_*)+k(B_*-H).
\tag{11}
\]
Equations (5)--(6) give \(\eta>0\). The actual circle identity and
(3) give
\[
 qk+Hl=(R^2-q^2-H^2-1)/2\le d.
\]
Hence (7) gives \(\xi=A_*k+B_*l-(qk+Hl)>0\). Finally
\[
\begin{split}
 |p_*-F|^2
 &=(q-A_*)^2+(B_*-H)^2\\
 &< (61/60-12/25)^2+(23/20-37/50)^2
 <61/100<1.
\end{split}
\tag{12}
\]
Both positive own coordinates are less than one, proving
\[
                               p_*\in B^\circ.
\tag{13}
\]

## 3. The complete original leaf-side pocket lies in a cap of height greater than one half

The global coordinates satisfy
\[
 F_x=\frac12+a(q-A_*)+b(B_*-H)>\frac12,\qquad
 F_y=a-bZ\in[a-b,a],\qquad a-b>43/61>1/2.
\tag{14}
\]
The actual adjacent circle corner \(z=F+e\) therefore satisfies
\[
                 z_x>F_x-b>1/2-b>0,\qquad z_y>F_y>1/2.
\]
The occupied path
\[
 (d+1,1/2),\ (d,1/2),\ p_0,\ F,\ z
\tag{15}
\]
runs respectively through L, A and B. Its successive nonzero
segments are separated by their actual support sides. It is the
original first-quadrant crosscut; a zero-length endpoint segment may
be deleted. Both C circle corners are outside the first quadrant:
its radial axis is southwest and each of the two corners has a
negative global coordinate. Thus no C spoke is inserted in the
selected outer arc of (15).

The positive contact embedding and occupied-path homotopy put the
actual L-A-B pocket inside the bounded side of (15). A second physical
circle corner of radial B may subdivide that containing side; equality
with the whole bounded side is not needed. The compact-interior
argument retains tangencies and any extra zero-selected-weight
contacts, which can only subdivide the containing region.

The chord normal
\[
                            N=-f_1+Zf_2
\]
has positive global components \(a-bZ,b+aZ\), and
\[
                  N\cdot p_0=N\cdot F=D-hZ.
\]
The other vertices in (15) lie on its outward side. On the B segment
this follows from \(N\cdot e=k+Zl>0\); on the leaf segments it follows
from the positive global components. The first-quadrant outer arc
also lies on that side, since its N projection has its minimum at an
endpoint. Every whole extra in the pocket therefore lies beyond a
line at distance greater than
\[
 \frac{1-1/60-4/15}{\sqrt2}
 =\frac{43/60}{\sqrt2}>\frac12.
\tag{16}
\]
Its center norm is greater than one.

## 4. The actual free inner-circle interval is too short for one extra

ANNULAR_CENTER_ARC_BUDGET.md gives every such whole extra a connected
open arc on the circle of radius \(5/4\), of length greater than
\(\pi/4\), containing its center direction.

The actual leaf blocks the centered closed arc whose upper endpoint
is at \(\gamma=\arcsin(2/5)\). The actual B is wholly above the x-axis:
\[
                    \min_{z'\in B}(z')_y\ge F_y-b>a-2b>27/61.
\]
Its center has norm at least \(R-1/\sqrt2>1\), so its own circle
intersection is connected. It contains the interior point (13), at
angle \(\pi/2-\gamma\).

Here is an explicit exclusion of a possible second free arc. The
containing side of (15) and its selected outer arc lies in the first
quadrant. Let a point of the inner circle in that quadrant be outside
the occupied core and have angle greater than
\(\theta_*=\pi/2-\gamma\). Since B's blocked interval is connected
and contains \(\theta_*\), the point is above that entire blocked
interval. Increasing its angle to \(\pi/2\) therefore avoids B.
Along this inner-circle path the height is at least
\(\sqrt{21}/4>1\), whereas all leaf and root segments of (15) have
height at most \(a<1\) (and at most \(1/2\) on L). Thus the path
avoids the whole crosscut. From \((0,5/4)\), the upward ray on
\(x=0\) avoids the positive-x Jordan boundary of the containing
region and escapes that region. The initial point was therefore
outside the containing side, as well. The compact-interior argument
retains all actual touching endpoints.

Below \(\gamma\) the inner circle is blocked by L. The actual
crosscut (15) consequently routes an extra's entire connected open
inner-circle arc into the same consecutive free interval between the
leaf and B blocked arcs. That interval is contained in
\[
                          (\gamma,\pi/2-\gamma).
\]
Its length is less than \(\pi/4\), because
\(\arcsin(2/5)>\pi/8\). This contradicts the required open arc length.
Thus the entire original pocket is empty:
\[
                              \boxed{n_{LB}=0.}
\]

The proof uses no equality \(h^2=4\delta\), so includes both original
channel forms. It retains both physical B masks and individual radial
weights, all means, sliders and all nine physical squares. No actual
extra or terminal is moved in this proof.

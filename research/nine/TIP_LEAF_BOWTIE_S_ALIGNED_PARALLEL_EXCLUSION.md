# An aligned S leaf at a bowtie tip: the entire parallel wall is impossible

**Status: complete whole-interface hand exclusion; root and separate
independent full hand audits passed.** Work in
\[
 \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16},\qquad
 D=\sqrt{R^2-\frac14}-1,\quad \delta=D-1,\quad r=R-\sqrt2.
\tag{1}
\]
The exact positive graph is H–A–B–H, H–C–E–H, and A–L.
The radial S leaf L points east, and its aligned articulation is
\[
              A=[\delta,\delta+1]\times[\ell,\ell+1],
                           \qquad -1\le\ell\le0.
\tag{2}
\]
A has exact degree three, H degree four, and B,C,E degree two.
All three further physical units remain present.

**Theorem.** The two positive triangle reactions at A cannot be
parallel. Together with
TIP_LEAF_BOWTIE_S_ALIGNED_NONPARALLEL_EXCLUSION.md, this excludes
the entire aligned S-leaf alternative, including every actual
side mean, circle mask and contact owner.

## 1. The actual wall domain and the two genuine resultants

Opposite parallel triangle normals would put B,H beyond opposite
A supports, so they could not touch. The two normals therefore
have the same direction, and A's force balance makes it \(-e_x\).
Write the actual applications and positive magnitudes as
\[
       P=(\delta,y)\in A\cap B,\quad
       Q=(\delta,z)\in A\cap H,\qquad \mu,\nu>0.
\tag{3}
\]
These are the actual weighted means for shared sides. Both whole
units B,H lie in \(x\le\delta\), each attaining that support.
The true A torque equation is
\[
                              \mu y+\nu z=0.
\tag{4}
\]

The unit-transmitter obstruction makes B,C,E loaded: each has
exact degree two and physically touching neighbors. H is physically
clear because H,C,E cannot be a boundary triangle; A is clear by
its actual radial leaf.

The window gives
\[
          -\frac9{100}<\delta<\frac1{60},\qquad r>\frac{14}{25}.
\tag{5}
\]
Every point of a boundary unit has norm at least r. In particular
\(\delta^2+y^2\ge r^2\), so \(y\ne0\). Reflect vertically to make
\(y>0\), and put \(z=-w\). Then
\[
                         w>0,\qquad y+w\le1.
\tag{6}
\]
When \(\delta\ge0\), also \(R\ge\sqrt{17}/2>103/50\), hence
\[
       r>\frac{129}{200},\qquad
       y>\frac{16}{25},\qquad 0<w<\frac9{25},\qquad |Q|<r.
\tag{7}
\]
The inequalities use \(\sqrt2<283/200\) and
\((129/200)^2-1/3600>(16/25)^2\).

Let g be the B-to-H unit normal, T its actual application, and
\(\gamma>0\) its magnitude. It is not horizontal: a positive-width
unit with maximum x equal to \(\delta\) cannot lie strictly to
the right of B, or wholly to the left of B's minimum x while
still attaining \(x=\delta\).

The nonparallel proper-concurrence calculation for a loaded tip
therefore applies to B. This is the general-neighbor part of
TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md, Lemma 2.1; its additional
boundary-neighbor hypothesis is used only to establish
nonparallelism, which we have established directly. The actual
force equation
\[
                             F_B=-\mu e_x-\gamma g
\tag{8}
\]
has proper radial concurrence on the horizontal line through P.
That concurrence has height \(y>0\) and is a positive multiple
of \(F_B\). Thus
\[
                                  g_y<0.
\tag{9}
\]
No assertion that a radial two-corner concurrence lies inside B
is needed.

Keep the entire other petal, and write \(M=F_C+F_E\). H's genuine
degree-four equation and the two true petal-tip moment equations
give
\[
                  M=-\nu e_x+\gamma g,\qquad M_y<0.
\tag{10}
\]
The pure physical-triangle behind-ports lemma at H in triangle
H,A,B puts its intersection at
\[
                              q_H=Q-\alpha e_x,\qquad \alpha\ge0.
\tag{11}
\]
The complete moment equation gives \(\det(q_H,M)=0\). Since
\((q_H)_y=-w<0\) and \(M_y<0\), \(q_H\) is a strictly positive
multiple of M.

Two whole end-triangle inputs will be used at H:
\[
                             c_H\cdot M>0,
\tag{12}
\]
from BOWTIE_CELL_CLOSED.md, Section 2, and the proper-root and
maximizing-port statements of END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md.
Both allow arbitrary additional positive forces at H and retain
every physical C/E mask and actual mean. In the nonparallel C/E
interface its intersection is \(q_0=-tM\), \(t>0\), and each
actual port is
\[
                         p=q_0+\lambda n,\qquad\lambda\ge0.
\tag{13}
\]
The both-H-owned perpendicular interface is already excluded by
BOWTIE_PERPENDICULAR_CONTACT_EXCLUSION.md. Every other nonparallel
interface has an actual port maximizing \(M\cdot x\) on H.

## 2. Two elementary complete root-port consequences

These consequences concern the actual C/E petal, so its two tips
are loaded degree-two bodies throughout.

First, if a side-axis coordinate of H has minimum value \(q\ge0\)
and the corresponding component of M is positive, both actual
petal ports lie on its maximum side. For a nonparallel interface,
the same coordinate of \(q_0\) is negative. A minimum-side vertex
has outward normal component nonpositive and cannot satisfy
(13); an H-owned transverse axis would place its actual mean at
the negative \(q_0\) coordinate, outside H. All remaining features
belong to the maximum side. For a parallel interface, the common
normal is \(M/|M|\), so the conclusion is immediate.

Second, if M is exactly a side axis of H, both actual petal ports
are on its maximizing side. For nonparallel root forces, an
H-owned axis parallel to M would force the other normal parallel
by transverse balance. An H-owned transverse axis is impossible:
the unit-triangle nonobtuse-normal lemma forces the other
transverse component to have the same sign, so the total could
not be zero. Thus both normals strictly expose vertices. Their
transverse components have opposite signs, they cannot expose
opposite vertices, and their positive longitudinal sum puts both
vertices on the maximizing side. The parallel case is immediate.
This proof includes zero proper lengths and every side-mean endpoint.

We also use the direct nonobtuse consequence
\[
       n\text{ H-owned at a petal port}\quad\Longrightarrow\quad
                                  n\cdot M>0.
\tag{14}
\]
It follows from \(M=\lambda n+\lambda' n'\), positive magnitudes,
and \(n\cdot n'\ge0\).

## 3. Every tilted H is excluded

If H is not aligned with A, Q is its unique rightmost vertex.
Write its inward orthonormal axes as
\[
 u=(-a,b),\qquad v=(-b,-a),\qquad
             a,b>0,\quad a^2+b^2=1,\qquad
 H=Q+[0,1]u+[0,1]v.
\tag{15}
\]
Use the true-origin coordinates in this frame:
\[
       Q_u=-a\delta-bw,\qquad Q_v=-b\delta+aw,\qquad
       (q_H)_u=Q_u+a\alpha,\quad(q_H)_v=Q_v+b\alpha.
\tag{16}
\]

### 3.1. Nonnegative minimum v support

If \(\delta\le0\), then \(Q_v>0\) and \((q_H)_v>0\).
Consequently \(M_v>0\). Section 2 puts both petal applications
on the far-v side, of height \(1+Q_v>1\).
END_TRIANGLE_HIGH_FACE_EXCLUSION.md excludes it.

For \(\delta>0\), both center coordinates
\[
                   (c_H)_u=Q_u+\tfrac12,\qquad
                   (c_H)_v=Q_v+\tfrac12
\]
are strictly positive, using (7) and \(\delta<1/60\).
If \((q_H)_v\le0\), then
\[
                    b(q_H)_u-a(q_H)_v=-w<0
\]
would make \((q_H)_u<0\). Since \(q_H\) is a positive multiple
of M, this contradicts (12). Therefore
\[
                                  M_v>0
\tag{17}
\]
throughout the complete tilted-H domain, including
\(Q_v=\alpha=0\). If \(Q_v\ge0\), the first consequence of
Section 2 now puts both ports on the far-v side, of height
at least one. It remains only
\[
                    \delta>0,\qquad -\delta<Q_v<0.
\tag{18}
\]

### 3.2. A nonpositive u component also forces the far-v side

If \(M_u=0\), the axis consequence of Section 2 puts both ports
on the far-v side.

If \(M_u<0\), its unique maximizing H vertex is \(Q+v\).
A parallel interface has both actual ports there. Otherwise
one actual port is \(Q+v\), and the other feature is exhaustive:

* Q cannot belong to a boundary tip, by (7).
* \(Q+u\) is the opposite strict vertex, forbidden by the
  physical unit-triangle support-span lemma.
* \(Q+u+v\), or the same vertex \(Q+v\), is on the far-v side.
* The H-owned normals \(+u,-v\) are excluded by (14).
* For an H-owned \(-u\) application, its v-coordinate is
  \((q_0)_v<0\). If the actual point belongs to H at all,
  this coordinate lies in \([Q_v,0)\). Its u-coordinate is
  \(Q_u<0\), so its norm is at most \(|Q|<r\), impossible.
* An H-owned \(+v\) application lies on the far-v side.

Thus every actual mean and strict vertex alternative has been
covered. Both petal ports lie on a face of height
\[
                            1+Q_v>1-\delta>59/60.
\]
The high-face theorem excludes this whole case.

### 3.3. A positive u component leaves one other high side

Now \(M_u,M_v>0\). Its maximizing vertex is \(F=Q+u+v\).
Parallel root forces have both ports there. Otherwise an actual
port is F. The opposite strict vertex Q is forbidden, the two
adjacent vertices are on the far-u or far-v side, and (14)
excludes both negative H-owned axes. Thus both actual ports
share the far-u side or share the far-v side. This statement
includes every positive-axis side mean and its endpoints.

The far-v case is already excluded. Suppose both lie on the
far-u side, and set
\[
                     P_u=1+Q_u>0,\qquad P_v=1+Q_v>0.
\]
Every actual outward normal there has nonnegative u-component.
The sum of the two actual tip moments therefore gives
\[
             P_u M_v=\sum_i (p_i)_v(f_i)_u
                              \le P_v M_u,
\tag{19}
\]
where \(f_i\) are the actual positive root force vectors.
No application mean has been replaced by an endpoint.
Since the world vertical component is \(bM_u-aM_v<0\),
(19) implies
\[
                            bP_u<aP_v,\qquad b-a<w.
\tag{20}
\]

Together with \(Q_v<0\), this forces \(a>2/3\). Indeed,
if \(a\le1/2\), then
\[
             b-a\ge(\sqrt3-1)/2>9/25>w,
\]
contrary to (20). Thus \(a>1/2\). If still \(a\le2/3\),
then
\[
           b-a\ge(\sqrt5-2)/3>1/30,
                \qquad w<\delta\,b/a<1/30,
\]
again a contradiction. The strict rational comparisons follow
from \(\sqrt3>43/25\) and \(\sqrt5>21/10\).

Finally \(aw<\delta b\) gives
\[
              P_u=1-\delta a-bw
                   >1-\frac{\delta}{a}>1-\frac1{40}
                   =\frac{39}{40}.
\tag{21}
\]
The strengthened high-face theorem excludes the entire far-u
alternative too. This completes every tilted H, for all radii.

## 4. A high-radius wall boundary unit lies strictly above 1/2

This short geometric fact will close the aligned-H case. Suppose
\[
    0\le\delta<1/60,\quad R^2\ge17/4,\quad
    B\subset\{x\le\delta\},\quad
    P=(\delta,y)\in B,\quad 0<y\le1,
\tag{22}
\]
and B touches the circle. Then every point of B has \(y>1/2\).

If B is aligned, its horizontal interval is \([\delta-1,\delta]\).
The farther horizontal endpoint is \(\delta-1\), so its circle
corner has vertical magnitude
\[
                \sqrt{R^2-(1-\delta)^2}\ge\sqrt{13}/2>3/2.
\]
Because its vertical interval contains \(y>0\) and has length one,
that far endpoint must be the upper one. Its lower endpoint
is therefore strictly above \(1/2\).

Otherwise P is its unique rightmost vertex. For some
\(c,s>0\), \(c^2+s^2=1\),
\[
                   B=P+[0,1](-c,s)+[0,1](-s,-c).
\tag{23}
\]
P is circle-clear. Its upper adjacent corner has squared norm
\[
       (\delta-c)^2+(y+s)^2
           \le2+2s-2\delta c+\delta^2
           <4+1/3600<17/4.
\]
Its lower adjacent corner also has squared norm less than two.
Thus only its opposite corner can lie on the circle. Its
horizontal magnitude is at most \(\sqrt2\), so its vertical
coordinate \(Y=y+s-c\) has magnitude at least \(3/2\).
Since \(Y>-1\), actually \(Y\ge3/2\). The lowest point of B
has height
\[
                             y-c=Y-s>1/2.
\tag{24}
\]
Every frame and every actual support-side mean has been covered.

## 5. Every aligned H is excluded

Write
\[
                   H=[\delta-1,\delta]\times[t,t+1],
                              t\le-w\le t+1.
\tag{25}
\]
If \(\delta<0\), (11) gives \((q_H)_x<0\), hence \(M_x<0\).
The minimum coordinate of H along its west side axis \(-e_x\)
is \(-\delta>0\). Section 2 immediately puts both petal ports
on the west side, whose height is \(1-\delta>1\). The high-face
theorem excludes it.

It remains \(\delta\ge0\), including the exact critical radius.
Section 4 applies to B. Since H physically touches B, its top
is strictly above \(1/2\); since it contains Q of negative height,
\[
                              -1/2<t<0.
\tag{26}
\]
Its center has negative x-coordinate and positive y-coordinate.
Together with \(M_y<0\), the strict pressure (12) forces
\[
                                  M_x<0.
\tag{27}
\]
In particular this exhausts the possible
\(\delta=0,\alpha=0\) zero-horizontal-concurrence limit; that
limit would have \(M_x=0\), contrary to (27).

The unique maximizing H vertex is now its lower-left vertex
\((\delta-1,t)\). For parallel petal forces both ports are there.
For nonparallel petal forces one actual port is there. The other
feature is exhaustively covered as follows:

* The lower-right vertex \((\delta,t)\) has norm less than
  \(\sqrt{1/3600+1/4}<129/200<r\), so is circle-clear.
* The upper-right strict vertex is opposite and forbidden.
* The upper-left or the same lower-left vertex lies on the west side.
* H-owned east or north normals have negative dot product with M
  and are excluded by (14).
* An H-owned south application has x-coordinate
  \((q_0)_x>0\). If it lies on the actual side, that coordinate
  is in \((0,\delta]\). By (26) its norm is again less than r.
* An H-owned west application is on the west side.

Every surviving port is therefore on the west side of height
\[
                              1-\delta>59/60.
\]
The high-face theorem gives the final contradiction.

## 6. Whole aligned-S conclusion and exact scope

Sections 1–5 cover all parallel A reactions, both aligned and
tilted H, both original B circle masks, every mutual owner and
every actual side mean. No pair equation at H was substituted:
its genuine degree-four equation appears in (10), while the
pressure and proper-port implications use only the exact
degree-two C/E tip equations.

The present theorem and
TIP_LEAF_BOWTIE_S_ALIGNED_NONPARALLEL_EXCLUSION.md exclude the
entire aligned S-leaf articulation. All three arbitrary extras
remain physically present. The tilted S articulation is a
separate whole family, and no parent-cell closure is claimed here.

No additional normal is selected after extraction, no unit is
moved, and no numerical pose sampling, Lean compilation or CI is used.


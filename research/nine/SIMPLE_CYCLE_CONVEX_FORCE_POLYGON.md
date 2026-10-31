# Every multi-load simple positive cycle has a convex contracted force polygon

**Status: complete whole-family structural theorem; root and separate independent
full hand audits passed.**
Work in
\[
                    \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16}
\tag{1}
\]
with the existing compatible selected physical certificate, including
its planar embedding, exterior circle spokes, strict point normals
and diagonal avoidance. Let the **entire positive component** be a
simple cycle with \(k\ge3\) loaded bodies.

**Theorem.** Contract each maximal unloaded run. The \(k\) actual
loaded concurrences, in cycle order, form a strictly convex polygon
containing the origin in its open interior. Each edge has the direction
of its actual channel force and has length at least that channel's
physical reserve. The physical boundary-center order of the loaded
bodies is the same as this polygon order.

The theorem covers every allowed number of loads, not only a triangle
or quadrilateral. It retains physical two-circle-corner bodies whose
concurrence is outside the body or containing disk. It uses no bound
on such concurrences and no completion-square motion.

## 1. Proper concurrences and exact channel contraction

SIMPLE_CYCLE_LOADED_FORCES_NONPARALLEL.md proves that each loaded
body has nonparallel actual pair forces. Hence
FIVE_CYCLE_FORCE_POLYGON_DOMAIN.md, Lemma1.1, applies at every load:
its two lines meet at
\[
                      q_i=\tau_i m_i,\qquad\tau_i>0,
\tag{2}
\]
where \(m_i\ne0\) is its circle resultant, and
\[
                          p-q_i=\alpha n,\qquad\alpha\ge0
\tag{3}
\]
at each actual application with outward normal \(n\).

List the loaded bodies in the original cycle order. Each intervening
unloaded run is an actual straight normal channel of reserve
\[
                          w_i\in\{0,1,\sqrt2,2\}.
\tag{4}
\]
The reserve is0 for a direct edge,1 or \(\sqrt2\) for one transmitter,
and2 for two side-normal transmitters. The usual center-diameter
bound excludes every longer run and every two-transmitter run
containing a diagonal.

Direct the \(i\)-th channel toward load \(i+1\), with unit direction
\(n_i\) and positive magnitude \(\mu_i\). Equal and opposite forces
on each unloaded body preserve this magnitude and its actual force
line. Formula (3) at its two loaded ends gives exactly
\[
                          q_{i+1}-q_i=L_i n_i,
                          \qquad L_i\ge w_i.
\tag{5}
\]
In fact \(L_i>0\). For \(w_i>0\) this is immediate. For a direct
edge, equality would identify two loaded concurrence directions.
Those directions pierce disjoint open square interiors at radius
\(5/4\), by CYCLIC_GLOBAL_CONTINUATION.md, Section8, and are distinct.
Thus equality is impossible.

All side-normal transmitter applications remain their actual
weighted means. No midpoint of a loaded contact segment is substituted.

## 2. Nonzero common moment, with no boundary-edge premise

Torque balance about the circle origin gives one common number
\[
                    H=\det(p_i,\mu_i n_i)
\tag{6}
\]
on every original edge and hence on every contracted channel.
Subtracting (3) along the normal gives
\[
                    \det(q_i,n_i)=\frac{H}{\mu_i}.
\tag{7}
\]

Suppose \(H=0\). Equations (5)--(7) make every consecutive pair
\(q_i,q_{i+1}\) collinear with the origin. Neither point is zero.
Their positive radial directions are distinct, so the two directions
must be antipodal. Following the cycle would consequently put every
loaded direction on the same two rays. Since different loaded bodies
have different resultant directions, this permits at most two loads,
contradicting \(k\ge3\). Therefore
\[
                                  H\ne0.
\tag{8}
\]

This argument works even when the cycle has no direct contact between
two loaded bodies.

## 3. The physical spoke order fixes one winding

We use the following elementary planar fact.

**Annular order lemma.** Let a Jordan curve \(\Gamma\) lie strictly
inside a circle \(C\). Suppose distinct marked points of \(\Gamma\)
are joined to distinct points of \(C\) by pairwise disjoint arcs in
the closed exterior annulus; each arc meets the two boundary curves
only at its endpoints. The marked points on \(\Gamma\) and their
endpoints on \(C\) have the same cyclic order, up to reversing both
orientations.

To prove it, cut the annulus along any one arc. This gives a disk
whose two corresponding boundary intervals are the cut copies of
\(\Gamma\) and \(C\). The remaining disjoint arcs are crosscuts
between these intervals. Two crosscuts with reversed endpoint order
would intersect by the Jordan separation theorem. Thus their linear
orders, and then the original cyclic orders, agree.

Apply this to the selected plane embedding of the exact simple
positive cycle. Its embedded cycle is a Jordan curve strictly
inside the containing disk. PHYSICAL_BODY_GRAPH_UNCROSSING.md,
Section6, constructs a disjoint spoke from each physical boundary
body's center to a chosen circle corner, meeting the embedded cycle
only at that center. These spokes lie in the exterior face: their
other endpoints are on the containing circle, and they cannot cross
the embedded cycle. The junction and tube perturbations can avoid
all these finitely many spokes simultaneously.

Choose one positive circle corner on each loaded body. The annular
order lemma therefore gives their cyclic order from the positive
cycle order. The same construction permits both circle spokes of a
physical two-corner body simultaneously, as detailed in
UNIQUE_POSITIVE_COMPONENT.md, Section1.

For completeness, replacing a chosen corner direction by its actual
resultant direction preserves that cyclic order. Every physical
circle corner is within20 degrees of its body's center, and distinct
boundary centers are more than40 degrees apart. Thus the full corner
direction intervals of distinct boundary bodies are disjoint and
inherit their center order. A positive circle resultant lies inside
its body's own closed interval, including a zero individual corner
weight. Formula (2) gives the same direction for \(q_i\).

Consequently the loaded concurrence directions and loaded center
directions, in cycle order, make exactly one circuit around the origin,
with one of the two possible orientations. Choose the cycle
orientation matching their counterclockwise circular order. Let
\(\gamma_i\in(0,2\pi)\) be its actual consecutive angular gaps. Then
\[
                              \sum_i\gamma_i=2\pi.
\tag{9}
\]
By (5)--(7),
\[
                \det(q_i,q_{i+1})=\frac{L_iH}{\mu_i}.
\tag{10}
\]
The determinant signs are all the same and nonzero. If \(H<0\),
every gap in (9) would be greater than \(\pi\), impossible for
\(k\ge3\). Hence this orientation has
\[
                    H>0,\qquad 0<\gamma_i<\pi.
\tag{11}
\]

In particular the angular sum has been established by the actual
plane embedding and its exterior spokes. It is not inferred from a
bound of fewer than four angular increments.

## 4. Simplicity, positive turns and strict convexity

Each straight segment \(q_iq_{i+1}\) lies in the angular sector
between its two endpoint rays. By (9)--(11), these consecutive sectors
have disjoint interiors. The polygon in (5) is therefore simple
and winds once about the origin.

Write the loaded circle force as
\[
                            2m_i=\kappa_i q_i,\qquad\kappa_i>0.
\]
Its exact degree-two force equation is
\[
            \kappa_i q_i+\mu_i n_i-\mu_{i-1}n_{i-1}=0.
\tag{12}
\]
Taking its determinant with \(n_{i-1}\), and using (7), gives
\[
             \mu_i\det(n_{i-1},n_i)
                     =\frac{\kappa_iH}{\mu_{i-1}}>0.
\tag{13}
\]
Thus every turn of the simple polygon is strictly left, so it is
strictly convex. Moreover (7) puts the origin strictly to the left
of every directed side. The origin lies in its open interior.
This proves the theorem.

## 5. Uniform whole-channel consequences

The channel endpoint half-plane lemma in
FIVE_CYCLE_FOUR_LOAD_EXCLUSION.md, Sections1--2, now applies to
every edge of this polygon with positive reserve. Its proof uses
only proper endpoint concurrences, actual supporting applications
and the origin on the inward side of that edge.

In coordinates with a channel horizontal and the vertical direction
away from the origin, its applications and centers have the form
\[
 \begin{gathered}
       P_X=(l,h),\qquad P_Y=(l+w,h),\qquad h>0,\\
       c_X=(-x,y_X),\qquad c_Y=(y,y_Y),\\
       x,y>0,\qquad y_X,y_Y\ge0.
 \end{gathered}
\tag{14}
\]
Indeed the horizontal center gap is
\(w+H_X(e_x)+H_Y(e_x)\ge2\), while every center has norm below
\(91/60<2\). This forces the two horizontal signs; the full corner
argument in that lemma then gives the nonnegative heights. It does
not assume that a two-corner concurrence belongs to its body.

The consecutive loaded center arc across this channel is the upper
minor arc
\[
     \gamma=\pi-\delta_X-\delta_Y,\qquad
     \delta_X=\arctan(y_X/x),\quad
     \delta_Y=\arctan(y_Y/y).
\tag{15}
\]
Its identity as the actual consecutive arc follows from the physical
order just proved. In particular the remaining loaded bodies occur
on the complementary arc.

For one transmitter, with \(w=1\) or \(\sqrt2\), the exact metric
proof of FIVE_CYCLE_THREE_LOAD_EXCLUSION.md, Sections2--4, gives
the uniform upper bound
\[
                        \gamma<\pi-\frac12\arccos\frac9{25}.
\tag{16}
\]
That proof uses (14)--(15), the actual one-transmitter width, and
the common frame at diagonal endpoints; it does not require a C5
or a third particular loaded vertex. A direct boundary edge instead
has its angular-neighbor gap strictly below
\[
                               \arccos\frac9{25}.
\tag{17}
\]
Reserve2 remains governed by the exact center gap at least3 and the
global endpoint-matching theorem; it is not put under (16).

These are necessary geometric conditions for all mixed simple cycles.
They do not yet close the four remaining simple C6 load orbits or
any larger mixed coarse cell. The entire physical completion remains
present, and no conclusion about its location or capacity follows
from the force polygon alone.


# The nonparallel singleton D articulation in the three-loaded C4

**Status.** Complete hand exclusion of the stated whole contact family;
root and separate independent full hand audits passed. The positive
articulation-concurrence theorem in Section 2 retains arbitrary actual
side means. The height theorem in Section 3 also permits the other A
contact to be shared. The final exclusion assumes both A-cycle
intersections are singletons. Every physical circle-corner mask of
`B,U,C`, every other shared-side mean and all four extra squares are
retained. The parallel articulation and the vertical shared-A-contact
families require their separate proofs.

## 1. Full domain and the physical selections

The positive graph is
\[
 A-B-U-C-A,
 \qquad A-L,
\tag{1}
\]
where `L` is a radial D leaf, `A` is clear, and `B,U,C` are loaded
with exact positive pair degree two. Work throughout
\[
 \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16},
 \qquad r=R-\sqrt2,\quad s=1-r,
\]
\[
 A=[-s,r]\times[-v,H],
 \qquad H+v=1,\quad H,v>0.
\tag{2}
\]
The leaf application is `(r,0)` in the relative interior of A's right
side. Its force on the articulation is a positive multiple of `e_x`
in the outward-normal convention. The selected force and origin-torque
equations on A are therefore
\[
 \mu_B n_B+\mu_C n_C+\gamma e_x=0,
 \qquad
 \mu_B\det(P_B,n_B)+\mu_C\det(P_C,n_C)=0,
 \qquad \mu_B,\mu_C,\gamma>0.
\tag{3}
\]
Here each `P` is the actual application, including its actual weighted
mean when the intersection is a side segment.

The following uniform strict bounds will be convenient:
\[
 \frac{11}{20}<r<\frac23,
 \qquad \frac13<s<\frac9{20}.
\tag{4}
\]
The lower bound for `r` follows from `sqrt(2)<57/40`. For its upper
bound, `sqrt(2)>45/32` gives
\[
 (\sqrt2+\tfrac23)^2>
 \frac{22}{9}+\frac{15}{8}
 =\frac{311}{72}>\frac{1105}{256}.
\]
The last difference is `7/2304`.

Every point of a physical circle-touching unit square has norm at
least `r`: its distance to a circle corner is at most `sqrt(2)`.
A square with two physical circle corners is radial S. In its own
radial frame it is
\[
 [h,h+1]\times[-\tfrac12,\tfrac12],
 \qquad h=\sqrt{R^2-\tfrac14}-1>\frac9{10}.
\tag{5}
\]
The last inequality follows from `5841>5776`. In particular every
point of such a square has norm greater than `9/10`. These are
physical statements, independent of whether either of its individual
circle multipliers is zero.

Use the compatible necessary-certificate selections in
RADIAL_LEAF_ARTICULATION_FIXED_POINT_SELECTION.md and
BOUNDARY_TIP_FIXED_APPLICATION_SELECTION.md. Their finite conditions
are imposed before multiplier extraction, and retain every actual
shared-side mean. When both A-cycle intersections are distinct
singletons, the first selection makes both A-cycle normals side-axis
owned. A normal strictly between two A axes is consequently owned by
the neighboring tip, with the A vertex in the relative interior of
that tip's side. No such fixed-application inference is made below
when an A intersection is shared.

## 2. Positive concurrence for every nonparallel D articulation

**Lemma 2.1.** If the two cycle normals in (3) are nonparallel, their
force lines meet at
\[
                         q_A=(q,0),\qquad q>0.
\tag{6}
\]
This conclusion holds for arbitrary actual A side means and every
physical circle-corner mask of `B,U,C`.

*Proof.* The vertical equation in (3) labels the normals so that
\[
                  (n_B)_y>0>(n_C)_y.
\tag{7}
\]
Neither can have zero vertical component in a nonparallel pair.
The corresponding actual applications satisfy
`(P_B)_y=H>0` and `(P_C)_y=-v<0`, including at every shared-side
endpoint.

Apply TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md, Lemma 2.1, separately
to `B,U,C`. Each has a boundary neighbor and two positive pair edges.
It gives nonparallel pair-force lines, a concurrence `q_i` which is
a positive multiple of the actual circle resultant, and, for every
actual contact `p` with outward unit normal `g`,
\[
                         p-q_i=\ell g,\qquad\ell\ge0.
\tag{8}
\]
For a body with one physical circle corner, its concurrence belongs
to the body. The proof of (8) does not make that interior assertion
for the two-corner case, and neither do we.

At the two A contacts, (8) writes
\[
 q_B=P_B+\ell_B n_B,
 \qquad q_C=P_C+\ell_C n_C,
 \qquad\ell_B,\ell_C\ge0.
\]
Thus `(q_B)_y>0>(q_C)_y`.

Here is the complete angular-order justification for the moment sign.
By CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS.md, Section 2, every physical
circle corner differs from its body's center direction by less than
`pi/9`. By CENTERED_INNER_ARC.md, distinct circle-touching centers
differ by more than `2pi/9`. Hence the physical corner intervals of
distinct bodies are disjoint and have their center order. Every
positive circle resultant lies in its own body's interval, even when
one of two physical corner weights is zero.

The D leaf center has direction zero. Thus the intervals of `B,U,C`
avoid that direction and may all be represented in `(0,2pi)` without
wrapping. The strict signs of the preceding paragraph put the B
resultant in `(0,pi)` and the C resultant in `(pi,2pi)`, so the B
interval precedes the C interval in this linear order.

The physical contacts BU and UC join consecutive boundary-center
directions along minor arcs shorter than `2pi/5`, by
CIRCLE_CONTACT_ANGULAR_ORDER.md. Neither contact arc can skip the
leaf center or the third body. Therefore their linear order is
`B,U,C`. The positive angular difference from the B resultant to
the U resultant is at most their center gap plus `2pi/9`, hence is
strictly less than
\[
                   \frac{2\pi}{5}+\frac{2\pi}{9}
                         =\frac{28\pi}{45}<\pi.
\]
Consequently `det(q_B,q_U)>0`.

Let `g` be the actual B-to-U normal and `T` its actual application.
Equation (8) on both bodies gives
\[
 q_U-q_B=\ell g,\qquad\ell>0,
 \qquad
 \det(T,g)=\frac{\det(q_B,q_U)}\ell>0.
\tag{9}
\]
The coefficient is strictly positive since the two concurrence
directions belong to disjoint intervals. Torque balance on B now
gives `det(P_B,n_B)>0`, with its positive edge magnitude included.

The nonparallel force lines on A have an intersection. Equation (3)
and torque about that intersection put it on the leaf's horizontal
force line. Thus it is `(q,0)`, and
\[
                   q=\frac{\det(P_B,n_B)}{(n_B)_y}>0.
\tag{10}
\]
This proves the lemma, with no restriction on a shared application
mean. `square`

## 3. An all-mask height bound when the lower A contact is tip-owned

**Lemma 3.1.** Keep a nonparallel articulation and (6). Suppose
`0<q<=r`, its lower normal is strictly southwest and owned by C,
and its actual lower application is A's lower-left vertex. Then
\[
                              v>\frac34,
                       \qquad H<\frac14.
\tag{11}
\]
The upper A contact may be a singleton or a positive-length shared
side with its arbitrary actual mean. No UC owner or U circle mask
is assumed.

*Proof.* Put `L=q+s`. The hypotheses give `s<L<=1`. Use the
orthonormal side frame of C at its actual owned A contact:
\[
 n=(-d,-c),\quad k=(c,-d),\quad c,d>0,\quad c^2+d^2=1,
 \qquad P=(-s,-v),
\]
\[
 C=P+[0,1]n+[-\rho,1-\rho]k,
 \qquad 0<\rho<1,\quad V=1-\rho.
\tag{12}
\]
The intersection of the A force line with `(q,0)` gives
\[
 \frac cd=\frac vL,
 \qquad X=P\cdot n=sd+vc>0,
 \qquad Y=P\cdot k=vd-sc>0.
\tag{13}
\]

First suppose C has two physical circle corners. Its own n-coordinate
interval is `[X,X+1]` with `X>0`, so its radial axis cannot be `k` or
`-k`: those alternatives would have n-coordinate interval
`[-1/2,1/2]`. Its radial axis is necessarily `n`, and (5) gives
`X=h>9/10`. If `v<=3/4`, however,
\[
 X\le |P|<\sqrt{(9/20)^2+(3/4)^2}
            =\frac{\sqrt{306}}{20}<\frac9{10},
\]
a contradiction. This handles every two-corner multiplier split.

Now suppose C has a unique physical circle corner. By (8) its
concurrence is `P+eta n`, `eta>=0`, and is a positive multiple of
that corner. Its k-coordinate is `Y>0`. Its n-coordinate is positive
as well. Thus the actual circle corner is
\[
                      z_C=P+n+Vk=(X+1,Y+V)_{(n,k)}.
\tag{14}
\]
The concurrence equation gives the exact identity
\[
                \eta=\frac{Y-VX}{Y+V}\ge0,
                    \qquad V\le\frac YX.
\tag{15}
\]
It follows that
\[
 R^2=(X+1)^2+(Y+V)^2
       \le(X^2+Y^2)(1+1/X)^2.
\tag{16}
\]
For fixed `s,v`, (13) writes
\[
             X=\frac{sL+v^2}{\sqrt{L^2+v^2}}.
\]
Its derivative with respect to `L` is
`v^2(s-L)/(L^2+v^2)^(3/2)`, so it is decreasing for `L>=s`.
Since `L<=1`, equation (16) yields
\[
 R\le g(s,v):=
 \sqrt{s^2+v^2}
 \left(1+\frac{\sqrt{1+v^2}}{s+v^2}\right).
\tag{17}
\]

We show uniformly that `g(s,v)<79/40` for
`1/3<=s<=9/20` and `0<v<=3/4`. Write `t=v^2` and
`a=sqrt(1+t)`. Differentiating with respect to `t`, the numerator
over the positive denominator
`2sqrt(s^2+t) a(s+t)^2` is
\[
                      a(s+t)^2+(1-s)^2(s-t).
\tag{18}
\]
It is positive when `t<=s`. When `t>s`, use
`(s+t)^2>=4st` and `4s>(1-s)^2` to obtain positivity again.
Thus `g` increases with `v` throughout this rectangle.

For fixed `t`, the sign of the derivative with respect to `s` is
the sign of
\[
 N(s)=s(s+t)^2+a t(s-1),
 \qquad N'(s)=(s+t)(3s+t)+a t>0.
\tag{19}
\]
Hence any interior critical point is a minimum, and the maximum
over the s interval occurs at an endpoint. At `v=3/4`, the two
endpoint values are exactly
\[
 g(1/3,3/4)=\frac{103\sqrt{97}}{516},
 \qquad
 g(9/20,3/4)=\frac{181\sqrt{34}}{540}.
\tag{20}
\]
Both are strictly less than `79/40`. For an entirely rational check,
the differences of their squares from `(79/40)^2` are
\[
 \frac{949181}{26625600}>0,
 \qquad \frac{94193}{1166400}>0,
\]
respectively. This contradicts (17) if `v<=3/4` and proves (11).
`square`

## 4. The entire strict right-vertex alternative

Suppose both A intersections are singletons and the upper A normal
has strictly positive first coordinate. Equation (3) forces the
lower normal to have strictly negative first coordinate. Thus the
actual A applications and normals are
\[
 P_B=(r,H),\quad n_B=(\cos\phi,\sin\phi),
 \qquad P_C=(-s,-v),\quad n_C\text{ strictly southwest},
 \quad0<\phi<\frac\pi2.
\tag{21}
\]
Both contacts are tip-owned by the selection in Section 1. Lemma 2.1
gives `q>0`; the upper line through `(q,0)` and `(r,H)` gives
`q<r`. Lemma 3.1 therefore applies to C and proves `H<1/4` for
every original physical C mask.

In particular
\[
           |P_B|^2=r^2+H^2<\frac49+\frac1{16}<\frac9{16}.
\tag{22}
\]
By (5), B has a unique physical circle corner. Write its actual
owned side frame as
\[
 k_B=(-\sin\phi,\cos\phi),
 \qquad
 B=P_B+[0,1]n_B+[-\rho,1-\rho]k_B,
 \qquad0<\rho<1.
\tag{23}
\]
The proper radial concurrence has the same k-coordinate as P_B,
namely `-q sin(phi)<0`. Its n-coordinate is positive. Thus B's
unique circle corner is
\[
                         z_B=P_B+n_B-\rho k_B.
\tag{24}
\]

The actual side segment `P_B-t k_B`, `0<=t<=rho`, starts above
the inner upper edge of the D leaf. It meets that edge
`y=x-r` at
\[
                 t_0=\frac{H}{\sin\phi+\cos\phi}<\frac14.
\tag{25}
\]
At the meeting point `x-r=y=t_0 sin(phi)` lies strictly between
zero and `1/sqrt(2)`, so this is a relative-interior point of the
leaf edge. If `rho>t_0`, the B side enters the open leaf just past
the meeting point, which forces open square overlap. Therefore
`rho<=t_0<1/4`. Equations (22) and (24) now give
\[
 R=|z_B|\le|P_B|+\sqrt{1+\rho^2}
       <\frac34+\frac{\sqrt{17}}4
       <\frac{15}{8}<\frac{79}{40},
\tag{26}
\]
a contradiction. The middle inequality uses `sqrt(17)<9/2`.

Reflection excludes the lower right-vertex alternative as well.
No hypothesis on BU, UC or the U circle mask entered this proof.

## 5. The entire pure-vertical singleton alternative

Suppose the upper A normal is `e_y` and both A intersections are
singletons. Its actual point is
\[
                         P_B=(q,H),\qquad0<q\le r,
\tag{27}
\]
by Lemma 2.1 and the actual top-side interval. The lower normal
is strictly southwest, at `P_C=(-s,-v)`, and the fixed-point
selection makes AC owned by C. Lemma 3.1 gives
\[
                              H<\frac14.
\tag{28}
\]
This use of the selection is restricted to the two singleton
intersections; no assertion about a shared AB mean is being made.

Since P_B lies in a boundary square, `|P_B|>=r`. Hence
\[
       q\ge\sqrt{r^2-H^2}>\frac{\sqrt6}{5}>\frac25,
       \qquad |P_B|<\frac34.
\tag{29}
\]
The last bound follows just as in (22). Thus B has one physical
circle corner. The singleton intersection means B has its bottom
vertex at P_B. Its frame is genuinely oblique: an aligned B would
have either a positive-length AB side intersection or a point-only
vertex/vertex contact with the forbidden nonstrict axis normal.
Consequently write its two inward side vectors as
\[
 u=(a,b),\quad w=(-b,a),
 \qquad a,b>0,\quad a^2+b^2=1,
 \qquad B=P_B+[0,1]u+[0,1]w.
\tag{30}
\]
An adjacent vertex cannot be a circle corner, since its norm is at
most `|P_B|+1<7/4<79/40`. The actual unique circle corner is
therefore the opposite vertex
\[
 z_B=P_B+u+w=(q+\delta,H+\Sigma),
 \qquad\delta=a-b,\quad\Sigma=a+b=\sqrt{2-\delta^2}.
\tag{31}
\]

B's proper radial concurrence lies in B and on the vertical force
line through P_B. It is `tau z_B` with `0<tau<=1`, since it is
inside the radius-R disk. Its first coordinate is q, so
`q=tau(q+delta)` and
\[
                                  \delta\ge0.
\tag{32}
\]
Set `g_0=r-q>=0`. From (29),
\[
 0\le g_0\le\frac{H^2}{r+q}<\frac1{16},
\tag{33}
\]
where `r+q>11/20+sqrt(6)/5>1`.

If `delta>=1/2`, the actual B side `P_B+t u` meets the inner
upper D-leaf edge `y=x-r` at
\[
       t_0=\frac{H+g_0}{\delta}<\frac58<1.
\tag{34}
\]
At that meeting point
\[
        x-r=y=\frac{aH+b g_0}{\delta}
                    <\frac58<\frac1{\sqrt2}.
\]
Thus it is in the relative interior of the leaf edge, and the B
side enters the open leaf immediately afterwards. This contradicts
interior disjointness. We have proved
\[
                              0\le\delta<\frac12.
\tag{35}
\]

For fixed q,H, the squared norm in (31) has derivative
\[
 2\left(q-\frac{H\delta}{\sqrt{2-\delta^2}}\right)>0
               \qquad(0\le\delta\le\tfrac12),
\]
using `q>2/5`, `H<1/4`. Equations (4), (28), (31) and (35)
therefore imply
\[
 \begin{aligned}
 R^2
 &<(\tfrac23+\tfrac12)^2
                   +(\tfrac14+\tfrac{\sqrt7}{2})^2\\
 &=\frac{49}{36}+\frac{29}{16}+\frac{\sqrt7}{4}
   <\frac{553}{144}<\left(\frac{79}{40}\right)^2.
 \end{aligned}
\tag{36}
\]
The penultimate inequality uses `sqrt(7)<8/3`; the final positive
difference is `869/14400`. This contradiction excludes every
vertical singleton upper contact, and reflection handles the lower
one.

## 6. Exhaustion of the nonparallel singleton family

For nonparallel normals, label their vertical signs as in (7).
The positive horizontal leaf force in (3) means that at least one
cycle normal has a negative first coordinate. If both have strictly
negative first coordinates, their applications are exactly the two
left A vertices, and D_FOUR_CYCLE_LEFT_VERTEX_EXCLUSION.md excludes
the entire branch. If one has strictly positive first coordinate,
Section 4 excludes it. The only remaining possibility is a zero
first coordinate for one normal, and Section 5 excludes that
vertical singleton branch. Both first coordinates cannot be zero,
by the horizontal equation in (3).

These alternatives cover every nonparallel D articulation whose
two physical A-cycle intersections are singletons. All normal
selections used here and in the two-left-vertex source are the
previously established compatible finite pre-certificate choices.
No force has been rotated after extraction, no actual side mean
has been frozen, and no physical two-corner body has been silently
treated as a one-corner body.

The proof is a core exclusion and therefore retains all four
arbitrary extra squares. It uses no secondary minimizer, numerical
infeasibility assertion, Lean compilation or CI. To close the entire
D articulation one still combines it with the vertical shared-A-side
and parallel-horizontal-reaction exclusions. This source alone does
not assert that parent-cell conclusion.

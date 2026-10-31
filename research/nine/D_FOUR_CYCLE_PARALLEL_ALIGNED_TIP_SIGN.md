# The aligned wall tip in a parallel D-leaf C4 cannot push west

**Status.** Complete hand force-sign theorem for every aligned tip in
the full parallel-articulation branch; root and two independent full hand audits passed. Every actual A-side mean, every normal/owner at the
other tip contact, and every physical circle mask of the middle body
are retained. This source supplies one input to the whole parallel
D-leaf exclusion; it does not by itself assert that parent theorem.

## 1. The entire parallel wall domain

Let the selected positive graph be `A-B-U-C-A` with a radial D leaf
at the clear articulation A, and let B,U,C be loaded of exact
positive pair degree two. Work in
\[
 \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16},
 \qquad r=R-\sqrt2,\qquad s=1-r,
\]
\[
 A=[-s,r]\times[-v,H],\qquad H+v=1,\qquad H,v>0.
\tag{1}
\]
Suppose the two A-cycle normals are parallel. Equilibrium with the
eastward radial leaf makes both normals horizontal. They cannot both
equal `e_x`. We first exclude their opposite-sign alternative, rather
than presupposing that their individual signs agree.

In that alternative write the actual left and right applications as
`P_-=(-s,y_-)` and `P_+=(r,y_+)`, with outward normals `-e_x`
and `e_x` and positive magnitudes `mu_-` and `mu_+`. Force and
origin torque on A give
\[
             \mu_- =\mu_++\gamma,
             \qquad \mu_- y_-=\mu_+ y_+.
\]
The height `y_-` cannot vanish, since `s<r` while every point in
its boundary neighbor has norm at least r. Hence both heights have
the same strict sign. The proper boundary concurrence theorem of
TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md, Lemma 2.1, applies to both
neighboring tips: each has U as a boundary neighbor. Its concurrence
lies on its horizontal A-force line and is a positive multiple of
its circle resultant. Thus the two tip resultants have that same
strict vertical sign, for every physical corner mask and every
actual A-side mean.

Their physical circle-corner intervals avoid the east direction of
the D leaf and inherit their center order: the corner-to-center
angular displacement is less than20 degrees, whereas distinct
boundary centers are more than40 degrees apart. These are the exact
theorems in CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS.md, Section 2,
and CENTERED_INNER_ARC.md. The actual BU and UC contacts join
consecutive boundary centers on minor arcs which cannot skip the
leaf, by CIRCLE_CONTACT_ANGULAR_ORDER.md. Consequently U's entire
corner interval is between those of the two tips on the arc avoiding
the east cut. Its positive resultant angle is therefore strictly
between their resultant angles in `(0,2pi)`, and has the same strict
vertical sign. Summing the five body-force equations is now
impossible: all three non-leaf circle resultants have this sign,
whereas the radial D leaf has zero vertical resultant. This excludes
the entire opposite-sign parallel alternative.

Both surviving A-cycle normals thus equal `-e_x`, and their actual
weighted-mean applications lie on A's left side.

Every point of a circle-touching unit square has norm at least r.
The uniform bounds `1/3<s<9/20` and `11/20<r<2/3` therefore
show that neither wall application has height zero. The zero origin
moment on A gives strict opposite signs. Label them
\[
                P_B=(-s,y),\qquad P_C=(-s,-w),
                  \qquad y,w>0,\quad y+w\le1.
\tag{2}
\]
No application has been replaced by a wall endpoint. The boundary
point bound gives
\[
                  y^2,w^2\ge r^2-s^2=1-2s.
\]
Consequently
\[
        \frac38\le s<\frac49,
        \qquad \frac13<y,w<\frac23,
        \qquad |P_B|,|P_C|<\frac56.
\tag{3}
\]
For the upper bound on s, `sqrt(2)<17/12` gives
`s<53/120<4/9`. The other bounds follow respectively from
`2sqrt(1-2s)<=y+w<=1`, from `s<4/9`, and from
`s^2+y^2<52/81<25/36`.

A physical two-circle-corner unit is radial S, all of whose points
have norm at least
\[
                    h_R=\sqrt{R^2-\tfrac14}-1>\frac9{10}.
\tag{4}
\]
Thus both B and C have one physical circle corner. This exhausts
their original physical masks without assuming that a zero individual
weight removes a physical corner.

The proper two-force concurrence theorem of
TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md, Lemma 2.1, applies to B
and C because they each have the boundary neighbor U. It supplies
a concurrence inside the body, a positive multiple of its circle
corner. At the actual wall application, its second coordinate equals
that actual wall height. It follows that B's circle corner is strictly
northwest and C's strictly southwest. These statements include all
aligned wall means.

## 2. The complete aligned upper-tip statement

**Theorem.** Suppose B is aligned with A. Let g be its actual outward
unit normal toward U. Then
\[
                                  g_x\ge0.
\tag{5}
\]
The contact can be side-owned by either body, shared with its actual
mean, or a selected vertex/vertex point. No U force equation or U
circle-mask hypothesis is used in the proof.

*Proof.* Put `S=s+1`. Since B's unique circle corner is northwest,
its full aligned form is
\[
 B=[-S,-s]\times[Y-1,Y],
 \qquad z_B=(-S,Y),\qquad Y>0,
 \qquad S^2+Y^2=R^2.
\tag{6}
\]
The actual wall mean lies in this interval, so `Y-1<=y<=Y`.
Equations (3) and (6) imply the convenient exact bounds
\[
            \frac{11}{8}\le S<\frac{13}{9},
                  \qquad\frac43<Y<\frac53.
\tag{7}
\]
Indeed,
\[
 Y^2>\left(\frac{79}{40}\right)^2
            -\left(\frac{13}{9}\right)^2
       =\frac{16}{9}+\frac{4721}{129600},
\]
and `Y<=y+1<5/3`.

The radial concurrence of B is exactly
\[
                         q_B=(-S y/Y,y).
\tag{8}
\]
The positive AB force on B is horizontal, while B's unique positive
circle force has positive second coordinate. Its other positive pair
force therefore satisfies
\[
                                  g_y<0.
\tag{9}
\]

Suppose, for a contradiction, that `g_x<0`. On the aligned square
(6), the actual support for this strict southwest normal is its
unique lower-left vertex
\[
                              T=(-S,Y-1).
\tag{10}
\]
By the proper concurrence theorem, `T-q_B` is a nonnegative
multiple of g. It is nonzero: `q_B=T` would force both `y=Y-1`
and `y=Y`, which is impossible. Hence g is proportional to
\[
                     (-1,-t),\qquad
 t=\frac{Y(y-Y+1)}{S(Y-y)}>0.
\tag{11}
\]
The denominators are positive by (3) and (7). We now bound the
support of (6) in this actual normal direction.

First, `y<2/3` and `Y>4/3` give
\[
 \begin{aligned}
 S t
 &=\frac{Y}{Y-y}-Y\\
 &\le\frac{Y}{Y-2/3}-Y
 \le\frac23.
 \end{aligned}
\]
For the last step the displayed function of Y is strictly decreasing:
its derivative is `-(2/3)/(Y-2/3)^2-1`, and its value at `Y=4/3`
is `2/3`. Therefore
\[
                                t\le\frac{16}{33}<\frac12.
\tag{12}
\]

Second,
\[
 (Y-1)t
 \le\frac1S\,
        \frac{Y(Y-1)(5/3-Y)}{Y-2/3}
 \le\frac{2}{9S}.
\tag{13}
\]
Here all factors have their indicated signs by (7). The last
inequality is a direct polynomial identity. If `x=Y-4/3`, so
`0<=x<=1/3`, then
\[
 \frac29(Y-\tfrac23)-Y(Y-1)(\tfrac53-Y)
          =\frac{x}{9}+\frac43x^2+x^3\ge0.
\tag{14}
\]

Let `h=g dot T` be the actual common support value. From (11),
\[
 h=\frac{S-(Y-1)t}{\sqrt{1+t^2}}
   \ge\frac{S-2/(9S)}{\sqrt{1+t^2}}.
\tag{15}
\]
The numerator increases with S and is therefore at least
\[
                   \frac{11}{8}-\frac{16}{99}
                            =\frac{961}{792}.
\]
By (12), the denominator is strictly less than `9/8`, since
`sqrt(5)/2<9/8`. Thus
\[
                  h>\frac{961}{891}>\frac{97}{90}>R-1.
\tag{16}
\]
The first rational difference is `7/8910`. For the final comparison,
\[
 \left(\frac{187}{90}\right)^2
                  >\frac{1105}{256}
\]
is equivalent to `8952064>8950500`.

Every unit square has width at least one in every unit direction.
Since U lies on the other side of the actual support line,
`g dot x>=h` for all `x in U`, some point of U has projection at
least `h+1>R`. This contradicts `U subset D_R`. We have excluded
every negative first component, proving (5). `square`

## 3. Reflected form and the intended whole-branch use

Reflection in the horizontal axis proves the same statement for an
aligned lower tip C: its actual outward normal toward U also has
nonnegative first coordinate. Reflection changes no first coordinate
and preserves every actual application mean.

The theorem is deliberately a sign conclusion. It need not discard
the lower-right vertex of an aligned upper tip, a bottom-side contact,
or their endpoint limits: all of their surviving normals have the
required nonnegative first component. It does not replace them by a
single guessed contact type.

In the complete parallel-D assembly, the separate tilted-tip argument
gives the same sign for every tilted tip. The middle body U then has
two outward pair forces with nonpositive first coordinate. Its circle
resultant has strictly negative first coordinate: each physical U
circle corner is acute to the northwest B corner and the southwest C
corner, by ACUTE_LOADED_CONTACT_GRAPH.md, Section 2, and a vector
with nonnegative first coordinate cannot be acute to both. Thus its
horizontal force balance would be strictly negative. This final
contradiction applies once the entire tilted-tip sign theorem has
also been proved and audited.

No numerical certificate, additional normal selection, secondary
minimizer, Lean compilation or CI is used here.

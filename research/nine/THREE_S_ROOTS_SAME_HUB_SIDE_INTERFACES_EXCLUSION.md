# Three S roots cannot use the same owned hub side twice

Date: October 27, 2026.

Full root review: REVIEW_THREE_BRIDGE_CELL_SS_DIAMOND_AND_ADJACENT_C4_ROOT_2026_10_27.md.
Separate full-source/scope review: REVIEW_THREE_S_ROOTS_SAME_HUB_SIDE_LEAF_PAIR_2026_10_27.md.
The reviews pin the mathematical source before this acceptance-only header edit.

**Status: accepted complete whole same-H-side interface exclusion.** This excludes the same-H-side
owner form in the final original C2.33.b3 attachment, with its genuine
H leaf and actual degree H5 retained.

## 1. Original scope and the complete local port inputs

Keep the original nine physical unit squares, disjoint open interiors,
and common compatible selected certificate. The actual triangles are
HAB,HCD, with genuine S leaves at H,A,C and true degrees H5,A3,C3,B2,D2.
Keep every original force, physical mask, zero weight, selected normal
and actual mean; the ninth physical square is arbitrary and unchanged.

Write

    d=sqrt(R^2-1/4)-1=1+epsilon,
    0<epsilon<1/60.

Suppose HA and HC use the same H-owned side normal. Rotate it west:

    H subset {x>=h},
    A,C subset {x<=h},
    n_HA=n_HC=-e_x.

Each genuine root contains its actual inward point epsilon e_i. Those
of A,C give h>=-epsilon, and H's own gives h<=epsilon. Therefore

    |h|<=epsilon.                                      (1)

If H is parallel to A or C, the complete
THREE_S_ROOTS_PARALLEL_TRIANGLE_INTERFACE_EXCLUSION.md applies:
the tilted root uses its owned +u axis, or the aligned root has its
full parallel back-face pair. Both cases keep H's actual leaf and
the third genuine S root. Hence assume H is nonparallel to both.

The actual H-owned contacts are then strict rightmost vertices of A,C:

    p_A=(h,y_A),       p_C=(h,y_C).

The complete local S-star cover, with H's full external aggregate,
makes either root aligned with two strict back vertices or tilted
with its strict P/W pair. Its other actual triangle application is
a distinct strict adjacent vertex of the same root. In particular
the AB and CD ports are genuine original vertices, not moved means.

The local estimates in Sections 2--5 of
TWO_S_TIP_TRIANGLES_HIGH_RADIUS_HUB_CLEARANCE.md give, for either
actual hub port,

    |p|<11/30.                                         (2)

For an aligned root, the squared bound is
1/3600+(9/25)^2<(11/30)^2, with reserve 137/30000.
For a tilted root it is 241/3600<(11/30)^2. The other genuine
root supplies the actual near point used in the tilted bound.
No H4 force cancellation or origin-interior premise is used.

Exchange the two original triangles if necessary so y_A>=y_C.
Set D=y_A-y_C. The exact two real frames can be written

    A=p_A+[0,1]u+[0,1]v,
    u=(-a,b),       v=(-b,-a),       a,b>0, a^2+b^2=1,

    C=p_C+[0,1]u'+[0,1]v',
    u'=(-c,s),      v'=(-s,-c),      c,s>0, c^2+s^2=1.

Equation (2) gives 0<=D<11/15.

If D=0, the two rightmost vertices coincide. The strict west ray
from that point lies in the open inward right-angle sector of each
root, because all a,b,c,s are positive. Their interiors would overlap
near the point. Thus actually D>0.

## 2. Exact physical separation of the two same-wall roots

Put

    K=ac+bs>0,       L=bc-as,
    K^2+L^2=1.

Apply the ordinary physical separating-axis test to these two actual
unit squares. This is a statement about their unchanged rectangles,
not a reselection of a force normal. A horizontal axis cannot separate
them since both attain x=h and have nonzero width to the left. Choose
the separator with positive vertical component. Because p_A is no
lower than p_C on the same vertical line, A must be on its positive
side. Testing the four possible positive-y own axes gives exactly:

| separating axis | necessary separation inequality |
| --- | --- |
| u=(-a,b) | b D>=K+max(0,-L) |
| -v=(b,a) | a D>=1+max(0,-L) |
| u'=(-c,s) | s D>=1+max(0,-L) |
| -v'=(s,c) | c D>=K+max(0,-L) |

For example, on u the minimum A projection is p_A.u, while the
maximum C projection is p_C.u+K+max(0,-L); the other three rows
follow from the same actual endpoint projections. The test includes
physical touching and equal projections. The second and third rows
would give D>=1 and are impossible. If L<=0, then K-L>=1, so the
first and fourth rows would do the same. Consequently

    L>0,
    D>=K/max(b,c).                                     (3)

Write a=cos(theta_A), b=sin(theta_A), c=cos(theta_C),
s=sin(theta_C), with both angles in (0,pi/2). Then L>0 gives
theta_A>theta_C. If b<=2/3, the angle difference is smaller than
theta_A, so K>cos(theta_A)=a>=sqrt(5)/3>11/15. This contradicts
(3). If c<=2/3, the difference is smaller than pi/2-theta_C,
giving K>sin(theta_C)=s>=sqrt(5)/3 and the same contradiction.
Thus

    b,c>2/3.                                          (4)

## 3. The two actual epsilon points make both inward slopes tiny

Set

    r_A=a/b,       r_C=s/c.

The actual A near point epsilon e_A lies at horizontal deficit
t_A=h-(epsilon e_A)_x between zero and 2epsilon. In its original
A coordinates write it p_A+xi u+eta v. Since
a xi+b eta=t_A, its height is at least y_A-r_A t_A. Hence

    y_A<=epsilon+2epsilon r_A.

Similarly the actual C near point has height at most
y_C+r_C t_C, where 0<=t_C<=2epsilon. Therefore

    y_C>=-epsilon-2epsilon r_C,
    D<=2epsilon(1+r_A+r_C).                            (5)

But K=bc(r_A+r_C), so (3)--(4) imply

    D>=min(b,c)(r_A+r_C)>(2/3)(r_A+r_C).

Combining with (5),

    r_A+r_C<3epsilon/(1-3epsilon)
               <(60/19)epsilon<1/19.                 (6)

In particular

    a,s<(60/19)epsilon<1/19,
    b,c>99/100,
    |y_A|,|y_C|<(21/19)epsilon.                        (7)

For the last assertion use y_C<=y_A and the two one-sided bounds
in (5). The bound b,c>99/100 follows by squaring from a,s<1/19;
the exact reserve is 360/361-(99/100)^2=61839/3610000>0.

All these statements concern the unchanged actual roots and their
original radial points. Their force magnitudes have not been varied.

## 4. The complete genuine-leaf support cover at the two roots

At A, the actual vertex p_A is too close to O to be its radial
S support d e_A. Its opposite vertex p_A+u+v has first coordinate
less than -59/60 and second coordinate greater than 4/5, by (7).
Its squared norm exceeds d^2: already

    (59/60)^2+(4/5)^2-(61/60)^2=43/75>0.

The two near owned axes -u,-v have support heights bounded in
absolute value by |h|+|y_A|<d, so they cannot be its genuine leaf
direction either. The complete remaining A support cover is:

* north type: the owned +u axis or strict vertex p_A+u;
* west type: the owned +v axis or strict vertex p_A+v.

All side-axis endpoint descriptions are included in their owned
case. The reflected calculation at C gives only its south type
(owned +v' or strict p_C+v') and west type (owned +u' or strict
p_C+u'). Its far opposite vertex is too far by the reflected
same estimate. This is a physical leaf-support cover and does not
assume the leaf direction equals a root side axis.

## 5. A west leaf at either root repeats the other actual S leaf too closely

First suppose A has the west type. In either of its two cases its
actual unit leaf direction satisfies

    (e_A)_x<0,
    |(e_A)_y|<(81/19)epsilon<3/40.                    (8)

For the owned +v case use |(e_A)_y|=a and (7); for the strict
vertex use d e_A=(h-b,y_A-a), d>1 and (7).

Both cases also force

    h<-(17/20)epsilon.                                (9)

For the owned case its exact support identity is
1-bh-a y_A=d, so

    h=(-epsilon-a y_A)/b
       <-epsilon+(1260/361)epsilon^2
       <-(340/361)epsilon<-(17/20)epsilon.

The numerator used in this division is negative; replacing the
denominator b<1 by one is therefore an upper bound, as displayed.

For the strict west vertex, its unchanged radius identity gives

    h=b-sqrt(d^2-(y_A-a)^2)
       <1-sqrt(d^2-((81/19)epsilon)^2).

The needed exact square comparison is

    d^2-((81/19)epsilon)^2-(1+(17/20)epsilon)^2
       =epsilon[3/10-(6561/361-111/400)epsilon]
       >epsilon*(4957/2888000)>0.

This proves (9). Reflection gives the identical result for a west
leaf at C, including its owned-axis identity and both signs of y_C.

The other root, say C, has its actual point epsilon e_C in x<=h.
Thus (9) forces (e_C)_x<-17/20. The west leaf's direction also
has first coordinate below -17/20 by (8). The two unit directions
therefore differ horizontally by less than 3/20. Vertically they
differ by less than

    3/40+sqrt(111)/20<3/40+11/20=5/8.

Their squared distance is less than 661/1600. The two original
genuine radial S leaf centers are (d+1/2)e_A,(d+1/2)e_C, so
their squared distance is strictly below

    (91/60)^2(661/1600)
       =5473741/5760000<1,

with reserve 286259/5760000. Their open inscribed disks overlap,
contradicting distinct actual units. Thus neither root has a west
leaf. The full remaining leaf cover is

    A has its north type,       C has its south type.  (10)

## 6. A's complete true force equation pins its actual B port near the west axis

In either north type, the genuine A leaf direction has v-component
at most zero: it is zero for +u and strictly negative at the strict
vertex p_A+u. The original A-to-H normal is e_x, whose v-component
is -b<0. Project the complete true A3 equation, with all positive
magnitudes retained, onto v. Its actual A-to-B normal must have
strictly positive v-component.

The full local cover in Section 1 makes the other A port a distinct
strict adjacent vertex. At p_A+u, strict outward normals have
negative v-component. The opposite vertex is not an allowed
physical triangle port. Therefore the unchanged actual AB point
is exactly

    P_B=p_A+v=(h-b,y_A-a).                             (11)

Its vertical coordinate has absolute value less than
(81/19)epsilon<3/40 by (7). This is the actual strict vertex from
the original local cover; no side mean is moved to it.

## 7. That actual B cannot be a physical boundary unit

The same B has its original physical HB contact T in H, so T_x>=h.
Every point of a unit square lies within 1/sqrt(2) of its center.
Using T and the unchanged point (11), its center (X,Y) satisfies

    X>=h-1/sqrt(2)>-3/4,
    X<=h-b+1/sqrt(2)
       <epsilon-99/100+71/100<0,

and

    |Y|<3/40+71/100=157/200<4/5.

Consequently

    |c_B|^2<9/16+16/25
       <1833/1000,

with exact reserve 1261/2000. This contradicts the original true
loaded B2's physical boundary-center lower bound. The argument
does not need to identify a positive circle corner or change any
individual zero weight.

Sections 1--7 exhaust the actual parallel-frame exits, full same-wall
separating-axis alternatives, all genuine S leaf features, and the
actual root's full force projection. They exclude the entire
same-H-owned-side interface. H's own leaf is retained as a real near
root and in every prior interface caller; its force is never deleted.
The actual H5 equation is not replaced by an H4 equation. All nine
physical units remain.

Together with the separately reviewed two-root-owned and adjacent-
H-owned sources, the only remaining high-radius all-S owner form is
the mixed one-root-owned/one-H-owned interface. This source does not
by itself claim the whole C2.33.b3 cell closed.

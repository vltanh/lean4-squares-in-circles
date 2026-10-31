# A D-leaf diamond cannot have a parallel second hub

**Status: complete hand proof; root and separate independent full hand audits passed.** Work in

\[
                    79/40\le R\le\sqrt{1105}/16.
\tag{1}
\]

Consider the selected positive diamond with hubs A,U, tips B,C and a
radial D leaf L attached to A. Its positive pair edges are

\[
                    AL,\ AU,\ AB,\ AC,\ UB,\ UC.
\tag{2}
\]

The tips are loaded by the degree-two triangle obstruction. U is loaded
by NO_UNLOADED_DIAMOND_HUB.md. The articulation A is physically clear.
The physical two-circle-corner mask of U is already excluded in
D_DIAMOND_RADIAL_HUB_EXCLUSION.md. Here U has exactly one physical
circle corner z.

**Theorem.** The frames of A and U cannot be parallel. The proof retains
both physical masks of B,C, every individual zero corner weight, all
shared-side application means and all four arbitrary extra squares.
It never applies a degree-two force or concurrence equation to U.

The generic fixed-tip selection used below is made simultaneously with
the existing strict, nonradial point-normal choices before invoking the
physical multiplier theorem. No normal is changed after extracting a
stress.

## 1. The articulation and the complete central-normal cover

Rotate the D leaf east. As in
D_DIAMOND_RADIAL_HUB_EXCLUSION.md, Section 1, put

\[
 s=1+\sqrt2-R,\quad r=1-s=R-\sqrt2,\quad
 A=[-s,r]\times[H-1,H],\qquad 0<H<1.
\tag{3}
\]

The D articulation form and strict height range follow from
RADIAL_BRIDGE_AND_LEAF_REDUCTION.md and the local articulation argument
in TRIANGLE_LEAF_CORE_REDUCTION.md, Section 3. The leaf force on A is
a positive multiple of e_x, applied at (r,0), and has zero origin
moment. We use

\[
 0<s<9/20,\quad r>11/20,\quad
 h:=\sqrt{R^2-1/4}-1>9/10,\quad R^2>61/16.
\tag{4}
\]

Every positive circle atom of B or C has positive scalar product with
z, because U physically touches both tips. Summing the component force
equations and taking a scalar product with z therefore shows z_x<0:
the only remaining load is the positive eastward leaf resultant.

The case z_y=0 would give z=(-R,0). Its distance from every point of A
is at least R-s>61/40>sqrt(2), impossible because U touches A and has
diameter sqrt(2). Reflect in the horizontal axis so that

\[
                              z_x<0<z_y.
\tag{5}
\]

Every actual AU contact point p has p_y>0. Indeed, for p in A with
p_y<=0, if z_x<=-s then

\[
 |z-p|^2\ge(z_x+s)^2+z_y^2
             =R^2+s^2+2sz_x\ge(R-s)^2>2.
\]

If -s<z_x<0, instead |z-p|^2>=z_y^2>R^2-s^2>(R-s)^2>2.
Both cases contradict p,z belonging to one unit square.

Let n_0 be the actual outward AU normal from A. A negative vertical
component would expose A's bottom side, whose height H-1 is negative.
Consequently (n_0)_y>=0.

We next exclude (n_0)_x>0. Its application would have x=r. The strict
support-span lemma, reflected from
UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md, puts the whole unit U in
x>r-1=-s. In particular 0<-z_x<s. Global vertical load balance supplies
a positive circle atom w of B or C with w_y<0. Its acuteness with z
forces w_x<0. Since that tip touches A,

\[
                         0<-w_x\le s+\sqrt2.
\]

Two radius-R vectors with negative horizontal and opposite vertical
coordinates can be acute only if z_x^2+w_x^2>R^2. This follows by
squaring their positive horizontal product against the absolute
vertical product. But here

\[
 z_x^2+w_x^2<s^2+(s+\sqrt2)^2
       <(9/20)^2+(19/10)^2=61/16<R^2,
\tag{6}
\]

where sqrt(2)<29/20. This is impossible.

Finally n_0=e_y is impossible. That normal is owned by A. Applying
UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md to the physical triangles
AUB and AUC gives (n_B)_y,(n_C)_y>=0, where n_B,n_C are the actual
outward normals from A. Positive force balance on A would then have
a strictly positive vertical component from AU and no negative term.

Thus, without any frame hypothesis yet, the complete central cover is

\[
                       (n_0)_x<0,\qquad(n_0)_y\ge0.
\tag{7}
\]

The horizontal alternative is n_0=-e_x, with an application on A's
left wall at positive height. Every nonhorizontal alternative is
strictly northwest, with the fixed A application Q=(-s,H).

## 2. Parallel frames and an oblique central normal

Suppose the frames of A and U are parallel and (n_0)_y>0. Since Q is
A's northwest support vertex and U's southeast support vertex,

\[
                         U=[-s-1,-s]\times[H,H+1].
\tag{8}
\]

The positive upward AU reaction requires a negative vertical component
from at least one of the A-tip normals. Call that tip C. Its A
application has height H-1. The strict support-span lemma in the
vertical direction puts every point of C strictly below height H.
It cannot touch U in (8). This excludes the entire oblique alternative,
including all actual point-normal choices.

## 3. A horizontal central normal gives an upper aligned wall unit

We are left with n_0=-e_x. The parallel frames make the two physical
support sides vertical. A singleton intersection would be a
point-only vertex/vertex contact carrying a side-axis endpoint normal,
contrary to the selected strict point-normal convention. Hence AU is a
positive-length shared side, whose actual weighted mean is retained.

Define

\[
       Y=\sqrt{R^2-(s+1)^2},\qquad k=Y-1.
\tag{9}
\]

The unique physical circle corner in (5) forces

\[
                 U=[-s-1,-s]\times[k,k+1],\qquad z=(-s-1,Y).
\tag{10}
\]

Indeed the upper-left vertex is the unique farthest vertex of this
aligned unit. We have

\[
 Y^2>(79/40)^2-(29/20)^2=2877/1600>16/9,
 \qquad Y>4/3,\quad k>1/3.
\tag{11}
\]

The shared AU side requires H>k. Its actual mean has height
y_0 in [k,H], so y_0>0.

Applying the side-normal obstruction with n_0=-e_x gives
(n_B)_x,(n_C)_x<=0. Vertical force balance on A now leaves precisely
two alternatives:

* both tip normals are horizontal and equal -e_x;
* their vertical components have strict opposite signs.

Neither statement fixes either of their application means.

## 4. The all-horizontal alternative is impossible

Suppose n_B=n_C=-e_x. Write the three actual left-wall application
heights y_0,y_B,y_C, with positive magnitudes mu_0,mu_B,mu_C.
Origin-moment balance on A is

\[
                     \mu_0y_0+\mu_By_B+\mu_Cy_C=0.
\tag{12}
\]

Since y_0>0, label a tip with negative mean as C, so y_C<0.
The unit C has rightmost support x=-s and touches U.

If C is aligned, its physical circle contact forces its vertical
interval to be either [Y-1,Y] or [-Y,1-Y]. The negative application
mean selects the second, which is disjoint from U. Thus C has a
unique rightmost vertex p_C=(-s,y_C).

Let f be any actual separating normal from U to C. We first have
f_y<0. If f_y>0, evaluate f at p_C and at the upper support vertex
of U: for f_x>=0 they have the same x-coordinate and p_C has lower
y-coordinate; for f_x<0 the additional horizontal difference also
has negative scalar product. Either violates the minimum support
inequality for C. If f_y=0 and f_x<0, that inequality fails by the
horizontal difference alone. If f_y=0 and f_x>0, C would be wholly
in x>=-s while also having rightmost support -s, impossible for a
unit square.

For f_y<0, all three horizontal signs are now exhausted. If f_x<0,
the U application is (-s-1,k), and strict support span makes
max_C x<-s, a contradiction. If f_x>0, the U application is
(-s,k), which must equal C's unique rightmost vertex; that gives
y_C=k>0. If f_x=0, C has top support y=k as well as right support
x=-s. The purely geometric Lemma 2.1 of
D_LEAF_PARALLEL_LEFT_EXCLUSION.md then makes C strictly circle-clear.
That lemma applies with exactly (9), retains every frame and its
aligned endpoints, and uses no force equation on either square.

Each case contradicts the physical circle contact of C. This excludes
the all-horizontal alternative with arbitrary shared-side means.

## 5. A downward tip is unique-corner and meets U through its top

Choose C with (n_C)_y<0 in the remaining alternative. If (n_C)_x=0,
then C lies in y<=H-1<0 and cannot touch U, which lies above k>0.
Hence n_C is strictly southwest and its A application is

\[
                              P=(-s,H-1).
\tag{13}
\]

This application is too central for C to have two physical circle
corners. Indeed H>k>1/3 gives

\[
                |P|^2=s^2+(1-H)^2
                         <81/400+4/9<81/100.
\tag{14}
\]

Every point of a physical two-circle-corner unit has norm at least
h>9/10: it is a radial S unit with inner radial support h. Thus C
has exactly one physical circle corner. This conclusion is about the
physical mask, independent of its individual multiplier values.

We next show that the actual UC normal f, directed from U to C, is
vertical down, using no force or torque equation on U. We have
P_x=-s and P_y<0<k. The support comparison at P excludes f_y>0 for
both signs of f_x, just as in Section 4. It also excludes f_y=0,
f_x<0. If f_y=0,f_x>0, then C lies in x>=-s. Since n_C is strictly
southwest and P minimizes n_C on C, every point of C would then have
y<=P_y<0. It could not touch U. Therefore f_y<0.

If f_x<0, U's support point (-s-1,k) and strict support span contradict
P_x=-s. If f_x>0, its support point T=(-s,k) belongs to C, but
n_C dot T<n_C dot P because their x-coordinates agree and T_y>P_y.
This contradicts P being a minimum of n_C. Consequently

\[
                     f=-e_y,\qquad \max_C y=k.
\tag{15}
\]

## 6. The remaining fixed-tip geometry has a strict radius deficit

The unit C cannot be aligned. Its strict southwest minimum would
be a vertex, but P_y=H-1 lies strictly between the two possible
vertex heights k-1 and k, since H>k and H<1.

Thus its top support is a unique vertex T, and for a,b>0 with
a^2+b^2=1 write

\[
 p=(-a,-b),\qquad q=(b,-a),\qquad
 C=T+[0,1]p+[0,1]q.
\tag{16}
\]

The actual UC application is the fixed point T. The scalar product
n_C dot p is positive. Therefore the minimum feature of n_C on C
is T, the side T+[0,1]q, or the vertex T+q. The first is impossible
because P_y<k=T_y.

If P=T+q, AC is a point-only vertex/vertex contact and its chosen
normal is free and strict. The unique-corner body C has two distinct
fixed applications P,T. GENERAL_FIXED_TIP_NORMAL_SELECTION.md excludes
that positive star in the simultaneous selected certificate. There
is no variable shared-side mean at UC: C's top is a unique vertex.

It follows that, for some 0<t<1,

\[
                        P=T+tq,\qquad n_C=p.
\tag{17}
\]

Let mu>0 be the AC magnitude and gamma>0 the UC magnitude. With the
circle force written outward, force balance on C is

\[
 F_C=\mu p-\gamma e_y
      =(\mu+\gamma b)p+\gamma a q.
\tag{18}
\]

Both coefficients in its own frame are strictly positive. Because C
has a unique physical circle corner, its circle vector has the same
direction as that corner, whose two own coordinates must be positive.
The corner is therefore the one opposite T:

\[
 z_C=T+p+q
      =(-s-a+(1-t)b,\ k-a-b).
\tag{19}
\]

Both global coordinates of z_C are negative, by (18). Using (11),
0<t<1 and sqrt(2)<43/30 gives

\[
 0<-(z_C)_x<s+1<29/20,
 \qquad
 0<-(z_C)_y<\sqrt2-1/3<11/10.
\tag{20}
\]

Consequently

\[
         R^2=|z_C|^2<(29/20)^2+(11/10)^2=53/16<R^2,
\tag{21}
\]

a contradiction. This finishes both alternatives from Section 3.

## 7. Scope of the complete exclusion

The physical radial mask of U was already excluded by
D_DIAMOND_RADIAL_HUB_EXCLUSION.md. Sections 1--6 exclude every remaining
parallel-frame U, for every actual central support normal and every
tip mask. The central shared-side mean is retained until A's actual
moment equation is used. All later singleton applications are forced
by physical geometry before invoking fixed-tip selection.

The argument excludes the core itself and does not move or constrain
any of the four extra squares. It does not assert that the entire
D-leaf diamond is closed: the nonparallel second-hub alternatives,
including a horizontal central contact at a U vertex and a northwest
central contact at A's upper-left vertex, remain separate gates.

# Complete classification of the distinct-S/S parallel-articulation wall

**Status: complete hand classification; root and independent full hand audits passed.**
This is a classification of the entire parallel-articulation wall chart
in C1.3.b2. The four arbitrary completion squares are bounded separately
in DISTINCT_S_LEAF_WALL_UPPER_CAPACITY.md and DISTINCT_S_LEAF_WALL_LOWER_EMPTY.md;
TRIANGLE_TWO_BRIDGES_CELL_CLOSED.md assembles the complete cell.

Put
\[
 R_0=\frac{\sqrt{17}}2<R\le\frac{\sqrt{1105}}{16},\qquad
 d=\sqrt{R^2-1/4}-1=1+\delta,\qquad 0<\delta<1/60.
\tag{1}
\]
The positive triangle is A,B,C, with radial S leaves at A and B.
The previously audited domain and corner-mask theorems give exactly
one physical circle corner on C, nonzero triangle moment, and positive
radial concurrence at every nonparallel three-force body. Suppose A
has parallel cycle forces. The full reduction in
DISTINCT_S_LEAVES_PARALLEL_ARTICULATION_REDUCTION.md supplies this
chart for a compatible necessary certificate; its final section also
derives the following form directly from the parallel premise:
\[
 A=[\delta,d]\times[t-1,t],\quad 0<t<1,\qquad
 n_{AB}=n_{AC}=-e_x.
\tag{2}
\]
Write the actual two wall applications as
\[
             P_B=(\delta,Y),\quad P_C=(\delta,Z),
                    \qquad Y>0>Z,\quad Y-Z\le1.
\tag{3}
\]
Every shared-side mean remains an actual variable throughout.

**Theorem.** After the indicated rotation, reflection and labeling,
every selected core in (2) belongs to the following one-parameter family:
\[
 \begin{gathered}
 x=\frac{\sqrt{70}-8}{4},\quad \delta=x^2,\quad d=1+x^2,
 \quad R^2=(2+x^2)^2+\frac14,\qquad u=1-x^2,\\
 A=[\delta,d]\times[t-1,t],\\
 B=[-u,\delta]\times[2x-1,2x],\qquad
 C=[-u,\delta]\times[2x-2,2x-1],\\
 \frac{x(1-2x)}{1-x}\le t<2x.
 \end{gathered}
\tag{4}
\]
The A leaf is \([d,d+1]\times[-1/2,1/2]\). The B leaf is
\[
 p+[0,1]e+[-1/2,1/2]Je,\qquad
            p=(-u,2x),\quad e=p/d.
\tag{5}
\]
All cores in this interval are physically realizable and admit the
positive stresses described in Section7. In particular the family is
nonempty; core exclusion is not a valid exit. Its universal completion
capacity of at most three is proved in the two cited capacity sources.

## 1. Preliminary signs and the complete oblique-C chart

C's positive radial concurrence has height Z, so its unique circle
corner has negative y-coordinate. The BC direction k from B into C
therefore has negative y-component, by C's force balance. B's two
cycle forces cannot be parallel: their balance would make its leaf
horizontal, contradicting vertical balance of the three global loads.
Positive radial concurrence at B then puts its leaf direction strictly
above the horizontal axis.

Every point of a circle-touching unit square has norm at least
\(r=R-\sqrt2>5/8\). Applied to P_C, with (1)--(3), this gives
\[
                     -1<Z<-3/5,\qquad 0<Y<2/5.
\tag{6}
\]
For example \(\delta^2+(3/5)^2<(5/8)^2\); the upper bound on Y
then follows from Y-Z<=1.

If C is oblique to A, P_C is its unique rightmost vertex. Write
\[
 C=P_C+[0,1]n+[0,1]m,\qquad
 n=(-a,b),\quad m=(-b,-a),\quad a,b>0,\quad a^2+b^2=1.
\tag{7}
\]
The strict point-normal convention makes P_C a relative-side-interior
point of A. Its adjacent corners have norms less than
\(61/60+1=121/60<R_0\), so C's unique circle corner is opposite:
\[
                     z_C=(\delta-a-b,Z+b-a).
\tag{8}
\]
If a<=b, then its y-coordinate has absolute value less than1 and
its x-coordinate has absolute value less than sqrt(2), contradicting
R^2>17/4. Thus a>b. Put
\[
 S=a+b>1,\qquad T=a-b>0,\qquad \rho=b/a\in(0,1).
\]
The concurrence is \(q_C=(q_x,Z)=\kappa z_C\), where
\[
 \kappa=\frac{|Z|}{|Z|+T}=1-\frac{T}{|z_{Cy}|},\qquad
 |z_{Cy}|^2-T^2=\frac94+\delta(4+2S)>\frac94.
\]
Since T<1, this gives the uniform quantitative obstruction
\[
 \kappa>1-\frac2{\sqrt{13}}>\frac49,
 \qquad q_x<0,\qquad |q_x|>\frac49\frac{59}{60}=\frac{59}{135}.
\tag{9}
\]
Also C is wholly below the horizontal axis. Otherwise Z+b>=0,
so \(|z_{Cy}|\le a\), and (8) would again give R^2<3.

## 2. The complete oblique-B leaf cover

For an oblique B, its unique rightmost vertex is P_B. Write
\[
 B=P_B+[0,1]v+[0,1]w,\qquad
 v=(-c,s),\quad w=(-s,-c),\quad c,s>0,\quad c^2+s^2=1.
\tag{10}
\]
Exactly the following two positive-y radial S-leaf features can remain:

* **Vertex feature:** the upper adjacent vertex
  \(V=P_B+v=(\delta-c,Y+s)\), with
  \[
                       Y^2+2Ys=2\delta(1+c).
  \tag{11}
  \]
* **Side feature:** direction v on the far-v side, with actual radial
  application dv and
  \[
                              Ys=\delta(1+c).
  \tag{12}
  \]

For completeness, P_B has norm less than d. The opposite vertex has
own-frame coordinates greater than 59/60 and 7/12, respectively;
its squared norm exceeds 4706/3600>(61/60)^2>d^2. The lower adjacent
vertex could have positive radial y-component only if Y>c. Its
outward-support condition would then give Ys<=delta c, hence
s<delta and c>9/10, contradicting c<Y<2/5. The only positive-y
side normals are v and -w. The latter has support delta s+Yc<d.
Thus (11)--(12) are exhaustive, including their radial endpoint
states. No actual side application is replaced by a midpoint.

Whenever C is oblique, its wall contact is fixed and its BC contact
is fixed unless B and C are parallel. Those parallel oblique frames
are impossible: both have rightmost support x=delta, and their
vertical vertex displacement is Y-Z<=1. Its projections onto both
oblique axes are strictly less than1, forcing interior overlap.

The two C applications are distinct. If they coincided, C's torque
and force equations would make P_C a radial multiple of z_C;
their negative y-coordinates make that multiple positive, whereas
their x-coordinates have opposite signs. The general fixed-tip
selection therefore removes every free BC vertex normal in this
chart. It is the finite compatible selection of
GENERAL_FIXED_TIP_NORMAL_SELECTION.md, not an assumption on a
post-extraction normal. Thus at least one of B,C owns the BC axis.

## 3. Both B and C oblique: all four owners are impossible

Use (7) and (10), and put
\[
                      D=Y-Z\le1,\qquad E=bc-as.
\]
The equality E=0 is exactly the parallel-frame case already excluded.
As k_y<0, the complete owned-axis list is
\[
                 k=m,\quad -n,\quad w,\quad -v.
\tag{13}
\]
These alternatives also retain every owned-side endpoint.

### 3.1. C owns its near m-normal face

Here k=m and the C point is P_C+tau n. The B maximum of m is
P_B+v+w when E>0. Its x-coordinate would require tau a=c+s>1,
impossible. Therefore E<0, the contact is P_B+w, and
\[
 \tau=s/a,\qquad D=c+\rho s,\qquad
 K:=s-\rho c>0,\qquad q_B=(\delta-K,Y).
\tag{14}
\]
Since D<=1,
\[
                 \rho\le\frac{s}{1+c},\qquad K\ge\frac{s}{1+c}.
\tag{15}
\]
For the vertex feature, positive concurrence with V gives
\[
                     K=\frac{Yc+\delta s}{Y+s}.
\]
Combining this with (11) and (15) yields
\[
                  s^2\le Y(1+c-s)+\frac{s}{2}Y^2.
\tag{16}
\]
If s>=2/5, then c<=sqrt(21)/5<23/25 and
\(Y<(1+c)/(60s)\). Dropping the negative term in (16) and
using that last bound once more gives
\[
 s^3<\frac{121(1+c)^2}{7200}
     <\frac{121(48/25)^2}{7200}<\frac8{125},
\]
a contradiction. Hence s<2/5.

For the side feature, concurrence is along v, so
\[
 K=\delta+\frac{cY}{s}=\frac{\delta}{1-c}.
\]
Equations (12) and (15) imply
\(\delta\ge s^3/(1+c)^2\). If s>=2/5, then again c<23/25,
and
\[
                    s^3<\frac{(48/25)^2}{60}<\frac8{125},
\]
which is impossible. Thus s<2/5 for both leaf features, so c>9/10
and rho<4/19. At C, intersection of the contact line with y=Z gives
\[
                       q_x=\delta-\frac{s}{a^2}
                           =\delta-s(1+\rho^2).
\]
Its negative sign from (9) now implies
\[
           |q_x|<\frac25\left(1+\frac{16}{361}\right)
                  =\frac{754}{1805}<\frac{59}{135},
\]
contradicting (9). This covers both complete B-leaf features.

### 3.2. C owns its far n-normal face

Here k=-n and C's point is P_C+n+tau m. The dot products with B's
axes are -ac-bs<0 and E. If E<0, B's contact would be P_B, whose
x-coordinate is delta, whereas this C face is strictly left of it.
If E>0, the B contact is P_B+w and the x-equation gives
\(s=a+\tau b\ge a>1/\sqrt2\). Thus s>c and a>b, which imply
as>bc, contradicting E>0. This owner is impossible.

### 3.3. B owns its far w-normal face

Here k=w and B's point is P_B+w+eta v. Its dot products with C's
axes are -E and bs+ac>0. If E<0, C's contact would be P_C, again
with an impossible x-coordinate. If E>0, it is P_C+n. Consequently
\[
                \eta=(a-s)/c,\qquad D=b+\frac{1-as}{c}.
\]
But E>0 means as<bc, giving D>1/c>1. This contradicts (3).

### 3.4. B owns its near v-normal face

Here k=-v and B's point is P_B+eta w. The C dot products are
-ac-bs<0 and -E. If E>0, the contact would be C's circle corner,
which no other contained unit square can share. If E<0, the
contact is P_C+n and eta=a/s<=1.

The B side-leaf feature is impossible by translation balance: the
leaf and BC directions are parallel to v, while its positive wall
reaction is horizontal. For the vertex feature, concurrence gives
\[
 q_B=(\delta-a/s^2,Y)=\kappa_B V,\qquad
                 \kappa_B=Y/(Y+s)\in(0,1).
\]
Thus \(a/s^2=(1-\kappa_B)\delta+\kappa_B c<\delta+c\).
On the other hand
\[
 \frac{a}{s^2}-c
 \ge a(1+c^2)-c
 \ge a-\frac1{4a}
 >\frac1{2\sqrt2}>\frac13>\delta,
\]
because a>1/sqrt(2). This is the last contradiction in (13).

## 4. B aligned and C oblique

Now B=[delta-1,delta] times an interval [T_B-1,T_B]. Since it
contains the positive-height mean Y, T_B>0. C is wholly below zero
by Section1, so B's bottom is strictly below zero. A positive-y
radial S leaf can therefore occur only at B's upper-left vertex:
the top side would require T_B=d>1, and the upper-right vertex
would require \(T_B=\sqrt{1+2\delta}>1\). Both would put B
strictly above C. Consequently
\[
                       T_B=T_0:=2\sqrt\delta<4/15.
\tag{17}
\]
No other side direction or lower vertex has a positive radial
y-component. The same fixed-tip selection still removes a free BC
normal; all other contacts on C are fixed, and coincidence was
excluded above.

If C owns its near m-normal face, B's support point is its bottom-left
vertex, requiring tau a=1 on a unit C side, impossible. If C owns
its far n-normal face, B's support point is its bottom-right vertex
at x=delta, whereas that C face lies strictly to the left. B's only
possible owned direction with negative y-component is -e_y. It
contacts C's upper adjacent vertex P_C+n, giving
\[
                       Z=T_0-1-b.
\tag{18}
\]
Since Z>-1, we have b<T_0<4/15 and a>14/15. C concurrence is
\((\delta-a,Z)\), and its determinant with (8) is
\[
                       (a-b)(a-\delta)=b(1-T_0+b).
\tag{19}
\]
The left side exceeds (2/3)(55/60)=11/18; the right side is less
than (4/15)(19/15)=76/225. Equation (19) is impossible. Shared BC
would make the two frames parallel, outside this case. All owners
have now been covered.

## 5. C aligned and B oblique, including its variable wall mean

Write C=[delta-1,delta] times [V_0-1,V_0]. Its negative-y circle
corner must be its lower-left corner. Indeed the left x-coordinate
has larger absolute value than the right, and a lower circle corner
is farthest only when V_0<=1/2; equality would give two physical
circle corners and is already excluded. Thus
\[
 h_C=\sqrt{13/4+6\delta}>9/5,\qquad
 V_0=1-h_C<-4/5,\qquad z_C=(\delta-1,-h_C).
\tag{20}
\]
Since Z<=V_0 and Y-Z<=1, we have Y<1/5. The exhaustive B-leaf
features remain exactly (11)--(12).

### 5.1. A force/torque selection that does not fix C's mean

A free BC vertex contact has a fixed physical application q with
q_y<=V_0<0. B's other cycle application is its fixed vertex P_B.
Let p_L=d e_B be its actual fixed radial-leaf application, whose
y-coordinate is positive. Translation and torque balance at B
give the necessary determinant
\[
 \det(p_L,e_x)\det(q,k)
       -\det(p_L,k)\det(P_B,e_x)=0.
\tag{21}
\]
Its coefficient vector, up to sign, is
\[
                W=-Yp_L+(p_L)_yq,
            \qquad W_y=(p_L)_y(q_y-Y)<0.
\]
It is therefore nonzero. Prelisting the finite physical leaf/frame/
vertex assignments, choose each free BC normal outside this finite
set of determinant zeros. The BC junction is independent of the
wall junction, since their y-coordinates have opposite signs.
Matched opposite pairs do not identify edges sharing B. This is
compatible with the prior finite strict and generic choices,
uncrossing and thinning, for the same reasons as the general fixed-tip
selection. No unknown weight, C wall mean or B leaf-side mean is
chosen in advance. Thus BC again has an actual side owner.

### 5.2. Every remaining owner is impossible

If B owns its far w-normal face, C's contact is its top-right vertex
at x=delta, while the B face is strictly left of that line. If B
owns its near v-normal face, C's contact is its top-left vertex;
the x-equation on P_B+eta w would require eta s=1, impossible.
The only negative-y C axis is -e_y. In that case the B contact is
P_B+w, and
\[
                      Y=c+1-h_C.
\tag{22}
\]
C's concurrence has x-coordinate delta-s. Comparing it with
z_C gives \(\kappa_C=(s-\delta)/(1-\delta)\). Its height Z<=V_0
then forces
\[
                  s\ge1-\frac{1-\delta}{h_C}>\frac49.
\tag{23}
\]
For B's vertex leaf, concurrence is
\((\delta-s,Y)=YV/(Y+s)\), or
\[
                         Y(c-s)=s(s-\delta).
\tag{24}
\]
The left side is less than (1/5)(5/9)=1/9. The right side exceeds
\((4/9)(4/9-1/60)=77/405>1/9\), a contradiction.

For B's side leaf, concurrence along v gives
\(s^2-\delta s=cY\). With (12), this simplifies to Y=s^2.
Equation (22) becomes h_C=c+c^2. Since h_C>9/5, this forces
c>9/10 and hence s<sqrt(19)/10<4/9, contradicting (23).
Shared BC would make B aligned. This completes the entire case.

## 6. Both remaining frames align and force one exact radius

Sections3--5 force B and C parallel to A. Their horizontal interval
is [delta-1,delta]. Equation (20) still fixes C's top at
V_0=1-h_C<0. B contains Y>0 and physically touches C, so its bottom
equals V_0. Its top T_0=V_0+1<1. The positive-y radial S-leaf
feature check in Section4 then gives T_0=2sqrt(delta). Therefore
\[
                     h_C=2-2\sqrt\delta.
\]
With x=sqrt(delta), squaring (20) yields
\[
                         8x+2x^2=\frac34,
                  \qquad x=\frac{\sqrt{70}-8}{4}.
\tag{25}
\]
This proves all fixed positions and the exact radius in (4)--(5).
In particular 9/100<x<1/10, as direct substitution in (25) shows.

The A/C contact must have positive side length. At t=2x the two
aligned squares would have only a vertex/vertex contact with an
axis normal, which violates the strict selected convention. Thus
0<t<2x. The possible actual means are determined next; they supply
the sharper lower endpoint for t in (4).

## 7. All force magnitudes, all actual means and the whole slider interval

Normalize C's circle vector to z_C=(-u,-v_0), where
\[
                     u=1-x^2,\qquad v_0=2(1-x).
\]
Its two axis reactions have magnitudes u on AC and v_0 on BC.
Global force balance then fixes the remaining positive magnitudes:
\[
 \gamma_{AB}=w=\frac{u(1-x)}x,\qquad
 \alpha_A=\frac ux,\qquad
 \beta_B=\frac{d(1-x)}x.
\tag{26}
\]
Here alpha_A and beta_B are the two radial leaf reactions. Each
leaf's two outer circle weights are equal, respectively
\(\alpha_A/[4(d+1)]\) and \(\beta_B/[4(d+1)]\); C's single
circle weight is 1/2. All are strictly positive.

Let Y denote the AB wall mean as before, Z the AC wall mean, and
xi the BC mean's x-coordinate. The A and C torque equations give
\[
              Z=-\frac{1-x}{x}Y,\qquad
              \xi=-\frac{u}{2x}Y.
\tag{27}
\]
The B torque equation is then automatic. Every actual contact
interval, including its endpoints, is retained:
\[
 \begin{array}{c|c}
 AB & Y\in[2x-1,t]\\
 AC & Z\in[t-1,2x-1]\\
 BC & \xi\in[-u,\delta].
 \end{array}
\]
Substitution of (27), with Y>0 and t<2x, is equivalent to
\[
 \frac{x(1-2x)}{1-x}
       \le Y\le\min\left(t,\frac{x(1-t)}{1-x}\right).
\tag{28}
\]
This interval is nonempty exactly when
\[
                       \frac{x(1-2x)}{1-x}\le t<2x.
\tag{29}
\]
For t at the lower endpoint, some means are endpoints of genuine
positive-length sides. They are valid and are not discarded.
The common moment is nonzero because Y>0.

Conversely every t in (29), with any Y in (28), gives this positive
equilibrium on the whole five-body core. The fixed B,C and two
leaves are exactly the audited positive control in
DISTINCT_S_LEAF_CORE_AND_CORNER_MASK.md. Moving A within (29)
preserves its two shared wall contacts and its radial east-leaf
contact. It stays disjoint from the B leaf, whose right support is
\(-u+x/d<\delta\). The other nonincident pairs are unchanged.
Its corner norms satisfy \(|z_A|^2<d^2+1<R^2\), so it remains
physically circle-clear. All four completion squares remain arbitrary
physical obstacles and must still be counted.

## 8. The completed capacity input and this classification's scope

The full wall chart has now been reduced to (4)--(5), with the
entire interval (29), every force and mean in (26)--(28), and no
assumption on the four additional frames or centers.

The universal capacity exit, now proved in the upper/lower sources, is:

> Every disk packing containing one of the five cores (4)--(5), for
> any t in (29), contains at most three further unit squares.

The classification itself supplies the complete input domain. The cited
capacity sources prove whole-square routing, upper capacity three and
lower capacity zero for every parameter above. They do not select the
previously convenient height t=x or impose common frames on a completion
square. TRIANGLE_TWO_BRIDGES_CELL_CLOSED.md consequently closes C1.3.b2.
The unrestricted sharp theorem and equality classification remain open.

No Lean compilation, CI, numerical pose subdivision or unproved
normal convention is used in this manuscript.

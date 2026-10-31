# Both boundary neighbors of an off-origin tilted S root lie on one strict circle half-plane

Date: October 27, 2026.

**Status: complete hand local theorem, submitted for full root and
separate independent review.** The theorem retains the genuine root's
full three-force equation. Its two other neighbors may have arbitrary
degrees, other forces, actual means and physical circle masks.

Keep the original physical unit squares and compatible selected
certificate, with

    sqrt(17)/2<=R<=sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1=1+epsilon,
    0<=epsilon<1/60,       r=R-sqrt(2).

Suppose A has true positive degree three, with one genuine S leaf L
and two other actual physical boundary neighbors B,D. The genuine
leaf direction is not an own side axis of A. Suppose additionally
that O is not in int A; a side-boundary origin is retained.

Choose an own orthonormal frame and, if necessary, reflect the whole
packing so the actual leaf port and its direction are

    P=(U,V),       e=(U,V)/d,
    U>=V>0,       U^2+V^2=d^2,
    A=[U-1,U] times [V-1,V].                           (1)

The actual radial S unit is

    L=P+[0,1]e+[-1/2,1/2]f,       f=Je=(-V,U)/d.

Since V<d/sqrt(2)<1, the origin condition in the theorem is exactly
U>=1. Consequently, writing a=U-1 and b=V-1,

    0<=a<=epsilon<1/60,
    0<V<11/60<1/5,
    -1<b<-49/60,
    1<=U<=d<61/60.                                    (2)

Indeed V^2=d^2-U^2<=d^2-1<(61/60)^2-1=121/3600.

**Theorem.** Every physical circle corner z of B or D satisfies

    f dot z<0.                                         (3)

After naming the actual two neighbors, their exact root features
are a west normal at an actual left-side point and a strictly
southeast normal at A's lower-right vertex. No actual circle force
at B or D is needed in the proof of (3).

## 1. Two root vertices cannot support any boundary neighbor

Every point of a physical boundary unit has norm at least r, by
comparison with one of its actual circle corners and the unit's
diameter. The upper-left root vertex (a,V) has

    |(a,V)|^2<122/3600<r^2.

The lower bound follows, for example, from

    r^2>=25/4-sqrt(34)>419/1000,

using sqrt(34)<5831/1000. Thus no boundary neighbor can touch
A at that upper-left vertex.

No third physical unit can touch the actual leaf port P either.
At P, the open tangent sector of A is the southwest quadrant,
whereas the open tangent half-plane of L points along the strictly
northeast e. Their complement has two connected angular components:
the northwest gap of angle angle(e), and the southeast gap of angle
pi/2-angle(e). Both are strictly smaller than pi/2. An additional
unit at P has a connected inward tangent sector of angle at least
pi/2. It cannot fit in either gap without interior overlap. This
includes a vertex, side-interior or endpoint contact of the third
unit and uses the real inner-side midpoint of L.

Hence an actual boundary normal with positive second component
could only be the north own axis of A, acting at a point

    Q=(q,V),       a<=q<=U.                            (4)

The northwest and northeast strict normal cones have just been
excluded, with every shared-mean endpoint retained.

## 2. The real tilted S leaf excludes every north boundary neighbor

We prove the following force-free part using only (1)--(2) and
the actual L. Suppose a unit T physically touches the circle and
has minimum-y support at some Q in (4), with T contained in y>=V.
Its actual boundary point obeys

    q^2>=r^2-V^2>419/1000-(1/5)^2>(3/5)^2.

As q>=a>=0, this gives

    3/5<q<=U.                                         (5)

If its minimum-y support is a side, T is aligned:

    T=[z,z+1] times [V,V+1],
    q-1<=z<=q.

Physical avoidance of L gives z+1<=U. Indeed, if z+1>U, then
at height V+eta for a sufficiently small positive eta the actual
L's inner edge has x=U-(V/U)eta<U, its horizontal section continues
strictly to the right of U, and T's interval has z<=q<=U<z+1.
The two open sections overlap. Therefore every T corner has
horizontal magnitude below 61/60 and vertical magnitude below 6/5;
all are strictly inside the radius-R circle. This contradicts
physical boundary contact.

Otherwise Q is T's unique bottom vertex, and its complete tilted
frame is

    T=Q+[0,1](c,s)+[0,1](-s,c),
    c,s>0,       c^2+s^2=1.                           (6)

Put g=U-q>=0 and eta=V/U. Along the right upward edge in (6),
the original inner supporting line of L is first crossed at

    t_*=g/(c+eta s).

If g>=c+eta s, its endpoint has q+c<=U-eta s<=U. Every horizontal
corner magnitude is then below 61/60 and every vertical magnitude
below 1/5+sqrt(2)<97/60. Their squared norms are strictly below

    [(61)^2+(97)^2]/3600=13130/3600<17/4.              (7)

The only remaining case has 0<=t_*<1. At that crossing the actual
tangential coordinate on L's inner line, measured from P, is

    f dot (Q+t_*(c,s)-P)
        =g d s/(U c+V s)>=0.

If this number were less than 1/2, the original edge would enter
int L immediately after crossing. Thus physical nonoverlap gives

    g s >= (U c+V s)/(2d),
    q<=U-V/(2d)-(U/(2d))(c/s).                       (8)

Equality is retained; it is the real endpoint of the inner leaf
side, not an omitted tangency. Equations (2), (5), (8) yield

    c/s<(61/60-3/5)/(30/61)=61/72<1.                 (9)

The actual opposite corner Q+(c-s,c+s) consequently has horizontal
magnitude below 61/60, and (7) bounds its squared norm. The left
adjacent corner Q+(-s,c) and Q itself have the stronger coordinate
bounds 61/60 and 6/5.

For the remaining right adjacent corner, put t=U/(2d)>30/61>3/8.
Equation (8) gives

    q+c <61/60+c(1-t/s)<61/60+3/8=167/120.            (10)

The last inequality is uniform over the complete angle range.
For fixed t, the positive maximum of sqrt(1-s^2)(1-t/s) occurs
at s^3=t and equals (1-t^(2/3))^(3/2). Since t>3/8,
t^(2/3)>1/2, so this maximum is below 1/(2sqrt(2))<3/8.
On its nonpositive part the bound is immediate. Its vertical
coordinate is V+s<6/5. Hence this corner also has squared norm
below (167/120)^2+(6/5)^2<17/4.

All four actual T corners are strictly internal in every frame,
contradicting its physical circle contact. This proves that no
actual boundary neighbor of A has a positive vertical normal.
No force or concurrence equation at T entered the screen.

## 3. The full unchanged root torque leaves exactly west and southeast

A is physically circle-clear by its genuine leaf. Write its actual
root leaf force as alpha e, alpha>0, with zero origin moment.
The two other normal forces have nonpositive y components by
Sections 1--2. Their full sum is -alpha e; in particular at least
one has strictly negative x component.

If both x components were nonpositive, every force with negative
x component would have its actual application on A's left face
at a negative height. For a west normal that height is negative
by the boundary-point bound and (2); for a strictly southwest
normal it is b<0. Since all root x coordinates are nonnegative,
its moment x F_y-y F_x is strictly negative. A pure south force
has nonpositive moment as well. Their sum could not be zero.

Thus one force has negative x component and the other has positive
x component. Denote the actual force vectors, with their original
magnitudes included, by

    (-u,-v), (w,-z),
    u,w>0, v,z>=0,
    u-w=alpha U/d,
    v+z=alpha V/d>0.                                  (11)

If v,z>0, their actual support points are (a,b) and (U,b).
Their total origin moment is

    b(u-w)-a v-U z<0,

again impossible. If v>0 and z=0, the second actual application
is (U,y_R) with b<=y_R<=V. The full moment equals

    b u-a v-w y_R
       =(alpha/d)(bU-aV)+w(b-y_R)
       =(alpha/d)(V-U)+w(b-y_R)<0.                    (12)

No value of the original right-side mean is lost in (12).
Both v,z zero are incompatible with (11). Therefore the only
remaining whole feature domain is

    v=0,       z>0.

Name the actual neighbors accordingly. B has west normal and
its unchanged root application is

    P_B=(a,y),       b<=y<=V,
    y<-647/1000.                                     (13)

The last inequality follows from y^2>=r^2-a^2>
419/1000-1/3600>(647/1000)^2 and V<11/60. D has a strictly
southeast normal and its original root application is

    P_D=(U,V-1).                                     (14)

This force/torque argument retains both positive original pair
forces and the full genuine leaf force. It never assigns a root
degree two or invokes a triangle concurrence theorem.

## 4. Each original application excludes an entire circle semicircle

Use the actual orthonormal radial coordinates (e,f). For (13),

    p_f=f dot P_B=(-Va+Uy)/d<0,
    |p_e|=|e dot P_B|=|Ua+Vy|/d
                 <=a+V<1/5.                         (15)

Here |y|<1, U/d<=1, d>=1 and (2) give the final bound.
If an actual circle corner Z of B had f dot Z>=0, then

    P_B dot Z<=R |p_e|,
    |Z-P_B|^2>=R^2+|P_B|^2-2R|p_e|
               >=(R-|p_e|)^2>(9/5)^2>2.

This contradicts the diameter sqrt(2) of the original unit B,
which contains both P_B and Z. Thus every physical circle corner
of B has strictly negative f coordinate.

For the actual point (14), its radial coordinates are

    q_e=e dot P_D=d-V/d>0,
    q_f=f dot P_D=-U/d<0.

For a circle corner Z of D with f dot Z>=0, the same scalar-product
bound gives

    |Z-P_D|^2 >= (R-q_e)^2+q_f^2
       =(R-d)^2+1+2V(R/d-1)>2.                       (16)

Indeed R-d=1+R-sqrt(R^2-1/4)>1 and R/d>1. Equation (16)
again contradicts the unit diameter. Consequently every physical
circle corner of D also has strictly negative f coordinate.

This proves (3) for both actual neighbors, including two-corner
masks and all individual zero-weight limits. Their own loads
and positive degrees were never used.

## 5. Scope of the local result

The theorem is a strict one-sided conclusion for all physical
circle corners, not just for a selected resultant or one corner.
It requires the genuine root to retain exactly three positive
neighbors, its leaf direction to be tilted, and O not to belong
to its open interior. It makes no assumption about another near
unit or about a positive edge joining B,D.

A separate original graph and full component balance are needed
to turn this local conclusion into a contradiction. In particular
the additional leaf in the opposite-root C4 is not removed here;
its actual circular order is established in the complete caller.

No numerical pose, coefficient packet, Lean compilation, CI,
post-extraction normal selection, remote mutation or shared-ledger
edit is used.

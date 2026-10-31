# Adjacent long/short cycles: original normal cone and endpoint vertex reduction

Date: October 30, 2026 UTC.

**Status: complete proposed common family reduction, awaiting full
independent review. This source does not exclude the entire adjacent
seven-cycle or an arbitrary nine-square packing.**

The short transmitter adjacent to a long endpoint need not touch the
circle. This proof nevertheless determines the endpoint's actual
contact vertex, by using the two physical boundary marks farther along
the return arc. It retains the original normal and every full endpoint
equation. An exact subcritical six-unit diagnostic at the end shows why
the local pair and endpoint equations alone are insufficient: the
remaining boundary return or completion geometry must still be used.

Put Q=1105/256, M=91/60, L=89/60, and rho=5/4.

## 1. Literal unchanged-certificate domain

Consider the actual positive simple cycle

    A -- U -- V -- B -- W -- C -- D -- A.

All actual closed unit squares have pairwise disjoint open interiors
and lie in the same centered disk of squared radius q<=Q. The marked
units A,B,C,D physically touch that circle. U,V,W have zero total
circle load and full true positive degree two in the original physical
force-and-torque certificate. A and B also have full true degree two.
The degrees of C,D may be larger. The original cycle admits the
compatible physical routing and circle spokes required by the adopted
marked-order theorem. All other actual units and all positive edges,
means and individual circle weights are retained.

Rotate about the unchanged disk origin to make the signed long normal
from A to B equal to e_x. Use one common reflection to put the two
other entire marked units C,D above the long pair, as justified below.
No assertion that W physically touches the circle is made or needed.

**Theorem.** In that frame the following statements hold for every
member of this whole adjacent run-count family:

    88 degrees < arg(c_C) < 103 degrees,
    129 degrees < arg(c_D) < 144 degrees.              (1)

Let n be the original signed common normal of B--W--C. Then

    n_x < -2/15, n_y > 1/12.                          (2)

Choose B's dominant outward own axis and its upper transverse axis as

    u=(a,epsilon*b), v=(-epsilon*b,a),
    a>=b>=0, a^2+b^2=1.

The same unchanged normal satisfies

    n.u < -63/1000, n.v > 21/1600.                    (3)

Consequently the original B--W mean is exactly B's upper-inner vertex

    p_B=c_B-u/2+v/2.                                 (4)

The original long force-line height t is negative, and the total circle
resultant at B has strictly negative y component. If B is aligned,
y_B<=0. If B is tilted, its upper axis is v=(b,a), its outward axis
is u=(a,-b), and

    t<-1/2, y_B<0.                                   (5)

If either long endpoint is tilted, the original return mean at A is
also its upper-inner vertex with a strict inward/upward original
normal. This conclusion at A uses its actual physical boundary
neighbor D; the proof at B uses (1)--(3), not an invented circle
contact for W.

## 2. Actual long geometry and the radius window

Every actual center has norm less than M. Indeed a unit with center c
has a corner of squared norm at least |c|^2+|c|+1/2, and the value of
this expression at M exceeds Q by 31/57600.

Full unloaded force equations at U,V propagate equal magnitudes and
one common signed normal. Full moments make the actual consecutive
means differ parallel to it. Opposite support means of a unit can
have this property only at width one or sqrt(2): a zero own-axis
normal component exposes opposite sides, while two nonzero components
expose opposite vertices and parallelism forces equal absolute normal
components. The endpoint center projection is at least the internal
width sum plus one. Its strict upper bound 2M excludes a diagonal
among these two internals, since 2+sqrt(2)>91/30. Thus both actual
internal widths are one.

Write the unchanged long means as

    q_A=(s-1,t), q_M=(s,t), q_B=(s+1,t).              (6)

Endpoint halfwidths are at least one half. Their actual support
equalities and center bound give |s|<1/60. At an actual unit support
point p with unit outward normal e, the point p-e remains in the
same unit: each nonzero own-axis component exposes its corresponding
coordinate endpoint and moving inward changes that coordinate by
at most one. This also holds at every original shared-side mean.
It supplies actual points (s-2,t) in A and (s+2,t) in B. Therefore

    q >= (2+|s|)^2+t^2 >=4,
    |t|<=9/16.                                      (7)

In particular R>=2>79/40. The lower radius window of each imported
boundary-arc theorem is derived from this actual channel.

The force-free long-gap estimates give

    c_A=(-X_A,y_A), c_B=(X_B,y_B),
    L<X_A,X_B<M, |y_A|+|y_B|<=1/8.                    (8)

Their center directions are within five degrees of the signed x axes.
The complete return-side theorem, with the original compatible cycle
and circle spokes, puts both entire original C,D in y>1/120 after
one common reflection. It supplies the marked center order
B,C,D,A along that upper arc. Thus angles can be chosen with

    -5 degrees < theta_B < 5 degrees,
    175 degrees < theta_A < 185 degrees,
    theta_B<theta_C<theta_D<theta_A,
    0<theta_C,theta_D<180 degrees.                    (9)

No force line is identified with a center line in (6)--(9).

## 3. The two return angles

The frozen physical boundary-arc theorem gives center-angle separation
strictly greater than 41 degrees for every pair of distinct boundary
units. It also gives separation strictly greater than 93 degrees when
their Euclidean set distance is at least one.

For the original B--W--C path, the genuine unloaded degree-two force
equation supplies the same signed normal n at both ends. Telescoping
actual support equalities gives a support gap equal to the actual
width w_W(n), which is at least one. Hence dist(B,C)>=1 and their
minor center angle exceeds 93 degrees. In the directed order (9) this
implies theta_C-theta_B>93 degrees, including any directed gap larger
than pi. The other two consecutive marked separations give

    theta_D-theta_C>41 degrees,
    theta_A-theta_D>41 degrees.

Together with (9), these yield

    theta_C>88 degrees,
    theta_C<theta_A-82 degrees<103 degrees,
    theta_D>129 degrees,
    theta_D<144 degrees,

which is (1). The proof has not marked W as a boundary body or used
an equation after removing another positive neighbor.

## 4. A uniform cone for the original short normal

Put Delta=c_C-c_B. Because C is physically boundary and R>=2,
its center radius r satisfies r>=R-1/sqrt(2)>5/4. From (1),
its center height is greater than (5/4)sin(30 degrees)=5/8.
Thus Delta_y>0. Also theta_C>60 degrees, so
c_Cx<M/2<L<X_B; hence Delta_x<0.

The elementary strict estimate

    sin(13 degrees)<13*pi/180<143/630

uses pi<22/7. For completeness the latter follows from the exact
positive integral

    22/7-pi = integral_0^1 x^4(1-x)^4/(1+x^2) dx >0.

Since theta_C<103 degrees, equation (8) and |c_C|<M give

    |Delta_x|<M*(1+143/630)=70343/37800=:K_x,
    Delta_y<M+1/8=197/120=:K_y.                       (10)

The actual short support equalities give

    n.Delta=w_W(n)+h_B(n)+h_C(n)>=2.                  (11)

If n_x>=-2/15, then, because Delta_x<0 and Delta_y>0,

    n.Delta < (2/15)K_x+K_y
             =2-8927/81000<2,

contradicting (11). If n_y<=1/12, then

    n.Delta < K_x+K_y/12
             =2-49/21600<2.

Thus (2) is forced over the full actual width and orientation domain.

The long endpoint gap and the strict center bound imply
a+b<16/15 for B. The complete endpoint estimate gives

    b<7/100, a>399/400.                               (12)

One direct verification is as follows. First a-b>9/10 gives b<1/12
and a>99/100. Then ab<31/450, so b<62/891<7/100. Finally
1-(7/100)^2-(399/400)^2=3/32000>0.

Using (2), (12) and |n_x|,|n_y|<=1 gives, for either epsilon,

    n.u < -(399/400)(2/15)+7/100=-63/1000,
    n.v >  (399/400)(1/12)-7/100=21/1600.

Both own components are strictly nonzero with the stated signs.
The square's exposed support face is therefore the unique vertex
c_B-u/2+v/2. Every original positive-atom mean on that support face
is that same actual vertex. This proves (3),(4) even though W may
be entirely circle-clear.

## 5. Full endpoint equations and tilt consequences

Write P=c_B.u and T=c_B.v. The actual endpoint estimates give

    P-|T|>721/600>1, |T|<589/1800<1/2.

In particular P-1/2>0 and T+1/2>0. With
n=-gamma*u+eta*v, gamma,eta>0, the actual return moment is

    p_B cross n=(P-1/2)eta+(T+1/2)gamma>0.            (13)

All circle forces are radial about the unchanged origin and have
zero origin moment. The other positive body force at B is the
original inward horizontal long force, applied at q_B. Its moment
is mu*t, where mu>0. Full angular balance and (13) yield
mu*t+nu*(p_B cross n)=0, hence t<0.

The same full endpoint force equation has no vertical contribution
from the long force, while nu*n_y>0. Thus its original total circle
resultant has strictly negative y component. If B is aligned and
y_B>0, its only physical circle corner is its upper outer corner,
with positive y coordinate. This is impossible. Hence aligned B has
y_B<=0, retaining both physical corners and both original weights
when y_B=0.

Suppose b>0. If epsilon were positive, the long minimum-x support
vertex would be c_B-u/2+v/2, of height
y_B+(a-b)/2>-1/8+9/20=13/40>0. This contradicts t<0.
Therefore u=(a,-b), v=(b,a), and the actual long point is the
lower-inner vertex q_B=c_B-(u+v)/2. The actual return point remains
q_B+v.

If T>0, the unique physical circle corner is q_B+u+v. Its height
is y_B+(a-b)/2>13/40>0, again contradicting the negative circle
y resultant. Therefore T<=0. Since

    T=b(s+1)+a*t+1/2,

we obtain t<=-(1/2+b(s+1))/a<-1/2. Also
T=bX_B+a y_B<=0 gives y_B<0. Both physical circle atoms at T=0
remain in this argument; no weight is selected or discarded.

At A the unchanged other neighbor D is physically boundary and wholly
above. The complete endpoint contact-locus source applies literally.
If A is tilted, it gives its strict inward/upward upper-inner return
vertex and t<-1/2. If B is tilted and A aligned, the same source's
aligned endpoint result at t<=-1/2 excludes an upward side-interior
normal at A and forces its strict upper-inner vertex. Thus whenever
either endpoint is tilted, both original return means are their
upper-inner vertices, with the stated original normal cones. At B
this conclusion was proved without any boundary premise on W.

## 6. Useful aligned-endpoint section premise

If both endpoints are aligned, the original A--D contact-locus and
full endpoint force equation also give y_A<=0. Consequently their
actual upper-side heights f_i=y_i+1/2 satisfy

    3/8<=f_A,f_B<=1/2, f_A+f_B>=7/8.                  (14)

The actual B--W point is p_B=(s+1,f_B), and the original common
short normal is n=(-alpha,beta), with alpha,beta>0. For every point
(X,z) of C's actual section at z=5/4, the unchanged short support
inequality gives

    -alpha*X+beta*z >= -alpha*(s+1)+beta*f_B+1,
    X <= s+1+(beta*k-1)/alpha,
    k=5/4-f_B.                                      (15)

In particular

    X <= s+1-sqrt(1-k^2), 3/4<=k<=7/8,              (16)

because (1-beta*k)^2-alpha^2(1-k^2)=(beta-k)^2>=0,
and both sides before taking square roots are nonnegative.

This is an actual original-normal support bound for every C section
point. It assumes neither C's own frame nor a floor for W. Existence,
width and order of that section can be supplied by independent actual
square geometry; they are not inferred merely from (15).

## 7. Exact diagnostic: the local chain can exist below Q

The following six-unit pose shows that B/C containment, the angle
interval (1), the long endpoint geometry, and full equations at B
and the three transmitters alone do not exclude the family. It is
not a seven-cycle or a complete stress certificate on all six bodies.
The missing boundary unit D and the remaining endpoint equations are
not asserted to exist.

Set q_0=17/4<Q and a=1/sqrt(2). Take aligned actual units with centers

    c_A=(-3/2,0), c_B=(3/2,0),
    c_U=(-1/2,-3/4), c_V=(1/2,-3/4).

Put

    p=(1,1/2), n=(-a,a), v=(a,a),
    E=2-a/2, T=sqrt(q_0-E^2).

Define the other two actual unit squares in their orthonormal n,v
coordinates by

    W=[E-2,E-1]n+[T-1,T]v,
    C=[E-1,E]n+[T-1,T]v.                              (17)

All constants have exact analytic bounds

    329/200<E<3293/2000,
    6201/5000<T<5/4.                                 (18)

For E, use 707/1000<a<71/100. For the lower T bound,

    17/4-(3293/2000)^2-(6201/5000)^2
      =94171/100000000>0.

For the upper bound, (329/200)^2-43/16=741/40000>0.
Both radicands are therefore positive.

The C own coordinates are positive at all four vertices, with largest
absolute coordinates E,T. Its farthest corner has norm squared
E^2+T^2=q_0, so C is a physical boundary unit. W's largest absolute
normal coordinate is E-1, since E-1>a/2, and its largest transverse
coordinate is T. Thus its maximum corner norm is
(E-1)^2+T^2=q_0-2E+1<q_0. A,B have maximum corner norm squared q_0;
U,V have maximum corner norm squared 1+(5/4)^2=41/16<q_0.

The units are pairwise interior-disjoint. A,U,V,B meet only at their
successive vertical sides. W has minimum y coordinate
a(T-1)-1/4>-1/4, strictly above U,V. C has minimum height

    a(E+T-2)>(7/10)(329/200+6201/5000-2)>1/2,

strictly above A,B,U,V. W has minimum x coordinate a(T-E)>-1,
so it misses A. B and W are separated by their common support at p
in direction n. Finally W and C share only their common n-side.

Indeed n.p=-a/2=E-2 and v.p=3a/2. The number
r=T-3a/2 lies strictly between zero and one by (18). Thus p is
in the relative interior of W's first n-side, and p+n is in the
relative interior of the shared W/C n-side. The support gap from B
to C in direction n is exactly one. The original means p,p+n can
therefore be retained for a side-normal short transmitter W.

The center of C is (E-1/2)n+(T-1/2)v. Its x coordinate is
a(T-E)<0 and its y coordinate is a(E+T-1)>0. Moreover

    79T-51E-14 > 43/10000 >0,
    (E-T)/(E+T-1) < 14/65 < 13/60
                         < 13*pi/180 < tan(13 degrees).

Here pi>3 and tan x>x for 0<x<pi/2 suffice. Therefore its center
angle is strictly between 90 and 103 degrees, within the required
adjacent-C interval. This is an exact radical construction, without
a sampled pose or a numerical angle evaluation.

The long means can be kept at (-1,-1/2),(0,-1/2),(1,-1/2).
They are actual support points of A,U,V,B. Give all long edges
magnitude 3/2 and both short edges magnitude a. Then U,V,W have
their full positive degree-two force and moment equations. At B,
keep its physical lower circle corner z=(2,-1/2) with weight1/2,
its upper physical corner with weight zero, and its actual two body
means q_B=(1,-1/2), p=(1,1/2). The full force equation is

    z-(3/2)e_x+a*n=(0,0),

and the two body origin moments are -3/4 and +3/4. Thus the full
B force and angular equations hold with exactly those original
means and positive body forces. No equation at A or C is claimed.

This diagnostic identifies a real limitation of a local-pair attack.
The missing D contact, the global cycle equations or the actual
completion units must be used in any exclusion beyond the common
reduction proved in Sections 1--6.

## 8. Frozen sources and verification boundary

| Source | SHA256 | Exact role |
| --- | --- | --- |
| TWO_ENDPOINT_EXPANDED_SQUARE_COVER_AND_LONG_CHANNEL_TRIANGLE_EXCLUSION_2026_10_30.md | `78dfc5ed83b1538b2484007fc6d60d047c078b7f124944c0aef4dce6593558f6` | Coupled actual endpoint-center bounds |
| LONG_RUN_RETURN_MARKS_WHOLE_SIDE_CLEARANCE_AND_SHORT_NORMAL_CONE_2026_10_30.md | `c10361ea546b8e5681b4ac38c09b1b2e9b14fa0a2621c541f689857c73acbd1e` | Original compatible order, above-side localization and endpoint angular bounds |
| BOUNDARY_ARCS_41_AND_UNIT_GAPS_93_DEGREES_EXCLUDE_FIVE_LOAD_EIGHT_CYCLES_2026_10_30.md | `aec4e482006c95ceadb6e3c9456c900ff6321511ea7bf61b1f7db2468c6c4c09` | Full physical 41-degree and set-gap 93-degree estimates |
| LONG_ENDPOINT_RETURN_CONTACT_LOCUS_FORCE_LINE_SIGN_AND_TILTED_VERTEX_REDUCTION_2026_10_30.md | `cf942c1069e451ad043c80c8075fd67c85d2b71faa05c29b9baa3dae32f66fe3` | Actual endpoint own-frame bounds and the literal A--D return caller |

No numerical pose search, discarded square, original mean replacement,
certificate reselection, abstract planar/torque substitution, original
ledger mutation, Lean/Lake compilation, CI dispatch or publication is
used in this source. The exact six-unit diagnostic is explicitly not
a complete stressed seven-cycle or a counterexample to the nine-unit
target theorem.

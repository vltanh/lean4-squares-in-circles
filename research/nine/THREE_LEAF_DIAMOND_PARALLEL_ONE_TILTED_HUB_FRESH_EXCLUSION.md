# A parallel three-leaf diamond cannot have exactly one tilted hub

Date: October 27, 2026.

**Status: complete fresh hand proof of the entire exactly-one-tilted-hub
parallel-tip interface, submitted for full independent and root review.**
Every original side mean and both full hub fourth forces are retained.

## 1. Original graph and unchanged mean chart

Work with the original nine actual unit squares and

    sqrt(17)/2<R<=sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1=1+epsilon,  0<epsilon<1/60.

The positive component has edges HK, HB, KB, HD, KD and genuine S
leaves at H,K,B. Its exact degrees are H4/K4/B3/D2 and three leaf
degrees one; the two other actual packing units remain present.

Use the whole parallel alternative of
`GENUINE_S_THREE_FORCE_ROOT_TWO_NEAR_NEIGHBORS_FRESH_DOMAIN.md`.
The actual B leaf is East, both original B-to-hub normals are West,
and their unchanged means have opposite strict signs. Reflect and
exchange the hubs so H is the hub owning its B axis and its mean
is the positive one. Write

    P_H=(epsilon,t),   P_K=(epsilon,-u),
    t,u>0,  t+u<=1,   mu_H*t=mu_K*u.                 (1)

Thus for an actual q the aligned H and tilted K are

    H=[epsilon-1,epsilon] times [q,q+1],
    K=P_K+[0,1]f+[0,1]j,
    f=(-c,s),  j=(-s,-c),  c,s>0, c^2+s^2=1.         (2)

In particular q<=t<=q+1; the original HB mean has not been moved
to a corner. Each genuine S root contains its real epsilon-radial
point and is physically clear. The full true-D2 channel argument
makes D positively loaded: if it were unloaded, its width at least
one would be at most 2 epsilon by the two genuine hub near points.
Hence every actual D point has norm at least R-sqrt(2)>129/200.
No D2 concurrence or force equation is used below.

Only the degree-free physical triangle statement of
`UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md` is needed for owned axes.
It applies to each actual H-B-K or H-K-D triangle without changing
any force at the hubs.

## 2. The whole HK feature is H-owned South, with its actual mean

Because H owns HB East, the actual H-to-K normal has nonnegative
x component. If that component were positive, its H support would
be on x=epsilon. The unique K point with that x coordinate is P_K.
It cannot lie on H's right side: at a relative side interior H's
left half-plane overlaps K's leftward vertex sector, and at either
endpoint K's two strictly tilted leftward axes overlap the respective
left upper or lower H quadrant. This covers East and both strict
right-corner normal cones without a generic-position assumption.

The HK normal is therefore vertical. North is impossible because
the actual point P_K has y=-u<t<=q+1. Thus H-to-K is South.
K's unique top vertex is Q=P_K+f, and it lies in the relative
interior of H's bottom side because 0<c<1. Consequently

    Q=(epsilon-c,q),  q=s-u,
    HK is the actual H-owned South force at Q.       (3)

Both genuine near points give -epsilon<=q<=epsilon. The complete
real H-leaf feature cover then leaves only its North axis or strict
upper-right vertex. The bottom vertices and the East, West, South
axes are too central for radial norm d, while the upper-left vertex
has squared norm exceeding d squared by 1-4 epsilon+2q+q squared;
even q>=-epsilon makes this positive. In the two surviving features

    q=epsilon                                      (owned North),
    q=sqrt(1+2*epsilon)-1                           (strict upper-right).

In particular

    epsilon/(1+epsilon)<q<=epsilon,
    q>(59/60)*epsilon>0.                            (4)

Its genuine leaf unit vector (e,l) has e>=0,l>0.

The actual K near point gives a strong alternative without any
force equation. Write it relative to Q with inward axes -f,j as
Q+alpha*(-f)+beta*j, alpha,beta in [0,1]. Its x and y lower bounds
give

    c*(1-alpha)+s*beta<=2*epsilon,
    s*alpha+c*beta<=q+epsilon<=2*epsilon.

Therefore c*s<=2 epsilon*(c+s). If m=min(c,s) and M=max(c,s),
then m<4 epsilon<1/15, M>99/100. Substitution back yields

    m<2*epsilon*(1+20/297)<9*epsilon/4<3/80,
    M>999/1000.                                    (5)

The exact first coefficient reserve is 9/4-634/297=137/1188.
These two alternatives exhaust the original K tilt; no frame is
chosen anew.

## 3. A physical West-leaf cap, with all actual tip frames

We record the complete physical estimate used in the large-tilt case.
Every physical boundary center c_D here has

    |c_D|^2>11/6,  |c_D|<91/60.

The lower bound follows from |c_D|>=R-1/sqrt(2) and
(sqrt(17)/2-1/sqrt(2))^2=19/4-sqrt(17/2)>11/6,
using sqrt(17/2)<35/12. The upper bound is the standard contained
unit center bound d+1/2<91/60.

Suppose an actual genuine leaf center ell satisfies

    -91/60<ell_x<-161/108<-7/5,
    |ell_y|<91/540<1/5.                             (6)

A boundary unit wholly in x<=epsilon-1 has center x<-37/25 and
absolute y<1/3, using

    1/9-[(91/60)^2-(37/25)^2]=37/30000>0.

Its distance to ell is less than
sqrt((7/60)^2+(8/15)^2)<1, impossible for distinct unit squares.

The same impossibility holds for any boundary unit containing a point

    P=(-X,Y),  49/50<X<=1,  |Y|<1/50.               (7)

Indeed put z=c_D-P, with |z|<=1/sqrt(2)<71/100. Then

    P.z>1/6-1/5000,
    -X*z_x>1/6-9/625>3/20,
    z_x<-3/20.

The exact strict reserve is 17/7500. For a=ell-P, (6),(7) give
-27/50<a_x<-53/108 and |a_y|<19/100. Thus

    |c_D-ell|^2
      <1/2+(27/50)^2+(19/100)^2
         -2*[(3/20)*(53/108)-(71/100)*(19/100)]
      =3421/3600<1.                                (8)

This estimate needs no D normal, force equation, circle weight or
orientation. It is an actual incircle overlap with the real leaf.

## 4. Large s: the complete original West-leaf branch

Suppose s>999/1000 and c<9 epsilon/4. Equation (3) gives
u=s-q>999/1000-epsilon.

For completeness, the full genuine tilted K leaf cover, for any
0<u<1, is as follows. Put

    E=epsilon*c+u*s>0,  T=-epsilon*s+u*c,
    P_K.f=-E, P_K.j=T.

The near vertex and both near-axis heights are below d. The far
+f height 1-E is below one. A radial leaf at P_K+f would require
u^2-2su=2 epsilon*(1+c)>0, so u>2s, and its support cone would
also require u*c<=epsilon*s. With u<1 these are incompatible.
Thus only P_K+j, owned +j, or the opposite vertex P_K+f+j can
carry the actual real S leaf; axis endpoints are included in the
owned case.

In the present large-s branch, P_K+j has both coordinate magnitudes
greater than 999/1000-epsilon, so its norm exceeds d. The remaining
leaf is therefore owned +j or the opposite vertex. For the owned
case its direction is j=(-s,-c). For the opposite vertex its real
radial application is

    (epsilon-c-s,q-c).

Its x coordinate is negative and its absolute y coordinate is below
max(q,c)<3/80. In either case the actual leaf direction differs
from West by less than 1/9: its absolute y component is below 3/80,
whereas sin(1/9)>=1/9-(1/9)^3/6>3/80. Its actual center therefore
satisfies (6).

Now use the entire H4 equation. Its HB force is East, its HK force
is South, and its genuine North leaf has nonnegative x component.
The remaining HD force has strictly negative x component. The actual
H-K-D triangle with H-owned South makes its y component nonpositive.
Thus HD is West or strict Southwest. The West alternative puts D
wholly in x<=epsilon-1. The Southwest alternative has original port

    P_0=(epsilon-1,q),

which satisfies (7) by (4). Both are excluded by Section 3. This
closes the entire large-s branch without changing any H4 or K4 force.

## 5. Small s: complete K leaf and D-port cover

It remains that c>999/1000 and s<9 epsilon/4. By (3),(4),
0<u=s-q<19 epsilon/15. Hence P_K is small. The preceding complete
K-leaf cover applies. Its opposite vertex has both far own coordinate
magnitudes greater than 9/10, so its norm is greater than d.
Only the following two actual leaf types remain:

    V: P_K+j,   u^2+2cu=2*epsilon*(1+s);
    S: owned +j, u*c=epsilon*(1+s).                 (9)

Both give

    19*epsilon/20<u<11*epsilon/10,
    |P_K|<1/40,
    0<E<21*epsilon/20<1/50.                        (10)

For the upper u bound in V discard the positive u squared; in S
the equality gives it directly. Use (5) and
(1+3/80)/(999/1000)=2075/1998<11/10. The lower bound follows
from substituting 19 epsilon/20 into (9), with the same exact
reserve 2039/24000 as in the quadratic identity. These estimates
also justify the preceding opposite-corner exclusion before it is
used: initially E<epsilon+(57/20)epsilon squared<21 epsilon/20
and T>-epsilon*s.

We now retain every actual KD feature. P_K is too central for boundary
D. The far opposite corner, whose own coordinates exceed 9/10,
cannot be shared by any contained unit: an actual neighbor must have
a unit inward direction in the opposite closed quadrant, giving a
corner norm squared greater than 221/50>1105/256.

The leaf vertex P_K+j cannot be a D port. In type V its strict radial
leaf sector leaves no other unit sector. In type S it lies in the
relative interior of the real leaf's inner side, since E<1/50.
The one remaining ninety-degree sector forces a third unit with
all corners of norm at most |P_K|+sqrt(2)<R, hence circle-clear.

The original K-to-H force is North, at Q=P_K+f. The physical K-H-D
triangle excludes the K-owned -f and +j normals, since each has
negative dot product with North. An owned -j mean would be
P_D=P_K+lambda_D*f. Its boundary norm and (10) give lambda_D>31/50.
But D then contains the actual inward unit-segment point

    W=P_D-j
      =(epsilon-lambda_D*c+s,
        q+(lambda_D-1)*s+c).

It lies in the open interior of H: its x coordinate is strictly
between epsilon-1 and epsilon, and its y coordinate is strictly
between q and q+1. Indeed lambda_D>31/50>s/c, c<1, and c>s.
This contradiction includes every original mean endpoint.

Consequently the complete remaining KD form is

    F_KD=A*f-B_0*j,  A>0, B_0>=0,
    P_KD=P_K+f+lambda*j,
    0<=lambda<=1,  B_0>0 implies lambda=0.          (11)

In particular every far +f side mean is retained, not replaced by
the vertex Q.

## 6. The full K4 equation controls its original D mean

Let alpha be the genuine K-leaf magnitude and mu_K the original
KB magnitude. In type V set e=E/d, l=(1+T)/d, m=E/d; in type S
set e=0,l=1,m=E. The leaf's own force components are (-e,l) and
its actual moment about P_K is alpha*m. For the owned leaf, its
original point d*j has relative coordinates (E,1), proving this
moment without altering its mean. In both types

    0<m<21*epsilon/20,  l-m>19/20.

The actual KH unit normal North has own components (s,-c) and
applies at the actual adjacent vertex Q. Let gamma>0 be its full
magnitude. The unchanged K4 force and torque equations are

    A=mu_K*c-gamma*s+alpha*e,
    B_0=alpha*l-mu_K*s-gamma*c,
    B_0+lambda*A=alpha*m-gamma*c,
    alpha*(l-m)=mu_K*s-lambda*A.                    (12)

Thus, with all four original terms present,

    alpha/mu_K<(5/2)*epsilon,
    gamma/mu_K<3*epsilon^2,
    A>(99/100)*mu_K,
    B_0/A<4*epsilon^2,
    lambda<4*epsilon^2.                            (13)

These follow successively from s<9 epsilon/4, c>999/1000,
and B_0+lambda*A<=alpha*m<(21/8)*mu_K*epsilon squared.
For example 999/1000-1/900-99/100=71/9000>0 is more than
sufficient for the A bound.

The actual D port in world coordinates is now

    P_KD=(epsilon-c-lambda*s, q-lambda*c).          (14)

D's outward normal there, reversing F_KD, has positive x and
strictly negative y:

    (c*A-s*B_0,-s*A-c*B_0).

Its absolute y/x slope is less than 1/10 by (5),(13).

## 7. Full H4, actual H mean, and the final close ports

The full H4 x equation and the physical H-K-D triangle give HD
West or strict Southwest exactly as in Section 4. If it were West,
every actual D point would satisfy x<=epsilon-1. But (14) gives

    P_KD.x-(epsilon-1)=1-c-lambda*s
       =s*[s/(1+c)-lambda]>0.

The last inequality follows from s=q+u>q>59 epsilon/60 and
lambda<4 epsilon squared, since s/(1+c)>59 epsilon/120>
4 epsilon squared. Thus the entire H-owned West mean interval is
physically impossible, without moving that mean or invoking D2.

The actual HD force is therefore strict Southwest at
P_0=(epsilon-1,q). Write it (-M,-N), M,N>0. Let the genuine H
leaf force have magnitude alpha_H and unit direction (e_H,l_H),
where e_H>=0, 0<l_H<=1. Its moment about P_0 is alpha_H*m_H,
with

    m_H=1-epsilon                  for owned North,
    m_H=l_H-e_H                    for the strict upper-right leaf.

Both satisfy m_H>19/20; in the second case
m_H=(1+q-epsilon)/d>(1-epsilon)/d>59/61.

The actual HB force still applies at (epsilon,t), not at a chosen
corner. The original HK force is South at (epsilon-c,q). The full
H4 moment about P_0 is consequently

    alpha_H*m_H
       =mu_H*(t-q)+gamma*(1-c).                    (15)

Its complete force equation gives

    M=mu_H+alpha_H*e_H>=mu_H,
    N=alpha_H*l_H-gamma<alpha_H.

By the original B3 ratio (1), (10),(13),

    gamma/mu_H
      =(gamma/mu_K)*t/u
      <(60/19)*epsilon*t<t/19.

Since c>999/1000 and t<1, equation (15) therefore gives

    0<N/M<alpha_H/mu_H
       <[t+t/19000]/(19/20)<2.                    (16)

No mean has been suppressed to obtain this slope. D's outward
normal at P_0 is (M,N), positive in both components; its other
outward normal in (14) has opposite strict y sign and absolute
slope below 1/10. Equation (16) makes their dot product strictly
positive.

Both actual ports have x<-29/30 and absolute y<1/4. Their actual
distance is at most 1-c+lambda<7 epsilon squared<1: use

    1-c=s^2/(1+c)<3*epsilon^2

and (13). These are precisely the literal hypotheses of the complete
force-free `CLOSE_SUPPORT_PORTS_STRADDLING_NORMALS_FRESH_EXCLUSION.md`.
Its actual opposite corner exceeds the containing-circle radius.
This excludes the entire small-s branch.

## 8. Entire original interface conclusion

The actual HK feature cover was complete before any force estimate.
The real owned hub leaf fixes q>0 and every actual near point leads
to one of the two cases in (5). The large case closes by a physical
overlap with the genuine tilted hub leaf; the small case keeps all
original H4/K4 moments and the unchanged B3 mean ratio to reach the
force-free close-port obstruction. Every original leaf feature,
support owner, boundary mask and side-mean endpoint is included.

Thus the parallel B interface with exactly one hub tilted relative
to East is impossible. The statement is a whole original interface
of A8, not a proof for a three-force surrogate hub. All nine squares
remain. No ledger, frozen source, Lean compilation, CI or remote
state is changed.

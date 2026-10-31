# An oblique B-owned root return has no K-owned central contact

Date: October 27, 2026.  
Author: cert_final_review.

**Status: complete new analytic candidate, pending full independent review.**
This theorem excludes the entire K-owned central feature of the explicit
lower-leaf B-owned root chart below. Both genuine H leaves, every actual
HC type and owner, every actual CK owner and shared mean, and the whole
oblique BK interval are retained. No K2 law or computational certificate
is used. The proof is freshly saved after the workspace rollback.

The displayed chart is a hypothesis of the local theorem, not a claim
that missing normal-form source bytes have been restored. Section 15
states the original-caller recovery boundary precisely. All logical
inputs used to prove the local theorem itself are present and pinned.

## 1. Full actual lower-root chart

Retain physical interior-disjoint unit squares H,B,K,C, the two genuine
radial S leaves of H and B, and all other physical packing squares.
Their common containing disk has center zero and

    d=1+delta, 0<delta<1/60,
    R^2=(d+1)^2+1/4,
    17/4<R^2<=1105/256, R<25/12.                    (1)

H has exactly the four positive pair forces to its genuine leaf,
B,K,C. B has exactly the three positive pair forces to its genuine
leaf,H,K. C has exactly the two positive pair forces to H,K and a
positive circle load at its unique physical circle corner. K is a
physical boundary square; its degree, other forces and physical circle
mask are unrestricted. In particular the original true K3 remains
present when this theorem is used on the hub-tip graph.

Use the following origin-preserving orthonormal H coordinates:

    P=(-x,-A), G=1-A,
    H=[-1-x,-x] x [-A,G],
    0<=A<31/120.                                  (2)

The genuine H leaf has one of exactly these two actual features:

* Vertex row: its radial application is (-1-x,-A), with
  (1+x)^2+A^2=d^2 and 1+x>0.
* Aligned row: its radial direction is -E1, its actual radial mean
  is (-d,0), and x=delta. Its full actual side position A is retained.

The actual B axes in these H coordinates are

    e=(beta,-alpha), f=(alpha,beta),
    alpha,beta>0, alpha^2+beta^2=1.

HB is a singleton owned only by B, with actual H-to-B normal e and
actual application P. Put

    h_B=P.e=-beta*x+alpha*A,
    t=-P.f=alpha*x+beta*A,
    |h_B|<=delta,
    0<t<b<31/120,
    D_0=1-b+t in (0,1),
    B=P+[0,1]e+[D_0-1,D_0]f.                      (3)

The genuine B leaf is at its actual radial vertex

    p_B=(1+h_B)e-bf,
    (1+h_B)^2+b^2=d^2.                            (4)

The actual BK is a singleton owned only by K at

    Q=P+D_0 f,

and its actual normal is oblique in the B frame:

    M=-c_B e+s_B f,
    c_B,s_B>0, c_B^2+s_B^2=1.                     (5)

Finally assume HK is a singleton owned only by K. The selected
physical certificate has its strict side-interior/vertex convention
and the existing compatible fixed-singleton unique-C2 selection.
All original normals and all shared HC/CK means stay unchanged.

**Theorem 1.1.** No configuration satisfying this entire actual chart
exists.

The actual H4 and B3 laws are retained. The proof only invokes C's
genuine two-force boundary concurrence. There is no assertion that
K has two positive neighbors.

## 2. Both genuine H leaves force x>0; the actual B3 normal

The aligned row has x=delta>0. In the vertex row, subtract the two
genuine radial equations using h_B^2+t^2=x^2+A^2:

    2x=2h_B+(b^2-t^2),
    (1+beta)x=alpha*A+(b^2-t^2)/2>0.              (6)

Thus both rows have

    0<x<=delta,
    h:=-x in [-delta,0),
    X=1+x=1-h in (1,61/60),
    R_0=(h,G), F=(h-1,G).                         (7)

For the vertex row x<=delta follows from its real radius equation;
for the aligned row it is equality. No aligned vertex equation is
introduced.

Both H and B are physically circle-clear. In each displayed genuine
leaf feature the unit radial segment inward from its actual radial
application belongs to its root: at a vertex its two inward own-axis
components are between zero and one, and at the aligned side it is
the unit inward normal segment. Its inner endpoint has norm delta.
Every point of that root therefore has norm at most
delta+sqrt(2)<1/60+17/12<2<R. In particular neither the B3
concurrence nor the later H4 moment omits a root circle force.

The genuine radial B leaf and the actual HB force line meet at

    q_B=sigma*p_B, sigma=t/b in (0,1).

Their lines are nonparallel because b>0. The true B3 torque makes
the BK force line pass through this same q_B. In the actual e,f
frame, the difference Q-q_B has components

    h_B(1-sigma)-sigma,
    1-b(1-sigma)>0.

Its proportionality to the actual M has positive sign, because
s_B>0. Therefore

    c_B/s_B=[sigma-h_B(1-sigma)]/[1-b(1-sigma)]>0.
                                                        (8)

The denominator exceeds its numerator by
(1-sigma)(1+h_B-b)>0. Hence c_B<s_B. In particular

    c_B<1/sqrt(2)<17/24.                          (9)

This is the actual B3 line and mean, not an independently selected
direction.

## 3. The actual central point is H's upper-right vertex

In the original B frame K is on its owned BK side at Q, with a
strict actual position theta_B in (0,1):

    K=Q+[0,1]M+[-theta_B,1-theta_B]T_B,
    T_B=s_B e+c_B f.

Every point of K has f-coordinate strictly greater than

    1-b-c_B>1-31/120-17/24=1/30.                  (10)

The two lower H vertices P and P-E1 have f-coordinates -t and
-t-alpha, both negative. Neither can belong to K.

Because HK is a singleton owned only by K, its actual application
is a strict H vertex. If it were F=P-E1+E2, its actual H normal N
would have negative first and positive second component. Thus
N.e<0. The full unit-square backward-support span at the actual
minimum-N point F of K gives

    max_K e.(Z-F)<1.

But e.F=e.P-alpha-beta, and alpha+beta>1. Hence max_K e.Z<e.P,
whereas every point of B has e-coordinate at least e.P. This would
separate K from B, contradicting their actual contact Q.

The only remaining actual central application is therefore

    P_HK=R_0=P+E2=(h,G),
    N_x>0, N_y>0.                                (11)

The same actual HK point is in the relative interior of K's owned
side. No third physical unit can contain R_0: K contributes a
tangent half-plane there, and H's right-angle tangent sector is
strictly inside the opposite half-plane except for its vertex.
The two remaining tangent gaps are each strictly smaller than a
right angle, while every unit square containing the point has a
tangent sector of at least a right angle. In particular R_0 is
not in C.

## 4. Every physical C circle has positive height

Every physical K circle point z_K has positive second coordinate.
Otherwise its distance from the actual K point R_0 satisfies

    |z_K-R_0|^2
      >=R^2-2|h|R
      >17/4-(25/12)/30>2,

contradicting the unit diameter sqrt(2). This argument uses only
physical boundary contact, not a K force or circle mask.

Apply only the complete physical Sections 1--2 of
S_LEAF_CONNECTED_BOUNDARY_NEIGHBORS.md to H's genuine leaf and
the touching boundary neighbors K,C. Those sections say their
physical circle points lie on the same strict side of the actual
H-leaf line. They also give a circle-corner angular separation
strictly greater than pi/9 from the genuine leaf direction. The
global force-sum conclusion of that source is not used: the
present B leaf is an additional genuine loaded unit.

For aligned H, the leaf is -E1, and the positive K height gives
positive C height immediately. For the vertex row, write its
actual leaf as (-X,-A), X^2+A^2=d^2. If A=0 it is the same
horizontal line. If A>0, use the perpendicular functional

    Phi(z)=-A*z_x+X*z_y.

For a K circle point with positive height, Phi(z)<=0 would force
z_x>=R*X/d>120/61>sqrt(2), whereas K contains the point R_0
with h<0. This contradicts the unit diameter. Thus Phi is positive
at all K circle points and, by the physical connected-neighbor
argument, at every C circle point.

A C circle point with nonpositive height would then lie strictly
between the negative horizontal direction and the genuine leaf
direction. Its angular distance from that leaf direction would be
less than arctan(A/X)<arctan(31/120)<pi/12<pi/9, contrary to
the same physical corner separation. Consequently

    every physical C circle point has positive height.             (12)

Since C is uniquely and positively loaded and K is a boundary
neighbor, the actual proper C2 concurrence is a positive multiple
of that actual circle point. If the HC normal had negative height,
its H application would be on y=-A and its proper incoming line
would have nonpositive height throughout. This is impossible.
Thus the actual H-to-C normal has nonnegative height.

## 5. The complete HC feature cover

The rightward axis E1 is impossible by the occupied triangle
P,R_0,Q. Its three closed sides lie in H,B,K respectively. Its
area is alpha*D_0/2<1/2. Every H-owned E1 singleton or positive
shared HC overlap contains a relative-interior point of the side
P--R_0, and C's open interior enters the open triangle on its
right. The open interior of C cannot cross the triangle boundary,
which lies in the other closed physical squares. Connectedness
would put the whole unit C inside this triangle, whose area is
less than one. This is impossible. The entire shared HC overlap
is treated geometrically; its mean is never moved.

The leftward axis -E1 is also impossible. Since N_x>0 at the
actual minimum-N point R_0 of K, the backward-support span in
direction -E1 gives min_K x>h-1. A left HC puts C in x<=h-1,
so K and C could not touch.

A strictly northeast HC would use the already forbidden third-body
point R_0. Negative-height HC was excluded in Section 4. Thus the
exhaustive remaining HC alternatives are:

* The H-owned top normal E2, with its actual singleton point or
  full actual shared mean.
* A strictly northwest normal at the opposite upper vertex F,
  either C-owned or genuinely free.

If A=0 in the top alternative, use the true H4 moment about P.
The genuine H leaf and HB contribute zero moment. The actual
central R_0=P+E2 contributes -tau*N_x<0. A top application
P+E2-eta*E1 with 0<=eta<=1 contributes -omega*eta<=0.
Their sum cannot vanish. Therefore the top row has G<1.

For every K-owned central side at R_0 with N strictly northeast,
write U=N=(C,S), V=(S,-C), C,S>0. K has the actual form

    K=R_0+[0,1]U+[-a_0,1-a_0]V, 0<a_0<1.

All hypotheses of HIGH_CORNER_CENTRAL_TOP_PAGE_EXCLUSION.md now
hold, including h<0, the strict height window, true unique C2,
the original compatible fixed-singleton selection and the whole
shared mean. That complete theorem excludes the entire top HC row.

Only the opposite-upper northwest page remains.

## 6. The free northwest page with shared CK

If CK is singleton, its actual C application cannot coincide with
F. Otherwise F would belong to H and K, contradicting the actual
singleton HK intersection {R_0}. Thus the existing compatible
fixed-point unique-C2 selector gives side owners on both actual
singleton page contacts. HC cannot be H-owned in a strict oblique
direction, so it is C-owned.

A remaining free HC therefore has CK physically shared. Write
the actual central frame as

    m=(-c,s), t=(s,c), c,s>0,
    K=R_0+[-ell,1-ell]m+[0,1]t,
    0<ell<1,

where t is the actual central normal. This frame is available
regardless of which actual K axis carries BK. The full theorem
HIGH_CORNER_FREE_OPPOSITE_PAGE_SHARED_RETURN_EXCLUSION.md applies
with the actual F, actual free cone, all shared CK means, and
89/120<G<=1. It excludes this entire feature without a K force law
or a unique K circle mask.

The only remaining row is C-owned HC at F. The rest of the proof
excludes it for every actual CK owner and shared mean.

## 7. The signed C circle chart and its whole leaf budget

Write the actual C-owned HC normal and tangent as

    n_C=(-u,v), t_C=(v,u), u,v>0, u^2+v^2=1,
    C=F+[0,1]n_C+[-lambda,1-lambda]t_C,
    0<lambda<1,
    a=F.n_C=Xu+Gv>0,
    B_0=-F.t_C=Xv-Gu.                             (13)

Proper unique C2 gives q_C=F+ell_C*n_C=r_C*z_C in C, r_C>0.
The actual circle has nonzero own coordinates, so B_0 is nonzero
and fixes the sign of its transverse circle coordinate.

Define the actual nonnegative H radius surplus

    E_H=X^2+A^2-d^2.

It is zero in the genuine vertex row and A^2 in the genuine aligned
row. If B_0<0, then

    a-X=v[G-Xv/(1+u)]>0.

The actual point F+n_C belongs to C. Its squared-radius excess is

    3/4-2A+2(a-d)+E_H>1/6>0,

using d-X<1/30 and A<31/120. Thus B_0>0. The actual C circle is

    z_C=F+n_C-lambda*t_C,
    z_C.n_C=a+1,
    z_C.t_C=-B_0-lambda.                          (14)

Physical uniqueness makes B_0+lambda>1/2, hence a<d. The full
own-frame and circle identities are

    a^2+B_0^2=d^2+1-2A+E_H,
    lambda^2+2B_0*lambda+2(a-G)
      =2d-11/4+4A-E_H<19/60.                     (15)

They imply, on both genuine H rows,

    B_0>83/120, B_0<X<61/60,
    u<1/3, v>14/15, v>47/50,
    a-G>(1411/1740)u>(4/5)u,
    lambda<1/5,
    A>A_0:=43/240.                               (16)

Here B_0^2>1-2A>29/60>(83/120)^2, with reserve71/14400.
The function Xu+G*sqrt(1-u^2) is increasing up to the actual u
because its derivative has the sign of B_0. At u=1/3 it exceeds
(59/60)/3+(89/120)(14/15)=51/50>61/60, proving u<1/3.
Then v^2>8/9>(47/50)^2. The displayed a-G bound uses

    a-G=u[X-G*u/(1+v)]

with X>59/60, G<=1 and 1+v>29/15. Finally
(1/5)^2+(83/60)(1/5)=19/60, giving lambda<1/5.
Positivity in (15), with E_H>=0, proves A>A_0.

The aligned surplus E_H is retained with its correct sign. No
aligned vertex equation has been inserted.

## 8. The actual B leaf forces a strong angle gap

Since h_B=-beta*x+alpha*A<=delta and x<=delta,

    alpha*A<=delta(1+beta)<1/30.

With A>A_0 this first gives alpha<8/43<1/5 and beta>9/10>delta.
The actual B radius and b>t then give

    d^2>1+2h_B+h_B^2+t^2
       =1-2beta*x+2alpha*A+x^2+A^2.

The function 2beta*x-x^2 is increasing for 0<x<=delta because
beta>delta. Therefore

    A^2+2alpha*A<2delta(1+beta)<1/15,
    A^2<4delta.                                  (17)

The decreasing function 1/(30A)-A/2 now gives

    alpha<1/(30A)-A/2
         <8/43-43/480=1991/20640<1/10,
    beta>99/100.                                 (18)

Every inequality used the real B radius and t<b. Both genuine H
rows are still retained; no multiplier ratio is chosen.

Now sigma=t/b, t=alpha*x+beta*A>beta*A, and b<31/120. Thus

    sigma>4257/6200,
    sigma-1/60>2/3,
    4257/6200-1/60-2/3=61/18600>0.

The actual normal formula (8), whose denominator is positive and
less than one, consequently gives c_B/s_B>2/3, so c_B>1/2.
In the unchanged H coordinates the actual BK normal is therefore

    M=(-c,s),
    c=beta*c_B-alpha*s_B>79/200>1/4,
    s=alpha*c_B+beta*s_B>0,
    c^2+s^2=1.                                   (19)

In particular it points northwest in the H frame too. The only K
axis pointing strictly northeast is t=(s,c). It must be the
actual central normal N from (11). This simultaneously removes the
alternative in which BK and HK used the same actual K side axis.

## 9. The actual central position and the complete K circle

Use the actual strict K side positions

    K=S_0+[0,1]m+[0,1]t,
    R_0=S_0+ell*m, 0<ell<1,
    Q=S_0+theta*t, 0<theta<1.

The actual Q-R_0=D_0 f-E2 gives exactly

    alpha*D_0=ell*c+theta*s,
    beta*D_0-1=theta*c-ell*s.

Because D_0<1 and (18)--(19) hold,

    ell<alpha*D_0/c<20/79<1/2.                   (20)

As in Section 4, |R_0|<61/60. The two minimum-t K corners are
each less than one unit away and have norm below121/60<R.
For a maximum-t/minimum-m circle corner, its own m coordinate
would have to be at most -1/2. But that coordinate is

    R_0.m-ell=-ch+sG-ell> -ell> -20/79> -1/2,

because h<0 and G>0. Hence every actual K circle point is the
same actual opposite corner

    z_K=R_0+t+(1-ell)m,
    z_K=(h+s-zc,G+c+zs), z=1-ell in (0,1).        (21)

No K force equation, proper K ray, or assumed unique K mask entered
this whole physical corner identification.

## 10. Every K-alone-owned CK axis is impossible

Let w point from C to K and omega,gamma>0 be the actual HC,CK
magnitudes. The unchanged genuine C2 force is

    kappa_C*z_C=omega*n_C-gamma*w.

Its transverse component, using (14), requires w.t_C>0.
Define D=vc-us, J=vs+uc>0 and eta=1-lambda>4/5.

If K alone owns CK, the actual H-K-C triangle gives w.t>=0.
The complete K-axis alternatives are m,-m,t. The choice m is
excluded by the same triangle rule at C, because n_C.m=J>0.

For w=t, the C triangle gives D<=0. Equality is a coframed axis
contact, incompatible with the K-alone-owned singleton convention,
so D<0. The actual C support is Z=F+eta*t_C and its actual proper
coefficient is ell_C=eta*(-D)/J. Since D<0 implies u>c,

    J-v=c[u-vc/(1+s)]>0,
    0<(-D)/J<u/v<5/14.

The actual radial n_C,t_C coordinates give

    B_0=a*lambda+eta[(-D)/J](B_0+lambda).

The right side is less than

    61/300+(5/14)(73/60)=893/1400<83/120,

with reserve113/2100. This contradicts (16) over the entire actual
K-side interval.

For w=-m, one has n_C.w=-J<0 and w.t_C=D>0. The actual C point
is again Z=F+eta*t_C. Keep its entire actual K-owned side position:

    Z=R_0+(1-ell)m+zeta*t.

The m projection gives exactly

    ell=1-c+eta*D
        =1-c(1-eta*v)-eta*u*s
        >eta(v-u)>12/25.

Here 1-eta*v>0, c<1 and s<1 justify both strict comparisons.
But (20) gives ell<20/79, and

    12/25-20/79=448/1975>0.

This contradiction retains every real side position and requires
no K2 law. All K-alone-owned CK possibilities are excluded.

## 11. The full C-owned CK chart, including its unchanged shared mean

If C owns CK, the positive transverse force w.t_C>0 leaves only
w=t_C among its own side axes. This includes every shared CK.
The actual K projections are t_C.t=J>0 and t_C.m=-D.

For D<0 the K minimum support would be S_0=R_0-ell*m. But

    S_0.n_C=a-u-ell*J<a,

so it cannot belong to C. Hence D>=0.

For D>0 the actual CK point is R_0+z*m. Its unchanged C-side
representation gives

    Z=F+eta*t_C+rho*n_C,
    lambda=1-v+zD,
    rho=zJ-u, 0<=rho<=1.                          (22)

The closed rho bounds harmlessly retain the actual strict singleton
position. For D=0, the frames coincide and the full shared segment
instead has

    u=c, v=s, lambda=1-v,
    Z=F+eta*t_C+rho*n_C,
    0<=rho<=z-u, z>u.                             (23)

Its actual mean and both endpoints remain. In particular no singleton
value of rho is assigned to the shared row.

Both types retain lambda=1-v+zD. From (15)--(16), with E_H>=0,

    (83/60)lambda+(8/5)u<4A-43/60,
    lambda+u<(240A-43)/83.

Since zvc=lambda-(1-v)+zus<lambda+u and v>47/50, the actual
j=zc satisfies

    0<j<q(A):=(12000A-2150)/3901,
    A_0=43/240<A<A_1=31/120,
    q(A_1)=Q_0=950/3901<1/4.                     (24)

These estimates use the whole actual shared interval and do not use
any K moment, K force or chosen mean.

## 12. The complete continuous circle comparison forces c<1/4

The actual K circle in (21) is

    z_K=(h+s-j,1-A+c+(j/c)s).                     (25)

All divisions by c are legitimate. The following whole-interval
argument is reproduced in full; it is not an invocation of a result
for a different original root owner.

If c>=1/2, then s<=sqrt(3)/2<13/15 and j<Q_0<1/4, so
|h+s-j|<53/60. Its positive vertical coordinate is below

    1-A+c+2q(A)s<=1-A+sqrt(1+4q(A)^2).

The last expression is convex in A. At A_0 it is437/240<223/120.
At A_1 it is less than89/120+67/60=223/120 because

    (67/60)^2-(1+4Q_0^2)
      =532625089/54784083600>0.

Thus R^2=|z_K|^2<(53/60)^2+(223/120)^2<17/4, with reserve
47/2880. This excludes the entire c>=1/2 interval.

For 1/4<=c<=1/2, the actual horizontal coordinate is positive:
h+s-j>-1/60+6/7-1/4>0. Also (17) gives A^2<4delta, so
R^2-A^2>17/4. Replace only h by its strict upper bound1/60 and
consider

    F_*(A,c,j)=(1/60+s-j)^2
                +(1-A+c+(j/c)s)^2-A^2.

It is convex in j on the entire necessary closed interval[0,q(A)].
At j=0 it is below(61/60)^2+(3/2)^2<17/4, with reserve3479/3600.
At j=q(A), it is convex in A: its A^2 coefficient is

    (kappa/c)(kappa/c-2s)>0, kappa=12000/3901>3.

The A_0 endpoint is already the j=0 row. At A_1 set

    F_1(c)=(1/60+s-Q_0)^2
             +(89/120+c+(Q_0/c)s)^2-(31/120)^2.

Its exact full derivative is

    F_1'(c)=2(89/120)-2Q_0^2/c^3
             -2(1/60)c/s-2(89/120)Q_0/(c^2s)<0.

Indeed c^2s<=sqrt(3)/8<7/32<Q_0 makes the first and last terms
already have negative sum. The other two terms are negative.
The maximum therefore occurs at c=1/4. There s=sqrt(15)/4<31/32
and both squared coordinates are positive. The full endpoint bound is

    F_1(1/4)
      <(1/60+31/32-Q_0)^2
        +(89/120+1/4+4Q_0(31/32))^2-(31/120)^2
      =17/4-72980760071/3506181350400<17/4.

This contradicts the actual strict R^2-A^2>17/4. Both full angle
intervals and all their endpoints have been covered, so

    c<1/4.                                       (26)

But the actual B3 and the two genuine leaves gave c>79/200 in (19).
The reserve79/200-1/4=29/200>0 proves the final contradiction.
Every C-owned CK, including its whole shared mean, is excluded.

## 13. Exhaustive union and force preservation

Sections2--3 derive the actual central point and normal from the
entire explicit B-owned lower-root chart and actual K-owned central
contact. Sections4--5 prove the complete physical page-height and HC
feature cover. The top HC row, including its aligned-H endpoint,
is excluded. The free opposite-upper HC/shared-CK row is excluded
by its complete degree-free helper. Every remaining singleton page
has its legitimate preselected side owner.

Sections7--12 then exclude every C-owned opposite-upper HC, first
retaining the signed transverse circle coordinate, both genuine H
leaves and actual B3, then identifying the physical K corner before
splitting the complete CK owner cover. Both K-owned CK axes are
closed, and the C-owned/shared row has the full continuous circle
contradiction. These alternatives exhaust the actual feature.

The H4 law is used only at its genuine aligned-height endpoint,
with all four original pair forces. The B3 law uses its genuine
leaf and actual HB mean. Every C2 concurrence is the proper
boundary-neighbor theorem. No K2, K concurrence, fictitious H3,
fixed shared mean, removed force, removed physical unit or sampled
angle is used. This proves Theorem1.1 with zero new certificates.

## 14. Present exact logical inputs

| Complete input | SHA256 | Exact scope used |
| --- | --- | --- |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Actual singleton owner convention, full H4/B3/C2 force and moments, unchanged shared means |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 | Full backward-support span, actual H-K-C side-owner signs only |
| S_LEAF_CONNECTED_BOUNDARY_NEIGHBORS.md | 70a3488bb613b1ce1cb4ac778d6f2b2acb2e04bae226741a0665378d096e28ec | Complete physical Sections1--2 only; no global leaf-force-sum conclusion |
| TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md | 29e38d3f641fe16c6db587e51245f92ad4c447f9536db7d14c221f56b5357e82 | Genuine true-C2 proper ray with physical boundary neighbor K |
| C7_FORCE_POLYGON.md | d50d8ca48ea19156175e651bfa74be30ef3e58065ec14d8d1834670a41559089 | Physical circle-corner own-coordinate signs and containing-circle point cannot be shared |
| GENERAL_FIXED_TIP_NORMAL_SELECTION.md | ef8ae8a219af9fa15a70698e485bbb337925e5caf2cd64b6b5c2619d9c4bd194 | Existing selection at two actual distinct fixed singleton applications; never a variable shared mean |
| HIGH_CORNER_CENTRAL_TOP_PAGE_EXCLUSION.md | 580c065de7812c889f91d0e06e7319a3126134b31b8bd31c2044960b7819083b | Complete actual top-HC feature with arbitrary-degree/mask K, full central offset and every page owner |
| HIGH_CORNER_FREE_OPPOSITE_PAGE_SHARED_RETURN_EXCLUSION.md | 7df434664a33019260a1b5b41983989a536f223edca4702cfed9a91786bb4f9e | Complete actual free far-HC/shared-CK feature, all translations/means and both possible K circle corners |

The first six original sources are present under current_pr11 or,
for the exact recovered connected-neighbor source, under
recovery_2026_10_27. The two new complete helpers are present in the
recovery directory. Their independent full reviews remain separate
artifacts and do not replace review of the whole theorem above.

The convex comparison in Section12 was independently reproduced
from the physical quantities (15),(21),(24), inspired by the recent
northwest-page source b6975fe4. No original H-owned-HB hypothesis
or conclusion from that other source is a logical input here.

## 15. Original-caller and recovery boundary

The previously accepted B-owned singleton lower-H-leaf normal form
at the preserved pin3ad155e266b71e0c2e91ca67be9328a04e204ede77289a375fbd01c77f48653f
was intended to supply the entire chart(2)--(5) for the original
hub-tip family, after its complete parallel-tip, positive-concurrence,
genuine-H-leaf and physical-mask reductions. Its exact source bytes
were missing from the restored workspace when this new proof was
written. This file does not claim to restore them or to freshly
verify that complete original reduction from a remembered hash.

The local theorem above is self-contained under its explicit actual
chart and uses only the present complete logical inputs in Section14.
It proves the whole oblique-BK/K-owned-central contradiction on that
chart. A fully recovered original-family assembly must restore the
exact earlier normal-form and physical-C-uniqueness source bundle,
or supply and independently review complete replacement reductions.
The actual vertical BK feature is separate and is not claimed here.

No original gate, ledger, remote source, Lean file or CI workflow is
changed by this candidate. Mathematical local exclusion, independent
acceptance, and recovery of the full original publication bundle are
kept distinct.

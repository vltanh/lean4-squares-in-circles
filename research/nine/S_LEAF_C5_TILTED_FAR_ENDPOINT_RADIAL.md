# The far endpoint of a tilted S-leaf C5 channel is radial

Date: October 26, 2026.

**Status: complete hand necessary-geometry theorem, accepted after root
and separate full-source and original-domain reviews in
REVIEW_S_C5_TILTED_AND_RADIAL_POCKET_ROOT_2026_10_26.md and
REVIEW_S_C5_TILTED_RADIAL_FAR_ENDPOINT_C6_2026_10_26.md.** This does not close the
three-extra-square completion problem or the original S-leaf gate.

Keep the exact original component

    A--B--V--C--U--A, with a genuine S leaf L at A.

The original labels are A=0, B=1, V=2, C=3, U=4. Only B,C have
positive block circle load; U,V are true unloaded degree-two
transmitters; A has its true degree three and B,C their true degree
two. All nine physical units, original positive forces, physical
circle masks, individual radial weights and actual means remain.
Use the original strict point-normal and diagonal-avoidance
conventions throughout. No normal is reselected.

Put

\[
 79/40\le R\le\sqrt{1105}/16,\qquad
 d=\sqrt{R^2-1/4}-1,\qquad \delta=d-1.
\tag{1}
\]

Normalize the genuine S leaf as

\[
 L=[d,d+1]\times[-1/2,1/2],\qquad p_0=(d,0).
\]

This source covers the entire TILTED root family. After reflection
and, if needed, interchange of its inward axes, write

\[
 A=p_0+[0,1]f_1+[0,1]f_2,\qquad
 f_1=(-a,-b),\quad f_2=(-b,a),\qquad
 a\ge b>0,\quad a^2+b^2=1.
\tag{2}
\]

In particular det(f_1,f_2)=-1. Coordinate statements about A below
are relative to p_0 and these actual inward axes. Denote its
vertices by P_0=(0,0), P_1=(1,0), P_2=(0,1), P_12=(1,1).
The original outward root normal through U toward C is n, its
force magnitude is mu, and the original direct normal toward B
is m, of magnitude nu. The genuine leaf force has magnitude
lambda. All three magnitudes are strictly positive.

**Theorem.** Every surviving tilted member of the original family
has the following necessary form:

\[
 \begin{gathered}
 0<\delta<1/60,\qquad
 n=x f_1-t f_2,\quad x>0,\quad t\ge0,\quad x^2+t^2=1,\\
 p_{AU}=p_0+f_1+Yf_2,\quad
 p_{AB}=p_0+Zf_1+f_2,\qquad 0\le Z\le1,\\
 Y=0\quad(t>0),\qquad
 0\le Y<db\quad(t=0),\\
 a>59/61,\qquad |p_{AU}|<13/50.
 \end{gathered}
\tag{3}
\]

Let f be the clockwise quarter-turn of n, so

\[
                         f=t f_1+x f_2.
\tag{4}
\]

Then C is physically radial, the actual U--C interface is
genuinely shared, and

\[
 \begin{gathered}
 C=[d,d+1]n+[-1/2,1/2]f,\qquad
 h_A(n)=\delta,\qquad
 p_{CU}=p_{AU}+n=d n-Tf,\\
 0<T<13/50,\qquad w_U=w_V=1.
 \end{gathered}
\tag{5}
\]

The two original C corner weights remain arbitrary nonnegative
weights with positive total. No equal-weight conclusion is used.
The actual transverse sliders of U,V and all three extra units
remain.

## 1. Radius, reserve, and parallel-load prerequisites

The sharp center/half-width bound at the physical boundary
endpoint C gives

\[
                  h_A(n)+w_U\le d,\qquad w_U\in\{1,\sqrt2\}.
\tag{6}
\]

The central endpoint lemma for a genuine radial leaf, as used in
Section 1 of RADIAL_LEAF_TWO_BOUNDARY_CHANNEL_FORK_EXCLUSION.md,
gives dist(0,A)<=max(delta,0). If d<1, the root contains 0, so
(6) is impossible. Therefore d>=1. For d>=1 it also gives
h_A(n)>=-delta, and hence

\[
 0\le\delta<1/60,\qquad
 w_U\le d+\delta<31/30<\sqrt2,\qquad
 w_U=1,\qquad -\delta\le h_A(n)\le\delta.
\tag{7}
\]

Both B and C have nonparallel pair-force lines. Here is a local
proof that does not assume that the full component is a simple
cycle. If either loaded endpoint had parallel pair forces, the
complete classification in Section 1 of
SIMPLE_CYCLE_LOADED_FORCES_NONPARALLEL.md would make it either a
radial D terminal or a physical radial S terminal. Both actual
normals point along its inward radial direction.

Its connection through V to the other physical boundary endpoint
has reserve one or sqrt(2). For reserve one, the unchanged far
application has norm at most

\[
 \max\{1-(R-\sqrt2),\sqrt{\delta^2+1/4}\}<R-\sqrt2.
\tag{8}
\]

For the D alternative this uses R-sqrt(2)>14/25>1/2. For S use
delta<1/60 and
1/3600+1/4<(14/25)^2. Every point of a physical boundary
unit has norm at least R-sqrt(2), by its diameter. Thus (8) is
impossible.

For reserve sqrt(2), a radial D endpoint is prohibited by the
original diagonal-avoidance convention: its actual application
would be a vertex rather than the required side-interior
application. A physical radial S endpoint is excluded at d>=1 by
RADIAL_BOUNDARY_DIAGONAL_CHANNEL_RADIUS_RESTRICTION.md. This
exhausts the original V widths and proves the assertion.

Consequently the actual B,C concurrences q_B,q_C exist, are
positive multiples of their original circle resultants, and have
nonnegative proper lengths at both ports, by Lemma 1.1 of
FIVE_CYCLE_FORCE_POLYGON_DOMAIN.md.

There are two useful contact consequences.

First, the two root applications p_AB,p_AU cannot coincide.
If they equaled p, then p belongs to B and p+n belongs to C.
Their distance is one. The actual B--V--C supporting gap has
width w_V>=1, so equality forces w_V=1 and its direction from B
to C to be n. In detail, the scalar product of its unit direction
with (p+n)-p is at least w_V and at most one. Equality fixes the
direction and puts p,p+n on its actual supporting lines. Both
actual outward C normals would then equal -n, contrary to the
nonparallel conclusion above. No equality of the two C means is
needed for this argument.

Second, a channel at the leaf point p_0 with n dot e_x>0 is
impossible. The exact segment [p_0,p_0+n] lies in U. A sufficiently
short initial part with positive length lies in the open interior
of L. Even if that segment lies on an edge of U, an open
neighborhood of any of those points meets U's interior, producing
an overlap of interiors. This retains original endpoint means.

## 2. The full tilted root moment cover removes every positive f_2 channel component

Write n=x f_1+y f_2 initially, with x^2+y^2=1. Its exact support is

\[
 h_A(n)=-d(ax+by)+\max(x,0)+\max(y,0).
\tag{9}
\]

The complete inequalities in Section 3 of
RADIAL_LEAF_TWO_BOUNDARY_CHANNEL_FORK_EXCLUSION.md apply separately
to this actual channel. For clarity, da>2/3, 1-db>19/80,
and delta<1/60. They exclude x<=0,y>=0. If y>0, they require
x>y>0: for y>=x>0, (9) is at least
(19/80-delta)y>53/360>delta.

For an actual application with own coordinates (X,Y), its signed
own-frame moment about p_0 is Xy-Yx. The physical determinant is
its negative, which is the same orientation factor for both
root cycle forces. The actual root equations in these axes are

\[
 \mu x+\nu u=\lambda a,\qquad
 \mu y+\nu v=\lambda b,\qquad
 \mu M_n+\nu M_m=0,
\tag{10}
\]

where m=u f_1+v f_2 and M_n,M_m are the actual own-frame moments.
The genuine leaf application is p_0 and has zero moment about it.

Suppose y>0. The channel application is P_12 and M_n=y-x<0,
so M_m>0. In this subdomain a>b: if a=b=1/sqrt(2), then
(9)=(1-d/sqrt(2))(x+y)>1/4>delta.
The full positive-moment support cover for m is:

| Original direct feature | Application | Positive moment |
| --- | --- | --- |
| u,v>0 and v>u | P_12 | v-u |
| u<0,v>0 | P_2 | -u |
| u=0,v>0 | (Z,1), 0<Z<=1 | Zv |
| u<0,v=0 | (0,W), 0<W<=1 | -Wu |

All other features have nonpositive moment. The first row would
give the forbidden coincident root applications. In the second
row, the moment equation says nu*u=mu*(y-x). Substituting in
the first force equation gives mu*y=lambda*a, and then the
second gives nu*v=lambda*(b-a)<0, a contradiction.

For the third row, mu*x=lambda*a and
nu*v=lambda*b-mu*y. The moment equation and Z<=1 give

    lambda*b-mu*y >= mu*(x-y),

and therefore b>=a, again impossible. In the fourth row,
mu*y=lambda*b and -nu*u=mu*x-lambda*a. Its moment equation
and W<=1 give

    mu*x-lambda*a >= mu*(x-y),

with the same contradiction. Thus y>0 is excluded with every
side-axis mean endpoint retained.

If x<0,y<0, the application is p_0 and n dot e_x>0, prohibited
by Section 1. The only remaining normal domain is consequently

\[
                    n=x f_1-t f_2,\qquad x,t\ge0.
\tag{11}
\]

The root force equation gives v>0, so the direct application
is always p_AB=p_0+Zf_1+f_2, with 0<=Z<=1.
If t>0,x>0, the channel application is P_1. If t=0 it is
(1,Y), 0<=Y<=1. If x=0 it is (X,0), with X>0 by the
leaf-point exclusion. These are all original feature endpoints.

## 3. Positive root concurrence without assuming a proper root channel

The two root cycle normals are nonparallel in (11), since the
leaf direction has strictly negative coordinates (-a,-b) in the
own axes. Full torque puts their intersection on the actual leaf
line: q_A=(q,0) in the global coordinates. Put k=d-q, so its
own coordinates relative to p_0 are (ka,kb).

When x,t>0, the P_1 channel line gives

\[
 k=\frac{t}{bx+at},\qquad
 1-ka=\frac{bx}{bx+at}>0,\qquad 1-kb>0.
\tag{12}
\]

Both root port coefficients are then positive. When x=0,
k=X/a, and the direct coefficient is
(1-bX/a)/v>0; the channel coefficient is bX/a>0.
Here db<=delta excludes a=b, so the first strict sign holds
even at X=1.

For t=0, the channel line gives k=Y/b. The direct coefficient
is (1-Y)/v. In fact Y<1. If Y=1, the equations (10), with
the direct application (Z,1), give bZ=a. For a>b this is
impossible; for a=b the channel support 1-d/sqrt(2) exceeds
delta. Thus the direct coefficient is strictly positive.
The channel coefficient 1-ka is not assigned a sign yet.

Here is the precise algebraic positive-sign argument, including
that last possibility. Use the three unchanged external
resultants F_A=lambda*e_x, F_B,F_C. They sum to zero and have
independent directions as in Section 2 of
D_LEAF_C5_TWO_SEPARATED_LOADS_EXCLUSION.md. This uses the genuine
leaf resultant, not a fictitious A circle force.

The original normal lines and exact reserves give coefficient
identities

    q_B-q_A = ell_AB f_AB,
    q_C-q_B = ell_BC f_BC,
    q_A-q_C = ell_CA f_CA.

The direct AB coefficient is strictly positive by the proper
root direct length just proved and the proper B length.
The BC coefficient is strictly positive because it contains V's
positive reserve and both loaded proper lengths. Only ell_CA
is provisionally allowed to be signed.

The coefficient comparison in Section 2 of
RADIAL_TRIANGLE_CONCURRENCE.md is algebraic and gives, for
L=ell_AB+ell_BC+ell_CA,

\[
 \tau_A=\frac{\ell_{AB}\ell_{CA}}L,\qquad
 \tau_B=\frac{\ell_{AB}\ell_{BC}}L,\qquad
 \tau_C=\frac{\ell_{BC}\ell_{CA}}L,\qquad q_i=\tau_iF_i.
\tag{13}
\]

One cannot have L=0: the summed edge identities would then
give ell_BC*F_B=ell_CA*F_A, contradicting independence and
ell_BC>0. Since tau_B>0 and ell_AB,ell_BC>0, (13) first
gives L>0; since tau_C>0 it next gives ell_CA>0; finally
tau_A>0. Therefore

\[
                               q>0.
\tag{14}
\]

In particular t=0 gives 0<=Y<db. The original loaded
concurrence triangle now has all three edge coefficients
positive. Its turns lie in (0,pi) and sum to 2pi, with the
orientation selected by the nonzero actual moment
mu*det(q_A,n). This is the same three-direction argument as
Section 3 of the D-leaf C5 source.

## 4. The entire remaining axis x=0 is impossible

In this case n=-f_2. Its support is db<=delta, so
b<1/60, a>59/60. The first force equation in (10) gives
u>0, and v>0 already, so p_AB=P_12. Its physical norm obeys

\[
 |p_{AB}|^2=d^2+2-2d(a+b)<d^2,\qquad
 |p_{AB}|\ge a-b>29/30>R-\sqrt2.
\tag{15}
\]

Every point of a physical radial unit has norm at least d.
Thus B is physically unique. Its ports are distinct: at a
coincident vertex a proper positive concurrence would have to
be the opposite radial-D vertex of norm R-sqrt(2), contrary
to (15); coincident side-interior ports would be parallel.
The complete local unique-corner calculation in Section 4 of
the D-leaf C5 source therefore gives

\[
 \theta_B\le3\pi/4,\qquad
 \theta_B>\pi/2\ \Longrightarrow\
                      |p_{BV}-p_{BA}|\le1.
\tag{16}
\]

The root turn is acute because the scalar product of its
incoming direction -m with outgoing n=-f_2 is v>0.
If C were physically unique, its two true transmitter neighbors
give theta_C<=3pi/4 by the complete local calculation in
SIX_CYCLE_ONE_DIAGONAL_INNER_CAPACITY.md, Section 1. These
three bounds would contradict the turn sum 2pi. Hence C is
physical radial. Its V channel cannot be diagonal by
RADIAL_BOUNDARY_DIAGONAL_CHANNEL_RADIUS_RESTRICTION.md.

Put E=-f_2,F=f_1. The actual C application from U has coordinates

\[
        p_{CU}=(1+db)E+(X-da)F,\qquad X-da=-aq<0.
\tag{17}
\]

The radial outer axis/vertices cannot support the channel to A.
A radial tangential axis would put the entire A beyond
projection 3/2 and one of its points beyond 5/2>R. Thus this
incoming C application is either on its inner face with
radial axis E, or is a strict inner vertex.

In the strict-vertex case write its radial frame as

    e=cos(eta)E+sin(eta)F,
    f_C=-sin(eta)E+cos(eta)F,   -pi/2<eta<pi/2.

The incoming inward direction is E. If eta>0, its support
application is d*e+f_C/2 and has positive F-coordinate; if
eta<0 it is d*e-f_C/2 and has negative F-coordinate. Hence
(17) forces eta<0. In particular f_C dot E>0. In the
inner-axis case eta=0 and f_C=F, while the original mean
in (17) is negative.

The local radial support cover in Section 1 of
RADIAL_LOAD_SIDE_CHANNEL_POCKET_CAPACITY.md applies to the
actual reserve-one channel to the physical boundary endpoint
B. It makes its application a strict inner vertex and its
normal strict in the two associated components.
The original cycle moment is negative:

    mu*det(q_A,n) = -mu*q*a < 0.

Since det(e,f_C)=-1, at the plus inner vertex and direction
g=-alpha*e+beta*f_C it equals

    det(d*e+f_C/2,g)=-d*beta-alpha/2<0;

the minus-vertex alternative has the opposite sign. Thus the
actual C return uses the plus vertex, with alpha,beta>0.
It follows in both incoming cases that

\[
 p_{CV}\cdot E\ge p_{CU}\cdot E=1+db,\qquad g\cdot E>-1.
\tag{18}
\]

The last inequality is strict because the outgoing normal is
strict at the plus vertex and cannot equal -E. Consequently

    p_BV dot E = (p_CV+g) dot E > db,
    p_BA dot E = db-1.

The B chord has length greater than one. But theta_C<pi and
theta_A<pi/2 force theta_B>pi/2, contradicting (16).
This excludes x=0, including X=1 and every original mean.

## 5. Uniform small norm of the actual remaining root port

Now x>0. If t>0, p_AU=P_1 and

\[
 h=(1-da)x+dbt\le\delta.
\tag{19}
\]

It follows that 1-da<=delta. Indeed if both 1-da and db
were greater than delta, (19) would exceed
delta*(x+t)>=delta. In the other possibility db<=delta,

    da=sqrt(d^2-(db)^2)>=sqrt(d^2-delta^2)
      =sqrt(1+2delta)>=1,

which gives the same conclusion. If t=0, the exact support
is already h=1-da<=delta.

Therefore

\[
 a\ge\frac{1-\delta}{d}>\frac{59}{61},\qquad
 |P_1|^2=d^2+1-2da
       \le4\delta+\delta^2<\frac{241}{3600}
       <\frac{169}{2500}.
\tag{20}
\]

The last rational reserve is 59/90000. At delta=0 these
inequalities would force a=1,b=0, contrary to the tilted premise.
Thus delta>0.

For t=0, the actual mean is p_AU=p_0+f_1+Yf_2, with
0<=Y<db by (14), and

\[
 |p_{AU}|^2=(1-da)^2+(Y-db)^2
                  \le(1-da)^2+(db)^2=|P_1|^2.
\tag{21}
\]

Together (20)--(21) give |p_AU|<13/50 throughout.
Let f be (4). Since the channel line contains q_A,

\[
 p_{AU}\cdot f=q_A\cdot f=-q(at+bx)<0.
\tag{22}
\]

Write T=-p_AU dot f. Then 0<T<13/50.

## 6. The far C application cannot be a strict C vertex

Its norm satisfies

\[
 |p_{CU}|^2=|p_{AU}|^2+1+2h
     <\frac{3961}{3600}<\frac54\le d^2+\frac14.
\tag{23}
\]

The last quantity is the squared norm of a radial unit's inner
vertices. In a physically unique boundary unit, both vertices
adjacent to its circle corner have norm at least
sqrt(d^2+1/4); this is the same corner calculation recorded in
Section 2 of S_LEAF_C5_ALIGNED_FAR_ENDPOINT_RADIAL.md.
The circle corner itself is unshareable. Thus if the current
application were a strict C vertex, C would be unique and it
would be the vertex opposite its circle corner.

Let u,v be its two inward unit side axes. Then
z_C=p_AU+n+u+v, and the actual strict support gives
n dot u,n dot v>0. Put

    L=n dot (u+v), W=f dot (u+v).

Then 1<=L<=sqrt(2), |W|<=1. Using h>=-delta,
|p_AU dot f|<13/50, and 1+sqrt(2)<5/2 gives

\[
 \begin{split}
 R^2
 &=|p_{AU}|^2+3+2L+2(1+L)h
                   +2W(p_{AU}\cdot f)\\
 &>5-5\delta-\frac{13}{25}
  >\frac{1319}{300}
  >\frac{1105}{256}.
 \end{split}
\tag{24}
\]

The final reserve is 1541/19200. This contradicts (1).
Consequently the unchanged n is a side axis of C.
U already has this side axis by w_U=1. Their opposing faces
must have genuine positive overlap: a singleton intersection
would be a point-only vertex/vertex contact with selected normal
equal to a side axis, contrary to the original convention.
No actual mean is moved.

## 7. Every unique-C axis-owner possibility violates one actual B half-plane

Suppose C were physically unique. Since q_C is a positive
multiple of its unique corner and its f-coordinate equals
p_AU dot f=-T<0, its exact box and circle corner are

\[
 \begin{gathered}
 C=[X,X+1]n+[-M,1-M]f,\qquad
 X=1+h,\quad z_C=(X+1)n-Mf,\\
 59/60<X<61/60,\quad M>1/2,\quad
 M^2=R^2-(h+2)^2<23/60<(31/50)^2.
 \end{gathered}
\tag{25}
\]

Weak endpoint versions of the X bounds suffice everywhere;
they are strict because delta<1/60. The final squared reserve
is 2/1875. Properness at the original inner-axis C port gives

\[
 q_C=\frac{T}{M}z_C,\qquad
 T\ge\frac{XM}{X+1}>\frac{59}{238}.
\tag{26}
\]

Let g be the original unit direction from C through V to B.
Its f-component is positive by the actual C force equation:
the unique circle resultant has negative f-component and the
U pair force has zero f-component. If g dot n>=0, its support
on C is at least

    (X+1)(g dot n)+(1-M)(g dot f)
       > (19/50)((g dot n)+(g dot f)) >=19/50.

The true endpoint bound h_C(g)+w_V<=d would require this
support to be at most delta<1/60. Therefore g dot n<0.
Its actual application is the strict vertex

\[
                      Q=Xn+(1-M)f.
\]

This also excludes a diagonal V by the existing endpoint-axis
requirement, so w_V=1. Write

\[
 \begin{gathered}
 g=-\alpha n+\beta f,\quad \alpha,\beta>0,\quad
 \alpha^2+\beta^2=1,\\
 Q-q_C=-v n+\ell f,\qquad
 v=\frac{T(X+1)}M-X,\quad \ell=1-M+T.
 \end{gathered}
\tag{27}
\]

Properness and the strict normal give v>0 and alpha/beta=v/ell.
The whole original range now has the simple bounds

\[
 \begin{split}
 \ell&>\frac{19}{50}+\frac{59}{238}>\frac35,\\
 v&<\frac{13}{50}\frac{121}{30}-\frac{59}{60}
       =\frac{49}{750},\\
 \frac{\alpha}{\beta}&<\frac{49}{450}<\frac19,\qquad
                         \alpha<\frac19.
 \end{split}
\tag{28}
\]

Put Delta=p_AB-p_AU. From the actual root feature cover,

    Delta=(Z-1)f_1+(1-Y)f_2,
    0<=Z<=1, 0<=Y<1, and Y=0 when t>0.

Since n=x f_1-t f_2 and f=t f_1+x f_2,

\[
 \Delta\cdot n\le0,\qquad \Delta\cdot f\le1,\qquad
                         -\Delta\cdot n\le\sqrt2.
\tag{29}
\]

The actual B contains p_AB and lies beyond the C--V supporting
gap of one. Since Q=p_AU+n+ell*f, it must satisfy

\[
 1\le g\cdot(p_{AB}-Q)
   =\alpha(1-\Delta\cdot n)
       +\beta(\Delta\cdot f-\ell).
\tag{30}
\]

If the last parenthesis is nonpositive, its term is nonpositive.
Otherwise its term is less than 1-ell<2/5. Thus (28)--(29)
give the following strict upper bound for the right side:

\[
               \frac19(1+\sqrt2)+\frac25
                   <\frac5{18}+\frac25
                   =\frac{61}{90}<1,
\tag{31}
\]

a contradiction. This proves that no physical-unique C
remains. It uses no feature choice at B beyond its original
application on A.

## 8. The unchanged radial chart and exact remaining scope

C is therefore physical radial. Its existing n side axis must
be its inner radial axis: the other three radial axes are
excluded by containment just as in Section 4. Its actual
inner support is d, so X=1+h=d and h=delta. Equations
(22)--(23) yield exactly

    C=[d,d+1]n+[-1/2,1/2]f,
    p_CU=d*n-T*f, 0<T<13/50.

The original B--V--C diagonal alternative is now excluded by
the accepted degree-free radial/boundary diagonal theorem at
d>1. Thus w_V=1. Together with Sections 1--7, this proves
the complete statement (3)--(5).

Combined with S_LEAF_C5_ALIGNED_FAR_ENDPOINT_RADIAL.md, the
entire original S-leaf C5 load13 family now necessarily has a
physical radial C, a genuine U--C shared inner face, two
side-normal transmitters and R^2>17/4. The aligned and tilted
root charts retain their separate actual equations and sliders.

This is a whole-domain structural theorem. It does not claim
that the surviving positive six-body cores are impossible.
The original gate M6.B5L.C5.L13.S still requires the full
three-extra-square completion proof. No new gate is counted,
no physical body is contracted away, and no force, circle
weight, original normal, mean endpoint or extra square is
deleted.

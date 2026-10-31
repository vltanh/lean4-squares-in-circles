# A boundary-endpoint transmitter forces uniform outward support at a three-force hub

Date: October 28, 2026 UTC. Author: shared_s continuation.

**Status: complete proposed general support theorem and whole original
roof-AC S-family exclusion, frozen for full root and separate independent
review. No original gate or metadata is changed by this manuscript.**

The general theorem uses the actual C2, U2 and H3. Its external unit X
has arbitrary degree, load and physical circle mask. It yields a strict
support lower bound of 1/5, without an owned-axis premise at HX.
The genuine S-root's actual inward unit segment supplies the conflicting
upper bound below 1/60 for every root position at once.

This is a compatible pre-extraction theorem. The fixed-tip, two-body
block and three-fixed-port selections are made simultaneously before
the original multipliers are extracted. No normal of an extracted
certificate is changed.

## 1. General local theorem

Retain all nine original units, their physical interior disjointness,
the original circle and

    79/40<=R<=sqrt(1105)/16.

Let C,U,A,H,X be distinct actual units, with positive contacts

    CU, UA, CH, AH, HX

and an actual physical AX contact. Assume:

* C is loaded and has true positive degree two, with neighbors U,H.
* U is unloaded and has true positive degree two, with neighbors C,A.
* H is unloaded and has true positive degree three, with neighbors C,A,X.
* A physically touches the circle.

No force equation at A or X is used. In particular their degrees,
circle masks, individual zero circle weights and all their other
positive forces remain. Retain every original application and
weighted mean.

Write m for the original unit normal from H into X and Q_X for
its original common application or shared-side mean. Let O be the
original circle center.

**Uniform support theorem.** In the common compatible physical
certificate described below,

    m.(Q_X-O)>1/5.                                  (1)

Consequently X contains no actual point of the closed disk of
radius 1/5 about O. This last conclusion follows from the actual
minimum-m support of the whole unit X; it does not identify X
with a half-plane or create a comparison neighbor.

## 2. The entire parallel H/U frame is impossible

The unit-bypass theorem applied to C-U-A with bypass H makes
U side-normal of reserve one and separates U,H transversely.
Choose channel coordinates

    U=[0,1]^2, C subset {y<=0}, A subset {y>=1},
    P_C=(xi,0), P_A=(xi,1), 0<=xi<=1,

and put H on the right. If H is parallel to U, then exactly

    H=[a,a+1]x[0,1], a>=1.

Both endpoints C,A must also be parallel. For example a tilted
C has a unique highest point, which would have to be both its
CU and CH point. It must be (1,0), with a=1, giving a point-only
vertex/vertex CU contact with U's axis normal, contrary to the
unchanged strict singleton convention. The same argument applies
at A. Thus

    C=[c,c+1]x[-1,0], A=[n,n+1]x[1,2],
    a-1<=c,n<1, 1<=a<2.                            (2)

Write O=(X0,Y0) in these translated coordinates. If C has two
physical circle corners, they must be its bottom corners:
the actual A top side at height 2 gives Y0>=2-R>-1/2.
Set L0=sqrt(R^2-1/4). The radial mask gives

    X0=c+1/2, Y0=L0-1, 19/10<L0<5/2.

Every A corner then has horizontal distance at most 3/2 from
O and vertical distance less than 11/10. Its squared norm is
less than 173/50<(79/40)^2. This contradicts the actual A circle
contact. Hence C has one physical circle corner.

A shared CH side would make both positive C pair forces
vertical, impossible for that unique physical corner. Therefore

    c=a-1, Q_C=(a,0), n_C=(r,s), r,s>0,

where n_C points from C into H. Its circle force points strictly
Southwest. Write its unique circle vector as (-X1,-Y1), with
X1>1/2. Let mu,nu>0 be the CU and CH magnitudes, lambda_C>0
the circle magnitude, and k=a-xi in [0,1]. Full C2 gives

    lambda_C*X1=nu*r,
    lambda_C*Y1=mu+nu*s,
    lambda_C*(Y1-X1)=mu*k.

The last identity is torque at the actual Q_C. Eliminating the
magnitudes gives Y1>=X1 and

    Y1-X1=k*(Y1-X1*s/r), hence s<=r.                (3)

If k=0, the positive mu gives the strict version; if k>0,
use k<=1. Every original CU mean is retained.

If AH is shared, its H force is rho e_y at an actual
Q_A=(zeta,1), with a<=zeta<=n+1<a+1. Full H force gives
m_x>0. If m_y<0, X is supported at H's bottom-right vertex
and its whole upward span is strictly less than one, so
max_X y<1 and AX is impossible. If m_y=0, the whole X
lies in x>=a+1 whereas max_A x=n+1<a+1. Thus m_y>0
and Q_X=(a+1,1). Full H torque there gives

    nu*(s-r)=rho*(a+1-zeta)>0,

contrary to (3).

If AH is singleton, then n=a-1 and its H normal is strict
Northwest. Again m_x>0; the same two alternatives force
m_y>0 and Q_X=(a+1,1). The strict unit support-span bound
in direction West now gives min_X x>a, whereas max_A x=a.
This contradicts AX.

This reproduces the full mathematical proof of
HOUSE_END_TRIPLE_PARALLEL_BYPASS_EXCLUSION.md at its actual
local scope. Its old external-roof load and degree never
enter any step. The general theorem therefore always has
H genuinely tilted to U.

## 3. Complete tilted chart and local endpoint features

The actual chart is now

    U=[0,1]^2, C subset {y<=0}, A subset {y>=1},
    P_C=(xi,0), P_A=(xi,1), 0<=xi<=1,
    H=P+[0,1]u+[0,1]v,
    P=(d0,e), u=(a,b), v=(b,-a),
    a,b>0, a^2+b^2=1,
    d0>=1, 1-b<=e<=a.                              (4)

Let L=P+v and V=P+u. The complete geometric tilted-domain
proof and its endpoint-feature refinement give

    n_C,x>=0, n_C,y>0,
    n_A,x>=0, n_A,y<0,                              (5)

for the original normals from C,A into H. Both CH and AH
are physical singletons. Their points lie strictly to the
right of xi. The original features are

    CH H-owned: n_C=u, Q_C=P+t v, 0<=t<=1;
    CH not H-owned: Q_C=L;
    AH H-owned: n_A=v, Q_A=P+sigma u, 0<sigma<=1;
    AH not H-owned: Q_A=V.                         (6)

Every A chord Q_A-P_A points right and weakly up and has
length at most one, including any original A side application.
For a tilted A it is on its rightward side incident to its
unique lowest vertex. For a parallel A it is on its whole
actual bottom side.

For clarity, (4)--(6) use only actual support gaps, square
center halfwidths, the true U2 channel and physical unit
features. No X load or equation is used. The sources give
all axis endpoints as well as strict vertex features.

Write nu,rho,omega>0 for the original H magnitudes toward
C,A,X. Its full equation is

    omega*m=nu*n_C+rho*n_A.                         (7)

The two endpoint contacts cannot both be H-owned. Otherwise
m=(nu u+rho v)/omega, while the actual H-A-X triangle and
the H-owned HA normal -v require (-v).m>=0, a contradiction.
This is a consequence of the entire H3, not a shortened star.

## 4. The lower boundary unit is parallel and physically unique

The following complete local export removes all other C masks
and frames. The imported containment inequalities are the
explicit scalar/corner subproofs of the cited sources; no
complete old theorem is applied with its external roof changed.

### 4.1. Unique physical circle corner, tilted C

The CU point is the unique highest vertex P_C. CH is a
distinct fixed physical singleton. The general fixed-tip
selection therefore excludes a genuinely free CH normal.
It needs no boundary neighbor and does not freeze a mean.

If C owns CH, write

    w=(-c,-s), k=(s,-c), c,s>0, c^2+s^2=1,
    C=P_C+[0,1]w+[0,1]k,
    n_C=(c,s), L=P_C+tau k, 0<tau<=1.

The actual chart gives tau*s>=b and tau*c<=a+b-1<b,
so c<s. The true C circle resultant has own components
(nu+mu*s,mu*c), both positive. Its unique corner is
P_C+w+k, and the original torque at P_C is

    nu*(1-tau)=mu*(c-s),

which is impossible. This is the complete short C-owned
calculation, with the original positive CU magnitude mu.

If H owns CH, n_C=u. The actual C support is its adjacent
vertex P_C+k: the alternative P_C is not to the right, and
a zero k projection would give either a shared CH side or
a forbidden singleton axis endpoint. Put

    A0=a*c+b*s>0, D0=a*s-b*c>0,
    P_C+k=P+t v, 0<=t<=1.

Its height gives e=t*a-c, so c<=a+b-1<sqrt(2)-1 and s>c.
The C circle resultant has own components

    (mu*s+nu*A0, mu*c-nu*D0).

Its unique corner is P_C+w+k or P_C+w. The first gives
the impossible torque mu*(s-c)+nu*D0=0. The second gives

    nu*(D0-A0)=mu*c>0,
    (a-b)*s>(a+b)*c, in particular a>b.             (8)

Since both H endpoints cannot be H-owned, the actual A
point is V. Its true chord is

    V-P_A=(s+a-t*b, t*a+b-c-1).

The squared norm decreases strictly with t<=1: half its
derivative is t-b*s-a*(c+1)<0, because
a*c+b*s>=b and a+b>1. With p=a+b and k1=a-b,

    |V-P_A|^2-1
      >=(s+k1)^2+(p-c-1)^2-1
       =3-2p+2s*k1-2c*(p-1)
       >3-2p+2c>3-2sqrt(2)>0.

The strict middle step is (8). This contradicts the complete
actual A chord bound in Section 3.

Thus no tilted unique-corner C survives. These are precisely
Sections 2--4 of the older unique-tilted-tip source; the last
argument uses only H3 and actual H-A-X contact, not X's degree.

### 4.2. Tilted C with two physical circle corners

Set h=sqrt(R^2-1/4)-1, so 9/10<h<51/50. Every actual
two-corner mask and either individual zero circle coefficient
is retained.

For H-owned CH, the same actual adjacent-vertex argument
gives P_C+k=P+t v, c<=sqrt(2)-1, and s>91/100.
Neither P_C nor P_C+k can be a physical circle point shared
with another unit. The radial axis is therefore w, and

    P_C-O=h*w-(1/2)k,
    P_A-O=(-A0,B0),
    A0=h*c+s/2, B0=1-h*s+c/2,
    Q_A=V,
    Q_A-P_A=(s+a-t*b, t*a+b-c-1).                  (9)

These are the exact inputs of Sections 1--4 of
HOUSE_END_TRIPLE_RADIAL_HUB_OWNER_EXCLUSION.md. That complete
local subproof puts every actual A corner strictly inside
D_R. For a tilted A, the true chord gives beta<psi/2,
where c=cos(psi), s=sin(psi); its adjacent vertices follow
from |P_A-O|<R-1, and its opposite-vertex deficit exceeds
(1+sqrt(1+s))*17/120. For parallel A its full bottom-side
mean interval is kept, with strict squared-radius margins
122829/1562500 and 1308919/196000000 on the two complete
continuous c ranges. All of these inequalities use only
(9), the radius window and the actual A shape.

For genuinely free CH, the actual point is L=P_C+k.
Again the radial axis is w and (9)'s origin coordinates
hold. The complete actual upper side is Q_A=P+sigma*u,
0<sigma<=1, and its chord satisfies

    q=(s-b+sigma*a, a-c+sigma*b-1),
    q_x>0, q_y>=0,
    |q-(s,-1-c)|^2=1+sigma^2<=2.

Section 5 of the same radial-hub-owner source proves
exactly the same entire tilted-A or parallel-A containment
from these actual coordinates, with every original mean.
It uses no extra free-normal selection.

For C-owned CH, retain the full actual side parameter

    L=P_C+tau*k, 0<tau<1,
    b<=tau*s, tau*c<=a+b-1<b.

The original C2 force cone excludes radial axis k, forcing
w and the same origin coordinates as (9). Its full torque,
with the actual two-circle weight parameter left in [0,1],
gives

    nu*(tau-1/2)=mu*(h*c+s/2)>0.                    (10)

Every actual upper chord is

    q=(tau*s-b+sigma*a, a-tau*c+sigma*b-1),
    0<sigma<=1, q_x>0, q_y>=0.

Sections 2--5 of HOUSE_END_TRIPLE_RADIAL_LOWER_TIP_EXCLUSION.md
use precisely these data and (10). They prove c<5/8,
beta<psi/2 and tan(beta)<1-sqrt(c+c^2/4) for tilted A;
the entire remaining corner bounds have strict margins,
including 411/80000 for the harder opposite-corner range.
For parallel A they retain the whole original bottom-side
interval and prove ell>=c/s, improved by 1/32 when c>=1/2.
The corresponding complete corner margins are 229/8000
and 795411/16000000. All actual A points are strictly
inside D_R in every case.

The only contradiction in these three subproofs is A's
physical circle contact. They use no A equation and no X
force, degree or circle-mask premise. The complete older
proofs and their exact scalar inputs were audited for this
export; only their headings carry the stronger old roof
assumption, which is not used by these calculations.

### 4.3. Parallel C with two physical circle corners

Write C=[q-1,q]x[-1,0], with q>1 from its actual CH
contact. By (5) its outward resultant
-mu*e_y-nu*n_C permits only radial axis -e_x or -e_y.
For -e_x the radial pose is O=(q+h,-1/2), making the
actual U corner (0,1) have squared norm greater than
(1+h)^2+9/4=R^2+2.

For -e_y write O=(x0,h). The actual CU mean satisfies
|xi-x0|<=1/2. Thus

    |P_A-O|^2<=1/4+(1-h)^2<13/50.

All actual A points then have norm below
sqrt(13/50)+sqrt(2)<1347/700<79/40<=R, again contrary
to physical boundary contact. This is the entire parallel
radial argument, retaining all original means and weights.

We have proved the uniform local conclusion

    C is parallel to U and has one physical circle corner.       (11)

It uses the full C2 and H3 exactly where stated. It has
no ownership or load assumption at the external unit X.

## 5. The free-CH feature has support greater than 3/10

The remaining parallel unique C cannot own CH: by (5)
its only possible owned axis is e_y, which would give a
vertical resultant at its unique physical circle corner.
Thus CH is H-owned or genuinely free.

First take the free case. Retain

    C=[q-1,q]x[-1,0], Q_C=L=(q,0),
    P=(q-b,a), k=q-xi in (0,1], k>=b,
    z_C-O=(-X0,-Y0), X0,Y0>1/2,
    X0^2+Y0^2=R^2, O=(q-1+X0,Y0-1).

The exact C2 force/torque equations give Y0>X0 and,
writing n_C=(c,s),

    k*(Y0-(s/c)*X0)=Y0-X0, 0<s/c<=1.

Consequently if theta=arg(u), psi=arg(n_C), then

    0<theta<psi<=pi/4,
    n_C=A_C*u-D_C*v, A_C>D_C>0.                    (12)

If UA were physically singleton, aggregate the original
C,U equations. The fixed external applications are Q_C
and P_A; their internal CU mean cancels. The necessary
virtual-work identity is

    det(W0,n_C)=0,
    W0=det(P_A-O,e_y)*(z_C-O)
          -det(z_C-O,e_y)*(Q_C-O),
    (W0)_x=X0*k>0.                                (13)

The compatible two-body block selection avoids this one
unoriented forbidden line on the original free interval.
All physical tuples, candidate channels and unique corners
are prelisted independently of eventual degrees, loads and
multipliers. The fixed external points have different
heights 0 and 1, so their junction parameters are distinct.
The finite common selection, matching and uncrossing
argument is exactly the one fully displayed in Section 5
of BOUNDARY_ENDPOINT_TRANSMITTER_OBLIQUE_HUB_OWNED_EXIT_POSITIVE_SUPPORT.md
and Section 2 of the old parallel-unique free-tip source.
No predicate about X's load, degree or HX ownership is
included in the prelist or enters (13).

Thus a surviving certificate has shared UA and parallel A.
Its actual AH contact is

    sigma=(1-a)/b=b/(1+a)=tan(theta/2),
    Q_A=P+sigma*u=(q-sigma,1), n_A=v,
    A=[q-sigma-1,q-sigma]x[1,2].

Full H force reads

    omega*m=nu*A_C*u+(rho-nu*D_C)*v.

The actual triangle and H-owned HA normal -v imply
m.v<=0. If this were strict, Q_X=V and the full H
torque would have the nonzero sign of

    nu*(A_C-D_C)+(1-sigma)*rho>0,

a contradiction. Therefore

    m=u, rho=nu*D_C, omega=nu*A_C.

Keep the original HX mean Q_X=P+u+ell*v. Its full
torque gives 1-ell=sigma*D_C/A_C>0. Physical AX contact
requires sigma+b>=1, since X lies beyond H's u=1 support
and A has maximum u-coordinate sigma+b relative to P.
Thus sigma>1/3 and a+b>7/5.

The original invariant support is consequently

    m.(Q_X-O)=1+a+b-a*X0-b*Y0
       >=1+a+b-R>1+7/5-21/10=3/10.                (14)

This is the full free-CH argument, including all original
HX and UA means. The old upper circle equation and all
later loaded-roof concurrence arguments are unused.

## 6. The H-owned-CH feature also has uniform positive support

Now n_C=u and the original application is

    Q_C=(q,0)=P+t*v,
    P=(q-t*b,t*a), 0<=t<=1,
    k=q-xi in (0,1], k>=t*b, t*a+b>=1.

The unique physical C corner again gives

    z_C-O=(-X0,-Y0), X0,Y0>1/2,
    R^2=X0^2+Y0^2, O=(q-1+X0,Y0-1).

Its full original C2 equations are

    lambda_C*X0=nu*a,
    lambda_C*Y0=mu+nu*b,
    lambda_C*(Y0-X0)=mu*k.

Hence

    Y0>X0,
    (1-k)*Y0=(1-k*b/a)*X0.                         (15)

If k<1, then a>b. If k=1, then a=b=1/sqrt(2).
The latter is impossible: AH is not H-owned by Section 3,
so its actual H point is V, and

    V-P_A=(1+a-t*b,t*a+b-1)

has norm greater than one for every t<=1. Its first
component exceeds one when t<1, and at t=1 the second
component is sqrt(2)-1>0. Therefore

    a>b>0, k<1, 0<theta=arg(u)<pi/4.               (16)

AH is not H-owned, so at V its inward H components obey

    n_A.u<0, n_A.v>0.

Equation (7) makes m.v>0. If m.u<0, its actual H
support is L and its world y component is negative.
The whole-X upward support span is strictly below one,
so max_X y<1 and AX is impossible. If m.u=0, then
m=v is H-owned and the actual H-A-X triangle contradicts
n_A.v>0. Thus

    Q_X=W=P+u+v, m.u>0, m.v>0.

Full H torque at W now gives

    rho*(n_A.u)=-nu*(1-t),
    D=rho*(n_A.v)>0,
    omega*m=nu*t*u+D*v, 0<t<1.                    (17)

These are the complete original forces. The strict t
interval follows from the equations and actual features.

### 6.1. The actual exit point has two positive hub coordinates

Relative to the true origin, put

    U0=(W-O).u=1+a+b-a*X0-b*Y0,
    V0=(W-O).v=(1-t)+b-a-b*X0+a*Y0.

Since a>b and X0<Y0,

    a*X0+b*Y0
      =[(a+b)(X0+Y0)-(a-b)(Y0-X0)]/2
      <(a+b)*R/sqrt(2).

Because R>sqrt(2) and a+b<=sqrt(2), this gives

    U0>1+sqrt(2)-R>3/10.                          (18)

The last strict comparison uses sqrt(2)>7/5 and R<21/10.

Using the exact C2 relation (15), the other projection is

    V0=(1-t)+(a-b)*(X0/(1-k)-1)>0.                 (19)

Indeed

    X0/(1-k)=Y0/(1-k*b/a)>Y0>R/sqrt(2)>1.

Every denominator is positive by (16). These are actual
point projections, not projections of an auxiliary line.

### 6.2. Compatible fixed-port selection and a uniform exit angle

The three original H contacts Q_C,V,W are physical
singletons at three distinct points. The first normal,
from H to C, is the geometric owned axis -u.

Relative to Q_C, the other two points are

    V-Q_C=u-t*v, W-Q_C=u+(1-t)*v.

Both are off the line Q_C+R*u because 0<t<1.
The general fixed-singleton off-line selector therefore
applies to the actual unloaded H3, with arbitrary neighbor
degrees and loads. In the common selected certificate,
AH is A-owned and HX is X-owned. The proof needs only
the first of these consequences.

The prelist is physical and is made before true degrees
or loads are known. Q_C is fixed by the actual CH
singleton, not by a selected value of the CU mean.
The two possible free normal parameters at V and W
belong to distinct actual junctions. No normal is
changed after (17) has been extracted.

Write j=(cos(beta),sin(beta)) for the actual rightward
side of A at its bottom support and use the proper
frame (j,Jj). For tilted A, P_A is its unique bottom
vertex and

    A=P_A+[0,1]j+[0,1]Jj,
    n_A=-Jj, V=P_A+ell*j, 0<ell<1.

For parallel A, take beta=0 and retain its whole bottom
side mean; the same chord has 0<ell<=1. Its actual
maximum j-coordinate relative to P_A is at most one.

The strict H components in (17) imply

    delta=theta-beta in (0,pi/4),

and the exact original chord equations are

    ell*cos(beta)=k+a-t*b,
    ell*sin(beta)=t*a+b-1,
    ell*cos(delta)=1-b+a*k,
    ell*sin(delta)=a+b*k-t.                        (20)

Throughout the complete original interval,

    ell+sin(delta)>1.                             (21)

Here is the full continuous proof. At fixed a,b,t, ell
increases with k and sin(delta) is nondecreasing:
writing x=k+a-t*b>0, y=t*a+b-1>=0, its derivative has
the sign of y*(a*x+b*y)>=0. It suffices to use k=t*b.
Put w0=1-a*t, so 0<w0<=b. At that endpoint

    ell0^2=a^2+(b-w0)^2=1-2b*w0+w0^2<1,
    ell0*sin(delta0)=a*w0.

Since a>=b and

    ell0*(2b-w0)/(1+ell0)<b,

we have a*w0>ell0*(1-ell0), proving (21).
The original mean k is never replaced: the endpoint
is used solely to bound the scalar expression.

Now

    W-P_A=(ell+sin(delta))*j-cos(delta)*Jj.

From (17),(20), the normalized exit force has

    (omega/nu)*m
       =cos(delta)*j
          +[(t-cos(delta)^2)/sin(delta)]*Jj.        (22)

Its j component is positive. If its Jj component
were nonpositive, (21) would put W's m projection
strictly above that of every actual A point: A has
j-coordinate at most one and Jj-coordinate nonnegative.
That would contradict actual AX contact with the
minimum-m support of X at W.

Hence the actual angle alpha=arg_j(m) is positive.
Equation (22) and t<1 give

    tan(alpha)=(t-cos(delta)^2)/
                         (sin(delta)*cos(delta))
                   <tan(delta).

Thus 0<alpha<delta<pi/4, including the entire parallel-A
mean case until any further contradiction. In particular

    m.u=cos(delta-alpha)>1/sqrt(2).                 (23)

No upper-body force equation or external-X load is
used in this angle bound. It is the short chord part
of the older parallel-unique-hub proof; its stronger
22.5-degree estimate and all later A3/X2 steps are
unnecessary.

Combining (18),(19),(23) with m.v>0 proves

    m.(Q_X-O)=(m.u)*U0+(m.v)*V0
        >3/(10*sqrt(2))>1/5.                      (24)

The last exact comparison is 9>8. This completes
the H-owned-CH case.

Sections 2--6 exhaust the H/U frames, all C masks,
all CH owner/free features and every actual mean.
Equations (14),(24) prove the general theorem (1).

## 7. Every genuine S root has the conflicting near-origin point

Let X have its actual genuine radial S leaf L, with
unit outward leaf direction e_L. The exact leaf theorem
gives the unchanged radial application

    p=d*e_L, d=sqrt(R^2-1/4)-1>0.

This is an actual maximum-e_L support point of X.
The inward unit-segment lemma therefore gives

    p-t*e_L in X for every 0<=t<=1.

If d<=1, choose t=d and obtain O in X. If d>1,
choose t=1 and obtain the actual point (d-1)e_L in X.
Thus in every feature, owner, side-mean and root-position
case there is a point Z in the actual X with

    |Z-O|<=epsilon=max(d-1,0)<1/60.                (25)

The strict upper bound follows from the original radius
cap; the exact squared comparison is

    (121/60)^2-1041/256=31/57600>0.

This argument uses no force equation or degree at X.
The original S leaf remains physically present; it is
not replaced by its radial line or resultant.

For the actual minimum-m HX support at Q_X, (25) gives

    m.(Q_X-O)<=m.(Z-O)<=|Z-O|<1/60,

contrary to (1). Thus the general local configuration
cannot have a genuine S leaf at X, in any root position.
The same local theorem also excludes any external X
containing O, including a genuine D-leaf root, but no
new closure credit is assigned to previously closed D rows.

## 8. Whole original roof-AC S join

The original full graph has the house edges

    AT, DT, AD, AB, BC, CD

and its genuine S leaf at T. In the original AC load
row, A and C are loaded, B and D are unloaded, and the
real leaf is loaded. The real root T remains unloaded
of true degree three, including its original leaf.

Apply the general theorem literally with

    X=T, H=D, U=B, upper endpoint A=A,
    lower endpoint C=C.

Then C has true degree two with neighbors B,D.
B has true unloaded degree two with neighbors C,A.
D has true unloaded degree three with neighbors C,A,T.
A physically touches the circle and retains its full
loaded degree three. The actual AX contact is AT.
Every premise is supplied by the original graph/load
row; no nonleaf is discarded to change a degree.

The pre-window portion is handled on the same nine
actual squares by NINE_RADIUS_TWO_MEASURE_LOWER_BOUND.md:
R<=2 is impossible. On the remainder,
R>2>79/40, so the general local theorem applies up to
the original upper radius sqrt(1105)/16.

The contradiction in Section 7 therefore excludes

    M6.B5L.HOUSE.ROOF.LAC.S

in its whole original physical domain. It covers low
and equality d<=1, aligned and tilted roots, origin-free
and origin-containing roots, all three HX physical
interfaces, every circle mask and zero individual weight,
all original shared means and the entire three-extra
completion problem.

The three extra squares and real leaf are kept throughout.
No disk-avoidance condition on an unnamed completion unit
is imposed. The proof never uses a three-force equation at
the loaded A, a two-force equation at X, or a fictitious
second leaf at H.

The ABC.S row has loaded B and fails the U2-unloaded
premise. The endpoint fan has true H4 and fails the H3
premise. No corresponding closure is claimed.

## 9. Exact operative inputs and audited proof boundaries

| Source | SHA256 | Exact use |
| --- | --- | --- |
| UNIT_BYPASS_NORMAL_CHANNEL.md | db073cd024a4f2e763e7cd0a21bf5cb6a2a8be67069f3f9d3aff638b8a40b258 | Actual unloaded U2 reserve one and complete transverse separation |
| HOUSE_END_TRIPLE_PARALLEL_BYPASS_EXCLUSION.md | d8351b5eb394a2d0a1324b1992d848865946303a4ad3bb4d884d206d6222394f | Entire local parallel-frame proof, reproduced in Section 2; external X load/degree unused |
| HOUSE_END_TRIPLE_TILTED_BYPASS_DOMAIN.md | 73b54547dfc5b04ece8aa137533ace68179b05cdc412bb7305074503cdc14cbf | Full actual tilted coordinates, singleton geometry and not-both-H-owned fact |
| HOUSE_END_TRIPLE_UNIQUE_TILTED_TIP_EXCLUSION.md | 23baa17e19c4bd5b8722ceb79b718eb310cfb717817d0eb879b7c75888469ffd | Complete local quadrant/chord and unique-C subproofs, rederived in Sections 3--4.1 |
| GENERAL_FIXED_TIP_NORMAL_SELECTION.md | ef8ae8a219af9fa15a70698e485bbb337925e5caf2cd64b6b5c2619d9c4bd194 | Actual tilted unique C2 with two distinct fixed physical singleton applications |
| HOUSE_END_TRIPLE_RADIAL_HUB_OWNER_EXCLUSION.md | 6ee367eca974a62c495eb9d8eda4ac3afb75ff5cf64a34581e43590780e0b144 | Complete H-owned/free radial containment subproofs, with literal inputs in Section 4.2 |
| HOUSE_END_TRIPLE_RADIAL_LOWER_TIP_EXCLUSION.md | a0bab9ed546b22f17f18e6d3dd4f07354d6a8f859ce5f172c4353ec2905522cf | Complete C-owned radial scalar/corner bounds and parallel radial exclusion |
| HOUSE_END_TRIPLE_PARALLEL_UNIQUE_FREE_EXCLUSION.md | d83d0938ca639e5712c3d910d35890fc823227262d7364f1110d73937c7f5784 | Sections 1--3 and support Equations (25)--(27); later loaded-X arguments unused |
| BOUNDARY_ENDPOINT_TRANSMITTER_OBLIQUE_HUB_OWNED_EXIT_POSITIVE_SUPPORT.md | 81ff70e50d96bee07e2f1612df700b9bb1fcf7b783387f856d6db71fb04c2cea | Fully displayed two-body block selection and exact local export scope; no reliance on its HX-owner hypothesis for another case |
| HOUSE_END_TRIPLE_PARALLEL_UNIQUE_HUB_EXCLUSION.md | e69f54f988f4b955774da429079f7c6da59096ea763899cf73053f82e4a1345b | Local Sections 1--3.1 and force/chord identities only; all later A3 and loaded-X2 arguments unused |
| FIXED_SINGLETON_THREE_FORCE_OFF_LINE_NORMAL_SELECTION_AND_H4_OWNED_END_REDUCTION.md | d5e02f317ecbfdbd3d948fd27f5f78d6eda8803fb679c435ef3101780e1f47b1 | General Sections 1--3 applied to actual H3, fixed CH axis and distinct off-line V,W; no H4 specialization imported |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 | Original physical triangle constraints and strict whole-unit support span, all mean endpoints |
| RADIAL_BRIDGE_AND_LEAF_REDUCTION.md | faf453b3c519b10590cf9d6f6dbf9282233bd2ff04c90aa0cd8cd89e060bc676 | Exact genuine S application and entire inward unit segment |
| NINE_RADIUS_TWO_MEASURE_LOWER_BOUND.md | 4c9e708945938c3f9df575e76f7573903d6b5a0ce4eccb5bcea760353a47458a | Unconditional same-nine pre-window entry R>2 |
| FIVE_BODY_BLOCK_LEAF_GRAPH_LOAD_COVER.md | e5c84071363e8dc43b09f9033c7cb3a7684f1de19bcd169d53c9eab55d51963b | Whole original AC.S graph/load row, true degrees and actual three-extra contract |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Full original equations, actual means and extraction order |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe | Compatible common finite selection, junction matching and preservation of surviving point normals |

All normal selections concern actual fixed physical singleton
points or a block whose shared internal force cancels. The
general fixed-port selector has no circle-degree predicate;
the block prelist has no eventual-load or multiplier predicate.
They are imposed together before extraction, with the original
strict normal and matching conditions.

No Lean compilation, CI, numerical pose search, angle mesh,
replacement support body, extra leaf, original gate edit or
remote action is used. This manuscript supplies the complete
mathematical implication; original bookkeeping remains for the
parent's independent adoption.

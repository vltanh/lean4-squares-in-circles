# A boundary-endpoint transmitter forces positive support at an owned exit of an oblique three-force hub

Date: October 28, 2026 UTC. Author: shared_s continuation.

**Status: complete proposed local theorem and complete shared-XH
exclusion for the open-origin roof AC.S interface, submitted for
full root and separate independent review. This is a compatible
pre-extraction implication, not an assertion for arbitrary choices
of free normals. No whole original fine gate is declared closed.**

The external unit X is allowed arbitrary load and degree. In the
literal roof application it remains the real unloaded degree-three
S root with its original leaf. The theorem does not turn that root
into the loaded degree-two roof of an older end-triple problem.
Only explicitly audited local parts of those older proofs are used.

## 1. The local theorem and complete physical scope

Retain the original nine interior-disjoint closed unit squares in
the original disk, with

    79/40 <= R <= sqrt(1105)/16.

Consider distinct actual units C,U,A,H,X with the positive edges

    CU, UA, CH, AH, HX,

and an actual physical AX contact. Suppose:

* U has zero circle resultant and true positive degree two, with
  exactly the neighbors C,A.
* C has a positive circle resultant and true positive degree two,
  with exactly the neighbors U,H.
* H has zero circle resultant and true positive degree three, with
  exactly the neighbors C,A,X.
* A physically touches the original circle. Its degree and circle
  resultant need no further restriction.
* H is not parallel to U, and H owns the original HX normal m.

All physical C masks, both original radial-circle coefficients,
every original U/HX mean and all independent square frames remain.
The original normal conventions are retained. In addition to the
general fixed-tip selection already available, Section 5 below
prelists the same fixed-external-contact block condition used in
the older parallel-unique free-tip proof, without a load or degree
condition on X.

**Local conclusion.** If Q_HX is the original HX application or
shared-side mean, measured relative to the original circle origin O,
then

    m.(Q_HX-O) > 3/10.                              (1)

The hypothesis that H owns m includes both singleton and physically
shared HX. The conclusion is independent of where the unchanged
mean lies on that owned side.

## 2. Complete channel chart and the actual H-owned exit

The unit-bypass theorem applied to C-U-A and the actual common
neighbor H makes U a side-normal transmitter of reserve one.
Its transverse-separation theorem permits a rigid coordinate
change and, if necessary, a reflection so that

    U=[0,1]^2, C subset {y<=0}, A subset {y>=1},
    P_C=(xi,0), P_A=(xi,1), 0<=xi<=1,
    H=P+[0,1]u+[0,1]v,
    P=(d0,e), u=(a,b), v=(b,-a),
    a,b>0, a^2+b^2=1,
    d0>=1, 1-b<=e<=a.                               (2)

O denotes the unchanged true circle origin in this translated chart.
The invariant scalar in (1) is unchanged by this coordinate choice.

Put L=P+v and V=P+u. Let n_C,n_A be the original unit normals
from C,A into H. The geometric parts of the complete tilted-bypass
proof, followed by Section 1 of the unique-tilted-tip proof, give

    (n_C)_x>=0, (n_C)_y>0,
    (n_A)_x>=0, (n_A)_y<0.                          (3)

Here is the exact scope of those local arguments. Every lower or
upper H contact has x>d0>=1>=xi. The actual support gap and the
unit center halfwidth bounds exclude a negative x component.
The lower support then lies on PL or at L, while the upper
support lies on PV or at V. These imply the strict y signs in (3).
Parallel H/endpoint supports cannot share a segment by the
coordinate-sign arguments in Section 3 of the tilted-domain
source. Thus CH and AH are physical singletons. These arguments
use only the actual units and channel (2), not a force or a circle
mask at X.

In particular

    n_C=A_C*u-D_C*v,
    A_C>0, D_C>=0,
    Q_A=P+sigma*u, 0<sigma<=1,                     (4)

The CH support is H-owned precisely in the D_C=0 alternative.
If D_C>0 its
actual H application is L. Every actual A chord Q_A-P_A
points right and weakly up, and

    |Q_A-P_A|<=1.                                  (5)

For a tilted A this is its rightward side incident to its unique
bottom vertex; for a parallel A both applications lie on its
bottom side. Thus (5) retains all possible A side applications.

Let nu,rho,omega>0 be the actual H magnitudes toward C,A,X.
The full original H force equation is

    omega*m=nu*n_C+rho*n_A.                        (6)

At least one endpoint x component is strict. Otherwise both
endpoint normals would be vertical, forcing simultaneously
e=a and e=1-b, hence a+b=1, impossible in the strict tilt.
Therefore m_x>0. Because m is H-owned, m is u or v.

The actual H-A-X triangle and H-owned HX give

    n_A.m<=0.                                      (7)

If m=v, then n_C.v=-D_C<=0 and (7) gives n_A.v<=0.
Taking the v component of (6) would give omega<=0.
Consequently

    m=u.                                          (8)

Since (3) implies n_A.v=b*(n_A)_x-a*(n_A)_y>0,
the v component of (6) now forces D_C>0. Thus

    HC is not H-owned, and its actual H point is L. (9)

This short argument works for every C physical mask. It is the
only use of the H-owned-exit hypothesis before the final support
calculation. It does not use an A or X force equation.

## 3. Every tilted unique-circle-corner C is excluded

Suppose C is tilted to U and has one physical circle corner.
The physical CU point is its unique highest vertex P_C.
The other physical application is the distinct fixed point L,
whose x coordinate exceeds xi. The general fixed-tip theorem
therefore excludes a genuine free CH normal in the compatible
pre-extraction selection. It requires no boundary neighbor and
does not freeze a shared mean: CU itself is physically singleton.

Together with (9), the only remaining CH owner is C. Write

    n_C=(c,s), w=(-c,-s), k=(s,-c),
    c,s>0, c^2+s^2=1,
    C=P_C+[0,1]w+[0,1]k,
    L=P_C+tau*k, 0<tau<=1.                        (10)

The displayed endpoint is harmlessly included. The actual strict
point convention gives the appropriate side-interior version.
Comparing (2),(10) gives

    tau*s>=b, tau*c<=a+b-1<b,

so c<s. Let mu>0 be the original CU magnitude. The true
outward circle resultant is

    F_C=(nu+mu*s)*w+mu*c*k.

Both own components are positive. The unique physical circle
corner is therefore P_C+w+k. C's complete original torque
about P_C gives exactly

    nu*(1-tau)=mu*(c-s).                           (11)

This is impossible: the left side is nonnegative, the right
side negative. This is the complete calculation in Section 3
of the older unique-tilted-tip source. Its Section 4, which
treats H-owned CH by a longer chord argument, is unnecessary
because (9) has already excluded that feature.

## 4. Every physical two-circle-corner C is excluded

This section explicitly exports the local containment subproofs
from the two radial-tip sources. They use C's actual radial pose,
the actual C2 equations where indicated, (2)--(5), and A's
physical circle contact. They use no X equation, circle contact,
or degree assumption. The complete older end-triple theorems
are not invoked with a changed roof hypothesis.

Put

    h=sqrt(R^2-1/4)-1, 9/10<h<51/50.               (12)

### 4.1. Tilted C with a genuinely free CH normal

C has the frame w,k in (10). Since CH is free, its original
point is the vertex L=P_C+k. A physical circle point cannot be
shared with another unit. Thus P_C and P_C+k are both inner
radial vertices, and the only possible outward radial axis is w:

    P_C-O=h*w-(1/2)*k,
    P_A-O=(-A0,B0),
    A0=h*c+s/2, B0=1-h*s+c/2.                     (13)

The actual coordinate equality at L gives e=a-c. Hence

    c<=a+b-1<=sqrt(2)-1,
    s>91/100.

Retain the entire actual upper H side as Q_A=P+sigma*u,
0<sigma<=1. Its actual chord is

    q=Q_A-P_A=(s-b+sigma*a, a-c+sigma*b-1),
    q_x>0, q_y>=0,
    |q-(s,-1-c)|^2=1+sigma^2<=2.                 (14)

These are exactly the inputs of Section 5 of
HOUSE_END_TRIPLE_RADIAL_HUB_OWNER_EXCLUSION.md. That section
applies the following complete algebraic bounds from its
Sections 2--4:

* For a tilted A, (14) puts its actual rightward side angle beta
  strictly below psi/2, where c=cos(psi), s=sin(psi). Equation
  (13) gives |P_A-O|<R-1. The opposite-corner squared-radius
  deficit is greater than
  (1+sqrt(1+s))*17/120. Thus all four actual corners are inside.
* For a parallel A, retain its actual lower-left corner as
  P_A-r e_x, with 0<=r<=1-ell and ell=q_x. The same section
  proves ell>=s-sqrt(1-2c-c^2), with no fixed mean. Its
  Sections 4 bounds have the strict squared-radius margins
  122829/1562500 for c<=1/4 and
  1308919/196000000 for 1/4<=c<=sqrt(2)-1.

Every input to those scalar bounds is (12)--(14), the actual
unit shape, and the displayed full mean interval. In particular
their earlier H-owned-CH discussion is not imported: Section 5
derives exactly (13),(14) for the free contact. Thus all of A
is strictly inside the original circle, contrary to its physical
circle contact. Both actual C circle weights were unrestricted.

### 4.2. Tilted C with a C-owned CH normal

Keep (10), now with 0<tau<1. These are all remaining tilted
radial cases because (9) excludes H ownership. The complete C2
pair equation and its actual radial circle cone first force
the radial axis to be w: if it were k, the force-component
ratio would be greater than s/c>1, while the physical radial
circle cone allows at most 1/(2(h+1))<1. Thus (13) holds.

Let the original weighted tangential circle parameter range
over its whole interval [0,1]. C's full original torque gives

    nu*(tau-1/2)=mu*(h*c+s/2)>0.                   (15)

Consequently tau>1/2; no equality or positivity of the two
individual circle weights was assumed. The actual H coordinates
and A chord are exactly

    b<=tau*s, tau*c<=a+b-1<b,
    q=(tau*s-b+sigma*a, a-tau*c+sigma*b-1),
    0<sigma<=1, q_x>0, q_y>=0.                    (16)

Sections 2--5 of
HOUSE_END_TRIPLE_RADIAL_LOWER_TIP_EXCLUSION.md are scalar and
actual-corner implications from precisely (12),(13),(15),(16)
and the A support-chord property (5). Their full domain gives

    c<5/8, s>39/50,
    beta<psi/2,
    tan(beta)<1-sqrt(c+c^2/4)                    (17)

for every tilted A. For c<=sqrt(2)-1 the complete corner
bounds already stated in Section 4.1 apply. For the remaining
tilted A range the opposite-corner squared-radius deficit has
the strict lower bound 411/80000. The two adjacent-corner
bounds split only the continuous c interval at 29/50 and have
strict positive margins in Equations (25),(26) of that source.

For a parallel A, that source keeps the whole original lower
side interval. It proves ell>=c/s, and the strict improvement
ell>c/s+1/32 for c>=1/2. The complete corner bounds then have
squared-radius margins 229/8000 for c<=1/2 and
795411/16000000 for 1/2<=c<5/8, in its Equations (35),(36).

No step in those Sections 2--5 takes a force or torque equation
at A or X. Their conclusion is that every actual A corner is
strictly inside D_R, contradicting A's required physical circle
contact. This excludes the entire original tilted radial mask.

### 4.3. Parallel C, with both physical circle corners retained

Write C=[q-1,q]x[-1,0]. The actual CH point has x>1, so q>1.
Its outward resultant is -mu*e_y-nu*n_C. By (3) the outward
physical radial axis can only be -e_x or -e_y.

For -e_x, its radial pose gives O=(q+h,-1/2). The actual U
corner (0,1) has squared norm greater than

    (1+h)^2+9/4=R^2+2,

a contradiction. For -e_y write O=(x0,h). Because P_C is on
the actual inner radial side, |xi-x0|<=1/2. Hence

    |P_A-O|^2<=1/4+(1-h)^2<13/50.

Every point of the actual unit A is at distance at most sqrt(2)
from P_A. Thus every point has norm less than

    sqrt(13/50)+sqrt(2)<1347/700<79/40<=R.

Again A cannot meet the circle. This is Section 6 of the radial
lower-tip source, reproduced in its entirety at the present scope.
It uses neither an A force equation nor an X hypothesis.

Together Sections 3--4 leave only C parallel to U and having
one physical circle corner.

## 5. The remaining unique parallel C: the exact compatible selector

C cannot own CH in this remaining frame. By (3) a C-owned
axis would be e_y, making its two positive pair forces parallel
and its circle resultant vertical. A parallel unit with a
unique physical circle corner has nonzero horizontal coordinate
at that corner relative to O, so cannot have a vertical circle
resultant. H ownership is already excluded by (9).
Therefore CH is genuinely free.

Use the original free-HC point and means:

    C=[q-1,q]x[-1,0], Q=L=(q,0),
    P=(q-b,a), q-b>=1,
    k0=q-xi in (0,1], k0>=b,
    n_C=(c,s), c,s>0.

Its unique physical circle corner z_C=(q-1,-1) has

    z_C-O=(-X0,-Y0), X0,Y0>1/2,
    X0^2+Y0^2=R^2,
    O=(q-1+X0,Y0-1).                               (18)

The full actual C2 equations give

    lambda_C*X0=nu*c,
    lambda_C*Y0=mu+nu*s,
    lambda_C*(Y0-X0)=mu*k0.

Thus Y0>X0 and, with r=s/c,

    k0*(Y0-r*X0)=Y0-X0, 0<r<=1.                   (19)

Write phi=arg(u), psi=arg(n_C). Strict freedom at L means
n_C=A_C*u-D_C*v with A_C,D_C>0. Equations (19) give

    0<phi<psi<=pi/4,
    A_C=cos(psi-phi)>D_C=sin(psi-phi)>0.            (20)

If the physical UA contact were singleton, its point P_A
would be fixed. Sum the true C,U equations and take common
translation and rotation of that two-body block. The internal
CU force cancels, including its entire variable shared mean.
The necessary fixed-external-contact condition is

    det(W,n_C)=0,
    W=det(P_A-O,e_y)*(z_C-O)
          -det(z_C-O,e_y)*(Q-O),
    W_x=X0*k0>0.                                  (21)

Therefore the original open free-normal interval at Q can
avoid its at most one unoriented forbidden line.

This is exactly Section 2 of
HOUSE_END_TRIPLE_PARALLEL_UNIQUE_FREE_EXCLUSION.md, with
its own load/degree premise on the external roof omitted:
that premise never enters the two-body virtual-work identity.
For the present theorem, prelist all ordered physical tuples
(C,U,A,H,X), every candidate U side channel and every physical
unique C corner, irrespective of eventual degrees, loads or
multipliers. True positive degrees and zero or positive circle
resultants are tested only after extraction; no prelist predicate
depends on them. Conditions (21) are nontrivial for every tuple
with the stated fixed physical features. The two external
applications have heights 0,1,
so their free-junction parameters cannot be the same or coupled
by a four-junction matching. The original finite-junction
selection and uncrossing argument applies unchanged. Additional
contacts or forces on X are retained and do not enter (21).

These conditions are selected simultaneously with the general
fixed-tip conditions before extraction. A surviving normal is
never altered, a side mean is never fixed, and every physical
candidate surviving thinning was prelisted. Thus a surviving
free-CH certificate has physically shared UA, so A is parallel
to U. This statement is an existence-of-compatible-certificate
implication; no exclusion of arbitrary free-normal choices is
claimed.

## 6. Physical triangle contact gives the strict support bound

A is now parallel to U, and a+b>1. The upper H vertex is
strictly above height 1. Therefore the actual AH point is
on the strict interior of PV and the upper unit's bottom-right
vertex. Exactly as in the geometric part of the free-tip
source, retain

    sigma=(1-a)/b=b/(1+a)=tan(phi/2),
    Q_A=P+sigma*u=(q-sigma,1),
    n_A=v,
    A=[q-sigma-1,q-sigma]x[1,2].                   (22)

The actual UA mean remains anywhere in its full physical
overlap. In (6), n_C=A_C*u-D_C*v and m=u by (8).
The full H force therefore gives rho=nu*D_C and
omega=nu*A_C. Write the original HX point or mean as

    Q_HX=P+u+ell*v, 0<=ell<=1.

The complete H torque gives

    1-ell=sigma*D_C/A_C>0.                        (23)

The exact value (23) is retained, although it will not be
needed to restrict the final support.

X lies entirely beyond H's u=1 support relative to P.
The whole actual A in (22) has maximum u-coordinate
sigma+b relative to P. Their physical AX contact requires

    sigma+b>=1.

If sigma<=1/3, then b=2*sigma/(1+sigma^2)<=3/5,
so sigma+b<=14/15, a contradiction. By (20),

    1/3<sigma<sqrt(2)-1,
    a+b>7/5.                                     (24)

The second bound follows from phi=2*arctan(sigma), the
increase of cos(phi)+sin(phi) on (0,pi/4), and its value
7/5 at sigma=1/3. No endpoint of the physical AX contact
inequality has been dropped.

Finally, (18),(22),(23) give the original invariant support

    m.(Q_HX-O)=u.(P-O)+1
       =1+a+b-a*X0-b*Y0
       >=1+a+b-R
       >1+7/5-21/10=3/10.                        (25)

Here R<=sqrt(1105)/16<21/10 and Cauchy's inequality used
the exact physical circle equation X0^2+Y0^2=R^2.

This is the support calculation through Equation (27) of the
older free-tip source. Its Section 4, which uses the upper
circle equation, is unnecessary here. Its later loaded-roof
proper-concurrence Equation (29) and every subsequent step
are explicitly unused. No load, degree, circle resultant or
concurrence of X has entered the proof. This proves (1).

## 7. Literal whole shared-root roof AC.S exclusion

Take the actual open-origin retained domain of

    M6.B5L.HOUSE.ROOF.LAC.S.

Use the original labels

    X=T3, H=D3, U=B2, lower endpoint C=C2,
    upper endpoint A=A3, with the real S leaf at T.

The actual C-U-A path is C-B-A. B and D have zero circle
resultant and their stated true degrees. C is the genuine
loaded degree-two endpoint. A physically touches the original
circle and retains its loaded degree three. The actual
physical triangle H-A-X is D-A-T.

Suppose HX is physically shared. The complete actual-hub and
positive-concurrence results, as assembled in
UNIT_SUPPORT_CAP_AND_SHARED_S_ROOT_ROOF_RETURN_SEPARATION.md,
give the unchanged common H/X chart

    H=[h0-1,h0]x[g-1,g],
    X=[h0,h0+1]x[-b0,1-b0],
    -epsilon<=h0<0,
    n_HX=(1,0),
    P_HX=(h0,-t), 0<t<=b0.

Every shared mean, including both root and hub side endpoints,
is retained. Section 6 of that same source proves that the
actual B channel is strictly Southwest in this chart. Thus
the original H and U are genuinely oblique. The shared HX
axis is owned by H and its unchanged actual support is

    n_HX.P_HX=h0<0.

All hypotheses of the local theorem are literal. It gives
the contradictory inequality h0>3/10. Hence the entire
shared-HX interface in this original open-origin AC.S row
is excluded, including the original three-horizontal-force
H feature and every physical C mask and actual mean.

The real X=T root stayed degree three with its original
S leaf. It was never relabeled as a loaded degree-two body.
The original lower window is supplied by the accepted same-nine
entry to this retained domain, which in fact has R>sqrt(17)/2.
All nine squares, masks and individual zero coefficients remain.

The analogous ABC.S row has a loaded B and does not satisfy
the unloaded U2 premise. No application to that row is made.
An H4 fan also does not satisfy the full H3 equation (6).
The remaining singleton-HX portions of the AC.S row are not
declared excluded by this shared-interface join.

## 8. Exact sources and audited boundaries

| Source | SHA256 | Exact use |
| --- | --- | --- |
| UNIT_BYPASS_NORMAL_CHANNEL.md | db073cd024a4f2e763e7cd0a21bf5cb6a2a8be67069f3f9d3aff638b8a40b258 | Original U2 reserve one and entire transverse separation, Sections 1--4 |
| HOUSE_END_TRIPLE_TILTED_BYPASS_DOMAIN.md | 73b54547dfc5b04ece8aa137533ace68179b05cdc412bb7305074503cdc14cbf | Local actual chart, weak endpoint directions and singleton geometry, Sections 1--3; no old roof premise |
| HOUSE_END_TRIPLE_UNIQUE_TILTED_TIP_EXCLUSION.md | 23baa17e19c4bd5b8722ceb79b718eb310cfb717817d0eb879b7c75888469ffd | Geometric quadrant/chord Section 1, fixed-tip Section 2, complete C-owned torque Section 3; Section 4 unused |
| GENERAL_FIXED_TIP_NORMAL_SELECTION.md | ef8ae8a219af9fa15a70698e485bbb337925e5caf2cd64b6b5c2619d9c4bd194 | Actual unique-corner C2 with two distinct physical singleton applications |
| HOUSE_END_TRIPLE_RADIAL_HUB_OWNER_EXCLUSION.md | 6ee367eca974a62c495eb9d8eda4ac3afb75ff5cf64a34581e43590780e0b144 | Section 5 free-contact coordinates and complete scalar/corner inequalities of Sections 2--4, with inputs (12)--(14) supplied here |
| HOUSE_END_TRIPLE_RADIAL_LOWER_TIP_EXCLUSION.md | a0bab9ed546b22f17f18e6d3dd4f07354d6a8f859ce5f172c4353ec2905522cf | C-owned original C2 and complete scalar/corner Sections 1--5; all-mask parallel Section 6 reproduced |
| HOUSE_END_TRIPLE_PARALLEL_UNIQUE_FREE_EXCLUSION.md | d83d0938ca639e5712c3d910d35890fc823227262d7364f1110d73937c7f5784 | Sections 1--3 and original support Equations (25)--(27), rederived here; Section 4 and loaded-X Equation (29) onward unused |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 | Literal H-owned HX in the actual H-A-X triangle |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Full original positive-body equations, actual mean convention and simultaneous finite selection |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe | Original junction-compatible finite selection and surviving-normal scope |
| UNIT_SUPPORT_CAP_AND_SHARED_S_ROOT_ROOF_RETURN_SEPARATION.md | 2b90b565591b3c9bbc30c2c1af48cf117771b96bbc58ad81441f9e99497067d6 | Literal shared roof AC.S negative original HX support and strictly oblique original B channel |
| FIVE_BODY_BLOCK_LEAF_GRAPH_LOAD_COVER.md | e5c84071363e8dc43b09f9033c7cb3a7684f1de19bcd169d53c9eab55d51963b | Exact original AC.S graph/load row and true degree contract |

This source proves a complete local support theorem and one whole
original shared interface. It makes no original-gate accounting
change. There is no sampled angle cover, replacement neighbor,
additional leaf, removed force, post-extraction normal change,
Lean compilation, CI, or remote action.

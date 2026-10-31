# A near-side boundary return excludes both complete strict-house force branches

Date: October 29, 2026 UTC. Author: broad_s_families continuation.
Exact published comparison: a5f3922a9c12830b76f2a7ee9dd4dbf1024f85b5.
Actual comparison Git tree: 2617ed629140d69171c86bfa68b0ee5784ab8c8c.

**Status: complete proposed continuous hand theorems, frozen for separate
full independent review and root adoption.** The entire original owned-leaf,
strict AD-corner, A-owned inward AT-side feature is excluded, simultaneously
for the parallel and nonparallel original C force rows. The whole original
TC family remains open at other original return features.

Two broad results are proved separately: an all-mask physical corner cone
from a real near-axis port, and a radius-free full-D3 axis obstruction from
one actual proper return ray. No original force, mean, physical unit or
individual circle coefficient is replaced. No geometric packing certificate
or finite orientation subdivision is used.

## 1. Complete physical near-axis and near-side corner bounds

Put R0=sqrt(17)/2 and R1=sqrt(1105)/16. Let K be an actual unit square
contained in the unchanged disk D_R(O), where R0<=R<=R1. The origin stays
O=0. Fix orthonormal coordinates and 0<=epsilon<=1/60. Its physical circle
corners are the actual Z in K with |Z|=R, whether their coefficients are
positive or zero. No degree or force equation is assumed.

**Theorem A1, a real near-axis port.** If an actual P=(epsilon,w) belongs
to K and w>=0, every physical circle corner satisfies

    Z_y>|Z_x|.                                      (1)

Indeed the diameter gives |Z_x|<=epsilon+sqrt(2), and

    (epsilon+sqrt(2))^2
      <2+1/20+1/3600=7381/3600<17/8<=R^2/2.        (2)

Here sqrt(2)<3/2, and the last strict reserve is 269/3600. If Z_y<=0,
then P.Z<=epsilon*R, so

    |Z-P|^2>=R^2-2*epsilon*R
             >17/4-5/72=301/72>2,                (3)

contradicting the actual unit diameter. In (3), R<25/12 follows from
625/144-1105/256=55/2304>0. Therefore Z_y>0, and (2) proves (1).
This is a statement about every physical circle corner, not merely a
positive-weight corner, a center, or an averaged contact.

**Theorem A2, an actual supporting near side.** Suppose additionally

    max_K x=epsilon,
    P=(epsilon,w) belongs to K,
    -3/8<=w<=1.                                    (4)

If K is physically a boundary unit, then

    w>1/2,
    Z_x<0 and Z_y>-Z_x>0
    for every physical circle corner Z.            (5)

Every point of a physical boundary unit has norm at least R-sqrt(2).
Throughout the closed radius interval,

    (R-sqrt(2))^2>=25/4-sqrt(34)>5/12,             (6)

because sqrt(34)<35/6, with squared reserve 1/36. If w<=0, (4)
would give

    |P|^2<=1/3600+9/64<5/12,

whose strict gap is 3971/14400. Thus w>0. Applying (6) again gives

    w^2>5/12-1/3600>1/4,                          (7)

with final reserve 599/3600, proving w>1/2.

From a maximum-x point of a unit, upward and downward vertical reach
are each at most one. At a tilted maximum-x vertex its two actual
inward axes are (-c,s),(-s,-c), with c,s>0 and c^2+s^2=1, so every
vertical displacement belongs to [-c,s]. At a right-side mean of a
parallel unit, each remaining tangential distance is at most one.
Both side endpoints are included. Consequently

    w-1<=Y_y<=w+1 for every Y in K.                (8)

If a physical circle corner had Z_x>=0, (4), w>0 and w<=1 would give

    |Z|^2<=epsilon^2+(w+1)^2
             <=1/3600+4<17/4<=R^2,              (9)

with strict reserve 899/3600. Thus Z_x<0. Theorem A1 applies at the
same actual P and supplies the remaining part of (5).

For any full nonnegative physical circle combination with positive total,
these conclusions give

    F_x<0, F_y>-F_x>0.                            (10)

The full one-corner and two-corner masks, individual zero coefficients,
epsilon=0, epsilon=1/60, w=1, and either actual side endpoint are all
included. The corner conclusions are independent of the star's degree.

## 2. A radius-free full-star obstruction from one proper return ray

Here no containing-circle or boundary-unit premise is needed. Let D be an
actual unit square with precisely its three original positive outward pair
forces toward its actual neighbors A,C,T. Keep the full unloaded vector and
moment equations. In orthonormal coordinates write the original data

    S=P_DA=(h,V), h>=0,
    F_DA=(rho,-omega), rho,omega>0,
    F_DC=nu*g, nu>0, g_x,g_y<0,
    Q=P_DC, |Q-S|>1,
    G=F_DT=-F_DA-nu*g,
    F=P_DT.                                      (11)

All three applications are unchanged actual points or full shared-side
means on D and the corresponding actual neighbor. In particular G_y>0.
Assume the literal proper-ray information

    q_*=(x_*,w), x_*<0, w<=V,
    q_*=F+ell*G for some ell>=0.                 (12)

The scaling ell in (12) absorbs the positive length of the original G;
it does not replace its direction or application. Neighbors may have
arbitrary other forces. Suppose at least one of the original DA and DC
normals is a side axis of this same D.

**Theorem B.** These actual full-star data are impossible.

First, (12) and G_y>0 give F_y<=w<=V. If F=S, equality forces w=V
and ell=0, hence q_*=S. Its x coordinate h>=0 contradicts x_*<0.
Thus

    F_y<=V and F!=S.                             (13)

### 2.1. The entire original D-owned DA case

Suppose DA is a D axis. Put

    alpha=sqrt(rho^2+omega^2),
    n=(-p,r)=(-rho,omega)/alpha,
    m=(r,p), p,r>0, p^2+r^2=1.

The original n is the inward direction from A into D. The whole mean
at S has the actual representation

    D=S+[0,1]n+[-theta,1-theta]m,
    0<=theta<=1.                                 (14)

Since both coordinates of g are negative and both coordinates of m are
positive, g.m<0. The full D3 gives

    G=alpha*n-nu*g, G.m=-nu*g.m>0.

Every original DT support mean therefore has exactly the form

    F=S+lambda*n+(1-theta)*m,
    0<=lambda<=1.                                (15)

The original support sign of G.n fixes lambda to an endpoint unless it
vanishes; the whole interval in (15) retains that zero case. Its height is

    F_y=V+lambda*r+(1-theta)*p>=V.

Equality requires lambda=0 and theta=1, which gives F=S. Both alternatives
contradict (13). This excludes the complete D-owned DA row, including
all original AD and DT means and the simultaneous-owned case.

### 2.2. The complete remaining D-owned DC case

It remains that DC is D-owned and DA is not a D axis. Write its actual
unit direction and perpendicular side axis as

    k=g=(-c,-s), j=(-s,c),
    c,s>0, c^2+s^2=1, det(j,k)=1.

The original DA force satisfies

    F_DA.j=-A0, A0=rho*s+omega*c>0,
    F_DA.k=-B0, B0=rho*c-omega*s.                (16)

If B0<0, DA's original maximum on D is at minimum j and maximum k.
Since Q is also on the maximum-k face, the actual segment S--Q lies
on that one D side and has length at most one. This contradicts (11).
If B0=0, DA itself is the D axis -j, already excluded in Section 2.1.
Hence B0>0 and S minimizes both coordinates:

    D=S+[0,1]j+[0,1]k,
    Q=S+sigma*j+k, 0<=sigma<=1.                 (17)

The complete full-star force and the actual DT mean are

    G=A0*j+(B0-nu)*k,
    F=S+j+lambda*k,
    lambda=1 if B0>nu,
    lambda=0 if B0<nu,
    0<=lambda<=1 if B0=nu.                       (18)

Equation (13) gives

    V+c-lambda*s=F_y<=w<=V,
    lambda*s>=c,
    s>=c>0.                                     (19)

The unchanged full D3 moment about S is exactly

    nu*sigma+B0-nu-lambda*A0=0,
    B0=nu*(1-sigma)+lambda*A0.                  (20)

All three original forces, both original support means and every endpoint
remain in (20). Moreover

    B0/A0<c/s<=1,                               (21)

because A0*c-B0*s=omega(c^2+s^2)=omega>0.

If B0<nu, then lambda=0 contradicts (19). If B0>nu, then lambda=1
and (20) gives B0>=A0, contradicting (21). At the full zero-projection
case B0=nu, (20) instead gives

    lambda=(B0/A0)*sigma<c/s,

again contradicting (19), since sigma<=1. This proves Theorem B across
the complete D-owned DC side, all co-owned endpoints, and every original
zero projection. Its proof has no normal reselection or neighbor-degree
truncation.

## 3. Literal original house feature and all retained equations

Keep all nine actual squares and exactly the original TC component

    AT,DT,AD,AB,BC,CD,AL,
    true A4,D3,B2,C2,T2,L1,
    positive circle loads precisely T,C,L.

B remains the original unloaded transmitter, D unloaded with all three
positive neighbors, and L the actual genuine S leaf. There is no BD
contact premise. The three additional arbitrary units remain throughout.

We use the owned-leaf residual from the complete original assembly and
the full upper-mean owner union:

    R^2=(2+epsilon)^2+1/4<=1105/256,
    d=1+epsilon, 0<epsilon<1/60,
    epsilon<q<3/8, V=1-q,
    u=(-a,t), v=(-t,-a), a,t>0, a^2+t^2=1,
    a=(q^2-epsilon^2)/(q^2+epsilon^2),
    t=2*epsilon*q/(q^2+epsilon^2),
    A=[epsilon,d]u+[-q,V]v,
    L=[d,d+1]u+[-1/2,1/2]v.                      (22)

In world coordinates the actual B channel and C are

    B=[epsilon,d] times [z,z+1],
    C=[d,d+1] times [-1/2,1/2],
    P_AB=(epsilon,q), P_BC=(d,q),
    z<=q<=z+1, max_D y<=z<=q.                    (23)

Unless labeled world, coordinates below are in the proper unchanged
(u,v) frame about O. Thus P_AB=(epsilon,-q) in this frame and the
same positive AB magnitude mu has force mu*(-a,-t).

**Theorem C.** The entire following actual feature is impossible:

    S=P_AD=R0=(epsilon,V),
    F_AD=(-rho,omega), rho,omega>0,
    P=P_AT=(epsilon,w), -q<=w<=V,
    F_AT=(-eta,0), eta>0.                        (24)

The AD force is the original strict (-u,+v) corner force. The AT normal
is the original A-owned -u axis, with its complete actual side mean.
No D owner, T frame, concurrence location, or physical T mask is imposed.
In particular w=V and coincident original AT/DT applications are retained
until separately contradicted below.

Write the real leaf force as F_AL=(kappa,0), kappa>0, at its genuine
radial point d*u. The complete original A4 vector and origin-moment
equations give exactly

    omega=mu*t,
    kappa=mu*a+rho+eta,
    mu*a*q=rho*V+eta*w.                          (25)

For the last identity the AB moment is -mu*epsilon*t-mu*a*q, the
AD moment is epsilon*omega+rho*V, the AT moment is eta*w, and the
leaf moment is zero. Thus all four original terms are present.

The full original C2 theorem retains the complete alternative

    parallel: g_world=East, Q_world=(d,y),
              -1/2<=y<0, mu*q+nu*y=0;

    nonparallel: (g_world)_x,(g_world)_y>0,
                 Q_world=(d,-1/2),              (26)

where nu>0 is its unchanged CD magnitude. Both physical C circle
coefficients are strictly positive. The original D-to-C normal is g;
the actual radial shape of C has not been turned into a leaf equation.
The true D3 and actual AT contact also supply the complete strict
support inequality

    g_world.Z<g_world.Q for every Z in A union T. (27)

The whole A4, D3, C2 and T2 equations remain in force; B2 supplies
only its real AB/BC transmission identity.

## 4. The whole original near-side T mask and proper-ray entry

The actual AT normal in (24) gives max_T u=epsilon, with the actual
point P=(epsilon,w) in T. Its whole allowed range is contained in
[-3/8,1]. Theorem A2 therefore gives

    w>1/2,
    (F_T)_u<0, (F_T)_v>-(F_T)_u>0.              (28)

Here F_T is the full original nonnegative physical circle resultant,
including either physical mask and every individual coefficient.

Write G for the original D-to-T force. The complete D3 and T2 are

    (rho,-omega)+nu*g+G=0,
    F_T=(-eta,0)+G.                             (29)

Both rows in (26) give g_v=-t*(g_world)_x-a*(g_world)_y<0. Hence

    G_v=omega-nu*g_v>0.                         (30)

The two original T pair forces are thus nonparallel. This is proved
from their full equations, not imported from a pending parallel-T exit.

If their actual applications P and F=P_DT coincide, the complete
one-application theorem 3808 gives P=s0*F_T with s0>0. Its u coordinate
epsilon>0 contradicts (28). Thus they are distinct. The complete
nonparallel part of that same boundary-neighbor-free theorem gives

    q_T=s0*F_T, s0>0,
    q_T=P-ell_A*(1,0)=F+ell_D*G,
    ell_A,ell_D>=0.                             (31)

The coefficient ell_D incorporates the positive norm of G. In particular

    (q_T)_u<0, (q_T)_v=w<=V,
    F_v<=w.                                    (32)

No inside-T inference is made for a two-physical-corner mask. Equation
(31) is the actual proper-ray conclusion including zero lengths, and
(32) is valid even when its concurrence is outside the physical T.
The present radius interval lies within sqrt(2)<R<1+sqrt(2), so every
radius hypothesis of 3808 is literal. No boundary status at A or D is
added.

## 5. The entire parallel-C row is excluded by full original moments

Suppose the first row in (26) holds, retaining its whole actual y interval.
Since -y<=1/2, its complete C2 moment gives

    nu=mu*q/(-y)>=2*mu*q.                       (33)

On the other hand w<=V and (25),(28) give

    mu*a*q=rho*V+eta*w>=w*(rho+eta),
    rho+eta<=mu*a*q/w<2*mu*a*q<=a*nu.            (34)

In the proper leaf frame g=(-a,-t). Equation (29) consequently gives

    (F_T)_u=a*nu-rho-eta>0,

contradicting (28). This excludes every original parallel C mean,
both closed y=-1/2 and w=V endpoints, every actual T frame and mask,
and every possible D owner. No concurrence premise is needed for
this whole force branch.

## 6. One continuous inequality in the entire nonparallel-C row

Now use the actual Q_world=(d,-1/2). Its unchanged coordinates relative
to S=R0 in the leaf frame are

    Q-S=(-K,-W),
    K=a+t*(q+1/2)>0,
    W=V+t*d-a/2>1/8.                            (35)

For example Q.u=-a*d-t/2 and Q.v=-t*d+a/2. The identities (35) use
epsilon+a*d=a+t*q, which follows from the actual owned-leaf equations.
No y from the parallel row has been substituted here.

Because the original F_AD=(-rho,mu*t) points inward to D at S, the
actual point Q in D satisfies

    rho*K-mu*t*W>=0.                            (36)

Equation (25), with eta>0 and w>1/2, gives rho*V<mu*a*q. Combining
this strict full-A4 inequality with (36) yields

    a*q*K-t*V*W>0.                              (37)

Put r=epsilon/q, so 0<r<1 and the actual leaf identities are

    a=(1-r^2)/(1+r^2),
    t=2*r/(1+r^2), epsilon=r*q.

An exact expansion, with no angle or mean subdivision, gives

    a*q*K-t*V*W
      =(1+r)*[q*(r^3-r^2+3*r+1)-r*(3*r+1)]
        /(1+r^2)^2.                            (38)

The coefficient D0=r^3-r^2+3*r+1 is positive on 0<r<1 and is
strictly less than 3*r+1. Indeed D0=1+3*r-r^2*(1-r)>0, since
1-r^2>0, and the subtracted term is strictly positive. Thus (37)
forces

    q>r*(3*r+1)/D0>r,
    q^2>epsilon.                               (39)

This deduction keeps the entire original positive rho,eta,mu system;
none of these magnitudes is assumed small or discarded.

## 7. The actual AD/DC points force an original D axis

From (39), r<sqrt(epsilon)<1/sqrt(60)<2/15. Consequently

    t<4/15, a>24/25,
    q>r=t/(1+a)>t/2.                            (40)

For a, square against 1-(4/15)^2; its difference from (24/25)^2
is 41/5625>0. The strict r comparison uses 4/225-1/60=1/900.

Let k0=q+1/2. Then

    K-1=t*(k0-t/(1+a))>t/2>0,
    K<1+(4/15)*(7/8)=37/30.                    (41)

Also, using d<61/60, (40), and 1+a>49/25,

    W=1/2-q+t*d+(1-a)/2
      <1/2+t*(d-1/2)+t^2/[2*(1+a)]
      <1/2+(31/60)*(4/15)+(25/98)*(16/225)
       =1607/2450<2/3.                         (42)

The final gap is 79/7350. Therefore the same actual D points obey

    1<|Q-S|^2=K^2+W^2
        <(37/30)^2+(2/3)^2=1769/900<2,          (43)

with final reserve 31/900. If neither original AD nor original DC
normal were a D side axis, both applications would be distinct actual
D vertices. Their squared distance would be exactly one or two,
contradicting (43). Thus at least one of those unchanged original
normals is D-owned. This is a conclusion about the original normals,
not an assumed axis owner or a new normal selection.

## 8. Complete entry into the radius-free full-D3 axis obstruction

We verify its remaining force signs without presuming an owner. The
world displacement between the same actual points is

    Q_world-S_world=(1+t,a-q-1/2).

The actual unit diameter, with k0=q+1/2>0, gives

    (1+t)^2+(a-k0)^2<=2,
    t<=a*k0-k0^2/2,
    a-t/k0>=k0/2>0.                            (44)

At the actual P_AB, the strict full-D3 return inequality (27) gives

    (g_world)_x-k0*(g_world)_y>0,
    (g_world)_y/(g_world)_x<1/k0.                (45)

Both world components are positive in this row. Consequently its
unchanged leaf-coordinate components satisfy

    g_u=-a*(g_world)_x+t*(g_world)_y
         <[-a+t/k0]*(g_world)_x<0,
    g_v=-t*(g_world)_x-a*(g_world)_y<0.           (46)

The actual D has S=(epsilon,V), h=epsilon>0, original DA force
(rho,-omega) with rho,omega>0, and original DC force nu*g with both
components negative. Its actual Q obeys |Q-S|>1 by (43), and at least
one original normal is its side axis. Its original DT application and
proper ray are exactly (31)--(32). Thus every premise of Theorem B is
supplied by the unchanged units and full stars. That theorem excludes
both complete D-axis classes, including their shared boundary and
the entire zero-projection support interval.

This contradicts the entire nonparallel-C row. Together with Section 5
it proves Theorem C for every configuration in the stated original
feature, with all actual side means, coincident-point possibilities,
T physical masks and individual coefficients retained.

## 9. Exact full imports, provenance, and limits of the conclusion

The following complete operative sources were read at their exact pins.
Their full original scopes, rather than a checklist or review summary,
are the mathematical inputs used above.

| Complete source | SHA256 | Literal use |
| --- | --- | --- |
| GENUINE_S_HOUSE_TC_TILTED_RADIAL_C_COMPLETE_ASSEMBLY.md | 6f5634d78b0e217f91898852e721aedbc06a09c4398528c86753f29e4aaf89c2 | Exact original aligned-C owned-leaf residual, all units, degrees and original C force alternatives |
| ALIGNED_RADIAL_C_OWNED_LEAF_WHOLE_UPPER_MEAN_OWNER_UNION_2026_10_29_CONTINUATION.md | ea076feb168f61c9928c2e3d35d6e36e736af04d2068c4f64aac16c32656f334 | Complete original complement q<3/8; no later force/owner claim is imported |
| HIGH_SUPPORT_SIDE_CHANNEL_TOUCHING_RETURN_FORCES_TWO_POSITIVE_CIRCLE_CORNERS.md | 2a6f8da941de756abbea77f5c9aac75e5225968efdf278c683295b0dec900143 | Entire actual C force/mask cover and whole full-D3 strict support inequality at the actual A,T returns |
| LOADED_TWO_APPLICATION_FULL_STAR_BOUNDARY_FREE_CONCURRENCE_DICHOTOMY.md | 3808b2b767a9e15c7270b50c4fbbb434ae0d69fe42c567d4da01f7d167f7fa78 | Complete actual one-application alternative and nonparallel positive radial/proper rays, with no boundary-neighbor assumption and no inside-physical-two conclusion |

The exact physical force/torque contract is printed in Sections 3--4.
Its provenance is PHYSICAL_CONTACT_STRESS.md, SHA256
d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5.
The new physical and radius-free Theorems A1,A2,B are proved fully here.
The author discovered their use and the full original row contradiction;
root corroborated the sign in (38)--(39) after receiving the complete
proposed derivation. That corroboration is not independent review.

Neither the separate proposed be0af78e support-face theorem nor H4's
separate parallel-T theorem is an operative input. The present feature
is stated literally in (24), and its T nonparallelity is derived from
the complete original D3 in (30). No claim is made that this feature
exhausts all remaining original TC configurations.

The A-owned AD side, other strict AD/AT feature pairings, the upper-adjacent
genuine-leaf chart, the remaining actual allocation obligations and the
whole original TC row remain outside this conclusion. No original fine,
parent or coarse flag, computational certificate or retirement receives
credit. All nine physical units, every full force/torque equation, original
normal and mean, physical mask and individual coefficient remain. No pose
sampling, finite packing certificate, Lean/Lake, CI, metadata/flag edit or
remote action was performed. Full separate independent review and root
adoption are required before these exact proposed bytes are accepted.

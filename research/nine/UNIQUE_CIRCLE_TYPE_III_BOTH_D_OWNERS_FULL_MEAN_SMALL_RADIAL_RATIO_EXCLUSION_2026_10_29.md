# Both Type III D owners: one full-mean projection excludes every radial ratio at most one half

Date: October 29, 2026 UTC. Author: root_triangles.

**Status: complete proposed hand theorem for the entire stated continuous
domain, frozen for full independent review.** The same actual-point
projection excludes the genuine sole-D owner and the physically shared-D
owner, including the complete original shared-mean interval, whenever
the radial ratio p defined below satisfies p<=1/2. Every genuine negative
p is included. The proof requires no equation or boundary premise at the
exterior B,C. It retains the actual full A3,D3,V2 stars and does not claim
an exit for the complementary p>1/2 domain of either D owner.

## 1. Original physical setting and both D-owner charts

Retain distinct actual unit squares A,D,V,B,C in the same disk D_R,
where

    79/40<=R<=sqrt(1105)/16<1039/500.                 (1)

Their complete original stars are

    A:{V,D,B}, D:{V,A,C}, V:{A,D},

with A,D unloaded true3 and V loaded true2. V has exactly one PHYSICAL
circle corner. In its actual own frame, with the actual circle origin,
write

    V=[a-1,a] x [b-1,b], Z=(a,b), a,b>1/2,
    |Z|=R, F_V=kappa*Z, kappa>0,
    P1=(a-1,b), P0=(a-1,b-1).                       (2)

The two actual roof contacts are strict at those V vertices and owned
by their corresponding hubs. Put

    h=nA=(c,-s), e=tA=(s,c), c,s>0, c^2+s^2=1,
    nD=(C,S), tD=(-S,C), C,S>0, C^2+S^2=1,
    H=c*S+s*C, K=c*C-s*S,
    nD=K*h+H*e, tD=-H*h+K*e.                       (3)

The original roof magnitudes are mu,nu>0; rho>0 is the original AD
magnitude. The only interface directions considered here are the
unchanged D-owned roof direction g=-nD, directed from A into D.
Both of its physical owner possibilities are included.

### 1.1. Genuine sole-D owner

Here K<0. The complete original chart is

    A=P1-[0,1]*h+[-r,1-r]*e,
    D=P0-[0,1]*nD+[-t,1-t]*tD,
    W=P1-r*e=P0+(s/H)*tD,
    r=S/H, 0<t<1-s/H, H>s, H>S.                    (4)

In particular r<1 is part of the original side-interior chart. The
full original exterior forces, their actual applications, and A's
complete moment are

    F_B=rho*nD-mu*h,
    Q_B=P1-h+(1-r)*e,
    F_C=-(nu+rho)*nD,
    Q_C=P0-nD+z_D*tD,
    z_D=rho*(s/H)/(nu+rho),
    mu*(1-r)=rho*(H+K)>0.                          (5)

The strict h,e components of F_B are negative and positive, so Q_B
is its actual unique A support vertex. The scalar z_D in (5) is the
actual DC application fixed by full D torque. It is not chosen to
help the argument, and its entire side-mean interpretation remains.

The complete geometric angular range is

    pi/2<alpha+beta<2*pi/3, beta>pi/4,              (6)

where c=cos(alpha), s=sin(alpha), C=cos(beta), S=sin(beta).

### 1.2. Physical shared-D owner, with its full original mean

Here K=0,H=1,C=s,S=c, and g=-nD=-e. The complete actual
shared chart is

    r=c, 0<t<1-s,
    W=P1-z*h-c*e=P0+(s+z)*tD,
    0<=z<=1-t-s.                                  (7)

Both closed overlap endpoints and every original mean between them
are retained. Its actual positive shared length is not replaced by
a vertex singleton. The full force and moment data are

    F_B=rho*nD-mu*h,
    Q_B=P1-h+(1-c)*e,
    F_C=-(nu+rho)*nD,
    Q_C=P0-nD+z_D*tD,
    z_D=rho*(s+z)/(nu+rho),
    rho*(1-z)=mu*(1-c).                            (8)

In particular the shared z remains in (8). It has not been replaced
by the genuine equation (5) or by either overlap endpoint.

These are the exact two D-owned same-axis rows in the direct input
listed in Section 7. Their full equations are reproduced so that the
scope of the uniform estimate can be checked without an owner swap.

## 2. One common scalar chart from the full V2 equations

V's complete force and torque, retaining both original roof forces,
are

    mu*h+nu*nD=kappa*Z,
    mu*det(P1,h)+nu*det(P0,nD)=0.                  (9)

Since P1=P0+North, these imply

    mu*c=kappa*(a-b)>0, nu*C=kappa*b>0,
    nu*(S-C)=mu*s.                               (10)

In particular a>b and beta>pi/4 are consequences, not an interchange
of the upper and lower original ports.

For the genuine row put k=-K/H; for the shared row put k=0. Write

    J=sqrt(1+k^2), H=1/J, K=-k/J,
    u=c+k*s=S/H,
    p=Z_h/Z_e=(mu/nu)*J-k,
    x=p+1, v=1+k, T=sqrt(x^2+v^2),
    c=x/T, s=v/T,
    Y=R/sqrt(1+p^2), Z=(p*Y,Y).                   (11)

Coordinates in the last expression, and below, are in the actual
orthonormal h,e frame. The equality for p follows by taking the two
components of the first equation (9). Because

    C=(s-k*c)/J, S=(c+k*s)/J,

the last equation (10) also gives

    p=(1+k)*c/s-1.                               (12)

This proves the formulas c=x/T,s=v/T in (11). We have p>-k,
so x>0. In the shared row k=0 and p=mu/nu>0. The genuine row
can have p<0; this is included in the theorem.

The actual genuine geometry implies

    0<k<1/sqrt(3)<3/5,
    u=c+k*s<1,
    k<(1-c)/s=s/(1+c),
    (2*p+1)*k+k^2+k^3<1.                          (13)

The first bound is (6). For the last bound, u<1 is equivalent to

    (x+k*v)^2<x^2+v^2;

all sides before squaring are positive. Canceling and dividing by
v>0 gives

    2*x*k+k^2*(1+k)<1+k,

which is precisely the last inequality (13). Every inequality in
(13) used below also holds at k=0 for the shared row, with the
initial strict positivity of k omitted.

In particular, in the whole subdomain p>=2/5,

    k<9/20.                                      (14)

Indeed (2*p+1)*k+k^2+k^3 is increasing in k>=0 there; at
p=2/5,k=9/20 its value is 8829/8000>1. This deduction uses
the original geometric inequality, not a selected tilt bound.

## 3. One actual B point for both original owner rows

In the genuine row, the unchanged F_B in (5) is a positive multiple
of -lambda*h+e, where

    lambda=mu*J/rho+k
          =(1-k)/(1-u)+k
          =(1-k*u)/(1-u)>1.                       (15)

The middle equality is the full A moment in (5). The last strict
inequality follows from 0<u<1 and k<1. No force has been omitted.

In the shared row, the unchanged F_B in (8) has the same form, with

    lambda=mu/rho=(1-z)/(1-c)>1.                  (16)

To check the strict inequality for every original mean, (7) gives
1-z>=t+s>s. Also c+s>1, so s>1-c. Thus (16) includes both
closed endpoints of (7), regardless of which endpoint carries the
original shared mean.

In both rows the actual support application is

    Q_B=P1-h+(1-u)*e,
    P1=(p*Y-c,Y-s).                              (17)

For any actual unit square E with minimum support at a point or
full side mean Q in its actual inward unit-normal direction f,

    Q+f belongs to E.                            (18)

Here is the full face argument. In the actual own axes of E, each
component of f has absolute value at most one. If a component is
positive, a minimum-support coordinate of Q is the lower endpoint
and adding that component stays in its unit coordinate interval.
For a negative component it starts at the upper endpoint and the
same conclusion holds. A zero component preserves the full original
side coordinate, including every mean and both endpoints. Hence (18)
holds for every owner or strict normal, without rotating E or replacing
it by a point.

Apply (18) to the actual B with its unchanged normal
(-lambda,1)/sqrt(1+lambda^2). The following point belongs to B:

    X_B=(p*Y-c-1-lambda/sqrt(1+lambda^2),
         Y-s+1-u+1/sqrt(1+lambda^2)).             (19)

Choose the fixed unit direction n=(-4,3)/5 and put P_B=n.X_B.
Its exact projection, using u=c+k*s, is

    5*P_B=7+c-3*(1+k)*s
          +(4*lambda+3)/sqrt(1+lambda^2)
          +R*(3-4*p)/sqrt(1+p^2).                (20)

For every lambda>1,

    (4*lambda+3)/sqrt(1+lambda^2)>4,              (21)

because the difference of the positive squared sides is 24*lambda-7>0.
Thus the complete original mean dependence is retained in (20), and
only afterward bounded uniformly by (21).

Define the auxiliary functions

    G(p,k)=c-3*(1+k)*s
          =(x-3*v^2)/sqrt(x^2+v^2),
    q(p)=(3-4*p)/sqrt(1+p^2),
    F_R(p,k)=11+G(p,k)+R*q(p)-5*R.                (22)

Equations (20)--(21) imply the strict bound

    5*(P_B-R)>F_R(p,k).                           (23)

It remains to show F_R>0 throughout p<=1/2. The next three
continuous regions cover that entire domain.

## 4. Every negative radial ratio

Suppose p<0. The actual chart gives k<3/5, c>0, s<1, so

    G(p,k)>-3*(1+k)>-24/5.

Moreover q(p)>3, because 3-4*p>0 and

    (3-4*p)^2-9*(1+p^2)=-24*p+7*p^2>0.

Consequently

    F_R(p,k)>11-24/5+3*R-5*R
             =31/5-2*R
             >31/5-2*(1039/500)=511/250>0.        (24)

This covers every allowed negative p, including all values approaching
the original positive-force boundary p=-k. No extension through that
boundary or vanishing original force is asserted.

## 5. Two continuous monotonicity estimates for 0<=p<=1/2

For the following comparisons, regard the explicit scalar function
F_R in (22) on the closed rectangle

    0<=p<=1/2, 0<=k<=3/5.                        (25)

Only its scalar values are compared. Auxiliary points of this rectangle
are not asserted to describe physical packings or permissible original
forces. In particular no original mean is varied along the comparison.

Differentiating the explicit G gives

    G_p=v^2*(1+3*x)/(x^2+v^2)^(3/2),
    G_k=-v*(x+6*x^2+3*v^2)/(x^2+v^2)^(3/2)<0.    (26)

On (25), x in [1,3/2], v>=1 and T>=sqrt(2). Therefore

    G_p<(1+3*x)/T<=11/(2*sqrt(2))<4.             (27)

The final square comparison is 121<128. Also

    q'(p)=-(4+3*p)/(1+p^2)^(3/2)<-8/3,           (28)

since (1+p^2)^(3/2)<3/2 on this rectangle; the closed endpoint
is included because 125/64<9/4. From R>=79/40,

    (F_R)_p<4-(79/40)*(8/3)=-19/15<0,
    (F_R)_k=G_k<0.                              (29)

Thus F_R strictly decreases with either p or k throughout the
entire closed comparison rectangle, for every R in (1).

### 5.1. The whole interval 0<=p<=2/5

The actual k<3/5 and (29) give

    F_R(p,k)>F_R(2/5,3/5)
      =11-157/(5*sqrt(113))+R*(7/sqrt(29)-5).      (30)

The exact elementary comparisons

    157/(5*sqrt(113))<3,
    7/sqrt(29)>9/7

follow respectively from

    225*113-157^2=776>0,
    49^2-81*29=52>0.

Hence

    F_R(p,k)>8-(26/7)*R
             >8-(26/7)*(1039/500)
             =493/1750>0.                       (31)

Both p=0 and p=2/5 are included. The auxiliary upper k endpoint
in (30) enlarges the comparison rectangle; it does not create a
spurious original contact feature.

### 5.2. The whole interval 2/5<=p<=1/2

The actual geometric consequence (14) now gives k<9/20. Applying
(29) yields

    F_R(p,k)>F_R(1/2,9/20)
      =11-1923/(20*sqrt(1741))+R*(2/sqrt(5)-5).    (32)

The exact comparisons

    1923/(20*sqrt(1741))<7/3,
    2/sqrt(5)>8/9

follow respectively from

    140^2*1741-5769^2=842239>0,
    4*81-64*5=4>0.

Therefore

    F_R(p,k)>26/3-(37/9)*R
             >26/3-(37/9)*(1039/500)
             =557/4500>0.                       (33)

Both closed radial endpoints are included. The genuine k=0 endpoint
is not claimed to be an actual genuine feature; it is separately the
physical shared-D row covered by the same displayed inequalities.

## 6. Uniform conclusion and literal original-family transfer

Equations (24), (31) and (33) give F_R>0 for every original p<=1/2
in either D-owner row. By (23), the actual point X_B in B satisfies

    n.X_B=P_B>R.

This contradicts B being contained in D_R, because n is a unit
direction. The contradiction uses a real point of the unchanged B;
it imposes no boundary or reduced-degree assumption at that neighbor.

**Both-D-owner theorem.** In the complete physical setting (1)--(10),
neither a genuine sole-D roof-direction interface nor a physical
shared-D roof-direction interface is possible when p<=1/2. The
shared conclusion holds for the complete closed original mean interval
(7). The genuine conclusion holds for every allowable k, r and t;
all continuous tilt endpoints used in its necessary geometric bounds
are included as stated.

In each literal original row D02.L135 and D02.L1345, retain

    rim A--V--D--C--N_original--B--A and chord AD,
    A=0, V=1, D=2, C=3, N_original=4, B=5.

The true stars are A3,D3,V2. B,C are loaded true2; N_original is
unloaded true2 in L135 and loaded true2 in L1345. Their complete
original equations and all three additional physical units remain.
The local proof does not remove or merge any of these bodies, or
require a different degree or mask for them.

The same prior Type III owner entry and its independent common-selector
premise remain required. This theorem does not reselect an original
normal, change an original mean, identify a physical zero coefficient
with a missing circle corner, or repair the global compatible-selector
domain. The genuine and shared D-owner subdomains with p>1/2 remain
open here. Type I, Type II and the other physical roof features receive
no new credit from this theorem. No entire D02 parent or global n=9
closure is claimed.

## 7. Direct source interface and verification boundary

| Source | SHA256 | Exact use |
| --- | --- | --- |
| UNIQUE_CIRCLE_TWO_STRICT_ROOF_PORTS_PERPENDICULAR_INTERFACE_EXCLUSION_AND_COMPLETE_SAME_AXIS_DOMAIN_2026_10_29.md | f8cce87f5bbc22ba898db4029676dd84f1fb1c448212a809ee6809cffc5056eb | Full original Type III chart, V2 equations, genuine and shared D-owner force/moment equations, entire mean intervals and literal callers; all operative equations reproduced above |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Unchanged positive coefficients, full shared means, physical masks and strict singleton convention; no new selection assertion |

The actual point lemma (18) is proved here in the whole support-face
domain. The complete continuous comparisons (24)--(33) are explicit;
their isolated rational checks corroborate those proofs and do not
stand in for a pose search or interval cover. Every force used is an
original full-star force and every application used is its unchanged
point or mean. This source makes no metadata or closure-flag edit and
uses no Lean/Lake, CI, numerical pose search, packing certificate,
remote mutation or merge. Full independent review is requested before
adoption.

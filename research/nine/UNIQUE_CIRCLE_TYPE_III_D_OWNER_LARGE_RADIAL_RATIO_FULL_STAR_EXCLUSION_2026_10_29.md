# Type III D owners: full-star large-ratio exits for every genuine tilt and every shared mean

Date: October 29, 2026 UTC. Author: root_triangles.

**Status: complete proposed hand theorems on the entire stated continuous
domains, frozen for independent review.** The genuine sole-D owner is
excluded for every p>=1 and every genuine tilt. The shared-D owner is
excluded for every p>=7/5 and its full original shared-mean interval.
The first exit uses the complete A and D torque equations to bound the
unchanged C application; the second is independent of that original
mean. Neither theorem closes the remaining finite radial-ratio band
of its owner row or either whole D02 parent.

## 1. The unchanged original data and common scalar chart

Retain the physical Type III setting, force notation and actual h,e
frame of the full same-axis source in Section 6. Explicitly,

    79/40<=R<=sqrt(1105)/16<1039/500,
    A:{V,D,B}, D:{V,A,C}, V:{A,D},
    A,D unloaded true3, V loaded true2,
    V=[a-1,a] x [b-1,b], Z=(a,b), a,b>1/2, |Z|=R,
    P1=(a-1,b), P0=(a-1,b-1),
    h=nA=(c,-s), e=tA=(s,c), c,s>0, c^2+s^2=1,
    nD=K*h+H*e, tD=-H*h+K*e,
    H>0, H^2+K^2=1.                              (1)

The original roof magnitudes mu,nu and the original AD magnitude rho
are strictly positive. The actual AD direction from A into D is
g=-nD. There is no change of owner, normal, application or mean.
V has exactly one PHYSICAL circle corner, namely Z. Its two actual
roof ports at P1,P0 are strict at those V vertices and owned by their
respective hubs, with the full side-interior hub charts retained.

The full V force and moment are

    mu*h+nu*nD=kappa*Z, kappa>0,
    mu*det(P1,h)+nu*det(P0,nD)=0.                  (2)

They imply mu*c=kappa*(a-b)>0, nu*C=kappa*b>0 and
nu*(S-C)=mu*s, where nD=(C,S) in the original V frame. Therefore
the common scalar variables are

    k=-K/H>=0, J=sqrt(1+k^2), H=1/J, K=-k/J,
    u=c+k*s,
    p=Z_h/Z_e=(mu/nu)*J-k=(1+k)*c/s-1,
    x=p+1, v=1+k, T=sqrt(x^2+v^2),
    c=x/T, s=v/T,
    Y=R/sqrt(1+p^2), Z=(p*Y,Y),
    P1=(p*Y-c,Y-s),
    P0=(p*Y-c+s,Y-s-c).                           (3)

The final three lines give actual coordinates in the h,e frame.
For the genuine sole-D owner the complete geometry gives

    0<k<1/sqrt(3)<3/5, u<1,
    r=u, 0<t<1-s*J,
    A=P1-[0,1]*h+[-r,1-r]*e,
    D=P0-[0,1]*nD+[-t,1-t]*tD.                   (4)

For the physical shared-D owner, k=0 and the entire original mean
interval is

    r=c, 0<t<1-s,
    W=P1-z*h-c*e=P0+(s+z)*tD,
    0<=z<=1-t-s.                                 (5)

Both closed endpoints in (5) are retained. Its positive physical
overlap is not relabeled as a singleton.

## 2. The exact genuine C point and its full-star coefficient

In the genuine row the complete original exterior equations are

    F_B=rho*nD-mu*h,
    Q_B=P1-h+(1-u)*e,
    mu*(1-u)=rho*(H+K),
    F_C=-(nu+rho)*nD,
    Q_C=P0-nD+z_D*tD,
    z_D=rho*(s/H)/(nu+rho).                       (6)

The equation for z_D is the full D moment, not a selected side
coordinate. Define the exact positive force ratio and fraction

    q=rho/nu=(p+k)*(1-u)/(1-k)>0,
    tau=q/(1+q),
    z_D=tau*s*J.                                 (7)

Indeed mu/nu=(p+k)/J by (3), and H+K=(1-k)/J.
The original support mean z_D remains in (6)--(7) before any estimate
is applied.

Every unit square with minimum support at an original point or full
side mean Q in its inward unit-normal direction f contains Q+f. In
its actual own axes, a nonzero component starts at the appropriate
support endpoint and moves inward by at most one; a zero component
preserves the whole original side coordinate. This proves the fact
for all actual owners and means without changing the square.

Since the actual inward normal of C at Q_C is -nD, C contains

    X_C=Q_C-nD=P0-2*nD+z_D*tD.

Using nD=(-k,1)/J and tD=(-1,-k)/J in the h,e frame gives the
full actual point

    X_C=(p*Y-c+s+2*k/J-z_D/J,
         Y-s-c-2/J-k*z_D/J).                     (8)

No boundary, degree or circle-mask premise is needed at C for this
point membership. All its original data remain in place.

## 3. A uniform original-ratio bound for all p>=1

Fix any actual p>=1. Set

    T0=sqrt((p+1)^2+1), c0=(p+1)/T0, s0=1/T0,
    delta0=1-c0.                                 (9)

The scalar comparison 0<=ell<=k holds p fixed and uses the explicit
c(ell),s(ell) in (3). It does not assert an auxiliary physical packing.
Along this whole interval s increases and

    u'=s*(1-c/T)+ell*c^2/T>s0/2.                 (10)

To check (10), put x=p+1>=2. Then c/T=x/(x^2+(1+ell)^2)<1/x<=1/2,
and s>=s0. Consequently, because the actual k>0,

    u(k)>c0+(s0/2)*k,
    1-u(k)<delta0-(s0/2)*k.                      (11)

The actual positivity 1-u(k)>0 makes the right side positive
where it is used. It is also useful that u increases, so its actual
upper bound u(k)<1 is preserved on the entire comparison interval.

The exact identity

    delta0/s0=1/(T0+p+1)

shows

    (p+1)*delta0<s0/2<=p*s0/2.                   (12)

Here T0>p+1, so the first inequality is strict even at p=1.
Combining (7), (11) and (12) gives

    q < (p+k)*(delta0-(s0/2)*k)/(1-k)
      < p*delta0.                               (13)

For the second inequality, subtract p*delta0 and multiply by the
positive 1-k. The numerator is exactly

    k*((p+1)*delta0-(p+k)*s0/2)<0.

Finally,

    p*delta0=p/[T0*(T0+p+1)]
             <p/[2*(p+1)^2]<=1/8,
    0<tau=q/(1+q)<1/9.                           (14)

The last weak comparison follows from (p-1)^2>=0; the previous
comparison is strict. Thus (14) includes the closed radial cutoff
p=1 and every original genuine tilt. It is a consequence of the
full original equations and geometry, not a new force normalization.

## 4. Genuine sole-D: a fixed C projection excludes all p>=1

Take the fixed unit direction n=(3,-4)/5 and let P_C=n.X_C. From
(7)--(8), its exact projection is

    5*P_C=R*(3*p-4)/sqrt(1+p^2)
           +c+[7+(4*k-3)*tau]*s+(8+6*k)/J.        (15)

Because k<3/5, the coefficient 4*k-3 is negative. Thus (14) gives
the strict lower bound

    5*P_C > R*(3*p-4)/sqrt(1+p^2)+A(p,k),
    A(p,k)=c+(20/3+4*k/9)*s+(8+6*k)/J.            (16)

This step retains the actual mean before applying its uniform
consequence. It does not replace z_D by a freely chosen mean.

### 4.1. The entire tilt variable is removed by one derivative

For the explicit scalar function A, on p>=1 and 0<=k<=3/5,

    A_k=[-c*s+(20/3+4*k/9)*c^2]/T
          +(4/9)*s+(6-8*k)/J^3>0.               (17)

Every displayed term is positive. For the first numerator,
c/s=(p+1)/(1+k)>=2/(8/5)=5/4, so (20/3)*c>s.
The last numerator is at least 6-24/5=6/5>0. Hence

    A(p,k)>=A(p,0)
       =8+(p+1+20/3)/sqrt((p+1)^2+1).            (18)

This scalar comparison permits the k=0 endpoint without asserting
that the actual genuine original interface has become shared.

### 4.2. The entire radial-ratio variable is removed by one derivative

Put

    L_R(p)=8+(p+1+20/3)/sqrt((p+1)^2+1)
             +R*(3*p-4)/sqrt(1+p^2).             (19)

Its geometric summand has derivative

    [1-(20/3)*(p+1)]/((p+1)^2+1)^(3/2)
       >-20/[3*(p+1)^2].                        (20)

For p>=1,

    (1+p^2)^(3/2)<p*(p+1)^2,

because 1+p^2<=p*(p+1) and sqrt(1+p^2)<p+1. Therefore

    d[(3*p-4)/sqrt(1+p^2)]/dp
       =(3+4*p)/(1+p^2)^(3/2)>4/(p+1)^2.

Using R>=79/40 together with (20) gives

    L_R'(p)>(37/30)/(p+1)^2>0.                   (21)

It follows from (16)--(21) that

    5*(P_C-R)>L_R(1)-5*R
       =8+26/(3*sqrt(5))-R*(5+1/sqrt(2)).         (22)

The exact endpoint estimates

    26/(3*sqrt(5))>31/8,
    1/sqrt(2)<71/100

follow respectively from 208^2-5*93^2=19>0 and
2*71^2-100^2=82>0. Thus

    5*(P_C-R)>95/8-(1039/500)*(571/100)
              =481/50000>0.                     (23)

The actual point X_C in C has a unit-direction projection greater
than R, contradicting C contained in D_R. This proves the genuine
sole-D theorem for the entire original p>=1 domain, with every
original side application and every genuine tilt retained.

## 5. Shared-D: a mean-independent vertical exit for all p>=7/5

Now keep the complete physical shared chart (5). Its full original
forces and moment are

    F_B=rho*e-mu*h,
    Q_B=P1-h+(1-c)*e,
    rho*(1-z)=mu*(1-c),
    F_C=-(nu+rho)*e,
    Q_C=P0-e+z_D*tD,
    z_D=rho*(s+z)/(nu+rho), tD=-h.                (24)

The actual point X_C=Q_C-e therefore has coordinates

    X_C=(p*Y-c+s-z_D, Y-s-c-2).                  (25)

Its second coordinate is independent of the unchanged full mean,
including both original z endpoints. Define

    H_R(p)=(-e).X_C-R
           =2+(p+2)/sqrt((p+1)^2+1)
                 -R/sqrt(1+p^2)-R.             (26)

For all p>0,

    H_R'(p)=-p/((p+1)^2+1)^(3/2)
               +R*p/(1+p^2)^(3/2)>0,           (27)

since R>1 and (p+1)^2+1>1+p^2. At p=7/5 the actual scalar
values are c=12/13,s=5/13, so

    H_R(7/5)=43/13-R*(1+5/sqrt(74)).              (28)

The strict comparison 5/sqrt(74)<7/12 follows from
49*74-25*144=26>0. Hence

    H_R(p)>=H_R(7/5)
       >43/13-(1039/500)*(19/12)
       =1367/78000>0                            (29)

for every p>=7/5. The actual X_C has (-e)-projection greater than
R, a contradiction. This proves the shared-D theorem for its
whole stated radial-ratio interval, retaining all original overlap
means and actual endpoints.

## 6. Exact joins, preserved original cases and limits

The two conclusions proved here are

    genuine sole-D owner: every original p>=1 is excluded;
    physical shared-D owner: every original p>=7/5 is excluded.

In both D02.L135 and D02.L1345 the literal graph is retained:

    rim A--V--D--C--N_original--B--A, chord AD,
    A=0,V=1,D=2,C=3,N_original=4,B=5.

A3,D3,V2 are the exact full stars used above. B,C retain their
loaded true2 roles. N_original retains its unloaded true2 role in
L135 and loaded true2 role in L1345. All their original forces,
physical circle masks, full side means and all three completing
actual units remain. No equation or boundary condition at B,C or
N_original is weakened to manufacture this contradiction.

The compatible original-owner entry, including its global common-
selector premise, is a separate input. These theorems do not prove
that premise or reselect an original normal. A physical two-corner
mask with a zero coefficient is not treated as a unique circle tip.
No Type I or Type II conclusion is imported.

The separate small-ratio theorem cited below proves p<=1/2 for
both D owners. When that independently reviewed theorem is joined
with the present results, the exact remaining necessary intervals are

    genuine sole-D: 1/2<p<1;
    physical shared-D: 1/2<p<7/5.                 (30)

No exit for the intervals (30) is claimed here. In particular neither
entire D-owner row, neither original D02 parent nor the global n=9
statement is declared closed.

| Direct source | SHA256 | Exact use |
| --- | --- | --- |
| UNIQUE_CIRCLE_TWO_STRICT_ROOF_PORTS_PERPENDICULAR_INTERFACE_EXCLUSION_AND_COMPLETE_SAME_AXIS_DOMAIN_2026_10_29.md | f8cce87f5bbc22ba898db4029676dd84f1fb1c448212a809ee6809cffc5056eb | Complete original Type III chart, full V2 and A3/D3 forces and moments, entire original mean domains, genuine angular bounds and exact literal callers; operative equations reproduced above |
| UNIQUE_CIRCLE_TYPE_III_BOTH_D_OWNERS_FULL_MEAN_SMALL_RADIAL_RATIO_EXCLUSION_2026_10_29.md | a4dbb88633fff667457ecab23ac1320c588bdb2fe0ddda46b2d8217ea13812c7 | Only the optional exact remaining-domain join (30); the two high-ratio proofs do not depend on its numerical estimates |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Unchanged positive coefficients, full shared means, physical masks and strict singleton convention |

All comparisons above prove full continuous intervals. Their rational
endpoint checks corroborate those analytic arguments; no pose sample
or finite angle mesh supplies an exit. No Lean/Lake, CI, packing
certificate, original-force deletion, normal change, mean change,
metadata or flag edit, remote mutation or merge is used. Full
independent review is requested before adoption.

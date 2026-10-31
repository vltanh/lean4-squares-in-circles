# The owned-leaf inner return excludes every perpendicular T frame with S0>=C

Date: October 29, 2026 UTC. Authors: house continuation and root
continuation. This uses the common radial torque/monotonicity method
developed for the upper-leaf return, with new whole owned-leaf bounds.

**Status: complete proposed hand proof, frozen for full independent
noncontributor review and root adoption.** In the entire owned genuine-S
leaf / owned-AD / strict-inner-AT / nonparallel-C original TC.S residual,
this excludes every actual perpendicular T-owned frame with S0>=C,
including the exact diagonal endpoint. Every original side mean, full
star and physical mask is retained through the complete prior entry.

The actual interval 0<S0<C remains a separate original obligation.
This source does not declare the whole TC.S family or a coarse cell closed.

## 1. Entire original owned-leaf entry

Keep all nine actual units, the same circle about O and the full original
component AT,DT,AD,AB,BC,CD,AL with true degrees A4,D3,B2,C2,T2,L1 and
positive total circle loads exactly T,C,L. Keep every original force,
torque, selected normal, physical singleton or complete side mean,
physical circle corner and individual zero coefficient. The real S leaf
remains occupied. B,D are truly unloaded.

The complete prior original owner reduction at d79bb4a7 gives

    d=1+epsilon, 0<epsilon<1/60,
    R^2=(2+epsilon)^2+1/4<=1105/256,
    u_world=(-a,t), v_world=(-t,-a),
    a,t>0, a^2+t^2=1,
    A=[h,h+1] times [-q,V], h=epsilon, V=1-q,
    epsilon<q<3/8, q*t=epsilon*(1+a),
    q*t<1/30, V>5/8,
    S_D=P_AD=(h,w), ell=w+q in (0,1),
    L0=V-w=1-ell in (0,1),
    AD=-rho*u, rho>0,
    P=P_AT=(h,V), AT=(-alpha,beta), alpha,beta>0.

The actual A4 has the genuine owned leaf force kappa*u, kappa>0, and
the original B-channel force mu*(-a,-t), mu>0. Its full equations retain

    beta=mu*t,
    rho*w+alpha*V=mu*a*q.

The entire nonparallel physical owner reduction has already established

    j=(-c,s), k=(-s,-c), c,s>0, c^2+s^2=1,
    D=S_D+[0,1]j+[0,1]k,
    Q=P_DC=S_D+k+sigma*j, 0<sigma<1,
    Q_world=(d,-1/2), DC=nu*k, nu>0,
    F=P_DT=S_D+j,
    U=(-C,S0), W=(S0,C), C,S0>0, C^2+S0^2=1,
    AT=lambda*U, DT=gamma*W, lambda,gamma>0,
    alpha=lambda*C, beta=lambda*S0,
    T=H+[0,1]U+[0,1]W,
    P=H+delta*W, F=H+eta*U,
    0<eta<1, 0<delta<1,
    c=eta*C+delta*S0,
    L0-s=-eta*S0+delta*C.                              (1)

The original full D3 gives

    gamma/nu=c/C,
    rho/gamma=s*C/c-S0>0,
    sigma=c^2+c*s*(S0/C),
    c>t,
    c<C.                                               (2)

The prior physical proof excluded every physical-two T before applying
the fixed-tip selector: its actual P has |P|<d. Thus T has exactly one
physical circle corner, both actual contacts in (1) are singleton and
genuinely T-owned, and the full original T2 concurrence is

    Z=H+U+W=P+U+(1-delta)*W,
    |Z|=R,
    K=P+eta*U=F+delta*W=sigma_T*Z,
    0<sigma_T<1.                                      (3)

The feature now excluded is the entire closed orientation range S0>=C.
It is a sign condition on the actual frame, not a chosen representative
pose. From (2) this implies c<C<=S0<s and c<1/sqrt(2).

## 2. A stronger uniform bound for the actual D frame

Put v0=S0/C>=1. The actual Q_u coordinate and the genuine owned-leaf
identity give

    M=s+c^3+c^2*s*v0=a+t*(q+1/2)
       <a+t/2+1/30
       <=sqrt(5)/2+1/30<173/150.                     (4)

Here sqrt(5)/2<28/25, whose squared reserve is 11/2500.
Also M>=f(c)=sqrt(1-c^2)*(1+c^2)+c^3. For c<s,

    f'(c)=c*[1+3*c*(s-c)]/s>0.

If c>=7/16, then s at the comparison endpoint is sqrt(207)/16>899/1000.
Consequently

    f(c)>=f(7/16)
       >(899/1000)*(305/256)+343/4096>173/150,

contradicting (4). Thus the entire feature has

    0<c<7/16,
    s>899/1000,
    a>s>7/8.                                          (5)

This strengthens the former upper-leaf comparison enough to cover the
larger complete owned interval V>5/8.

## 3. The full radial equation and its continuous upper bound

Set E=L0-s and use the actual means in (1):

    eta=c*C-E*S0,
    delta=c*S0+E*C,
    z=1-delta in (0,1),
    D0=C*(1-eta)-S0*z,
    J0=C*z+S0*(1-eta)>0,
    F1=D0-eta*z.

The exact radial concurrence (3), in the original U,W coordinates,
is equivalent to

    V*D0+h*J0=eta*z,
    F1+(h/V)*J0=(q/V)*eta*z>0.                       (6)

In particular J0<C+S0<=sqrt(2). Both original means remain open,
arbitrary and unchanged.

We reproduce the complete continuous comparison needed below, including
the diagonal endpoint S0=C. For fixed c,s,C,S0, compare the displayed
scalar function F1(E) from its actual E<1-s to 1-s. Both eta and z
stay positive throughout: at the upper endpoint,

    eta_1=c*[C-c*S0/(1+s)]>c*(C-c)>0,
    z_1=1-c*S0-(1-s)*C>s-c>0.

The exact derivative is 2*C*S0+S0*z+eta*C>0. Thus its actual value
is strictly less than the value at E=1-s.

Write c=cos(theta), s=sin(theta), C=cos(phi), S0=sin(phi).
Now pi/4<=phi<theta<pi/2. Expansion at E=1-s gives

    F1_endpoint=C*(1-c)-s*S0+c*sin(2*phi-theta).

Its derivative in phi is

    -(1-c)*sin(phi)-s*cos(phi)+2*c*cos(2*phi-theta).

On the complete interval pi/4<=phi<=theta, the first two terms are
at most -s, by the half-angle comparison
(1-c)/s>=tan(phi/2). The last cosine is at most s, because
pi/2-theta<=2*phi-theta<=theta inside [0,pi/2]. By (5), c<1/2,
so the full derivative is at most s*(2*c-1)<0. Therefore

    F1<g(c):=(1-c-s)/sqrt(2)+c^2.                     (7)

When phi=pi/4 the last comparison is equality, but the preceding strict
E comparison remains. Thus (7) covers S0=C too. These comparisons are
scalar inequalities; no actual unit or side mean has been moved.

## 4. Both whole c intervals contradict the original radial equation

For 0<c<=1/10, the same elementary identity 1-s=c^2/(1+s), together
with s>99/100 and 1/sqrt(2)>2/3, gives

    -g(c)/c>[1-10/199]*(2/3)-1/10>1/2.

The final reserve is 33/995, so g(c)<-c/2. In the actual owned chart,

    h=q*t/(1+a)<q*c/(1+a),
    q<3/8, 1+a>15/8,
    J0<3/2, V>5/8.

Consequently

    (h/V)*J0
       <c*(3/8)*(8/15)*(3/2)*(8/5)
       =(12/25)*c<c/2.

Thus the left side of (6) is negative on this whole interval.

For 1/10<=c<7/16, the function g is strictly convex since

    g''(c)=2+1/[sqrt(2)*(1-c^2)^(3/2)]>0.

At the lower endpoint g(1/10)<-1/20. At the upper endpoint,
s>899/1000 and 1/sqrt(2)>12/17 give

    g(7/16)
       <49/256-(673/2000)*(12/17)<-1/25.

Hence g(c)<-1/25 on the whole closed comparison interval. The
original bounds h<1/60, J0<sqrt(2)<17/12 and V>5/8 instead give

    (h/V)*J0<17/450<1/25.

The last reserve is 1/450. Again F1+(h/V)*J0<0, contrary to the
strict positive necessity (6). The two continuous intervals cover
all possible c in (5), with their common endpoint included.

This proves the entire stated owned-leaf S0>=C exclusion, including
every original eta,delta and the exact diagonal T frame.

## 5. Exact credit and input boundary

The new theorem excludes one whole actual orientation range of the last
owned-leaf perpendicular system. The previously completed upper-leaf
theorem excludes its entire corresponding leaf chart. The remaining
owned system must now have

    0<S0<C,
    alpha>beta,
    all the original equations (1)--(3).

The full original C2 moment and A4 force equations remain available
there. They are not replaced by the scalar inequalities above, and no
whole original flag changes until that final physical domain is closed.

The exact operative source is

    HOUSE_TC_BOTH_LEAF_INNER_NONPARALLEL_UNIQUE_T_PERPENDICULAR_OWNER_REDUCTION_2026_10_29.md
    d79bb4a7a43016e50e23c9878bbcfef27a48487373ee06136a9143d1c4544ce0.

Its complete source was read; its separate full independent PASS is
b96c8f566fac489077a467395cd78b8bc9fe8d2cefd3744a40c831d21b7d45a7.
The entire radial comparison is reproduced here rather than importing
an upper-leaf bound on V or a strict S0>C hypothesis into this chart.
The rational threshold and endpoint reserves were checked exactly.

Both authors contributed to the common mathematical strategy. This
new owned-leaf extension requires a full independent noncontributor
review and root adoption. No physical unit, force, selected normal,
mean, physical circle mask, coefficient, original source header,
identifier, ledger, denominator or flag was altered. No numerical pose
sample, new packing certificate, Lean compilation, CI or remote action
was used.

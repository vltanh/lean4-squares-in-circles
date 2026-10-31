# A quantitative vertical-support bridge theorem excludes the whole Type II D-direction side return

Date: October 29, 2026 UTC. Author: roofs continuation.

**Status: complete proposed general hand theorem and whole original
Type II D-direction side-return exclusion, frozen for independent
review.** A single quantitative support inequality excludes an actual
unloaded true2 return bridge at arbitrary endpoint degrees, loads,
frames and means. It strengthens the earlier vertical-separation
theorem without changing its original endpoint-ownership convention.

The entire Type II D-owned roof-direction row with its exact A-side
return mean satisfies this inequality. The proof retains every original
V/A/D force and moment and both original side applications. It closes
that entire return row in D02.L135, including all original angles and
positive force ratios. The loaded N of D02.L1345 remains outside this
unloaded conclusion.

## 1. A complete quantitative actual-support theorem

Let B,C,N be distinct actual unit squares with disjoint open interiors.
Fix an oriented orthonormal frame (h,e). Suppose B has an actual
minimum-support point or full support-side mean Q_B in inward unit
direction

    f=-a*h+b*e, a,b>0, a^2+b^2=1,

and C has an actual minimum-support point or full mean Q_C in
inward direction -e. Put

    X=(Q_B-Q_C).h<=0,
    D=(Q_B-Q_C).e>0.

Require the single strict scalar inequality

    D*(D-a)>2.                                  (1)

Retain the entire actual unloaded true2 star at N, its two positive
pair magnitudes, original actual applications T in B and U in C,
and full force and torque equations. Retain the same initial finite
incident-diagonal avoidance as in PHYSICAL_BODY_GRAPH_UNCROSSING.md:
at point-only vertex/vertex contacts the selected strict common normal
is not a diagonal of either incident unit. This is an explicit input
from the prior common selection, not a later change of normal.

**Quantitative bridge theorem.** These hypotheses are impossible.

No boundary status, load or degree equation at B,C is used. Their
actual support points may be strict vertices, any side point, full
shared means or either original side endpoint. The theorem keeps
the same entire actual B,C,N units.

## 2. The full N system is forced into its diagonal alternative

First (1) implies

    D-a>1.                                      (2)

If D<=2, (1) gives D-a>2/D>=1. If D>2, the strict
a<1 gives D-a>D-1>1. These two cases exhaust the positive D
domain and include D=2.

The complete whole-unit support estimate is

    min_B e>=Q_B.e-a,
    max_C e=Q_C.e.

For completeness, at a strict minimizing B vertex the two actual
inward own edges have positive f components. Since f.e=b>0,
at most one has a negative e component. If that unit edge has
e component -r<0, the inequality f.edge>=0 gives
its h component at most -(b/a)r. Unit length then gives r<=a.
At an actual minimizing side, f is the inward own normal; motion
along f cannot decrease e, and the full tangent displacement from
any original point or mean has length at most one and e component
of magnitude a. Thus the same estimate holds on every closed mean
interval and at every zero own-component tie.

The actual two applications consequently satisfy

    (T-U).e>=D-a>1.                             (3)

Full unloaded force at N gives equal positive magnitudes and opposite
normals d,-d. Its entire torque gives det(T-U,d)=0. The actual
opposite support conditions then give precisely the two original
transmission possibilities

    side: T-U=d;
    diagonal: T-U=sqrt(2)*d,
    |d|=1.                                     (4)

Indeed a side axis has support width one; otherwise the supports
are opposite actual vertices, whose normal-parallel difference has
length sqrt(2) and is an own diagonal. No other full two-force
orientation exists.

Equation (3) excludes the side alternative. Thus write

    d=u*h+v*e,
    u^2+v^2=1,
    v>1/sqrt(2),
    v>=(D-a)/sqrt(2).                           (5)

Both applications are actual vertices of N. The retained initial
diagonal avoidance makes them relative-side-interior in B,C: a
vertex in the other endpoint would be a point-only vertex/vertex
contact with an incident N diagonal normal. A positive shared length
is also impossible because that normal is not an N side axis.
Therefore both actual endpoint units own d and have parallel frames.

## 3. Every channel sign, original side tie and mean endpoint

If u<=0, then f.d=-a*u+b*v>0. Hence Q_B is on the same
actual minimum-d side as T. Because e.d=v>0, Q_C is on
the same actual maximum-d side as U. These facts include every
zero component along the other own axis and every full side mean.
Thus

    (Q_B-Q_C).d=sqrt(2).

But the exact coordinate bounds, including u=0, give

    (Q_B-Q_C).d=X*u+D*v
      >=D*v
      >=D*(D-a)/sqrt(2)>sqrt(2),                (6)

contradiction.

If u>0, set w=-v*h+u*e. In the actual common own frame (d,w),
Q_C is the maximum-d/maximum-w vertex of C. Since U is on its
maximum-d side, retain its full actual coordinate as

    U=Q_C-alpha*w, 0<=alpha<=1.

Write the unchanged B as

    B=T+[0,1]*d+[-beta,1-beta]*w,
    0<=beta<=1.

Here f.w=a*v+b*u>0, so its actual Q_B has the minimum w
coordinate, while its d coordinate can be any original support
value xi in [0,1], including the complete f.d=0 tie:

    Q_B=T+xi*d-beta*w.

Subtracting and using (4),

    Q_B-Q_C=(sqrt(2)+xi)*d-(alpha+beta)*w.

Its h coordinate is (sqrt(2)+xi)u+(alpha+beta)v>0,
contradicting X<=0. The strict first term covers every enlarged
zero endpoint of alpha,beta,xi. Together the two sign cases prove
the quantitative theorem over its entire original domain.

In particular D>=2 automatically satisfies (1), because a<1.
Thus the earlier vertical-separation theorem is an exact special
case, with the same original means and diagonal convention.

## 4. Full original Type II D-direction side-return entry

Keep all nine actual squares, their disk and origin, every original
positive force and selected normal, actual application or full mean,
physical circle mask and individual zero coefficient. A,D are the
original unloaded true3 hubs, and V is the loaded true2 unique-circle
roof. Its complete original local stars remain

    A:{V,D,B}, D:{V,A,C}, V:{A,D}.

Use the exact conditional Type II entry and the full owner/return
source at e63a1e1d. Its D-owned roof-direction row has

    V=[a0-1,a0] x [b0-1,b0], Z=(a0,b0),
    P=(a0-1,b0-1), R=P+omega*North,
    0<omega<1,
    nD=(C,S), tD=(-S,C), 0<C<S,
    h=(c0,-s), e=(s,c0), c0,s>0,
    H=c0*S+s*C>0,
    K=c0*C-s*S<0,
    nD=K*h+H*e, tD=-H*h+K*e,
    A=R-[0,1]*h-[0,1]*e,
    D=P-[0,1]*nD+[-t,1-t]*tD, 0<t<1.           (7)

All c0,s and C,S are actual sine/cosine coordinates in their
strict roof-vertex frames. Put k=-K, so 0<H,k<1 and

    H^2+k^2=1.

The unchanged AD normal is -nD. Its actual application and whole
geometric domain are

    W=R-e=P+v*tD,
    omega=H/S<1,
    v=s/S in (0,1-t).                           (8)

In particular H<S and 0<v<1. The true original V equations are

    mu*East+nu*nD=kappa*Z,
    mu*det(R,East)+nu*det(P,nD)=0,
    (mu/nu)*(1-omega)=S-C>0.                    (9)

All mu,nu,rho,kappa are positive.

The A-return side alternative is precisely the zero e component
in its full original exterior vector. Its full force and moment give

    rho*H=mu*s,
    F_B=-(mu*S/H)*h,
    Q_B=R-h-z*e,
    z=-K*s/S=k*v in (0,1).                     (10)

This z is the exact original full A-side mean, fixed by the complete
A3 moment. It is not an endpoint selected for this proof. The two
strict A-return alternatives are separate original rows; this theorem
does not silently identify them with the side row.

The full D3 force and moment retain their complete original mean

    F_C=-(nu+rho)*nD,
    Q_C=P-nD+delta*tD,
    delta=rho*v/(nu+rho), 0<delta<v.             (11)

The strict inequality uses nu>0 and v>0. Every original DC side
mean compatible with the full equations remains represented by (11).
No full exterior degree, force or physical circle coefficient is
changed by these identities.

## 5. Actual full-mean support data satisfy the quantitative theorem

Rotate the whole data into d0=-tD,n=nD. The actual own coordinates
are h=(H,-k), e=(k,H), and

    R-P=(-omega*C,H),
    Q_C-P=(-delta,-1).

Subtract the original Q_B,Q_C from (10),(11):

    Delta=Q_B-Q_C=(-E,D0),
    E=omega*C+H+k*z-delta,
    D0=1+k+H*(1-z).                            (12)

The inward unit direction into B is exactly -h=(-H,k), and
the inward direction into C is -n. Thus the generic horizontal
and vertical components are a=H,b=k, with both strict.

Let ell=C/S>0. The original identities in (8) give

    v=k+H*ell<1,
    z=k*v<k,
    omega*C=H*ell.                              (13)

Since delta<v, the entire unchanged horizontal difference has

    E>H*(1+ell)+k^2*v-v
      =H*(1+ell-H*v)>0.                        (14)

The final bracket exceeds 1-H because ell>0 and v<1. All
original means are retained; the proof never discards v from delta.

The vertical gap satisfies throughout the entire row

    D0-H=1+k-H*z
          >1+k-H*k
           =1+k*(1-H)>1.                       (15)

It remains only to prove the single continuous product

    D0*(D0-H)>2.                                (16)

All force ratios in (9)--(11) remain original. The proof of (16)
uses only their exact resulting support geometry and strict signs.

## 6. The whole interval 0<k<=2/5 has D0>2

The geometric inequality H<S in (8) implies

    H^2*(1+ell^2)<1,
    ell<k/H.

Combining this with (13) gives v=k+H*ell<2k and z<2k^2.
Consequently

    D0>1+k+H*(1-2k^2).                          (17)

For 0<k<=2/5, both 1-2k^2 and 1-k are positive. Their
exact squared comparison is

    (1-k^2)*(1-2k^2)^2-(1-k)^2
      =2k*[1-3k+4k^3-2k^5].                    (18)

The bracket Q(k)=1-3k+4k^3-2k^5 decreases on the entire
closed interval [0,2/5], since

    Q'(k)=-3+12k^2-10k^4<=-27/25<0.

At its upper endpoint Q(2/5)=111/3125>0. Thus (18) is
strictly positive for every actual k>0, and positive squaring
gives H*(1-2k^2)>1-k. Equation (17) yields D0>2.
Because H<1, this implies D0*(D0-H)>2 as required.
The auxiliary k=0 value is an equality only in (18); no actual
positive k or closed joining endpoint is omitted.

## 7. The whole interval 2/5<=k<1 satisfies the product directly

From z<k in (13), both positive factors have

    D0>1+k+H*(1-k),
    D0-H>1+k-H*k.

Thus their product is strictly greater than

    G(k)=[1+k+H*(1-k)]*[1+k-H*k].

Using H^2=1-k^2, the exact expansion is

    G(k)-2=-1+k+2k^2+k^3-k^4
             +H*(1-k-2k^2).                    (19)

### 7.1. Every 2/5<=k<=1/2

Here 1-k-2k^2>=0 and H>=sqrt(3)/2>173/200. The strict
radical comparison has squared reserve 71/40000. The complete
closed interval, including its zero coefficient at k=1/2, gives

    G(k)-2>=P(k),
    P(k)=-27/200+(27/200)k+(27/100)k^2+k^3-k^4.

Its derivative is positive throughout this interval:

    P'(k)=27/200+(27/50)k+k^2*(3-4k)>0.

Therefore

    P(k)>=P(2/5)=3/5000>0.                      (20)

The weak substitution at the coefficient-zero endpoint is sufficient;
the final reserve stays strictly positive there.

### 7.2. Every 1/2<=k<=1 in the closed comparison

Now 1-k-2k^2<=0 and H<=sqrt(3)/2<7/8. Multiplication by
the nonpositive coefficient has the correct reversed comparison,
giving

    G(k)-2
      >=(2k-1)*(k+1)/8+k^3*(1-k)>0.             (21)

Both terms are nonnegative. At k=1/2 the second is 1/16;
for k>1/2 the first is positive, including k=1, where it is
1/4. The exact squared radical reserve is 1/64. Thus the
entire interval, all signs and both scalar endpoints are covered.

Equations (19)--(21) prove G(k)>2 for every k>=2/5.
Together with Section 6 and the strict actual factor bounds, this
proves (16) over every original k in (0,1).

## 8. Whole original D02.L135 side-return row is excluded

Equations (12)--(16) supply the general theorem literally:

    f_B=-H*d0+k*n, H,k>0,
    f_C=-n,
    Delta.d0=-E<0,
    Delta.n=D0>0,
    D0*(D0-H)>2.

Retain the original labels

    A=0,V=1,D=2,C=3,N=4,B=5,
    rim A--V--D--C--N--B--A, chord AD.

A,D remain unloaded true3, V,B,C loaded true2, and N is exactly
the original unloaded true2 of D02.L135. Its two positive contacts
and its entire moment are precisely those used in Sections 1--3.
The same initial finite diagonal avoidance is retained. The theorem
therefore excludes the actual N across this ENTIRE original
D-owned roof-direction, exact A-side-mean return row.

All actual angles, original positive magnitudes, full z and delta,
exterior owners and physical circle masks are included. All six
core units and all three original completing units remain. No
boundary premise at B,C or completion allocation was required.

The full original upper-A-vertex return in this D-direction owner
was already excluded in L135 by Section 7 of e63a1e1d. The present
source adds the whole original side return; it does not declare the
remaining far-A-vertex return excluded. The separate A-owned h
row also retains its own missing exit.

For D02.L1345, N has positive total circle force and cannot be
assigned the unloaded equation. This source makes no new closure
of that loaded alternative. It also does not close either whole
D02 family, the unrestricted sharp nine-square theorem, equality
classification or the prior global common-selection obligation.

## 9. Complete inputs and verification boundary

| Complete operative source | SHA256 | Exact use |
| --- | --- | --- |
| UNIQUE_CIRCLE_TYPE_II_SINGLETON_WEST_COMPLETE_HUB_OWNER_AND_EXTERNAL_RETURN_DOMAIN_2026_10_29.md | e63a1e1d14c50363a244dae4d8927b2113a4222ca1064777660a366b092f351c | Exact Type II D-direction owner row, complete original V/A/D forces and both full means |
| VERTICALLY_SEPARATED_RETURN_SUPPORTS_NO_UNLOADED_TRUE_TWO_BRIDGE_AND_SHARED_D_L135_EXCLUSION_2026_10_29.md | 112510ba9d1ec141443b19bbcf4212879a628e2eab083335c3252640f32f36bd | Earlier support-span and full channel-sign argument, completely reconstructed and quantitatively strengthened here |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Full original true2 force/torque and exact side-or-diagonal alternatives |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe | Same initial finite diagonal avoidance and preserved actual endpoint owners |
| UNIQUE_CIRCLE_TRIANGLE_TIP_THREE_PORT_TYPES_AND_HUB_INTERFACE_OWNER_COVER_2026_10_29.md | 8266220efbb8ce769de90a90e27e86997400575d0b8bb80f5843af38ca447073 | Original conditional Type II port entry, unchanged D-side owner |
| D02_BOTH_UNLOADED_HUBS_UNIQUE_CIRCLE_ROOF_COMPLETE_NORMAL_OWNER_ASSEMBLY_2026_10_29.md | 97148714d460095f7e9c80332f01abdc45b5c9ad36950309973fe21b006972e7 | Exact prior compatible common-selection domain and original roof data |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 | Literal original graph, both true N loads and all three extra units |

All complete operative inputs were read. The entire new generic
theorem, full original application, exact mean dependence, continuous
scalar covers and joining endpoints are printed above. Only exact
algebra and rational arithmetic are needed. Independent full current-
source and original-cover review is required before adoption.

No numerical pose search, angle mesh, packing certificate, changed
normal, replaced mean, shortened star, altered physical mask, removed
unit, metadata mutation, remote write, build, CI or merge was used.

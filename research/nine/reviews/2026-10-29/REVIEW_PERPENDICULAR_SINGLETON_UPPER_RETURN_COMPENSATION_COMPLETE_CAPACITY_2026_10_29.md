# Complete independent review of upper-return angle compensation

Date: October 29, 2026 UTC. Reviewer: capacity continuation.

**Verdict: ACCEPT at the exact revised frozen source below.** I read the
entire current manuscript, independently reconstructed the angle
comparison and strict height compensation, checked the full concavity
argument and its new endpoint b=16/25, and verified the original-family
joins and retained remainder. No defect was found.

This review applies to the complete current 16/25 theorem. It does not
adopt an earlier cutoff or a superseded source version. The new endpoint
arithmetic was independently checked after the revised source was frozen.
No alteration to the author's source was supplied by this review.

## 1. Frozen manuscript and complete input chain

Reviewed source:

    PERPENDICULAR_SINGLETON_UPPER_RETURN_ANGLE_COMPENSATION_AND_LARGE_SIDE_COMPONENT_EXCLUSION_2026_10_29.md

Frozen SHA256:

    0afb19ae0fbde08c104b6e5bf554ab27885c31dc1c16275de625341f956ce167

The complete original chart and earlier full c<=3/4 exclusion are in

    PHYSICAL_TWO_WEST_STRICT_PERPENDICULAR_SINGLETON_ADJACENT_RETURN_EXCLUSION_AND_COMPLETE_RESIDUAL_2026_10_29.md

at SHA256

    f3718c86a99ef196eba1ee875b66375582a0fc588f10275ec171c442e46780dd.

I previously completed its full independent review and have again read
that complete source, including all continuous intervals of its
Theorem B. Its actual force and mean conventions remain unchanged.

The separate projection-bridge theorem used only to print the combined
residual is

    ACTUAL_UNIT_PROJECTION_BRIDGE_AND_PERPENDICULAR_SINGLETON_RETURN_INTERVALS_2026_10_29.md

at SHA256

    97815bf7d2558343a76316a8095096bb780a8e4fe1664274c1863bcbbb8d6132.

That source has also received my separate complete independent review.
The new compensation exclusion itself does not use its bridge premise.

The physical and literal graph inputs, read completely in the original
chart review, are:

| Complete input | SHA256 |
| --- | --- |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 |

All three directly operative mathematical manuscript hashes above were
independently recomputed for this review. No input was edited.

## 2. Original physical scope and unchanged A3 equation

All nine original units remain in the containing disk. The original
physical-two West/strict roof has full stars

    A:{V,D,B}, D:{V,A,C}, V:{A,D},

with A,D unloaded true3 and V loaded true2 with two physical circle
corners. The inherited chart keeps

    79/40<=R<=sqrt(1105)/16,
    P=(d,1/2), Q=(d,-t), 0<t<=1/2,
    H=t+1/2, 1/2<H<=1,
    h=(c,-s), e=(s,c), c,s>0, c^2+s^2=1.

The original A-owned roof normal is h. The genuine A-only perpendicular
singleton AD has unchanged A-to-D normal -e and actual application

    W=P-xh-le, 0<x,l<1,
    A=P+[-1,0]h+[-l,1-l]e.

The actual adjacent D side satisfies

    v=W-Q=-a h+b e,
    a=H s+x>0, b=H c-l>0,
    a^2+b^2=1, 0<b<c, 0<s<a.

The quantities a,b describe that actual side in A's frame. They are
not independent poses or circle-corner coordinates.

The complete A force equation is

    F_B=-mu h+gamma e, mu,gamma>0.

Its actual A support is the strict vertex

    K=P-h+(1-l)e.

The complete A moment about P is
gamma*x-gamma+mu*(1-l)=0, so the actual ratio is exactly

    r=gamma/mu=(1-l)/(1-x)
      =(1-H c+b)/(1-a+H s)>0.

Neither force magnitude nor application has been replaced. The proof
after this chart uses this entire A3 equation, not a reduced equation
at a higher-degree vertex. D3,V2 and all exterior equations remain in
the original configuration without being used or shortened.

## 3. The actual exterior point and its exact coordinates

The unit direction into the original B is

    f=(-h+r e)/sqrt(1+r^2).

The physical support separation makes K a minimum-f support point of
the actual B. The point K+f belongs to B for every actual owner and
support-face mean.

To check this fully, in either actual own-coordinate interval of B,
a nonzero component of f has the inward sign from the relevant
minimum-support endpoint and absolute value at most one. Adding that
component stays in the same unit interval. A zero component leaves
the original coordinate unchanged, including every side mean and
both endpoints. Applying this argument to both own coordinates
proves actual membership of K+f.

Its world vertical coordinates are exactly

    K_y=1/2+s+c*(1-H c+b),
    f_y=(s+r c)/sqrt(1+r^2).

This is a necessary containment test on the original full B. It does
not reconstruct an exterior unit from a point or assume an exterior
force equation or corner mask.

## 4. The entire angle comparison, including its strictness

Assume b>=1/2 and c>s. Write

    c=cos(phi), s=sin(phi), 0<phi<pi/4,
    D0=1-a>0, N0=1-H+b>=b>0,
    r0=N0/D0, psi0=atan(r0).

Since a,b>0 and a^2+b^2=1, one has a+b>1. Thus

    r0>=b/(1-a)>1, pi/4<psi0<pi/2.

The actual ratio can be written

    r=[N0+H*(1-c)]/[D0+H*s].

Because N0/D0>(1-c)/s, the original r is strictly below r0.
Consequently

    delta=atan(r0)-atan(r)

belongs to (0,pi/2). I recomputed its exact tangent from the displayed
two ratios:

    tan(delta)
      =H*[N0*s-D0*(1-c)]
       /[D0^2+N0^2+H*D0*s+H*N0*(1-c)].

All denominators are positive. The numerator is positive by the
strict r comparison. Dropping its negative term and the nonnegative
extra denominator terms gives

    tan(delta)
      <H*N0*s/(D0^2+N0^2)
      <=(H/N0)*s
      <=s/b
      <=2s.

The first inequality is strict throughout the physical domain.
It does not become equality at H=1 or b=1/2.

Meanwhile 0<2phi<pi/2, and

    tan(2phi)=2s*c/(c^2-s^2)>=2s.

The comparison is valid because the denominator is positive and

    c-(c^2-s^2)=(1-c)(2c+1)>=0.

Both angles are on the same increasing tangent branch, so

    0<delta<2phi.

The actual world direction angle is
psi=phi+atan(r)=psi0+phi-delta. Hence it lies strictly between
psi0-phi and psi0+phi. The whole comparison interval is contained
in (0,pi): its lower endpoint is positive because psi0>pi/4>phi,
and its upper endpoint is below 3pi/4.

Sine is concave on this interval, so its minimum occurs at an
endpoint. Their difference is
sin(psi0+phi)-sin(psi0-phi)=2*cos(psi0)*s>0.
Thus the lower endpoint has the smaller sine, and

    f_y>=sin(psi0-phi)
        =c*sin(psi0)-s*cos(psi0).

This is a comparison of scalars attached to the unchanged original
data. It does not assume that rotating an actual unit while fixing
a,b,H preserves a packing or a contact.

## 5. Strict compensation by the actual corner height

The loss in the preceding direction bound is compensated by the
actual K height. The exact difference is

    c*sin(psi0)-s*cos(psi0)-[sin(psi0)-s]
      =s*(1-cos(psi0))-(1-c)*sin(psi0)
      =s*sin(psi0)*
        [tan(psi0/2)-tan(phi/2)].

All factors before the bracket are positive. Since psi0>pi/4>phi,
the half-angle bracket is strictly positive. Therefore

    f_y>sin(psi0)-s.

The original geometric inequalities H<=1 and c>b give

    K_y>=1/2+s+c*(1-c+b)
        =1/2+b+s+(1-c)*(c-b)
        >1/2+b+s.

Here c<1 follows from the original s>0. The strict positive term
does not disappear at H=1 or b=1/2.

Combining the two original quantities yields

    (K+f)_y>1/2+b+sin(psi0).

Finally

    r0>=b/(1-a)=(1+a)/b,

and the function r/sqrt(1+r^2) is increasing on the positive
interval. Using a^2+b^2=1 gives

    sin(psi0)
      >=(1+a)/sqrt((1+a)^2+b^2)
      =sqrt((1+a)/2).

This proves the whole uniform bound

    (K+f)_y>1/2+b+sqrt((1+a)/2)

for b>=1/2 and c>s, without any D-return hypothesis, bridge edge or
equation at B,C,N. In particular the proof never imports the
adjacent-return inequality a<b.

## 6. Full concavity interval and the revised endpoint b=16/25

For 0<b<1 put

    a(b)=sqrt(1-b^2),
    J(b)=sqrt((1+a(b))/2),
    G(b)=1/2+b+J(b).

I differentiated directly:

    J'=-b/(4aJ),

    J''=-1/(4aJ)-b^2/(4a^3J)-b^2/(16a^2J^3)<0.

Thus G is concave. It has a continuous extension at b=1 with
J(1)=1/sqrt(2), so the same concavity holds on the closed
comparison interval [16/25,1]. A concave function lies above the
chord between its endpoint values; its minimum is consequently at
an endpoint.

At b=16/25, a^2=369/625. The independently checked exact reserve

    369/625-(959/1250)^2=2819/1562500>0

implies a>959/1250. Since

    (1+959/1250)/2=(47/50)^2,

one has J>47/50, and therefore

    G(16/25)>1/2+16/25+47/50=52/25.

At b=1, the positive reserve 1/2-(3/5)^2=7/50 gives

    G(1)=3/2+1/sqrt(2)>21/10>52/25.

Hence G(b)>52/25 on the entire closed comparison interval.
The physical b remains strictly below one; the endpoint one is used
only to bound a continuous scalar function. No degenerate square is
inserted into the packing.

The actual contained B therefore has a point higher than 52/25
whenever b>=16/25 and c>s. But

    (52/25)^2-1105/256=1599/160000>0.

This is a strict contradiction throughout the original closed
radius window, including its upper endpoint.

## 7. Complete complementary-angle and original-family joins

The new comparison used c>s. The full complementary domain c<=s
has

    c<=1/sqrt(2)<3/4.

The original chart source's complete Theorem B excludes every return
in c<=3/4 at arbitrary original exterior degree and mask. That
theorem includes the equality c=s. Combining these two actual
alternatives excludes the entire b>=16/25 feature, with every
original D exterior support row and all original means retained.

For both literal D02 callers the original labels remain

    A=0,V=1,D=2,C=3,N=4,B=5,

with rim A--V--D--C--N--B--A and chord AD. The original A,D true3
stars and V true2 star are exactly the ones in the chart. B,C stay
loaded true2; N stays unloaded true2 in L135 and loaded true2 in
L1345. All their equations remain, although none is needed in the
new local height proof. All three additional actual units remain
arbitrary and present.

Together with the separately reviewed full projection theorem, the
surviving necessary rows are exactly:

| Actual D return | Necessary remaining conditions |
| --- | --- |
| Opposite vertex | c>3/4, 0<b<16/25, 11/50<y<1/sqrt(2), original z=1 and q=(u-y)/b>0 |
| D-owned exterior side | c>3/4, 0<b<16/25, y>3/11, original q=u/b and z=u*a/c in (0,1) |

All original force and moment equations, physical support constraints,
circle data and the full bridge inequalities remain required in these
rows. The side mean z has not been replaced by a convenient point.

These are necessary remainders, not assertions that such packings
exist. The theorem does not close either complete original D02 load
family, any coarse inventory cell, a unique-physical-circle feature,
the equality classification or the global common-selection audit.

Whole-data reflection transports the entire chart, original forces,
physical masks and means. It does not transfer the result to a
different AD owner by relabeling only part of a fixed configuration.

## 8. Exact arithmetic and adoption verdict

The final current-source arithmetic was recomputed with exact integer
fractions:

| Check | Exact result |
| --- | --- |
| 369/625-(959/1250)^2 | 2819/1562500>0 |
| (1+959/1250)/2-(47/50)^2 | 0 |
| 1/2-(3/5)^2 | 7/50>0 |
| (52/25)^2-1105/256 | 1599/160000>0 |
| 21/10-52/25 | 1/50>0 |

Every squared comparison is between positive quantities. The proof
uses one complete continuous angle interval and one complete
concavity interval, with no pose or angle enumeration.

I accept the full current manuscript at
0afb19ae0fbde08c104b6e5bf554ab27885c31dc1c16275de625341f956ce167:
the uniform b>=1/2 height inequality, the complete b>=16/25
exclusion, the complementary-angle join, both literal D02 transfers
and the printed exact residual are sound.

The earlier conditional common-selection premise is retained at its
existing scope. No input manuscript, force, normal, mean, physical
corner coefficient, actual unit or original true degree was changed.
No original inventory flag, denominator or metadata was edited.
No pose search, angle mesh, packing certificate, Lean/Lake build,
CI, remote mutation or merge was performed.

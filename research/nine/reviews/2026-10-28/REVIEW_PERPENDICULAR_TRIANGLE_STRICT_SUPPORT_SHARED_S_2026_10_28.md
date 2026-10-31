# Independent full review: strict support separation from perpendicular owned returns

Date: October 28, 2026 UTC. Reviewer: shared_s continuation.

**Verdict: PASS for the complete radius-free full-three-force theorem,
the separately stated conditional higher-degree extension, and every
literal original-family interface listed. No whole open family closes
from these conditional interfaces alone.**

Reviewed source:
`UNLOADED_THREE_FORCE_PERPENDICULAR_TRIANGLE_STRICT_SUPPORT_SEPARATION.md`,
SHA256
`cd1395ad56ca635efc3075655b18a03009cf4bcf416313a7d4efcbcd318f17c1`.

I read the entire source, independently reconstructed the strict
one-return proof and the second-return coordinate change, checked the
complete higher-degree hypothesis, and matched each original graph/load
row and its true degrees. The source's full geometric proof is
self-contained; the earlier relay is provenance, not an unexpanded
new mathematical premise.

## 1. Complete full-star normalization and the original means

The original unloaded U has exactly the three actual positive neighbors
Q,V,W. Its entire full force and torque equations are retained.
The two original U-owned perpendicular return axes can be normalized
to East and South, giving the actual square and means

    U=[a,a+1] x [b,c], b=c-1,
    P_V=(a+1,c-delta),
    P_W=(a+tau,b),
    delta,tau in [0,1].

No support point is selected from either actual mean interval. With
positive original magnitudes lambda,mu,nu, the whole force equation
gives n0=(-u,v), u=mu/lambda>0, v=nu/lambda>0. Because n0
is its original unit normal, u^2+v^2=1. It therefore strictly
exposes U's actual upper-left vertex p0=(a,c); that location of
the third application is derived, not imposed on an original mean.

The full torque about p0 is mu*delta-nu*tau=0. Translating its
pivot is valid because the same full force sum is zero. Thus
delta=(v/u)*tau. No force or external moment at a neighbor is
used or discarded. Both u,v are positive, which is essential for
the strict parallel-orientation conclusions below.

## 2. The strict one-return relay is valid over the whole domain

The local geometric lemma has E,F>0 and rho=F/E, with the actual
mean condition delta<=rho*tau. It claims H=E*x-F*y>H0=E*a-F*c
on every original W point, assuming the actual V--W contact.

At the actual minimum-x point P_V of V, its two inward own axes
have nonnegative x components. At most one axis can have negative
y component and that component's magnitude is at most one. At a
relative-side-interior point the inward normal is East, and the
full tangent interval has length one. Consequently the whole V
satisfies y>=b-delta. This includes both support-side endpoints
and the exact equality orientation.

If W owns the original South normal, its entire square is
[ell,ell+1]x[b-1,b]. Any actual V--W point has x>=a+1, forcing
ell>=a. Hence min_W H>=H0+F>H0. Every actual upper-side mean
is retained, including either vertex endpoint.

Otherwise Q=P_W is W's unique top vertex. Its complete inward
frame is (C,-S),(-S,-C), with C,S>0 and C^2+S^2=1. Writing
an actual V--W point as Q+t(C,-S)+w(-S,-C), t,w in [0,1],
the real V half-plane gives

    t*C-w*S>=1-tau,
    Z_y<=b-(1-tau)*S/C-w/C<=b-(1-tau)*S/C.

Together with the whole V bound and delta<=rho*tau this yields

    tau>=S/(S+rho*C).

The positive denominator does not depend on deleting tau=0 or tau=1.
The two actual H increments along W's axes are E*C+F*S>0 and
-E*S+F*C. Its application already satisfies
H(Q)=H0+F+E*tau>H0. Thus any actual point with H<=H0
requires the second increment negative and gives the exact
whole-square minimum condition

    tau<=S-rho*(1+C).

The difference of the lower and upper bounds has numerator

    S*(1-S)+rho*S+rho^2*C*(1+C)>0

over the strictly positive denominator S+rho*C. The first term
is strictly positive throughout the complete oblique interval.
This rules out H<=H0, giving the claimed strict conclusion.
The two angular endpoints are precisely the parallel W chart
already treated. No semicontinuity or unsupplied limiting reserve
is used to recover them.

## 3. The reflected second return preserves every parameter

For the actual full star, E=u,F=v and rho=v/u satisfy the
local hypothesis with equality. This proves H>H0 on W.

I checked the complete coordinate change x'=-y,y'=-x for the
other unit. It maps the actual U to

    a'=-c, c'=-a, b'=-a-1,

and maps W's original South point to the new East point with
delta'=tau. V's original East point becomes the new South point
with tau'=delta. The new coefficients are u'=v,v'=u, so
delta'=(u/v)*tau' follows from the same full original torque.
The actual physical V--W contact is unchanged.

The new functional and corner level are exactly

    v*x'-u*y'=u*x-v*y,
    v*a'-u*c'=u*a-v*c.

The same strict local lemma therefore gives H>H0 on V too.
Since the actual third normal is n0=(-u,v), both conclusions
are precisely n0.z<n0.p0. Q's actual supporting half-plane is
n0.z>=n0.p0, so Q is closed-disjoint from both returned units.
This is strict separation of every actual square point, not a
center-only or force-line statement.

## 4. Higher true degrees: the additional moment premise is explicit

Section 5 preserves every original force at a higher-degree unloaded
U. Its additional premise is the exact sum of all other original
force moments **about p0=(a,c)** being zero. The phrase about
origin moments in that paragraph is read in this expressly stated
p0-pivot sense; origin torque alone about a different point would
not supply the displayed relation.

With that complete p0-moment premise, the full U torque gives
mu*delta=nu*tau. The full U force makes the aggregate of all
other forces (-mu,nu). Normalizing that aggregate supplies the
u,v needed for the two strict geometric relay uses. The source
does not delete any of those original forces or assert a false
three-force equation at U.

When all the other actual applications equal p0, their moments
about that point are individually zero, so the stated sufficient
condition is valid. Without an actual third body's own support,
no individual neighbor is asserted to lie beyond the aggregate
line. In particular this extension is not invoked automatically
at a four-force fan hub. The precise distinction is retained.

## 5. Every listed original caller has the literal graph and degree

Each application is conditional on the two displayed original axes
being perpendicular and owned by the displayed actual unloaded U.
Its return pair physically touches through the original edge, not
through an inferred or substituted contact.

| Listed S family | Checked full-star assignment | Physical return edge and retained degrees |
| --- | --- | --- |
| Lower house LTDC.S | U=A, Q=B, returns T,D | TD; A3,B3,T2,D3 |
| Roof house LAC.S | U=D, Q=C, returns T,A | TA; D3,C2,T3,A3 |
| Roof house LABC.S | U=D, Q=C, returns T,A | TA; D3,C2,T3,A3 |
| Hub house LTC.S | U=D, Q=C, returns A,T | AT; D3,C2,A4,T2 |
| Hub house LTCB.S | U=D, Q=C, returns A,T | AT; D3,C2,A4,T2 |
| Endpoint fan L234.S | U=1, Q=L, returns J,2 | J2; 1 has true degree3, L1,J4,2 has true degree3 |

The load masks leave the displayed U genuinely unloaded in every
row. The marked house hub A and fan hub J retain their actual
four forces as returned units. No smaller equation is assigned to
either. The roof root-level caller U=T,Q=L,returns A,D is also
literal: T is the actual clear genuine-leaf root of degree three
and AD is an original positive edge.

For the completed lower-TDC.D example, the stronger functional
ratio F/E>=nu/mu implies the local one-return hypothesis from
the actual full-star equality delta=(nu/mu)*tau. This explains
the full tilted-BA use without imposing a North-only restriction.

In the roof rows there is no original A--C contact. Strict
separation of those bodies is a necessary conclusion rather than
an immediate contradiction. The source explicitly keeps that gap,
the other owner alternatives and the higher-degree conditions.
Thus none of the listed still-open whole S families is falsely
declared closed.

## 6. Exact provenance and acceptance boundary

The direct graph input is
`FIVE_BODY_BLOCK_LEAF_GRAPH_LOAD_COVER.md`, SHA256
`e5c84071363e8dc43b09f9033c7cb3a7684f1de19bcd169d53c9eab55d51963b`.
The earlier weak relay source is
`LOWER_HOUSE_TDC_D_POSITIVE_ROOT_MOMENT_AND_FINAL_RELAY_EXCLUSION.md`,
SHA256
`e5368cd0761d4f10a203272a0df4fc695604318cfe478d4076cad7c7771a0aef`.
All new strict statements and the second-return step were proved in
the reviewed source and reconstructed above, rather than inferred
from that weaker statement alone.

There is no containing-radius, circle-mask, numerical angle, generic
normal, loaded-tip concurrence, computational certificate or hidden
degree premise in Sections 1--5. Every actual support mean and
endpoint is included. This review changes no mathematical source,
original ID, checklist, ledger, force, mean, mask, Lean file,
workflow or remote state, and ran no Lean build or CI.

## 7. Current clarified-pivot pin

The current source SHA256 is
`6630675274998befc40e87bfe67e15f0bdf0d74b7b814f82ccbc42b71dea4b24`.
Its Section 5 now says exactly that the moments of every other
original force **about p0=(a,c)** sum to zero, removing the one
extraneous word "origin" noted above. I checked the current paragraph
and the complete byte identity: restoring only that removed word
in memory reproduces the fully reviewed source SHA256
`cd1395ad56ca635efc3075655b18a03009cf4bcf416313a7d4efcbcd318f17c1`.
No other theorem, proof, endpoint, caller or dependency changed.

**Current-pin adoption: PASS at 66306752, with the exact pivot premise
now stated without ambiguity.**

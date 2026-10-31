# Two strict owned roofs and a shared hub edge admit no unloaded two-force bridge

Date: October 30, 2026. **Complete proposed hand theorem. Independent audit
and compiled Lean are deferred.**

This excludes the entire shared-AD alternative in the physical-two,
two-strict-inner-corner chart when both original roof normals are owned by
their actual hubs. The argument is uniform in every roof angle, radius,
physical circle weight and original shared-side mean. It uses no numerical
cover and no endpoint degree or load equation.

In fact the local theorem is radius-free. V need only be an actual unit
square with the two stated adjacent strict corner contacts; its other
neighbors, load and force equations are unrestricted. B and C may likewise
have arbitrary true degrees, loads and further forces. The essential full
stars are unloaded A3,D3 and an actual unloaded N2 between B,C, together
with the same original incident-diagonal avoidance.

## 1. Exact original data and common frame

Keep all actual units, every original positive force and application or full
aggregate mean, and every physical contact. In the literal D02.L135 caller
retain the nine units and

    A:{V,D,B}, D:{V,A,C}, V:{A,D},
    B:{A,N}, C:{D,N}, N:{B,C},

with A,D,N unloaded and V,B,C loaded. The proof will not use the V,B,C load
or degree equations. No equation is dropped when transferring the theorem
back to this caller.

The two original strict contacts of V are at the adjacent inner corners

    P=(d,1/2), Q=(d,-1/2).

Their outward V normals are (-c,s),(-C,-S), with all four components
strictly positive in magnitude. Both normals are owned by their actual
receiving hubs. Thus P and Q are genuine relative-side-interior points of
A,D, respectively. This is the original owned-roof alternative; no new
selector is imposed. The strict vertex/vertex convention and the original
singleton owner theorem are the same as in
`PHYSICAL_TWO_CORNER_TRIANGLE_TIP_FIVE_DISTINCT_APPLICATIONS_AND_HUB_SINGLETON_OWNER_COVER_2026_10_29.md`.

Assume the original AD contact has positive shared length. Its two actual
unit frames are parallel. Set

    h=(c,-s), e=(s,c), c,s>0, c^2+s^2=1.

The A-to-V direction is h. The D-to-V direction (C,S) is an own axis of
the parallel D frame. It cannot be parallel to h, since its two coordinates
are positive while h has opposite signs. Therefore it is e, and

    C=s, S=c.

Write the unchanged original units, including their actual roof locations,
as

    A=P+[-1,0]*h+[-l,1-l]*e, 0<l<1,
    D=Q+[-t,1-t]*h+[-1,0]*e, 0<t<1.             (1)

The positive shared AD normal g is one of the common own axes. The complete
physical side-normal obstruction for the actual touching triangle A,V,D
requires

    h.g>=0, e.(-g)>=0.

Hence g is either h or -e. The two cases are exchanged by reflection in the
horizontal axis together with the full exchange A,D and B,C. It suffices to
prove the case g=h; all units, coefficients, applications and means are
transported together in that exchange.

## 2. The shared geometry fixes the entire D unit

For g=h, the common AD support line is A's maximum-h line and D's minimum-h
line. Equation (1) therefore gives

    P.h=Q.h-t.

Since (Q-P).h=s, one has exactly t=s. Thus

    D=Q+[-s,1-s]*h+[-1,0]*e.                    (2)

No AD mean has been chosen to obtain (2). The whole original positive
shared segment and its original mean remain. More explicitly, its points
have the form

    W=P-(c+j)*e=Q-s*h-j*e,
    0<=j<=l-c,

whenever the shared interval is nonempty. Positive shared length implies
l>c, while either endpoint value of the original aggregate mean remains
permitted. The proof below will not need j or any AD torque equation.

Let the unchanged AV,DV,AD magnitudes be mu,nu,gamma>0. Full unloaded A3
force balance and the actual shared normal g=h give

    F_AB=-(mu+gamma)*h.

The entire original AB application or mean is consequently on A's
minimum-h side:

    K=P-h+z*e, -l<=z<=1-l.                       (3)

In particular z>-1, including either endpoint of this full side interval.
The actual B has minimum support at K in direction -h.

Full unloaded D3 force balance similarly gives

    F_DC=gamma*h-nu*e.

Both own components are strict, so its actual D support is the unique
corner

    L=Q+(1-s)*h-e.                             (4)

C has its actual minimum support at L in the unchanged unit direction

    f=(q*h-e)/sqrt(1+q^2), q=gamma/nu>0.         (5)

No degree, circle mask or normal ownership at B or C is needed for these
support statements. Every additional exterior force remains present.

## 3. One exact support difference closes both unloaded transmission types

Using Q-P=s*h-c*e in (3),(4) yields the identity

    L-K=2*h-E*e, E=1+c+z>c>0.                  (6)

This constant coefficient 2 is the useful uniform obstruction; it does
not depend on the original force ratio, AD mean or circle radius.

Reverse the names of the two exterior endpoints only for applying the
following geometric bridge lemma: take the new first endpoint to be the
actual C, the new second endpoint the actual B, and use the unchanged
orthonormal frame

    h0=e, e0=h.

The new first endpoint has minimum support at L in direction

    f=-A0*h0+B0*e0,
    A0=1/sqrt(1+q^2), B0=q/sqrt(1+q^2),
    0<A0<1, B0>0, A0^2+B0^2=1.

The new second endpoint has minimum support at K in direction -e0. Their
original support difference is

    L-K=-E*h0+2*e0, E>0.                       (7)

### Side transmission

The complete unit-square support-span inequality gives

    min_C e0 >= L.e0-A0,
    max_B e0 =K.e0.

Consequently every actual point T in C and U in B satisfies

    (T-U).e0>=2-A0>1.

The complete side-transmitter alternative of the actual unloaded N would
require T-U to be a unit vector. Its e0 projection cannot exceed one.
This contradicts the strict gap. The conclusion retains every original
endpoint mean and does not replace either whole square by its support point.

### Diagonal transmission

Apply the general radius-free diagonal-bridge obstruction proved in Section
2 of
`PHYSICAL_TWO_PERPENDICULAR_SINGLETON_WHOLE_SIDE_RETURN_EXCLUSION_2026_10_30.md`.
Its full hypotheses are: the first inward direction is
-A0*h0+B0*e0 with A0,B0>0; the second is -e0; their support difference is
-E*h0+G*e0 with E>=0, G>sqrt(2), and squared norm greater than three.
It retains arbitrary endpoint degrees and loads, every original support
mean and tie, and the same incident-diagonal avoidance at the actual N.

All those hypotheses follow immediately from (7):

    E>0, G=2>sqrt(2), |L-K|^2=4+E^2>4>3.

Therefore N cannot be a diagonal transmitter either. The lemma's proof
uses the actual relative-side-interior applications forced at the endpoints
by the unchanged incident-diagonal avoidance, and covers all signs of the
diagonal direction. It does not assume that B or C owns its exterior
AB/DC normal.

The full unloaded true2 force and torque theorem allows precisely side or
diagonal transmission. Both have now been excluded. This proves the whole
shared-AD feature, including every original shared-mean endpoint.

## 4. Reusable scope and original join

No circle equation, radius estimate, force-magnitude bound, sampled angle,
interval subdivision or completing-unit placement appears in the proof.
It only uses the two actual adjacent strict roof corners, their genuine
hub ownership, the actual shared AD interface, full A3/D3 force balance,
and the complete unloaded N2 transmission theorem. Accordingly B,C,V can
have further original neighbors or arbitrary loads where the stated local
physical chart and true A3/D3/N2 stars are retained. The whole-configuration
reflection covers g=-e as well as g=h.

For the literal physical-two D02.L135 caller this removes the entire AD
shared/both-owned case when both strict roofs are hub-owned. The existing
strict singleton convention means that a shared-axis AD contact with both
owners cannot be recategorized as an axial vertex/vertex singleton.
The free-AD alternative in this owned-roof chart is excluded separately by
`UNLOADED_TRIANGLE_OWNED_RETURN_AND_OWNED_EXTERIOR_FORCE_SAME_AXIS_2026_10_30.md`.
The two singly-owned AD alternatives retain their own obligations.

This source does not apply the unloaded transmission dichotomy to loaded N
in D02.L1345. It makes no new common-selection assumption, does not delete
the three actual completing units, changes no original fine/coarse flag,
and does not declare the full D02 row or nine-square theorem closed.

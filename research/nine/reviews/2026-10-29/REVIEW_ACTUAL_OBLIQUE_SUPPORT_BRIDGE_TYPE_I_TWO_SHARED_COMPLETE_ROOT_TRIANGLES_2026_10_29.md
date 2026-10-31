# Full independent review: oblique support gaps and Type I two-shared roofs

Date: October 29, 2026 UTC. Reviewer: root_triangles.

**Verdict: ACCEPT at the exact current source below.** This is a complete
independent, noncontributor mathematical review of the whole manuscript,
its original physical entry and both literal load joins. The reviewer did
not supply the new oblique projection argument, the two-shared-roof chart,
the Type I application, or any correction to the source under review.
The earlier generic unloaded-bridge input was independently reviewed by
this reviewer; it is reconstructed again at its exact operative scope.

## 1. Exact current manuscript and complete inputs

The reviewed source is

    ACTUAL_OBLIQUE_SUPPORT_BRIDGE_AND_TYPE_I_BOTH_SHARED_ROOFS_COMPLETE_UNLOADED_EXCLUSION_2026_10_29.md
    SHA256 a6fa97604073de0eca72491632aa6936f0a919075946de8dde92b099152aae51.

Every line of that current source was read. The complete following direct
inputs were also read, and all five displayed hashes were independently
recomputed from the current local bytes.

| Complete direct input | SHA256 |
| --- | --- |
| UNIQUE_CIRCLE_TRIANGLE_TIP_THREE_PORT_TYPES_AND_HUB_INTERFACE_OWNER_COVER_2026_10_29.md | 8266220efbb8ce769de90a90e27e86997400575d0b8bb80f5843af38ca447073 |
| VERTICALLY_SEPARATED_RETURN_SUPPORTS_NO_UNLOADED_TRUE_TWO_BRIDGE_AND_SHARED_D_L135_EXCLUSION_2026_10_29.md | 112510ba9d1ec141443b19bbcf4212879a628e2eab083335c3252640f32f36bd |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 |

The source hash and every input hash match exactly. No source, input,
ledger, inventory or metadata file was edited during this review.

## 2. The complete radius-free projection theorem

Let Q minimize an actual unit square S in unit direction n, and let d be
a unit direction with n.d>=0. The source proves the full-set inequality

    min_(X in S) d.X >= d.Q-|det(n,d)|.

I reconstructed both exhaustive support cases.

At a uniquely minimizing vertex, take the two actual orthonormal inward
edges u,v. Both coefficients n.u,n.v are strictly positive. If both d.u
and d.v were negative, their n-weighted sum would make n.d negative.
Hence at most one inward edge can decrease the d coordinate. For either
edge, orthogonal decomposition gives

    d.u=(n.u)(n.d)+(u.Jn)(d.Jn),
    |u.Jn|<=1, |d.Jn|=|det(n,d)|.

The first term is nonnegative. Therefore the sole possible negative edge
increment has magnitude at most |det(n,d)|. Taking the minimum over the
entire two-dimensional unit box proves the asserted bound, without
adding two independent negative losses. The n.d=0 endpoint and either
zero d-edge increment are included.

At an owned support side, retain the exact original transverse parameter:

    S=Q+[-lambda,1-lambda]u+[0,1]n,
    0<=lambda<=1, u perpendicular n.

The normal term cannot lower d. The full length-one tangent interval
lowers d by at most |d.u|=|det(n,d)|. This retains every original mean,
both side endpoints and either sign of d.u. It does not replace the
application by a vertex. Owned-axis endpoints of the vertex case belong
to this complete side case.

Applying the theorem to B in d and C in -d gives precisely

    min_B d-max_C d
      >=d.(Q_B-Q_C)-|det(n_B,d)|-|det(n_C,d)|

under n_B.d>=0 and n_C.d<=0. Any actual unit N has d-width at most
sqrt(2), by Cauchy--Schwarz on its two own edges. Actual contacts with
both B,C would give two points of N with at least the displayed projected
separation. Thus a strict right-side bound greater than sqrt(2) excludes
the whole actual bridge. This uses no stress, degree, radius, load,
contact-owner or selection premise. Weak physical contacts are covered
because the inequality concerns the closed complete units.

## 3. Exhaustive Type I two-shared physical placements

The exact three-port input supplies V's actual unique-circle chart and
its full original equations:

    V=[a-1,a] x [b-1,b], a,b>1/2,
    P0=(X,Y)=(a-1,b-1),
    R=P0+w North, P=P0+h East,
    0<=h,w<=1, (h,w)!=(0,0),
    mu=kappa a>0, nu=kappa b>0,
    mu(1-w)=nu(1-h).

No strict-corner owner or nonfree-AD conclusion from Types II/III is
imported into Type I. The current theorem additionally assumes the two
actual roof intersections have positive physical shared length. Their
actual frames consequently agree with V's frame, giving exactly

    A=[X-1,X] x [Y+delta_A,Y+delta_A+1],
    D=[X+delta_D,X+delta_D+1] x [Y-1,Y],
    -1<delta_A,delta_D<1.

The strict shift intervals are equivalent to positive overlap along
each roof's supporting line. Their closed limiting values +/-1 are
outside the stated feature and are not silently omitted from it.

Actual AD contact requires delta_D<=0 from the horizontal intervals and
delta_A<=0 from the vertical intervals. Both strictly negative would
make both interval intersections have positive length, producing open
interior overlap. Thus the exact remaining cover is

    (delta_A,delta_D)=(0,-ell), (-ell,0), or (0,0),
    0<ell<1 in the first two alternatives.

For either shifted alternative the physical AD overlap has exactly length
ell. At (0,0) the contact is exactly the single vertex P0. This is a
complete original placement cover. Original R,P membership in the actual
shared roof intervals is retained throughout; the proof never claims
that every formally enlarged h,w interval is physically realizable.

## 4. Entire point-only AD alternative, for either load of N

For delta_A=delta_D=0, the physical singleton convention makes the
original A-to-D normal g=(u,-v) with u,v>0. An axis would fail strict
exposure at the two actual vertices, so no axis endpoint is lost from
this original point-only feature. No new normal is selected.

The two complete unloaded hub forces give

    F_B=(-mu-rho u, rho v),
    F_C=(rho u,-nu-rho v), rho>0.

Their signs force the actual unique applications

    Q_B=(X-1,Y+1), Q_C=(X+1,Y-1).

The neighboring actual units B,C minimize their corresponding inward
directions n_B=(-a_B,b_B), n_C=(a_C,-b_C), with all four coefficients
strictly positive. For the fixed d=(-1,1)/sqrt(2), I recomputed

    d.(Q_B-Q_C)=2 sqrt(2),
    n_B.d=(a_B+b_B)/sqrt(2)>0,
    n_C.d=-(a_C+b_C)/sqrt(2)<0,
    |det(n_B,d)|=|a_B-b_B|/sqrt(2)<1/sqrt(2),
    |det(n_C,d)|=|a_C-b_C|/sqrt(2)<1/sqrt(2).

Strictness follows from (a_B-b_B)^2=1-2a_B b_B<1 and its C analogue.
Thus the full projected separation is strictly greater than sqrt(2).
The radius-free theorem excludes every actual N touching both returns.
This argument uses no N force equation, so the exclusion includes both
the loaded and unloaded original N roles. It also needs no diagonal
avoidance or common nonfree-AD assumption.

## 5. Complete original moments in the shared-AD alternative

For delta_A=0, delta_D=-ell, the exact applications are

    R=P0+(0,w), P=P0+(h,0),
    W=P0+(-z,0), 0<=z<=ell,
    Q_B=P0+(-1,1), Q_C=P0+(q,-1).

The original normal AD is South; the positive-length intersection fixes
it physically. The entire unchanged exterior forces are

    F_B=(-mu,rho), F_C=(0,-nu-rho).

I independently recomputed every moment about the same actual P0.
At A the three contributions are

    -mu w, rho z, mu-rho.

Their sum zero gives rho(1-z)=mu(1-w). The full V moment adds the
unchanged equality with nu(1-h). At D the three contributions are

    nu h, -rho z, -(nu+rho)q.

Consequently

    (nu+rho)q=nu h-rho z=nu-rho,
    q=1-2tau, tau=rho/(nu+rho) in (0,1).

The middle equality uses exactly rho(1-z)=nu(1-h). Thus q is the
derived original DC mean. Its actual support membership

    -ell<=q<=1-ell

remains a physical condition. Neither this coordinate nor the original
AD coordinate z is replaced or independently selected. The two closed
z endpoints are retained. In fact the full A moment and z<1 also force
w<1,h<1; the manuscript does not need that further consequence and
does not incorrectly demand endpoint positivity in advance.

Subtracting the same original applications now gives

    Q_B-Q_C=(-1-q,2)=(-2(1-tau),2).

Its horizontal component is strictly negative, and its vertical
component is exactly two, including every original mean endpoint.
The B inward direction is strict Northwest and the C inward direction
is exactly South, as required by the generic theorem.

## 6. Reconstructed generic unloaded-bridge use and selection boundary

The full radius-free bridge input requires only those actual support
data, an actual unloaded N of true positive degree two, and the same
prior finite diagonal avoidance. It has no boundary or degree premise
at B,C. I checked the full argument again:

1. If B's inward direction is (-a,b), a,b>0, its whole downward
   reach from Q_B is at most a. C's actual maximum height is Q_C.y.
   The actual N applications therefore differ vertically by at least
   2-a>1, including all B side means and support ties.
2. The complete unloaded N force and torque give a side transmitter
   of length one or a diagonal transmitter of length sqrt(2). The
   first is impossible by that strict height gap.
3. The diagonal endpoints are actual N vertices. The unchanged initial
   vertex/vertex diagonal avoidance makes both other endpoint owners
   B,C, at actual relative side interiors. Their frames are parallel
   to the channel; no frame is reselected.
4. For channel d=(u,v), v>1/sqrt(2), the entire u<=0 domain gives
   equality Delta.d=sqrt(2) from the actual common own support faces,
   but Delta.x<=0, Delta.y>=2 gives Delta.d>=2v>sqrt(2).
5. For u>0, with w=(-v,u), the full B support tie and C side position
   give Delta=(sqrt(2)+xi)d-(alpha+beta)w, with all three original
   parameters in their closed [0,1] ranges. Its horizontal component
   is strictly positive, contrary to Delta.x<=0.

Both channel signs, u=0, the exact B support tie, and all support
coordinate endpoints are included. The graph-uncrossing source permits
the finite avoidance initially and preserves it through uncrossing,
thinning and actual shared-mean aggregation. This is an explicit premise
on the same compatible certificate. The current source does not prove
the prior global common-selection compatibility and does not alter a
normal after multiplier extraction.

Reflection across V's own diagonal exchanges A,D, B,C, mu,nu and h,w.
It transports every original force, application and mean, and fixes the
actual return N. This proves the second positive-shift alternative from
the first. Together with the point-only argument it exhausts the entire
two-physically-shared-roof feature.

## 7. Exact original family join and limits

The literal rim is A--V--D--C--N--B--A with chord AD, under

    A=0,V=1,D=2,C=3,N=4,B=5.

A,D are the actual unloaded true3 hubs. V,B,C remain the actual loaded
true2 units. N is unloaded true2 in L135 and loaded true2 in L1345.
The graph reflection used above preserves each of these two load sets.
All three additional actual squares remain present. The contradiction
within the original core does not delete them or assign them a new role.

The fully justified new closure is therefore:

* The whole Type I feature with both AV and DV physically shared is
  excluded in D02.L135, for every original shift, full mean, force ratio,
  physical circle mask and zero individual coefficient.
* The entire point-only AD subfeature is also excluded in D02.L1345,
  by the same radius-free physical projection proof.

The positive-shared AD feature with loaded N remains outside the unloaded
bridge theorem. Singleton-roof Type I, Types II/III, physical-two V and
both full D02 parents receive no further closure from this manuscript.
Neither the unrestricted sharp n=9 theorem, its equality classification,
the global selection prerequisite nor Lean integration is closed here.

Every proof above is on the complete printed continuous domain. The
projection theorem is universal, the placement cover is exact, the force
identities are reconstructed from all original terms, and the literal
join uses the correct actual degrees and loads. No mathematical defect
or correction is requested. No numerical pose search, angle mesh,
packing certificate, Lean/Lake build, CI, remote mutation or flag edit
was used in this review.

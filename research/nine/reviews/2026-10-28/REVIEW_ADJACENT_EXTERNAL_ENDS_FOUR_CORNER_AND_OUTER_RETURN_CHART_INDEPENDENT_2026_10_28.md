# Independent full review: the adjacent external-end pentagon chart

Date: October 28, 2026 UTC. Reviewer: /root/pentagon_audit.

## 1. Exact frozen target, independence, and verdict

**PASS.** I read and independently checked the entire frozen
INNER_PENTAGON_ADJACENT_EXTERNAL_ENDS_FOUR_CORNER_AND_OUTER_RETURN_CHART.md,
13,726 bytes, 322 lines, SHA-256

    4d789a72e56cba5b4416f5231cf97fc3145488cfdaec0482ba9fabd808036db3.

I did not participate in construction, give construction advice, or
edit the source. The author's proof, including the root-requested
explicit local sector argument, was already frozen before my audit.
I checked the whole no-third-unit lemma, every HB/HC support feature,
the complete H4 identities, both full endpoint force and torque
systems, all original side means, and both finite concurrence formulas.
No mathematical blocker remains.

The accepted output is a complete radius-free necessary chart. From
adjacent genuine external end ownership, the four original H forces
occupy the four distinct strict H corners in the printed order.
After the separately complete same-axis return exclusion, each genuine
unloaded endpoint has a strict downward outer force at its actual
outer corner and a finite concurrence point in that same endpoint
square. The complete perpendicular inner-side mean remains.

This source supplies no contradiction for the resulting chart.
It does not close L124, H4_D0, any coarse gate, or the global theorem.

## 2. Original graph, side-owned end data, and actual coordinate change

The positive graph is exactly

    HA, HB, HC, HD, AB, BC, CD, DE, EA.

H is genuinely unloaded with complete positive neighborhood A,B,C,D.
A,D are genuinely unloaded with complete neighborhoods H,B,E and H,C,E.
All nine actual squares and every original force, normal, application,
shared mean, true degree, torque, physical mask and individual zero
circle coefficient remain. No equation at B,C,E is used or shortened.

A owns HA and D owns HD, with their actual H vertices in relative
endpoint-side interiors. Those original normals strictly expose two
adjacent actual H vertices. A rigid chart of the entire physical
configuration, including a whole reflection when needed, gives

    H=[0,1]^2, P_HD=(0,0), P_HA=(1,0),
    F_HA=Gamma_A(u,-v), F_HD=Gamma_D(-p,-q),
    u,v,p,q>0, u^2+v^2=p^2+q^2=1,
    Gamma_A,Gamma_D>0.

The labels of the original units are unchanged. This normalization is
not a displacement of one unit, a change of contact normal, or a
substitution of a new application.

## 3. The complete no-third-unit sector lemma

Let K have an actual vertex P in the relative interior of L's side,
with that side's separating normal strictly exposing P on K.
L has a tangent half-plane at P. Both inward edge rays of K have
strictly negative projection on the normal from K into L, so its
closed right-angle sector lies strictly inside the complementary
open half-plane, apart from its apex.

The angular gaps between K's two rays and the two boundary rays of
that half-plane are both strictly positive. Together they have
angle pi/2; each therefore has angle strictly less than pi/2.
The complement of the occupied interior sectors has those two
connected pieces, with their boundary rays included. Any third actual
closed unit containing P has a connected tangent sector of angle
at least pi/2 and a two-dimensional open interior sector. It cannot
fit in either gap or pass between the gaps without entering one
of the occupied open sectors.

Thus no third actual unit can contain P. This includes a third
unit at a vertex, side point or interior point; the latter two
need still larger tangent sectors. Closed edge directions do not
restore a missing pi/2 gap.

At the two original end contacts this excludes B and C from both
lower H vertices. It does not exclude every point on a lower H
side, so the subsequent axis cover must and does retain its
original full means until a separate contradiction.

## 4. Every HB/HC feature and the full H4 upper-sign argument

For HB, the actual H-A-B triangle and the strict Southeast HA
normal exclude North and West own H axes by their negative dot
products. Strict Northwest HB is opposite strict Southeast HA,
which is impossible because actual A and B touch. The whole-unit
support-reach proof places any common point of those opposite
neighbors in the open H, contradicting physical interior
disjointness even if that common point is on their boundaries.

Section 3 has separately excluded the two lower strict vertices.
Thus the complete nonzero HB normal cover is

    strict Northeast; East axis; South axis.

The corresponding complete H-C-D argument gives

    HC: strict Northwest; West axis; South axis.

These lists cover all four strict corners and all four own axes
for each original normal. The axis rows initially retain every
actual contact feature and closed mean interval.

Both end forces have negative y. The full original H4 y equation
therefore gives

    (F_HB)_y+(F_HC)_y=Gamma_A v+Gamma_D q>0.

At least one of HB,HC must occupy its strict upper corner.
If HB is Northeast, actual H-B-C excludes the West and South HC
axes because each has negative dot product with that unchanged
HB normal. HC is therefore Northwest. Starting with Northwest
HC similarly excludes East and South HB and forces Northeast.
No positive force is omitted, and no cyclic-normal order or
embedding premise is needed.

Consequently the entire strict H chart is

    P_HA=(1,0), P_HB=(1,1), P_HC=(0,1), P_HD=(0,0),
    F_HB=(e,f), F_HC=(-g,h), e,f,g,h>0.

Every previously allowed HB/HC side feature was first retained
and then excluded by its full original geometry. No original
shared mean was moved to a corner.

## 5. Exact full H4 force and torque identities

The x force balance is

    e-g=Gamma_D p-Gamma_A u.

The full y balance is f+h=Gamma_A v+Gamma_D q. The original
torque about (0,0), including all four original applications, is

    -Gamma_A v+f-e+g=0.

Substituting the x equation gives

    f=Gamma_A(v-u)+Gamma_D p>0,
    h=Gamma_A u+Gamma_D(q-p)>0.

I rederived these identities directly. The strict signs are the
already proved Northeast/Northwest force signs, not additional
parameter restrictions assumed without proof.

## 6. Entire A pose and all inner-return means

Use n=(u,-v), j=(v,u), with det(n,j)=1 and P=(1,0).
The complete actual A pose is

    A=P+[0,1]n+[-rho,1-rho]j, 0<rho<1.

Since A owns AH and H,B actually touch, the owned-axis triangle
theorem gives n.F_AB<=0. Write the unchanged vector as

    F_AB=-alpha n+beta j, alpha>=0.

The whole B lies strictly in y>0: its inward strict Northeast
support at (1,1), together with strict unit reach in direction
South, gives exactly that whole-unit bound.

If beta<0, every original maximum-F_AB support of A has
j coordinate -rho. Its n coordinate is zero when alpha>0 and
may range over [0,1] when alpha=0. Every such point has height

    -tau v-rho u<0.

It cannot be in the actual B. Hence beta>=0.

If beta=0, nonzeroness forces alpha>0. Its original AB normal
is precisely the same A side axis as AH. The complete same-axis
theorem applies after the exact original graph reflection
A<->D, B<->C. Its full true H4/A3/D3 and physical mean premises
are satisfied; no four-boundary or physical-boundary-A theorem
is imported. That separately complete exclusion therefore leaves

    beta>0,
    P_AB=P+tau n+(1-rho)j, 0<=tau<=1,
    alpha>0 implies tau=0.

When alpha=0, this is the full original perpendicular side mean,
including both endpoints before torque. A genuinely shared AB
interval is never assigned singleton status.

## 7. The full A3 force and torque fix its actual outer corner

With the original F_AH=-Gamma_A n, full unloaded force gives

    F_AE=(Gamma_A+alpha)n-beta j.

Both own components are strict. Its actual A support is therefore
the unique outer corner

    T_A=P_AE=P+n-rho j=(1+u-rho v,-v-rho u).

The original AE force has world y
-(Gamma_A+alpha)v-beta u<0, and the actual point has negative
y as well. Since A has a unique support point for this force,
the physical AE intersection is a singleton, with no additional
restriction placed on its owner at E.

In the positive frame (n,j), the actual AB moment about P is
tau beta+(1-rho)alpha. The actual AE moment is
-beta+rho(Gamma_A+alpha), while AH has zero moment at P.
The complete torque equation consequently gives

    beta(1-tau)=alpha+rho Gamma_A>0.

Thus tau=1 is impossible, but tau=0 and every other allowed
original mean remain. The equality is the full original A3
torque; there is no selected mean or dropped term.

## 8. Exact finite concurrence in the same A, including lambda=0

Define

    lambda=tau+alpha(1-rho)/beta
           =1-rho(Gamma_A+alpha)/beta.

The second expression follows by substituting the exact torque.
If alpha=0, lambda=tau in [0,1). If alpha>0, tau=0 and
beta=alpha+rho Gamma_A, so

    lambda=alpha(1-rho)/(alpha+rho Gamma_A) in (0,1).

Hence Q_A=P+lambda n is an actual point of the same A for
every allowed parameter. For lambda>0 it is an interior point,
since lambda<1 and j coordinate zero lies strictly between
-rho and 1-rho. For lambda=0 it is the original relative
side-interior HA point. That endpoint is retained explicitly.

Direct substitution gives

    P_AB-Q_A=((1-rho)/beta)F_AB,
    T_A-Q_A=(rho/beta)F_AE.

Both displayed multipliers are positive. Q_A also lies on the
original AH line; its corresponding displacement obeys
P-Q_A=(lambda/Gamma_A)F_AH with a nonnegative multiplier.
In particular no unjustified strict AH ray parameter is asserted
when lambda=0.

These are exact identities of the complete original A3 system.
Q_A is neither a replacement application nor an inferred
concurrence point for the loaded E.

## 9. Complete reflected D force, torque, and concurrence

The actual D chart uses

    n_D=(-p,-q), k=(-q,p), det(n_D,k)=-1,
    D=[0,1]n_D+[-kappa,1-kappa]k, 0<kappa<1.

The whole C lies in y>0 by its original strict Northwest H
support. Repeating the entire triangle/support cover, with the
whole same-axis DC case separately excluded, gives

    F_DH=-Gamma_D n_D,
    F_DC=-alpha_D n_D+beta_D k,
    F_DE=(Gamma_D+alpha_D)n_D-beta_D k,
    alpha_D>=0, beta_D>0,
    P_DC=tau_D n_D+(1-kappa)k,
    0<=tau_D<1, alpha_D>0 implies tau_D=0.

Every perpendicular original CD side mean remains. The frame has
negative determinant, but multiplying the entire world zero-torque
equation by -1 gives the own-frame zero equation. Direct expansion
therefore yields exactly

    beta_D(1-tau_D)=alpha_D+kappa Gamma_D.

Its actual outer contact is the strict D vertex

    T_D=n_D-kappa k=(-p+kappa q,-q-kappa p).

Both its y coordinate and the original DE vector's y component
are negative. The same full algebra gives

    lambda_D=tau_D+alpha_D(1-kappa)/beta_D in [0,1),
    Q_D=lambda_D n_D in D,
    P_DC-Q_D=((1-kappa)/beta_D)F_DC,
    T_D-Q_D=(kappa/beta_D)F_DE.

The possible lambda_D=0 endpoint is included exactly as at A.
No moment sign is transferred selectively between orientations;
the entire D equation uses the same common orientation factor.

## 10. Exact dependency and adoption boundary

All four direct target pins match unchanged current bytes:

| Direct source | SHA-256 |
| --- | --- |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 |
| INNER_PENTAGON_TWO_UNLOADED_ENDS_SAME_AXIS_RETURN_COMPLETE_EXCLUSION.md | 06db7377d2f6818fd73c9e684a64fd1b9691a051c0303721d41e96d225f85fd0 |
| SIX_BODY_INNER_PENTAGON_LOAD_COVER.md | cfe85a201b09182200d5270f0dcdc0e590bf99eded19aaf6d56f86830e959c0a |

All four complete sources were freshly read in this continuous
independent audit. The entire same-axis proof and its complete
708f predecessor/review were independently checked before the
separate review
REVIEW_TWO_UNLOADED_ENDS_SAME_AXIS_RETURN_COMPLETE_EXCLUSION_INDEPENDENT_2026_10_28.md
was frozen at SHA-256

    60cfaa763c2856b6cf761504cbce07901c9049dc670f7048a9ebbf5a1ea3174a.

That source's root adoption remains separate from this downstream
review. The four-strict-corner H result and full H4 identities use
only the adjacent external-owner premises and are independent of
the same-axis exit. The beta>0 endpoint charts invoke that exit
only after explicitly retaining and identifying beta=0.

The exact current residual includes both actual E points T_A,T_D
and their original inward support directions, actual BC, and every
original equation at B,C,E. None is itself contradicted by this
necessary chart. No E2 boundary-neighbor premise, E concurrence,
or special physical circle mask is added.

The audit used full reading and hand geometry/algebra, with
read-only hashes for identity. It used no pose search, angular
mesh, geometric exclusion certificate, mathematical checker,
Lean/Lake, CI or workflow. It edits no mathematical source,
old review, saved checkout, metadata, original gate or count,
and performs no commit, merge or remote write. Only this
separate complete review is new.

# Perpendicular returns of a full unloaded three-force star stay strictly behind its third support

Date: October 28, 2026 UTC. Authors: root and thin_d continuation.

**Status: complete proposed radius-free geometric and full-force theorem,
submitted for full root and independent review. The original-family
applications below are conditional interface restrictions; no whole
original fine or coarse gate is declared closed by this source.**

## 1. Exact full-star statement

Let U,Q,V,W be distinct actual closed unit squares with pairwise disjoint
open interiors. U has zero circle load and exactly the three positive
pair neighbors Q,V,W. Retain their original separating unit normals,
strictly positive force magnitudes and actual application points or
shared-side means. Suppose V,W physically touch, and the original
U-to-V and U-to-W normals are two perpendicular own side axes of U.

All forces at Q,V,W, their loads, physical masks and true degrees are
arbitrary. There is no containing-circle or radius hypothesis. Additional
zero-force physical contacts are permitted. U's complete original force
and torque equations, including both returned forces, are used.

Let n0 be the original U-to-Q normal and p0 its original application.

**Theorem.** The normal n0 strictly exposes the corner opposite the two
owned return sides, and the whole actual returned units satisfy

    n0.z < n0.p0   for every z in V union W.             (1)

In particular Q is closed-disjoint from both V and W, because its
original supporting half-plane is n0.z>=n0.p0. More generally neither
returned unit can touch any actual set contained in that closed opposite
half-plane. The strict inequality in (1) concerns the entire physical
units, not only their centers, applications, stress lines or circle
corners.

## 2. Normalize the actual owned sides and retain every mean

Rotate or reflect coordinates so the original return normals are East
and South and

    U=[a,a+1] x [c-1,c], b=c-1,
    P_V=(a+1,c-delta), P_W=(a+tau,b),
    0<=delta<=1, 0<=tau<=1.

These are precisely the original means. No endpoint or middle point is
selected. Write lambda,mu,nu>0 for the original Q,V,W force magnitudes.
The complete unchanged U force equation is

    lambda*n0+mu*(1,0)+nu*(0,-1)=0.

Consequently

    n0=(-u,v), u=mu/lambda>0, v=nu/lambda>0,
    u^2+v^2=1.

It strictly exposes U's actual upper-left corner, so the original third
application is necessarily p0=(a,c). This is a consequence of the
full force equation, not a chosen location for that third mean.

The complete torque about p0 gives

    mu*delta-nu*tau=0.

Therefore, with kappa=v/u>0,

    delta=kappa*tau.                                   (2)

The full original torque can be translated to p0 because the full
original force sum is zero. No external contribution or neighbor force
has been discarded. In the sign-reversed functional

    H(x,y)=u*x-v*y, H0=u*a-v*c,

the desired conclusion is H>H0 on both returned units.

## 3. A strict one-return relay lemma

The following slightly more general statement is useful independently.
Keep the actual U,V,W and the original owned supports of Section 2,
but suppose merely

    E>0, F>0, rho=F/E,
    H(x,y)=E*x-F*y, H0=E*a-F*c,
    delta<=rho*tau.                                    (3)

Then the actual physical V--W contact implies

    H(z)>H0 for every z in W.                          (4)

No force equation is part of this intermediate statement.

### 3.1. The actual V cannot extend downward by more than one

P_V is a genuine minimum-x support point of V. If it is a vertex,
the two inward orthonormal V axes have nonnegative x components. At
most one can have a negative y component, and that component has
magnitude at most one. If it is in a side interior, the inward side
axis is East and its tangent interval has length one. The downward
span from the unchanged mean is at most that length. Side endpoints
are included in the vertex argument. Thus the whole physical V obeys

    y>=c-delta-1=b-delta.                              (5)

### 3.2. Every parallel W and every side mean

If W owns the original South normal, write its full actual square as

    W=[ell,ell+1] x [b-1,b].

Since V lies entirely in x>=a+1 and V--W physically touch,
ell+1>=a+1, hence ell>=a. Therefore

    min_W H>=E*a-F*b=H0+F>H0.                         (6)

This includes every unchanged mean on the upper side and both endpoint
orientations of the following nonparallel cover.

### 3.3. Every nonparallel W

Otherwise P_W is its unique top vertex and its entire actual frame is

    W=P_W+[0,1](C,-S)+[0,1](-S,-C),
    C=cos(theta)>0, S=sin(theta)>0,
    0<theta<pi/2, C^2+S^2=1.

Choose an actual point Z=P_W+t(C,-S)+w(-S,-C) of V--W.
The real physical half-plane of V makes Z_x>=a+1. Consequently

    t*C-w*S>=1-tau,
    Z_y=b-t*S-w*C
        <=b-(1-tau)*S/C-w/C
        <=b-(1-tau)*S/C.

Combine this with (5) and then (3):

    rho*tau>=delta>=(1-tau)*S/C,
    tau>=S/(S+rho*C).                                 (7)

Suppose an actual point of W had H<=H0. At P_W,

    H(P_W)=H0+F+E*tau>H0.

The H increment on (C,-S) is E*C+F*S>0, so the only possible
negative increment is on (-S,-C). It must be negative for the
supposed point to exist. The exact minimum of H on the whole W
then occurs at P_W+(-S,-C), giving the necessary inequality

    tau<=S-rho*(1+C).                                 (8)

But the lower bound in (7) exceeds the upper bound in (8), because

    S-(S-rho*(1+C))*(S+rho*C)
      =S*(1-S)+rho*S+rho^2*C*(1+C)>0.                 (9)

The denominator S+rho*C is positive. This contradiction proves (4)
for every nonparallel W. All scalar and side-mean endpoints in
delta,tau remain in (7)--(9). The two theta endpoints were covered by
(6), so no limiting orientation is left open.

## 4. Apply the strict relay in both physical directions

For the full star of Section 2, take E=u,F=v in Section 3. Equation
(2) verifies its hypothesis, and therefore H>H0 on W.

For the other returned unit use the reflected, interchanged coordinates

    x'=-y, y'=-x.

In this frame W is the East return and V is the South return. The
complete parameters are

    a'=-c, c'=-a, delta'=tau, tau'=delta,
    u'=v, v'=u, rho'=u/v.

Equation (2) gives delta'=rho'*tau'. The same actual physical contact
V--W is retained. Moreover the functional and its corner level are
unchanged:

    u'*x'-v'*y'=u*x-v*y=H,
    u'*a'-v'*c'=u*a-v*c=H0.

The strict relay thus proves H>H0 on V too. Since n0=(-u,v), this
is exactly (1) for both whole returned units. All claims in Section 1
follow from their unchanged supporting half-planes.

## 5. A valid full higher-degree extension with an explicit extra premise

The geometric proof uses only the two actual owned returns and relation
(2). It therefore has the following literal extension without pretending
that a higher-degree star has degree three.

Keep all original positive forces at an unloaded U. Select two of them
with the perpendicular owned normals above. Suppose the sum of the
moments of every other original force about p0=(a,c) is exactly
zero. Then the full U torque gives mu*delta=nu*tau. The full U force
makes the aggregate of the other forces equal to (-mu,nu). Set
u=mu/sqrt(mu^2+nu^2), v=nu/sqrt(mu^2+nu^2). Sections 3--4 give

    (-u,v).z < (-u,v).p0  for every z in V union W.      (10)

Every original force and degree remains; the statement uses the exact
aggregate moment hypothesis explicitly. A sufficient special case is
that all other original applications are the same actual corner p0.

No actual third neighbor is asserted to lie beyond the aggregate
support line unless its own actual support supplies that additional
fact. In particular this extension is not automatically available at
an unloaded four-force fan hub whose other two moments have not been
shown to cancel about p0.

## 6. Literal current original-family interfaces

The graph/load cover gives the following actual true-three-force
callers. In every row, apply Section 1 only when the displayed pair
normals are perpendicular own axes of the displayed U. Their original
means remain arbitrary. The pair physically touches by the original
edge indicated, independently of any extra physical contacts.

| Original still-open S family | Actual unloaded U and third neighbor Q | The actual touching return pair V,W | True degrees retained at U,Q,V,W |
| --- | --- | --- | --- |
| M6.B5L.HOUSE.LOWER.LTDC.S | U=A, Q=B | T,D, with original TD | A3, B3, T2, D3 |
| M6.B5L.HOUSE.ROOF.LAC.S | U=D, Q=C | T,A, with original TA | D3, C2, T3, A3 |
| M6.B5L.HOUSE.ROOF.LABC.S | U=D, Q=C | T,A, with original TA | D3, C2, T3, A3 |
| M6.B5L.HOUSE.HUB.LTC.S | U=D, Q=C | A,T, with original AT | D3, C2, A4, T2 |
| M6.B5L.HOUSE.HUB.LTCB.S | U=D, Q=C | A,T, with original AT | D3, C2, A4, T2 |
| M6.B5L.FAN.ENDPOINT.L234.S | U=1, Q=its genuine leaf L | J,2, with original J2 | 1(3), L1, J4, 2(3) |

In each row the two returned physical units lie strictly on U's side
of its original third support. This supplies a whole interface bound,
not a new equation at any returned loaded or higher-degree body.
For example the genuine four-force house hub A and fan hub J retain
all their original forces.

For both roof families there is also the root-level caller U=T,
Q=L and return pair A,D, provided the original TA,TD normals are
perpendicular axes of T. The actual triangle AD is present; the root's
genuine third leaf force is retained in full. Its conclusion concerns
the original leaf support line, not a fictitious circle load at T.

The lower TDC.D perpendicular interface used in the final lower-house
proof is a further literal example. The stronger tilted functional in
that caller is covered by Section 3 whenever its ratio F/E is at least
the full-star ratio nu/mu. That is why the geometric theorem handles
the entire nonnegative horizontal BA cone, rather than only an exactly
North normal.

No full open family in the table is closed from the present theorem
alone. Other actual normal-owner/angle interfaces remain, and a caller
seeking contradiction must still supply a physical contact across the
proved strict half-plane or another exact obstruction. In the two roof
rows the actual A,C contact is absent and must not be invented. At the
fan inner root and fan hub, true degree four forbids using Section 1;
Section 5 is conditional on its additional full aggregate-moment premise.

## 7. Dependency boundary and exact source pins

Sections 1--5 are self-contained Euclidean unit-square geometry and
the displayed original full force and torque equations. They use no
selected generic-normal convention, physical circle classification,
loaded-tip concurrence, containing radius, numerical calculation or
finitary parameter cover.

| Source | SHA256 | Exact role |
| --- | --- | --- |
| LOWER_HOUSE_TDC_D_POSITIVE_ROOT_MOMENT_AND_FINAL_RELAY_EXCLUSION.md | e5368cd0761d4f10a203272a0df4fc695604318cfe478d4076cad7c7771a0aef | Provenance of the weak one-return relay; its proof is reproved here with strict endpoint handling and both directions |
| FIVE_BODY_BLOCK_LEAF_GRAPH_LOAD_COVER.md | e5c84071363e8dc43b09f9033c7cb3a7684f1de19bcd169d53c9eab55d51963b | Actual original graphs, load sets and true degrees for the conditional interface table |

Every original shared-side mean, endpoint, support owner, positive
force and possible physical zero-weight contact remains. No complete
neighbor equation is replaced by a smaller star. No Lean compilation,
CI, workflow, sampled pose, computational certificate, metadata edit or
remote operation is used.

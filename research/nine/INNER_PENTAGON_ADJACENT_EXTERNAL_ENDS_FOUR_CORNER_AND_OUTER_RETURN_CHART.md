# Adjacent externally owned pentagon ends force four strict hub corners

Date: October 28, 2026 UTC. Author: pentagon_owned continuation.

**Status: complete proposed radius-free necessary chart, frozen for
separate full independent and root review.** The complete H4 force
equation and actual unit contact geometry force the original HB and
HC normals to the two remaining strict hub corners. No embedding or
cyclic-normal order is assumed. Every axis endpoint is included in
the preliminary support cover.

After the separately complete same-axis exclusion, each true unloaded
end has a strict downward outer return, one fixed actual outer corner,
and a finite concurrence point in that same actual endpoint square.
The chart preserves the full original perpendicular inner-side means.
It is a necessary chart for the surviving adjacent-end class; it is
not a contradiction or a closure of the original L124 family.

## 1. Exact original physical setting

Keep the original nine actual units and the positive graph

    HA, HB, HC, HD, AB, BC, CD, DE, EA,

with H genuinely unloaded of true degree four and A,D genuinely
unloaded of true degree three. Their full neighborhoods remain
N(H)={A,B,C,D}, N(A)={H,B,E}, N(D)={H,C,E}. Every force, selected
normal, original application or full shared mean, original torque,
physical circle mask and degree at all other units remains.

Assume A genuinely owns HA and D genuinely owns HD, with the actual
H vertices in the relative interiors of their respective sides.
Both original H normals strictly expose their actual H vertices.
Assume these vertices are adjacent. Normalize the entire actual
own chart of H, with a whole reflection if needed, to

    H=[0,1]^2,
    P_HD=(0,0), P_HA=(1,0),
    F_HA=Gamma_A*(u,-v),
    F_HD=Gamma_D*(-p,-q),
    u,v,p,q>0, u^2+v^2=p^2+q^2=1,
    Gamma_A,Gamma_D>0.                               (1)

The original labels are fixed; only the entire physical chart has
been moved. All scalar components below include original positive
force magnitudes unless explicitly called unit directions.

## 2. No third actual unit can contain either side-owned H corner

We first prove the local geometric fact used in the feature cover.
Suppose an actual unit K has a vertex P in the relative interior of
an actual unit L side. Suppose the unique separating normal at that
L side strictly exposes the vertex P of K. Then no third actual
unit with disjoint open interiors can contain P.

In a sufficiently small disk about P, the open interior directions
of L form an open half-plane of angle pi. The two inward edge
directions of K have strictly negative dot product with the normal
from K into L, because that normal strictly exposes P. Therefore
the closed right-angle tangent sector of K lies strictly inside
the complementary open half-plane, except for its apex P. Its
two boundary rays each have positive angular distance from the
boundary of that complementary half-plane.

The complement of these two occupied open sectors has two connected
angular pieces. Each has angle strictly less than pi/2: together
they have angle pi/2, and each has strictly positive angle. Any
third closed unit containing P has a connected tangent sector with
angle at least pi/2, with a two-dimensional open interior sector.
That sector cannot fit into either complementary piece; it cannot
cross an occupied piece without open-interior overlap. This proves
the claim, including closed edge directions. A third unit containing
P as an interior or side point requires a still larger sector and
is also excluded.

Apply this fact at both points in (1). Neither B nor C can contain
either lower H vertex. Consequently no original strict HB or HC
normal can expose either lower H vertex. Their own-axis means
remain unrestricted at this stage and are not replaced by corners.

## 3. The full feature cover forces B Northeast and C Northwest

At H, the actual H-A-B triangle excludes a North or West HB axis:
either has negative dot product with the strict Southeast HA normal
in (1). This is the complete owned-axis triangle implication, with
the HB axis owned by H. Its proof applies to every physical side
contact and original mean.

A strict Northwest HB normal is also impossible: that would put A
and B at opposite strict corners of H, where two actual unit
neighbors cannot touch. For completeness, a strict Southeast
neighbor of H lies in x>0,y<1 by the unit strict support-reach
bound; a strict Northwest neighbor lies in x<1,y>0. Any common
point would be in the open H, which is impossible even for a
boundary point of another actual closed unit with disjoint open
interior. The unit support-reach theorem covers arbitrary external
frames and support features.

The two lower strict corners have already been excluded by Section 2.
Thus the full nonzero HB normal cover is exactly the following
three possible classes:

    strict Northeast; East axis; South axis.           (2)

The symmetric actual H-C-D triangle, using the strict Southwest HD
normal in (1), gives the complete HC cover

    strict Northwest; West axis; South axis.           (3)

All four strict corners and all four own axes have been accounted
for in each table. Original means in the surviving axis rows of
(2)--(3) are retained in their full closed intervals.

Both end forces in (1) have strictly negative y components. The
unchanged full H4 y equation therefore gives

    (F_HB)_y+(F_HC)_y=Gamma_A*v+Gamma_D*q>0.            (4)

At least one of HB,HC is in its strict upper row. If HB is strict
Northeast, the actual H-B-C triangle excludes both remaining HC
axes in (3): West and South each have negative dot product with
that strict HB normal. Therefore HC is strict Northwest. If HC
is initially the upper row, the same triangle excludes East and
South HB, giving strict Northeast. No assumption about center or
normal cyclic order is used.

Consequently every original H application is a distinct actual
vertex, and the exact complete H chart is

    P_HA=(1,0), P_HB=(1,1),
    P_HC=(0,1), P_HD=(0,0),
    F_HB=(e,f), F_HC=(-g,h), e,f,g,h>0.                (5)

This conclusion removes every HB/HC shared-side feature by its
actual original normal and geometry. It does not relabel a shared
mean as a vertex or choose a new normal.

The entire H4 force and torque equations now give the exact
identities

    e-g=Gamma_D*p-Gamma_A*u,
    f=Gamma_A*(v-u)+Gamma_D*p>0,
    h=Gamma_A*u+Gamma_D*(q-p)>0.                       (6)

Indeed the torque about (0,0) is
-Gamma_A*v+f-e+g=0; combining it with both full force coordinates
gives (6). All four original magnitudes remain positive.

## 4. Entire A-side pose and the complete inner-return cover

Put

    n=(u,-v), j=(v,u), det(n,j)=1,
    P=(1,0),
    A=P+[0,1]n+[-rho,1-rho]j,
    0<rho<1.                                          (7)

These are the complete actual A pose and actual HA-side parameter.
The H-A-B triangle and A's own AH axis give

    F_AB=-alpha*n+beta*j, alpha>=0.                   (8)

The strict Northeast HB support at (1,1) makes the whole actual B
lie strictly in y>0, by strict unit support reach in direction South.
If beta<0, every maximum-F_AB support point of A in (7) has tangent
coordinate -rho. Its normal coordinate tau is zero if alpha>0 and
can range over [0,1] if alpha=0. Every such actual point has height

    -tau*v-rho*u<0,

contrary to its belonging to B. Thus beta>=0.

If beta=0, nonzeroness of the original AB vector forces alpha>0.
Its axis is exactly the same A axis as AH. This is precisely the
whole same-axis row excluded by the separately complete
INNER_PENTAGON_TWO_UNLOADED_ENDS_SAME_AXIS_RETURN_COMPLETE_EXCLUSION,
after the original graph reflection exchanging A,D and B,C.

After that complete source is separately reviewed and adopted,
the remaining exact domain therefore has

    beta>0,
    P_AB=P+tau*n+(1-rho)j,
    0<=tau<=1,
    alpha>0 implies tau=0.                            (9)

For alpha=0 this retains the entire original perpendicular-side
mean, including either support endpoint before the full torque is
used. No physical shared AB interval is assumed to be a singleton.

The original full A3 force equation gives

    F_AH=-Gamma_A*n,
    F_AE=(Gamma_A+alpha)n-beta*j.                     (10)

Both own components in F_AE are strict, so its actual A support
is exactly the fixed outer corner

    T_A=P_AE=P+n-rho*j
       =(1+u-rho*v,-v-rho*u).                         (11)

In particular the original AE normal and the actual AE point both
have strictly negative world y components. AE is a physical
singleton on A; this conclusion follows from its two strict
components and does not restrict its owner at E.

The complete original A3 torque about P is

    beta*(1-tau)=alpha+rho*Gamma_A>0.                  (12)

Hence the endpoint tau=1 is impossible, while tau=0 and every
other original allowed mean are retained. No term of the A3
torque has been discarded.

## 5. Exact genuine A3 concurrence inside the same actual A

Define the scalar

    lambda=tau+alpha*(1-rho)/beta
           =1-rho*(Gamma_A+alpha)/beta.               (13)

If alpha=0, (9) and (12) give lambda=tau in [0,1).
If alpha>0, tau=0 and beta=alpha+rho*Gamma_A, giving

    lambda=alpha*(1-rho)/(alpha+rho*Gamma_A) in (0,1).

Thus in every actual case

    0<=lambda<1, Q_A=P+lambda*n in A.                 (14)

It lies on the original AH force line, and direct substitution
of (9)--(13) yields

    P_AB-Q_A=((1-rho)/beta)*F_AB,
    T_A-Q_A=(rho/beta)*F_AE.                           (15)

Both multipliers in (15) are strictly positive. These are exact
concurrence identities of the full original A3 system; Q_A is an
actual point of that same A. It is not an original application
replacement. If lambda=0 it is the original HA side point; if
lambda>0 it is an actual interior point of A.

No statement about the loaded E's concurrence follows from (15).
In particular no boundary-neighbor hypothesis for E2 is introduced.

## 6. The complete reflected D chart

Use the upward-left tangent k=(-q,p), so det(n_D,k)=-1, and write

    D=[0,1]n_D+[-kappa,1-kappa]k,
    n_D=(-p,-q), 0<kappa<1.

The same physical support cover, whole same-axis exclusion and
complete D3 give unchanged parameters

    F_DH=-Gamma_D*n_D,
    F_DC=-alpha_D*n_D+beta_D*k,
    F_DE=(Gamma_D+alpha_D)n_D-beta_D*k,
    alpha_D>=0, beta_D>0,
    P_DC=tau_D*n_D+(1-kappa)k,
    0<=tau_D<1,
    alpha_D>0 implies tau_D=0,
    beta_D*(1-tau_D)=alpha_D+kappa*Gamma_D.             (16)

Although this own tangent orientation reverses determinants, the
whole torque equation has the same zero after multiplying it by
-1; (16) is the exact reflected form of (12).

Its unchanged outer contact is the strict D vertex

    T_D=P_DE=n_D-kappa*k
       =(-p+kappa*q,-q-kappa*p).                       (17)

The original DE vector and this actual point have strictly negative
world y components. Its genuine concurrence point in the same D is

    Q_D=lambda_D*n_D,
    lambda_D=tau_D+alpha_D*(1-kappa)/beta_D in [0,1),
    P_DC-Q_D=((1-kappa)/beta_D)*F_DC,
    T_D-Q_D=(kappa/beta_D)*F_DE.                        (18)

All original CD means and complete D3 terms remain. The proof has
not used any force, torque, load or physical boundary property at
B,C,E, nor a containing radius.

## 7. Exact surviving scope

Sections 2--3 give the full four-strict-corner H chart from adjacent
external end ownership alone, at every original HB/HC support
feature. They do not depend on the pending same-axis source.

Sections 4--6 retain beta=0 explicitly before using that entire
pending source. Once its full review and root adoption are complete,
they give the two strict downward outer returns, exact fixed outer
corners, all perpendicular inner-side means, and proper original
endpoint concurrence identities above.

The actual E must contain both T_A and T_D in (11),(17), with its
two original inward support directions given by (10),(16). The
actual B,C still touch and keep their full original equations.
Those are genuine remaining conditions, not contradictions asserted
by this chart. Neither finite concurrence nor a circle mask is
assumed for E. No original whole L124 or coarse flag closes here.

## 8. Exact sources and preservation

| Source | SHA-256 | Exact role |
| --- | --- | --- |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 | Complete degree-free own-axis triangle and strict whole-unit support reach, every actual mean |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Complete original force, torque, normal, support and mean contract |
| INNER_PENTAGON_TWO_UNLOADED_ENDS_SAME_AXIS_RETURN_COMPLETE_EXCLUSION.md | 06db7377d2f6818fd73c9e684a64fd1b9691a051c0303721d41e96d225f85fd0 | Whole same-axis beta=0 exit at both genuine unloaded ends; pending separate complete review and root adoption |
| SIX_BODY_INNER_PENTAGON_LOAD_COVER.md | cfe85a201b09182200d5270f0dcdc0e590bf99eded19aaf6d56f86830e959c0a | Literal original graph, true H4/A3/D3 roles and permitted full graph reflection |

All new local-sector, quadrant and scalar arguments are printed in
full. No original term, normal, mean, circle corner, individual zero
coefficient, actual square or true degree is removed. The two Q points
are used only for exact concurrency identities and are not substituted
for original applications. No angle sample, numerical pose search,
computational geometric certificate, Lean/Lake run, old checker replay,
CI, workflow, original flag/count change, source repinning, commit or
remote operation is used. These exact new bytes require separate full
independent review and root adoption.

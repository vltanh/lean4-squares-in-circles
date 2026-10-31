# A free strict roof is excluded at both shared and perpendicular D-owned AD

**Date:** October 31, 2026 UTC. **Complete hand theorem for the original
common selected certificate.** Input PR #11 head:
`d896360d49bbdae72567ebe43fee939366ab2c20`.

The full A3,D3 force equations and full V2 torque impose one proper
polynomial condition on the free AV normal. The already established
common choice of algebraically independent physical normal parameters
avoids this condition. The factor contains no shared-side application
mean or unknown multiplier.

This excludes the entire mixed free/owned strict-roof feature with
physically shared AD, and the entire mixed free/owned feature with
genuine D-owned AD perpendicular to DV. Every N type, N load, endpoint
physical circle mask, individual zero coefficient, exterior degree,
and original shared mean is retained. These are conclusions about the
common certificate selected before extraction, rather than physical
infeasibility for every arbitrarily chosen stress normal.

No new normal is chosen after extraction. The universal algebraic
choice used here is already the explicit choice in Sections 1 and 8
of the common-domain theorem cited below. Sections 2--3 of this source
give the exact physical prelist and nonidentity proof for this factor.

## 1. The unchanged common normal domain

The operative input is
[GLOBAL_COMMON_NORMAL_DOMAIN_AFTER_FORCE_FREE_C7_AND_ALGEBRAIC_SELECTION_2026_10_29.md](GLOBAL_COMMON_NORMAL_DOMAIN_AFTER_FORCE_FREE_C7_AND_ALGEBRAIC_SELECTION_2026_10_29.md).
Its exact clauses needed here are:

* Section 1 fixes every actual unit, frame, circle corner and physical
  contact before choosing normals. Its generic-selection theorem chooses
  the genuine normal half-angle parameters algebraically independent
  over the countable field of fixed physical data, and extracts one
  certificate satisfying all proper polynomial avoidances.
* Section 3 identifies the actual independent variables. The two opposite
  pairs at one four-unit junction share one parameter. A physical
  singleton at a different point cannot use that same junction parameter.
  Genuine side-owned singletons and physical shared segments have fixed
  geometric side normals and add no free normal variable.
* Section 8, Lemma 8.1, avoids every nonzero polynomial in the genuine
  parameters after the actual matching substitutions. The coefficient
  field includes fixed positions, frames, circle data and algebraic
  quantities computed from those data. It excludes unknown multipliers
  and variable shared-side means.
* Section 10 chooses the normals once before multiplier extraction.
  Uncrossing preserves every surviving physical singleton normal and
  adds only actual shared-side endpoint atoms. Thinning changes no
  surviving normal. Shared aggregation keeps the original full segment
  and its actual coefficient-dependent mean.

We invoke that universal choice as already specified. For a construction
using the optional finite version instead, Section 8 Corollary 8.2
permits the finite geometric prelist below to be included together with
the prior proper factors **before** the one extraction. Its finite
product is nonzero by the same nonidentity proof. That alternative does
not license changing an already extracted normal or adding an unknown
mean to the coefficient field.

## 2. A finite physical prelist and a full-star determinant lemma

Prelist all ordered five-tuples (A,D,V,B,C) of distinct actual units,
all relevant actual physical contact features, and actual signed own
axes k,g with det(k,g)=-1 satisfying the following fixed geometry.
There are only finitely many unit labels, physical features and signed
axes. No future positive degree, circle coefficient or force magnitude
is used in making this list.

The AV contact is a physical vertex/vertex singleton at the fixed point
P, with a genuine free normal parameter h. The DV contact has fixed
normal k from D and actual application Q. The AD contact has fixed
normal g from A, with g perpendicular to k; it may be a genuine
D-owned singleton or a positive-length physical shared side. Its
eventual aggregate mean remains arbitrary.

The other directions are b from A to B and -cvec from D to C. They
are either actual fixed owner directions or strict physical singleton
normal parameters. In the prelisted geometric vertex cones their
components obey

    b_k=b.k<0, b_g=b.g<0,
    c_k=cvec.k>0, c_g=cvec.g<0.                      (1)

Their physical singleton points, when free, differ from P. A variable
shared mean is allowed on an exterior contact with fixed owner normal;
no such mean is a coefficient in the factor below.

The geometry also satisfies

    p=P.k>0, y=P.g, B0=det(Q,k)=Q.g>0.              (2)

These are predicates on fixed physical points and frames. The two
literal charts in Sections 4--5 establish all of them, including (1)
through the complete physical support cones and all required point
distinctness. The appropriate positive-star pattern is tested only
after the certificate has been extracted.

Suppose a resulting certificate had precisely the original positive
neighborhoods

    A:{V,D,B}, D:{V,A,C}, V:{A,D},

with A,D unloaded. Let the unchanged positive magnitudes of AV,DV,AD,
AB,DC be mu,nu,gamma,lambda,eta. Write the original free direction as

    h=J k+H g.

The two complete unloaded force equations are

    mu*h+gamma*g+lambda*b=0,
    nu*k-gamma*g-eta*cvec=0.                        (3)

Every radial circle force at V has zero moment about O. Its full
two-pair torque, including its full original physical circle mask and
all individual coefficients, is consequently

    mu*A0=nu*B0, A0=-det(P,h)=-yJ+pH.              (4)

Equations (3)--(4) contain all pair forces at A,D,V; no third force at
one of these bodies has been omitted. Other body equations and the
original A,D torques remain unchanged and are simply not needed for
this necessary contradiction.

The k,g components of the second equation in (3) give

    gamma/nu=-c_g/c_k.

Eliminating lambda from the first gives

    gamma/mu=(b_g/b_k)J-H.

The denominators here are nonzero by (1), and the magnitudes are
the original positive ones. Eliminating mu,nu,gamma with (4) now
gives the exact necessary polynomial condition

    F:=B0*c_k*(b_g*J-b_k*H)+b_k*c_g*A0=0.          (5)

Equivalently, direct multiplication of (3)--(4) gives (5) without
dividing by A0. Thus a possible zero of A0 was not discarded. In
an alleged positive realization (4) in fact gives A0>0.

The fixed-geometry expansion of (5) is

    F=(B0*c_k*b_g-b_k*c_g*y)*J
       +b_k*(-B0*c_k+c_g*p)*H.                     (6)

This is polynomial in the actual normal components h,b,cvec, with
coefficients in the fixed physical-data field. It contains no force
magnitude, unknown circle split, AD mean, or exterior shared mean.

## 3. Properness after every actual junction matching

Fix temporarily any permitted values of the b,cvec parameters, if
they are free. This is only a nonidentity proof, not a normal choice
after extraction. The coefficient of H in (6) is strictly positive:

    b_k*(-B0*c_k+c_g*p)>0.                          (7)

Indeed b_k<0, B0>0, c_k>0, c_g<0 and p>0. Thus F is a nonzero
linear functional of the two coordinates J,H of h. Such a functional
cannot vanish on any nonempty open unit-circle arc.

The free AV parameter belongs to the physical singleton P. Matching
at a four-unit junction can determine one other normal at that same
P, but it never identifies this parameter with a free singleton
normal at a different point. The latter normals here are the possible
b,cvec normals; Section 2 required their physical points to differ
from P. Fixed owner directions introduce no parameter at all.
Therefore varying the genuine AV parameter varies h on an open arc
while the b,cvec coordinates in (6) stay fixed. If an unused opposite
pair at P changes simultaneously, its normal does not occur in F.
Every retained nondense preference merely shortens the already
compatible open interval supplied by the common-domain theorem.

After the actual matched substitutions, express all free normals in
the rational half-angle charts of that theorem and clear their
positive denominators 1+t_i^2. If the resulting polynomial were zero
identically, the linear functional (6) would vanish for every h on
the just described open arc. This contradicts (7). Thus the correctly
substituted polynomial is nonzero over the fixed physical-data field.

Lemma 8.1 of the existing common-domain theorem therefore gives F!=0
on the already selected common normal tuple. This contradicts (5).
The finite-before-extraction version gives the identical conclusion
by multiplying these finitely many nonzero factors with the previously
required proper factors inside the same nonempty open domain.

The conclusion is valid after uncrossing and thinning. The alleged
positive AV, AB and DC physical singletons retain their selected
normals. Any fixed shared normal remains fixed when actual endpoint
atoms are added or its original full mean is aggregated. The eventual
true A3,D3,V2 equations are exactly (3)--(4). No mean was frozen, no
force was deleted, and no post-extraction selection occurred.

## 4. Complete mixed free-roof entry with physically shared AD

Use the entire physical derivation of Section 1 in
[TWO_STRICT_FREE_ROOF_SHARED_AD_COMPLETE_DIAGONAL_EXCLUSION_2026_10_31.md](TWO_STRICT_FREE_ROOF_SHARED_AD_COMPLETE_DIAGONAL_EXCLUSION_2026_10_31.md).
Before that source invokes any N hypothesis it gives

    V=[d,d+1] times [-1/2,1/2],
    P=(d,1/2), Q=(d,-1/2),
    k=(C,S), g=(S,-C), C,S>0, C^2+S^2=1,
    A=P-[0,1]k-[0,1]g,
    D=Q-[0,1]k+[-C,1-C]g,
    K=P-k-g,
    L=P-(1+S)k+g.

AV is the original free singleton at P. DV is genuinely D-owned
at Q. AD is the original positive-length shared side with fixed normal
g and complete mean W=P-t k, S<=t<=1. Its entire mean is still
retained; no eventual endpoint mean is relabeled a singleton.

The full A,D forces strictly expose K and L, respectively. Thus the
physical AB and DC intersections are actual singletons there, and
their allowed original normals lie in the strict A,D vertex cones

    b_k,b_g<0, c_k>0,c_g<0.

An exterior normal may be free or owned by its actual exterior unit;
both possibilities are allowed by Sections 2--3. This is a geometric
contact/owner distinction, with no imposed physical circle mask at B,C.

The free AV point is different from every other relevant point:

    |P-Q|=1, |P-K|=sqrt(2),
    |P-L|^2=(1+S)^2+1>2.

Also K-L=S k-2g is nonzero. Consequently no exterior free normal
can share the matched four-unit-junction parameter of AV. P is not
on the shared AD segment: its k coordinates end at P.k-S<P.k.

Finally

    p=P.k=dC+S/2>0,
    y=P.g=dS-C/2,
    B0=Q.g=dS+C/2>0.

Every coefficient and prelist predicate is fixed by the original
physical geometry. Applying Sections 2--3 excludes the whole shared-AD
mixed free-roof chart. No endpoint ownership, circle mask, N direction,
N load, or completion-capacity assumption is left over.

## 5. Complete mixed free-roof entry with genuine perpendicular D-owned AD

Use the full chart preceding all N assumptions in Sections 1--2 of
[TWO_STRICT_FREE_ROOF_OTHER_HUB_PERPENDICULAR_COMPLETE_DIAGONAL_EXCLUSION_2026_10_31.md](TWO_STRICT_FREE_ROOF_OTHER_HUB_PERPENDICULAR_COMPLETE_DIAGONAL_EXCLUSION_2026_10_31.md).
In its notation,

    P=(d,1/2), Q=(d,-1/2),
    k=(C,S), v=(-S,C), g=-v,
    h=J k-H v=J k+H g,
    u=-a k-w v, b=-w k+a v,
    a,w>0, a^2+w^2=1.

The genuine AD normal from A is -v=g, owned by D. DV has the
fixed D-owned normal k. The full A force makes AB physically shared
with the fixed own normal b. Its entire original application is

    K=P+b+t u, 0<=t<=1.

No value of t is selected here. The entire shared contact side has
distance at least one from P, since |b+t u|^2=1+t^2. The actual
AD singleton and exterior DC singleton are

    W=P+u,
    L=P-(1+S)k-(1+w)v.

DC is genuinely C-owned with cvec=c_k k+c_v v, c_k,c_v>0.
In the present k,g frame this is c_k>0,c_g=-c_v<0, while
b_k=-w<0,b_g=-a<0. Thus (1) holds, and both exterior
directions in this literal entry are fixed geometric owner normals.

All relevant contacts are separate from the free AV point:

    |P-Q|=1, |P-W|=1, |P-K|>=1,
    |P-L|^2=(1+S)^2+(1+w)^2>2.

The shared AB mean is absent from the factor; its full segment and
both endpoints remain. No variable mean is treated as a fixed
coefficient or assigned a free normal parameter. The values p,y,B0
are exactly the same positive geometric values as in Section 4.

For comparison in this source's original v notation, condition (5)
is, up to the nonzero sign used for b_k,

    B0*c_k*(a*J-w*H)-w*c_v*A0=0,
    A0=(P.v)*J+(P.k)*H.

Its H coefficient is -w*(B0*c_k+c_v*(P.k))<0, the same
nonidentity as (7). Thus Sections 2--3 exclude this entire genuine
perpendicular other-hub-owned feature as well. The original N and
both full exterior stars are unrestricted by this factor.

## 6. Whole-feature consequence and exact limits

Within the common selected physical certificate, neither original
two-strict mixed free/owned-roof chart treated here survives. The
conclusion covers both D02.L135 and D02.L1345, with their original
true degrees and every physical circle mask, and covers the reflected
free-D-roof cases by reflecting the entire data and exchanging roles.

The result does not require a side/diagonal classification of N. In
particular it closes the side-N remainders of both cited chart sources,
as well as their previously excluded diagonal alternatives. In the
shared chart it also subsumes, at this common-certificate scope, the
separate physical-two endpoint-mask exclusion.

The same-axis genuine D-owned AD feature, other original roof-owner
features and the both-owned strict-roof chart are separate. They are
not called instances of a perpendicular fixed-axis determinant. No
whole D02 row or unrestricted nine-square theorem is declared closed
by this source alone; the original feature cover must perform its
explicit remaining joins.

All nine actual units, original positive edges, side endpoints,
circle coefficients and unknown means remain. This proof applies
the existing universal pre-extraction choice and proves its full
properness and transfer at the actual physical patterns. It uses
hand force/moment elimination and an elementary nonzero-polynomial
argument, with no numerical certificate, external proof script,
Lean compilation or CI.

# Fresh independent review of the restored coincident-port star theorem

Date: October 28, 2026 UTC. Reviewer: pentagon continuation.

## Decision and source identity

**PASS at the full stated arbitrary-degree scope.** I freshly read and
checked the entire restored manuscript, all five direct sources listed
below, and every operative physical and literal graph premise. This is
a new review. It is not an exact-byte recovery of the lost review
4a464e42392f95cac4573751e7ee48964769164f1cf8da706ed7080ea7e31f78.

| Source read in full | Exact SHA-256 |
| --- | --- |
| LOADED_COINCIDENT_PORT_STAR_NO_BOUNDARY_NEIGHBOR.md | 18ad8dbde48a1c0ef6828ef199a321c54218e5ba3c39c4047025783ffb63bb83 |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 |
| TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md | 29e38d3f641fe16c6db587e51245f92ad4c447f9536db7d14c221f56b5357e82 |
| GENERAL_FIXED_TIP_NORMAL_SELECTION.md | ef8ae8a219af9fa15a70698e485bbb337925e5caf2cd64b6b5c2619d9c4bd194 |
| GENERAL_SINGLE_HUB_BOUNDARY_PATH_POCKET.md | 958bb122342783a824d023c221ccc2c93a68300b00b0ffc3496c25ad394aec84 |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 |

The physical-stress source supplies the unchanged force, origin-torque
and supporting-normal conventions, including aggregation on an actual
shared segment. The proper-concurrence and selector sources are used
only for the stated scope comparisons. The pocket and graph sources
supply the literal endpoint degrees and loaded neighbors. No geometric
exclusion from those comparison sources is needed in the new central
argument.

## 1. Full equilibrium gives the radial minimum support

For every actual circle corner Z of V, both Z and the unchanged common
application P belong to V, so their distance is at most sqrt(2).
The identity

    2P.Z=|P|^2+R^2-|Z-P|^2

therefore makes P.Z strictly positive when R>3/2. Positive total
circle load makes P.m>0, even if an individual physical corner has
zero coefficient.

The full force and torque equations give det(P,m)=0. The positive
dot product selects the positive collinear direction, so P=p e with
p>0 and e=m/|m|. Summing all actual support inequalities with their
positive original weights gives e.(X-P)>=0 for every X in V.
No individual pair normal has been replaced by e. This verifies the
essential use of the complete star at arbitrary degree.

## 2. Nonaxis support and diameter equality

When e is not an own side axis, the actual minimum P is one vertex.
In its inward square axes u,v, both components of P=p e are positive.
The farthest corner is therefore uniquely P+u+v. It is the sole
physical circle corner and the positive resultant is radial through it.
Consequently u+v=sqrt(2)e and P=(R-sqrt(2))e.

For another physical boundary unit W containing P, a circle corner
Z_W satisfies

    R<=|P|+|Z_W-P|<=R.

Both inequalities must be equalities. Because |P|=R-sqrt(2)>0,
triangle equality forces Z_W-P to be in the positive P direction;
the unit diameter equality forces its length to be sqrt(2).
Thus Z_W is exactly the same outer diagonal corner R e of V.

The maximum possible distance sqrt(2) in a unit square occurs only
between opposite vertices. The two points P and R e therefore are
opposite vertices of W as well as V. A diagonal with both endpoints
fixed determines the unit square uniquely: its center is their midpoint,
and the other two vertices are that center plus or minus one half of
the ninety-degree rotation of the diagonal. Hence W=V, contradicting
the distinct interior-disjoint bodies.

This checks both equality steps; a merely non-strict distance estimate
would not suffice.

## 3. Own-axis support, original endpoints and all circle masks

In the own-axis case the actual square has the form

    [p,p+1] times [b,b+1], -1<=b<=0,

because the original P=(p,0) lies on its inner face. The outer face
has strictly larger squared radius than the inner face since p>0.
If b+1/2 has either strict sign, the unique farthest corner has that
same nonzero second-coordinate sign. The loaded resultant could not
be parallel to e. Therefore b=-1/2.

This establishes the centered physical two-corner square and forces
equal circle coefficients; both coefficients are positive because
their sum is positive. In particular an initial side endpoint for P
has been ruled out by the actual equations, rather than omitted.

The derived P is in the relative interior of the inner side. Any
distinct interior-disjoint W containing it lies wholly in the opposite
closed half-plane. Indeed, a segment from P to a point of W on the
other side would immediately enter the open interior of V. A point
of a closed unit in that open set implies open-interior overlap,
because the interior of a square is dense in the square.

Writing d=p=sqrt(R^2-1/4)-1, every physical circle corner of W
then has squared distance from P at least

    R^2-d^2=2d+5/4>2.

The final strict inequality uses d>sqrt(2)-1>3/8. This contradicts
the unit diameter. The argument requires no selected force, weight,
degree or circle-resultant direction for W.

The axis/nonaxis split exhausts all unit directions e. It therefore
covers the whole original contact-feature and mask domain.

## 4. Corollaries and exact limits

If a true loaded V2 with an actual physical boundary neighbor had
coincident original pair applications, that neighbor would contain the
common point. The proved arbitrary-degree theorem excludes it.
This is an exact consequence for the unchanged pair means, including
a mean at a side endpoint.

For the original D02.L01345 row, the six cycle edges and chord02
give V=1 the true pair neighborhood {0,2} and T=3 the true pair
neighborhood {2,4}. Their loaded boundary neighbors are respectively
0 and 4. Both endpoint substitutions are valid, with no equation
deleted at the degree-three hub2.

The general boundary-path source likewise has actual true degree-two
endpoints and an actual boundary neighbor along the path. Its internal
vertices retain their true degrees. The new theorem's argument does not
need the pocket-capacity conclusion of that source.

I also checked the two stated restrictions. Distinctness on V does
not imply that two applications on U are distinct: a physical shared
segment can have a different original mean. Nor does it make a variable
shared mean into a fixed physical singleton required by the selector.
The selector's radial-diagonal exception remains possible outside the
additional physical-boundary-neighbor premise.

The proper-concurrence lemma is not contradicted: its coincident case
was retained safely, and the new theorem supplies a stronger strict
exclusion at the stated common physical-neighbor scope.

## 5. Accounting boundary

This PASS covers all positive star degrees, all original normal owners,
all aggregate means and endpoints, all physical circle masks and all
individual zero corner weights, with only R>3/2 as radius hypothesis.
Every other unit and positive force remains.

It certifies a uniform local theorem and its literal corollaries.
It does not close a whole original fine family or coarse gate.
No Lean compilation, CI, sampled geometry, altered normal, fake leaf
or numerical exclusion certificate was used.


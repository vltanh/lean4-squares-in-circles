# A loaded unit with one common positive-force application cannot share that point with another boundary unit

Date: October 28, 2026 UTC. Author: cycles continuation.

**Status: complete proposed uniform hand theorem, submitted for root and separate independent review.** The theorem has no upper-radius, degree, normal-owner, mean, graph-size or completion hypothesis. Its only radius premise is R>3/2. It retains the full original force and torque systems and covers every physical circle mask, including zero individual corner coefficients.

In particular every true loaded degree-two unit with a physical boundary neighbor has two distinct original pair-force applications. This removes the coincident-application alternative at that exact scope without assigning a genuine leaf or deleting an edge.

## 1. Exact physical theorem

Let V be an actual closed unit square contained in the unchanged disk D_R, with

    R>3/2.

Retain its original positive total circle load and all of its actual positive pair forces. Their number may be any positive integer. Suppose every one of their original application points or aggregate side means is one same actual point P in V. The unchanged full equations are

    m+sum_i mu_i*n_i=0,
    sum_i mu_i*det(P,n_i)=0,
    mu_i>0,
    m=2*sum_j lambda_j*Z_j,
    lambda_j>=0, sum_j lambda_j>0, |Z_j|=R.           (1)

Each original n_i is an outward unit normal of V supporting it at the same actual P. Every physical circle corner, including one with zero coefficient, remains part of the actual square. Additional zero-weight contacts and all other physical units remain arbitrary.

**Theorem.** No distinct actual unit W with disjoint open interior from V can both contain P and physically touch the same containing circle.

No equation or load premise is imposed on W. Its circle contact may have zero selected total weight. In particular a positive neighbor at the common application P cannot be a physical boundary unit.

The proof uses (1) in full. It does not replace the actual graph by a leaf, call a higher-degree body a transmitter, or change an original mean.

## 2. The full equations give an actual radial minimum support

For any actual physical circle corner Z of V,

    |Z-P|<=sqrt(2),

by the unit-square diameter. Hence

    2*P.Z=|P|^2+R^2-|Z-P|^2
          >=|P|^2+R^2-2>0,                         (2)

because R>3/2>sqrt(2). Summing with the original nonnegative circle coefficients gives

    P.m>0.

In particular P and m are both nonzero. The complete moment equation in (1), together with its full force equation, gives det(P,m)=0. Thus P is a positive multiple of m.

Put

    e=m/|m|, P=p*e, p=|P|>0.

For every original n_i and every actual X in V,

    n_i.(X-P)<=0.

Taking their positive weighted sum and using (1) gives

    m.(X-P)>=0,
    e.X>=p for every X in V.                        (3)

Therefore the actual P is the minimum-e support point of V, and the whole original circle resultant is in the direction e. This conclusion is proved from every force at once; no single original normal is asserted to be radial.

We now cover all actual support features of V for the unit direction e.

## 3. The complete nonaxis minimum-support case

If e is not an own side axis of V, its actual minimum support P is a unique V vertex. Choose the two actual inward orthonormal axes u,v there, so

    V=P+[0,1]u+[0,1]v,
    e.u>0, e.v>0.

Since P=p*e with p>0, both own coordinates of P are strictly positive. The unique physical farthest corner is consequently

    Z=P+u+v.

Every other V corner has strictly smaller norm, so Z is the sole physical circle corner. All of m is a positive multiple of this Z. But m is parallel to P; hence u+v is a positive multiple of e. Its norm is sqrt(2), and therefore

    Z=P+sqrt(2)*e=R*e,
    P=(R-sqrt(2))*e.                                (4)

This is a derived geometric classification of the same original square, not a new degree-one equation.

Suppose a distinct actual boundary unit W contains P. Choose any of its actual physical circle corners Z_W. Its unit diameter and (4) give

    R=|Z_W|
       <=|P|+|Z_W-P|
       <=R-sqrt(2)+sqrt(2)
        =R.

Every inequality is equality. Thus Z_W-P is a positive multiple of P, has length sqrt(2), and

    Z_W=R*e=Z.

The two actual points P and Z are distance sqrt(2) apart in W. In a unit square this maximum distance is attained only at opposite vertices. They are also opposite vertices of V. A pair of opposite vertices determines the unit square uniquely, so W=V, contrary to the distinct actual bodies and their disjoint open interiors.

This excludes every other physical boundary unit at P in the whole nonaxis case, independently of its degree, load, selected contact or force magnitude.

## 4. The complete own-axis minimum-support case, including side endpoints

Suppose e is an own side axis of V. In its actual frame e,Je, the minimum face in (3) has first coordinate p, and the unchanged square is

    V=[p,p+1] times [b,b+1],
    -1<=b<=0,

because its actual P=(p,0) lies on that whole face. This includes both possible side endpoints before the following force argument.

The first own center coordinate p+1/2 is strictly positive. Every physical circle corner is consequently on the outer face x=p+1. If b+1/2 were strictly positive, its unique physical circle corner would have positive second coordinate, and the second component of the positive circle resultant m could not vanish. If b+1/2 were strictly negative, the same argument gives a negative second component. Both contradict m=|m|*e.

Thus the entire physical and coefficient cover forces

    b=-1/2,
    V=[p,p+1]e+[-1/2,1/2]Je,
    P=p*e,
    R^2=(p+1)^2+1/4.                               (5)

The two actual circle corners are both retained. Their coefficients must be equal by the zero second component of m; this equality is a consequence of the full original equations, not a discarded individual-zero endpoint. In particular P has been proved to be in the relative interior of the inner side.

Write

    d=sqrt(R^2-1/4)-1=p.

Any other interior-disjoint actual unit W containing P lies entirely in the half-plane e.X<=d. Indeed, if one of its points had e projection greater than d, the open segment from P toward that point would enter the open interior of V immediately, since P is in V's side interior. A point of a closed unit in another unit's open interior yields open-interior overlap. This geometric half-plane assertion requires no selected positive force at that W contact.

Take any actual physical circle corner Z_W of W. By (5),

    |Z_W-P|^2
      =R^2-2*d*(e.Z_W)+d^2
      >=R^2-d^2
       =2*d+5/4.                                  (6)

But R>3/2 gives d>sqrt(2)-1>3/8, using sqrt(2)>11/8. Hence the right side of (6) is strictly greater than 2. This contradicts the squared unit diameter of W.

This excludes every other physical boundary unit at P throughout the whole own-axis domain. The possible endpoint locations in the initial face were ruled out by the actual circle resultant, not silently omitted.

Together Sections 3--4 prove the theorem.

## 5. True loaded-two-force corollary and literal broad uses

Let V have exactly two original positive pair neighbors, with positive total circle load, and suppose at least one of those two neighbors physically touches the containing circle. If its two original applications or side means coincided, that neighbor would be a distinct physical boundary unit containing the common P. The theorem gives a contradiction. Therefore

    P_1!=P_2.                                      (7)

This corollary holds for every original owner, free normal, shared-side mean and its endpoints, every physical one- or two-circle-corner mask, and either zero individual corner coefficient. It has no normal-selection premise.

It applies simultaneously to the two true endpoints of every actual single-unloaded-hub boundary-path component: each endpoint's other positive neighbor is a physical boundary path unit. The hub and every internal path unit keep their real degrees and forces. It also applies to every other true loaded degree-two unit satisfying that same literal neighbor premise, regardless of the rest of its graph.

For the original D02.L01345 component the literal endpoint substitutions are

| Actual loaded-two-force unit | Two actual positive neighbors | Physical boundary neighbor furnishing the premise |
| --- | --- | --- |
| V=1 | U=2, W=0 | W=0 |
| T=3 | U=2, 4 | 4 |

Thus the two actual applications on V are distinct, and the two actual applications on T are distinct. This statement covers the entire original normal/owner/mask domain, without assuming that the two U return normals agree.

No conclusion that U's own two return applications are distinct follows merely from (7): the actual VW contact can be a shared segment with a different mean even when several physical units contain one U vertex. Such an original coincident-U-port feature still needs its own full geometric join.

Similarly, the corollary does not by itself meet a fixed-tip selector's additional requirement of two fixed physical singleton points. If one actual application is a variable shared-side mean, that feature remains a shared-mean problem. A zero-weight physical circle contact at a purported boundary neighbor is sufficient, but an unloaded neighbor must not be assumed physically boundary without proof.

## 6. Relation to the accepted proper-concurrence theorem

The local Lemma 2.1 of TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md gives proper concurrence for a true loaded-two-force unit with a physical boundary neighbor. Its proof safely includes the coincident-application alternative. The new result proves that this alternative is actually impossible at that same physical-neighbor scope.

It does not invalidate the older lemma or alter any frozen source. All of its nonparallel-line and outward-ray conclusions remain available unchanged. The new theorem supplies an additional strict distinctness conclusion using the actual full equations.

The coincident radial-diagonal exception retained by GENERAL_FIXED_TIP_NORMAL_SELECTION.md is likewise not removed in arbitrary loaded-two-force settings: that selector allows situations without a physical boundary neighbor. The current result removes it only after the actual boundary-neighbor premise is established. No original normal or side mean is reselected.

## 7. Exact sources, self-contained proof and accounting boundary

The geometric and algebraic proof in Sections 2--4 is self-contained once the standard original physical force, torque and support equations (1) are given. The following pins record that original contract and the exact existing scopes compared above.

| Source | SHA256 | Exact use |
| --- | --- | --- |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Original full forces, radial circle atoms, common applications and actual supports |
| TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md | 29e38d3f641fe16c6db587e51245f92ad4c447f9536db7d14c221f56b5357e82 | Comparison with its local true-loaded-two-force properness lemma only; no step of the new proof assumes its coincidence case is absent |
| GENERAL_FIXED_TIP_NORMAL_SELECTION.md | ef8ae8a219af9fa15a70698e485bbb337925e5caf2cd64b6b5c2619d9c4bd194 | Exact selector-scope limitation in Section 6 only; no selector is used to prove the theorem |
| GENERAL_SINGLE_HUB_BOUNDARY_PATH_POCKET.md | 958bb122342783a824d023c221ccc2c93a68300b00b0ffc3496c25ad394aec84 | Literal complete boundary-path endpoint degrees and neighbors |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 | Literal original D02 labels, positive edges and loaded degrees |

This is one uniform local theorem and its whole-domain true-degree-two corollary. It does not on its own close an original fine family or coarse gate. Every actual unit, force, circle coefficient, original application and side mean remains.

No sample, angle mesh, computational pose certificate, artificial genuine leaf, force deletion, normal reselection, Lean compilation, CI, workflow, shared-ledger edit, commit or remote action is used.


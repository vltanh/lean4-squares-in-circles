# Independent review: physical radial-port annulus and both upper-root vertices

Date: October 27, 2026.  
Reviewer: rooted_final_review.  
Verdict: **Complete independent non-contributor PASS. No correction requested.**

## 1. Frozen target and whole reviewed domain

I read and reconstructed every section of the six-section target

    RADIAL_BOUNDARY_PORT_ANNULUS_AND_UPPER_ROOT_VERTICES.md
    SHA256 dd7adcc51f5696864ee6a551ba072d08ede39bddc5c8fb7af838446ddce19a59
    12,202 bytes.

I accept the entire physical annulus theorem, both distinct physical uniqueness tests, both complete genuine-leaf far-vertex rows, and the exact original normal-form application with its stated noncircular assembly boundary.

The main theorem has a substantially broader domain than the original nine-unit chart. C,H are distinct interior-disjoint unit squares in an origin-centered disk, C physically touches that circle, and

    R^2=(d+1)^2+1/4,       d>0.

The point P is an actual common point, and n is the actual unit normal directed H-to-C, so C has minimum n support at P and H has maximum n support there. If C has two physical circle corners and P·n>=0, then

    d^2<=|P|^2<=d^2+1/4.

No force, degree, contact ownership, generic normal selection, lower bound d>=1, or upper radius is needed. All actual shared means and all common supporting normals at a free vertex are retained. The conclusions concern physical circle corners, regardless of their individual stress weights.

I did not contribute proof arguments to this target. I had independently reviewed related local physical-C-mask and upper-corner arguments and communicated that this new result could help replace a missing global mask prerequisite. That is scope coordination, not authorship of the proof below. My separate positive-B-concurrence source is not a logical input to the physical theorem; the exact original application here retains the positive/nonparallel premises of its pinned normal form.

## 2. Complete source reads and verified pins

I read the complete target, all three complete present foundations, the complete fresh normal form, and its complete independent acceptance. I independently reconstructed the original rotation/reflection and both true leaf equations rather than relying only on an acceptance label.

| Exact source | Verified SHA256 | Scope actually checked |
| --- | --- | --- |
| RADIAL_BOUNDARY_PORT_ANNULUS_AND_UPPER_ROOT_VERTICES.md | dd7adcc51f5696864ee6a551ba072d08ede39bddc5c8fb7af838446ddce19a59 | All six sections and every theorem/corollary |
| C7_FORCE_POLYGON.md | d50d8ca48ea19156175e651bfa74be30ef3e58065ec14d8d1834670a41559089 | Entire source read; only its complete physical circle classification and unshareable-circle-point facts enter |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Actual normal directions, singleton/free/shared applications and unchanged physical means |
| RADIAL_BRIDGE_AND_LEAF_REDUCTION.md | faf453b3c519b10590cf9d6f6dbf9282233bd2ff04c90aa0cd8cd89e060bc676 | Entire source, especially actual radial S-leaf application and the occupied leaf's preserved physical meaning |
| POSITIVE_B_OWNED_ROOT_GENUINE_NEIGHBOR_NORMAL_FORM.md | 93cbef188a875c95b56f51498ebb6b55633da09f34ce311740f370e1586849ce | All eight sections, both actual H-leaf rows, x>0 and whole small-height bound without C uniqueness |
| REVIEW_POSITIVE_B_OWNED_ROOT_NORMAL_FORM_TOPOLOGY_INDEPENDENT_2026_10_27.md | 705bad0d0719b4712af8e6ba8c20f02715d566ad0832a5b10122f2d5df86df3d | Entire existing acceptance and exact original-domain boundary |

All six pins match present file bytes. No missing older manuscript or review is needed for any local theorem accepted here.

## 3. Physical classification and the entire contact-feature cover

I reconstructed the classification directly in the actual square's own orthogonal frame. At a circle corner write C=[a-1,a] x [b-1,b]. Comparing the two adjacent corners gives a,b>=1/2. Equality of the opposite-corner radius would imply a+b=1, hence a=b=1/2 and R^2=1/2. This cannot occur because d>0 gives R^2>5/4. A second actual circle corner must therefore be adjacent, with one own coordinate exactly 1/2 and the other sqrt(R^2-1/4)=d+1.

This proves the exhaustive two-corner form

    C=[d,d+1]e+[-1/2,1/2]f

for orthonormal e,f. Three or four actual circle corners are excluded by the same own-coordinate comparison in this radius domain. Thus a circle-touching C has either one or two physical circle corners, as required by the two uniqueness corollaries.

Every point of this rectangle has squared norm at least d^2. This already proves the first uniqueness test |P|^2<d^2 with no normal sign premise.

I also reconstructed the physical obstruction to sharing a containing-circle point. A nonvertex point cannot maximize squared norm on a unit side or in the square interior, by strict convexity. At a circle corner Z, every actual inward unit side axis v satisfies Z·v<=-1/2 from containment of Z+v. Hence -Z has strictly positive inward components for both units if two units share Z. A sufficiently small common displacement Z-epsilon Z enters both open square interiors. This contradicts interior disjointness, independently of force weights or ownership.

Consequently an actual common vertex P of C can only be one of the two inner vertices. Its squared norm is exactly d^2+1/4. This covers every actual normal in the full inner-vertex normal cone, including the genuinely free case and possible zero support P·n=0. No normal needs to be replaced by an axis or exposed strictly after the original extraction.

For a relative side-interior point, the actual normal n directed into C is uniquely the side's inward unit normal. I checked the complete table with the actual incoming sign:

| Actual C face | Inward unit normal | Exact incoming support value |
| --- | --- | --- |
| Inner radial face | e | d>0 |
| Outer radial face | -e | -(d+1)<0 |
| Lower transverse face | f | -1/2 |
| Upper transverse face | -f | -1/2 |

Thus the nonnegative support hypothesis leaves only the inner radial face in a relative side interior. Its full actual point is

    P=d e+t f,       -1/2<=t<=1/2,

and its norm squared is d^2+t^2. Both endpoints remain in the closed interval. An actual shared-side mean lies at such a physical point and is not replaced by a midpoint; the inequality is valid on the whole interval.

A common point cannot lie in the open interior of C: a small disk there meets the interior of the other positive-area square at any of its boundary points. Hence the side/vertex cover loses no physical intersection type.

This proves the entire annulus and both strict tests. Neither equality |P|^2=d^2 nor equality |P|^2=d^2+1/4 is excluded. The support equality P·n=0 is retained as well. The conclusion remains about the full physical corner mask, so a second physical corner carrying zero circle weight is still excluded when a strict test applies.

## 4. Both genuine far-vertex leaf rows

For the physical root

    H=[-X,1-X] x [-A,1-A],       X>0, A>=0,
    F=(-X,1-A),

the two theorem rows are genuinely different:

1. Vertex leaf: X^2+A^2=d^2, with 0<=A<3/8.
2. Aligned lower leaf: X=d, with 0<=A<1/2, and actual radial application (-d,0).

The second row does not carry the first row's vertex-radius equation. I checked this distinction at every use of the radius. The physical occupied leaf can remain in the original packing, and neither its force nor any other force is deleted to prove this local geometric implication.

The actual incoming normal at F is n=(-u,v) with u,v>0. Since 1-A>0 in both full row intervals,

    F·n=Xu+(1-A)v>0.

No C side owner is used. In particular the whole genuinely free HC cone with this strict sign is covered.

The vertex row gives the exact whole identity

    |F|^2-(d^2+1/4)=3/4-2A>0.

The aligned row instead gives

    |F|^2-(d^2+1/4)=(1-A)^2-1/4>0.

These are precisely the second annulus test. The intervals are complete: the first difference is linear in A and vanishes at A=3/8; the second factors as (1/2-A)(3/2-A) and vanishes at A=1/2. The strict thresholds are necessary for this particular argument and are not silently closed. A=0 is allowed in both stated local rows, including the aligned physical side endpoint.

The result uses no C2 equation, no proper concurrence, no K boundary condition, and no degree or central-owner information. Every additional contact and every original packing unit may remain present.

## 5. Exact recovered normal-form join and both upper vertices

I reconstructed the origin-preserving orthogonal map from the full fresh normal form at 93cbef18. Its actual chart is

    H=[x,x+1]v+[-y,1-y]u,
    0<x<=delta<1/60,       0<=y<31/120,
    d=1+delta.

Under P -> (-P·v,P·u), put X=1+x and A=y. This gives exactly

    H=[-X,1-X] x [-A,1-A],
    F=(-X,1-A),       W=(-x,1-A).

The two real normal-form rows become X^2+A^2=d^2 with A>0, or X=d with 0<=A<31/120. The original normal form establishes these leaf and height conclusions before any assumption of physical C uniqueness or central-owner split. Its Sections 4--5 explicitly need no C equation and no K degree reduction. Therefore this transfer itself is not circular.

At the near upper vertex W, the complete actual bound is

    |W|^2=x^2+(1-A)^2<=delta^2+1<d^2,

with exact final gap 2delta>0. It applies to every actual normal, owner or free contact at W. The aligned G=1 endpoint remains included, as does the maximum x=delta. The first annulus test therefore forces a unique physical circle corner at every such boundary neighbor.

At the far upper vertex F, the actual strict northwest incoming direction has positive support by the previous section. Both exact original height reserves are

    3/4-2A>7/30,
    (1-A)^2-1/4>4321/14400.

Thus every actual C-owned or free strict northwest upper-far contact is physically unique on both full true leaf rows. No CK owner or contact type enters, and all physical shared means elsewhere in the component are preserved.

The original graph and its true degrees remain

    HK, HB, BK, HC, CK, HL_H, BL_B,
    H4/K3/B3/C2.

The two occupied S leaves and every other physical packing square remain present. This argument supplies a physical mask conclusion; it does not replace an actual boundary unit by one selected circle atom. In particular it is stronger than a one-atom positive resultant assertion.

The recovered normal form still has its explicit actual nonparallelity and positive-B-concurrence hypotheses. This source does not prove either. A separately accepted positive-concurrence theorem can supply the second in an assembly; the full parallel-B feature remains separate. The current source does not establish HK-singleton either.

## 6. Noncircular assembly boundary

The target's stated limitation is correct and essential. The annulus/far-vertex theorem proves uniqueness once the actual physical HC point and normal have been placed at the near upper vertex or the strict northwest far upper vertex. It does not prove that every HC application is in one of those positions.

An H-owned top-side mean occupies a whole side interval and is a different physical feature. It is not legitimate to replace that mean by F or W. Nor can a normal be selected after extraction to impose the strict northwest condition. Every use must retain the same original mean and normal.

If an older local caller assumed physical C uniqueness before deriving its complete HC direction/position cover, this new result alone cannot retroactively remove that premise. A fresh all-mask physical cover or an independent derivation of its needed antecedents must precede the mask implication. The target states this boundary explicitly; I accept that scope without an implicit enlargement.

The local theorems are fully usable from present sources. They do not claim to restore the missing older global C-mask source or to close an entire original graph gate. No ledger or coarse attachment label follows from this source alone.

## 7. Independent exact reconstruction and final verdict

My separate exact audit is

    recovery_2026_10_27/rooted_radial_port_annulus_audit.py
    SHA256 37a2444f228dc5071894d6e3234debbea14f5c53dab189f6280107a61fd987ed

with report

    recovery_2026_10_27/rooted_radial_port_annulus_audit.json
    SHA256 944234a96c0d6d5e071207975faec132ffa9cfd3c1e4414a8488f6ec34790846.

It independently passes **17 complete exact support, coordinate or radius identities; nine exact rational values; and all six target/input/review pins.** The four side-support calculations are expanded in a general rotated own frame. The record also checks all adjacent/opposite corner comparisons, the full inner-face mean norm, both distinct true leaf radius expansions, the actual strict northwest dot product, the near-point budget, and both exact threshold factors.

The arithmetic record is subordinate to the complete physical feature cover and original-domain reconstruction above. It is not an exclusion certificate, a finite list of poses, or a subdivision of an angle domain. No Lean, CI, ledger or remote action was performed, and no frozen source was modified.

**Final verdict: complete independent non-contributor PASS of the entire frozen annulus theorem, both upper-vertex uniqueness results and their exact original join, with the stated noncircular assembly boundary retained.**

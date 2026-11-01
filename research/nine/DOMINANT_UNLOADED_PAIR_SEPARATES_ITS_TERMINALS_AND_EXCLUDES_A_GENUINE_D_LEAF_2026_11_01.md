# A dominant unloaded pair has disjoint terminals and cannot continue a genuine D leaf

Date: November 1, 2026 UTC. Constructor: articulation continuation.

**Status: complete new hand proof, frozen for independent review.**
The two local theorems and their exact original six-body caller are proved
below. No original coarse/fine flag or earlier frozen source is changed.

## 1. The original full-star interface

Keep all actual unit squares in the same disk about O, with pairwise
disjoint open interiors and

    R^2 <= 1105/256.

Retain their complete original positive force-and-torque certificate,
including all circle atoms, every true degree, support normal, positive
magnitude, and actual application or full shared-side mean. No force,
normal, physical body or mean endpoint is changed.

Let A and B be unloaded actual bodies with an original positive direct
pair of magnitude d>0, original unit normal n from A to B, and original
common application p. At A distinguish one other original positive force
z_A u_A, acting at q_A toward its actual neighbor P. At B distinguish
one other original positive force z_B u_B, acting at q_B toward its
actual neighbor Q. The distinguished force is an actual original pair
at each endpoint, not a resultant replacing several neighbors.

Let r_A,r_B be the sums of magnitudes of ALL other original positive
pair forces at the respective endpoints, excluding AB and the one
distinguished force there. Assume only

    (r_A+r_B)/d < 3/40.                              (1)

The actual endpoint degrees, all other incident normals and applications,
and all forces and loads at P,Q are arbitrary. P,Q may initially be the
same body; Theorem A below rules that possibility out as well.

**Theorem A.** The whole closed actual terminal squares P and Q are
disjoint. In particular they cannot physically touch, even with zero
selected force.

**Theorem B.** Neither distinguished force can be the actual bridge to
a genuine radial D leaf. Equivalently, this full-star interface cannot
continue a genuine D leaf through the two unloaded endpoints.

Neither conclusion uses the separate central-contact localization bound.
Only the complete original translations and actual square support facts
are used. Every torque equation remains part of the original certificate;
no endpoint is assigned a shortened two-force equation.

## 2. Exact normal error from the complete original forces

Put t_A=r_A/d and t_B=r_B/d. Complete translation at A and B gives

    |d n+z_A u_A| <= r_A,
    |-d n+z_B u_B| <= r_B,
    z_A >= d-r_A > 0,   z_B >= d-r_B > 0.

Define

    delta_A=|u_A+n|,     delta_B=|u_B-n|,
    Delta=delta_A+delta_B.

The exact identity

    |d n+z_A u_A|^2=(d-z_A)^2+d z_A delta_A^2

and its B analogue imply

    delta_A <= t_A/sqrt(1-t_A),
    delta_B <= t_B/sqrt(1-t_B).

Since each t_i<3/40, and

    sqrt(40/37)<26/25

by the exact integer comparison 25000<25012, both satisfy the weak
linear bound delta_i <= (26/25)t_i, including t_i=0. Therefore

    Delta <= (26/25)(t_A+t_B) < 39/500.              (2)

This is a bound on the original normals. It does not replace them by
opposite directions or remove the remaining forces.

We will also use the elementary exact support fact: if x maximizes a
unit direction v on an actual unit square S, then x-v belongs to S;
if x minimizes v, then x+v belongs to S. In own coordinates, each
signed component of v has absolute value at most one, so subtracting
it from its maximizing coordinate stays in the unit interval. This
includes an arbitrary point of a support side and either endpoint.

## 3. The distinguished terminal squares are closed-disjoint

Suppose, contrary to Theorem A, that an actual point x belongs to
P intersect Q. The original AB application p maximizes n on A and
minimizes n on B. Thus p-n belongs to A and p+n belongs to B.

The distinguished application q_A maximizes u_A on A and minimizes
u_A on its actual neighbor P. Applying these two unchanged support
relations to p-n and x gives

    u_A dot(q_A-p) >= -u_A dot n,
    u_A dot(x-p) >= -u_A dot n.

At B, the corresponding relations give

    u_B dot(q_B-p) >= u_B dot n,
    u_B dot(x-p) >= u_B dot n.

Adding yields the exact necessary inequality

    (u_A+u_B) dot(x-p)
       >= u_B dot n-u_A dot n
       = 2-(delta_A^2+delta_B^2)/2.                  (3)

The right side is greater than one, since
delta_A^2+delta_B^2<=Delta^2<(39/500)^2<1.
On the other hand |u_A+u_B|<=Delta. Both x and p are actual points
of the original disk, and R<25/12, so

    (u_A+u_B) dot(x-p)
       <= Delta |x-p|
       <= 2R Delta
       < (25/6)(39/500)=13/40<1.                   (4)

Equations (3)--(4) contradict one another. Thus P intersect Q is empty.
All supports in this argument are the original complete supports; it
also excludes a singleton physical contact and a shared side. QED.

## 4. A genuine D leaf forces an actual terminal point outside the disk

It suffices to exclude a D leaf distinguished at A; interchanging A
and B, with n replaced by -n, gives the other endpoint.

Let the actual genuine D leaf be L=P. Its original degree-one radial
form gives a unit direction e and

    u_A=e,       p_AL=r e,       r=R-sqrt(2).

The actual square A lies in the closed half-plane e dot y<=r and
attains equality at p_AL. This is its original supporting contact
with the genuine D leaf, independent of A's frame and true degree.

Write u=u_B and q=q_B for the other endpoint's distinguished original
normal and application. Then

    delta_A=|e+n|,
    delta_B=|u-n|,
    delta_0=|e+u| <= Delta.                         (5)

The support-segment fact puts p-n in A, so

    e dot p <= r+e dot n.                           (6)

It also puts p+n in B. Since q is an actual maximum-u point of B,

    u dot(q-p) >= u dot n.                          (7)

Finally q is a minimum-u point of the actual terminal Q, so the point

    x=q+u

belongs to Q and hence to the original disk. The two points q,p lie
in the same unit square B, so |q-p|<=sqrt(2). Using (6)--(7), without
an assumption about where either mean lies on its side, gives

    e dot x
       = e dot p - u dot(q-p) + (e+u) dot(q-p) + e dot u
       <= r+e dot n-u dot n+sqrt(2) delta_0+e dot u.

The three unit-vector identities are exact:

    e dot n = -1+delta_A^2/2,
    u dot n =  1-delta_B^2/2,
    e dot u = -1+delta_0^2/2.

Consequently

    e dot x
       <= r-3+(delta_A^2+delta_B^2+delta_0^2)/2
                  +sqrt(2) delta_0
       <= r-3+Delta^2+sqrt(2) Delta.                (8)

Here delta_A^2+delta_B^2<=Delta^2 and delta_0<=Delta.
Every error is controlled by the total original remainder in (1).
Using (2) and sqrt(2)<3/2 gives the exact rational upper bound

    Delta^2+sqrt(2) Delta
       < (39/500)^2+(3/2)(39/500)
       =30771/250000 < 1/8,                        (9)

where the last integer comparison is 246168<250000.

For the original radius,

    r+R=2R-sqrt(2)<25/6-7/5=83/30<23/8;            (10)

the elementary bounds R<25/12 and sqrt(2)>7/5 follow by squaring
positive numbers, and 83*8=664<690=23*30. Equations (8)--(10) imply

    e dot x < r-3+1/8 = r-23/8 < -R.

But x is an actual point of Q in the disk of radius R, so e dot x>=-R.
This contradiction proves Theorem B, including zero remainders and
every original endpoint or shared-side mean. QED.

The proof does not assume a radial or side-owned normal at B or Q.
Its near alignment follows quantitatively from the full original
translation equations, with all additional positive forces retained.

## 5. An exact cyclic three-cut path caller

Now keep a connected entirely unloaded original region K with full
positive cut of exactly three edges. Suppose its three cut hosts are
distinct actual hubs A,B,H, their exits are direct, and their induced
direct positive graph is exactly a two-edge path, with arbitrary other
internal bodies, channels, chords and degrees retained.

Suppose the three actual outside neighbors are respectively P,Q,L,
where P and Q physically touch and L is a genuine leaf at H. They
are the actual original cut endpoints, not effective terminal labels.

The complete accepted theorem

`CYCLIC_THREE_PORT_COMMON_SIDE_EXCLUSION_AND_OBTUSE_DOMINANT_PAIR_2026_11_01.md`

applies at this entire original path scope. Its Theorem 2 supplies one
of the two actual direct exit-hub pairs, of magnitude d, such that
after distinguishing the original cut force at each endpoint, ALL
other original incident magnitudes have total less than 3d/40.

If this pair is AB, its two distinguished actual neighbors are P and Q.
Their physical contact contradicts Theorem A. Therefore the dominant
pair necessarily includes H. If L is a genuine D leaf, Theorem B now
contradicts that pair. We have proved:

**Theorem C.** The entire D-leaf feature of this full-three-cut path
domain is impossible. If a genuine leaf survives, it is S, and the
dominant original exit-hub pair necessarily contains its root H.

The S conclusion uses only the accepted exhaustive genuine-leaf S/D
classification. The result does not exclude that S-leaf feature.
No force at the weaker exit-hub pair is deleted, and no false residual
distance lower bound is used. P and Q need only physically touch for
this theorem; their mutual contact need not carry positive force.

## 6. Complete remaining multicycle six-body and original C1.8.b1 join

Retain the unchanged original canonical prerequisites of the accepted
small-module exclusions and the complete C1.6.b3 theorem. The following
whole conclusions have already been independently reviewed:

1. Every still-unexcluded unloaded full-three-cut module of cycle rank
   at least two has exactly six actual bodies, is biconnected, and has
   three distinct actual exit hubs with direct exits.
2. Its actual direct graph on those three hubs is exactly a two-edge
   path. Zero edges contradict full work concentration; one edge is
   excluded by the complete dominant-pair/full-cut theorem; three edges
   are excluded by the physical terminal-triangle work argument at
   arbitrary rank at least two. No reduced subdivided edge substitutes
   for an original direct edge.
3. All three actual outside bodies are loaded and have exactly one
   K-cut edge each. Their outside positive graph has exactly one edge
   P--Q; the third body L is a genuine leaf at the third distinct host H.
   The zero-edge outside alternative is exactly the already excluded
   original C1.6.b3 case.
4. The whole original component is K plus AP,PQ,QB,HL, on all nine
   actual bodies. Its maximal eight-body block is K plus the actual
   ear A--P--Q--B; its only bridge is HL. Thus it is literally an
   original C1.8.b1 instance, with exactly P,Q loaded inside its block
   and all six K bodies unloaded.

Theorem C now applies with every original full-star and terminal premise
proved. The actual positive PQ edge supplies its physical contact. It
excludes EVERY genuine-D-leaf instance in this entire remaining module
family, at all original hub degrees, all allowed cycle ranks, every
physical circle mask and every unchanged original mean.

Equivalently, every surviving multicycle unloaded full-three-cut module
in the original canonical domain must enter C1.8.b1 with a genuine
S leaf, and its dominant direct exit-hub pair contains that S root.
This is a complete D-feature closure of the stated family, not a closure
of the whole C1.8.b1 parent or every possible three-port module.

## 7. Exact accepted composition boundary

| Source | SHA256 | Exact use |
| --- | --- | --- |
| `CYCLIC_THREE_PORT_COMMON_SIDE_EXCLUSION_AND_OBTUSE_DOMINANT_PAIR_2026_11_01.md` | `01c4c6e4ca426f7530c541d7e0dadf777fa3be30f794d727aedc941ebbea6650` | Entire original exit-path force ratio below 3/40; the central-contact conclusion is not used |
| `THREE_PORT_RANK_TWO_AND_ALL_SUBCUBIC_MULTICYCLE_EXCLUSION_2026_10_31.md` | `8c390ac0df81029e88377d0ec7d1d907c699132da100b846cdfb77e018a834da` | Sections 3--4 exclude zero/one/three direct exit-hub edges at rank at least two, using the complete earlier concentration statement |
| `CYCLIC_THREE_PORT_BICONNECTIVITY_AND_COMPLETE_FOUR_HUB_EXCLUSION_2026_10_31.md` | `cb926e78c8bd14b18f4b245b72614715460ad922e8efeaeb41d0276302e26d36` | Complete six-body, biconnected, direct distinct-exit remaining domain |
| `SIX_BODY_UNLOADED_THREE_PORT_MODULES_REDUCE_TO_ORIGINAL_C1_8_B1_2026_11_01.md` | `5edc189d7179af4b64456d71718949dbb8b7842554c8c088d11d73b497a5479a` | Complete loaded outside graph, one edge or three leaves, and literal original-parent join |
| `reviews/2026-11-01/REVIEW_SIX_BODY_UNLOADED_THREE_PORT_TO_ORIGINAL_C1_8_B1_2026_11_01.md` | `d08c9c2ca0ff9c343e85f6442732d0e2a225900bbc12041d0730b8ff3961b913` | Full independent acceptance of that entire physical classification and conditional canonical caller |

The original genuine-leaf chart and its exhaustive S/D alternatives are
the accepted `RADIAL_BRIDGE_AND_LEAF_REDUCTION.md`, especially its
degree-one classification. In Theorem B the exact D chart needed is
printed as an explicit premise before use. In Sections 5--6 the
original radius window and all compatible-certificate, normal-selection,
physical graph and canonical prerequisites of the imported whole
theorems remain in force.

The new mathematics consists of Sections 2--5 and the exact final
composition in Section 6. All inequalities and constants are hand
derivations. No mathematical script, numerical pose search, interval
certificate, force deletion, normal reselection, Lean, build or CI was
used. A clean noncontributor must review the whole new source before
adoption. The genuine S remainder and the unrestricted proof remain
open at this manuscript's boundary.

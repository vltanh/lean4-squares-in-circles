# A unit square cannot occupy a side gap closed by two touching neighbors

Date: October 28, 2026 UTC. Author: frontier_audit continuation.

**Status: complete proposed radius-free and force-free geometric theorem,
with a literal four-spoke end consequence; frozen for full root and separate
independent review. No original family or gate is declared excluded.**

All squares in this manuscript are the actual closed unit squares. Their
open interiors are pairwise disjoint. No position, frame, contact point or
normal is changed. Additional physical squares remain as obstacles.

## 1. Complete physical side-gap theorem

Let H,B,C,D be four distinct actual unit squares. Normalize a side of H to

    H=[0,1]^2, S=(0,1), T=(1,1).

Assume the following actual incidences:

* S belongs to B and T belongs to C.
* There is an actual Z in B intersection C with Z_y>1.
* D lies in the closed half-plane y>=1 and contains an actual point
  P=(p,1), with 0<p<1.

**Theorem.** These conditions are impossible.

No force, degree, load, containing circle, selected-normal convention or
contact owner is a premise. The contacts may carry zero force. The point P
may be a vertex, a relative side-interior point or an endpoint-valued mean
of a real shared side. The entire square D, rather than a center proxy,
is the object excluded from the gap.

### 1.1. A closed physical body cannot meet another body's open interior

For any two actual squares K,L with disjoint open interiors,

    int(K) intersection L is empty.

Otherwise a point of the closed square L in the open set int(K) has a
small open neighborhood contained in int(K). Every neighborhood of any
point of a closed square meets that square's open interior. That would
give a point in both open interiors. This elementary observation applies
also at a side endpoint or multiple physical junction.

### 1.2. The actual contact triangle traps the whole D interior

Let Delta be the closed triangle with vertices S,T,Z. It is nondegenerate
because Z_y>1. Its three entire sides lie in the actual physical bodies:

    [S,T] subset H, [S,Z] subset B, [T,Z] subset C.

Convexity gives the last two inclusions. By Section 1.1, int(D) avoids the
whole boundary of Delta.

The point P lies in the relative interior of the base [S,T]. Choose any
interior point W of D. Its height is strictly above 1, because D is a
full-dimensional square contained in y>=1. For all sufficiently small
t>0, the point

    P+t*(W-P)

belongs both to int(D) and int(Delta). The first assertion follows from
convexity and W in int(D). The second follows because, near a relative
interior point of the triangle's base, the triangle contains all
sufficiently close points strictly on the Z side of that base. No
horizontal bound on Z is needed.

The connected open set int(D) avoids the boundary of the triangle and
contains a point of its bounded interior. It must therefore be wholly
inside int(Delta). Taking closures gives D subset Delta. This is a direct
physical localization; it does not assume a preferred graph embedding
or an artificial face at a junction.

### 1.3. The contact triangle has area strictly below one

The points S and Z both belong to the actual unit B. Therefore

    0<Z_y-1<=|Z-S|<=sqrt(2).

The base [S,T] has length one. Hence

    area(Delta)=(Z_y-1)/2<=sqrt(2)/2<1.

But D is an actual unit square and D subset Delta, so
1=area(D)<=area(Delta)<1, a contradiction. This completes the theorem.
The same argument could use the C diameter; no equality or strictness of
the diameter bound is needed.

## 2. A complete supporting-normal criterion for the exterior contact

In the same H coordinates suppose B has an actual minimum support at S
with normal

    n_B=(-u,v), u>0, v>=0,

and C has an actual minimum support at T with normal

    n_C=(r,s), r>0, s>=0.

The normals need not be unit for this criterion. Suppose B and C
physically touch. Every actual Z in their intersection satisfies

    -u*Z_x+v*(Z_y-1)>=0,
     r*(Z_x-1)+s*(Z_y-1)>=0.

If Z_y<=1, the first inequality gives Z_x<=0 and the second gives
Z_x>=1, a contradiction. Thus every actual BC contact lies strictly
above the H side. Section 1 then excludes any further actual unit D
in y>=1 that touches the relative interior of that side.

This criterion includes both horizontal-axis endpoints v=0 and s=0
whenever the stated actual support points S,T are present. It does not
assume that an arbitrary side mean is one of those endpoints. All uses
must verify the literal incidences at S and T.

## 3. Literal four-spoke consequence with the original full stars

Retain the exact actual graph

    HA, HB, HC, HD, AB, BC, CD, DE, EA

and the complete hypotheses of
INNER_PENTAGON_H_OWNED_UNLOADED_END_FIXED_OPPOSITE_RETURN_VERTICES.md.
In particular H is the original unloaded degree-four hub, D is the
original unloaded degree-three end, and all other actual degrees and
loads remain. Suppose H owns HD. The accepted chart gives

    H=[0,1]^2, n_HD=North,
    n_HA strictly Southwest,
    n_HC strictly Northeast or East,
    D subset {y>=1}, P=(p,1) in D, 0<p<1.

**Corollary.** In the strict Northeast HC branch, the original HB normal
is necessarily strictly Southeast.

Here is the complete normal-feature partition. A strict Northeast HB
normal is impossible because A and B would occupy opposite strict H
corners while physically touching. A strict Southwest HB normal is
likewise impossible because B and C physically touch. Of the four H
axis normals, East and North have strictly negative dot product with
the original HA normal; West and South have strictly negative dot
product with the original HC normal. The corresponding actual
triangles HAB or HBC and the owned-axis triangle theorem exclude all
four axes, including their actual shared-side means.

The only remaining features are strict Northwest and strict Southeast.
If HB were Northwest, its actual H application would be S=(0,1), and
the strict Northeast HC application would be T=(1,1). The actual BC
contact and Section 2 put every BC contact above this side. The actual
D has precisely the exterior side-gap incidence in Section 1. That
theorem excludes the entire Northwest branch. Thus HB is Southeast.

No force or torque at B,C,E is used. The inherited complete H4 and D3
equations remain intact; neither is truncated to obtain the corollary.
It covers arbitrary owners or free normals at the strict HB and HC
vertices and every possible extra zero-weight contact.

For the original families H4_D0.L124 and H4_D0.L0124, substitute
(A,B,C,D,E)=(0,1,2,3,4), with the same graph-preserving reflection
already permitted by the accepted H-owned-end chart. The corollary
only strengthens that entire H-owned-HD, strict-NE-HC interface.
It does not exclude the Southeast residue, does not assert an endpoint
for the separate East-HC side mean, and does not close either family.

## 4. Exact proof inputs and scope preservation

Sections 1--2 have a self-contained proof from convexity, physical
interior disjointness, the unit-square diameter and elementary triangle
area. The contact-triangle manuscript below is included as provenance
for the same physical localization principle, not as a hidden extra
graph or winding hypothesis.

| Source | SHA256 | Exact use |
| --- | --- | --- |
| CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS.md | b61b0dec7ded00984c687e353fd3f3bfb5a5a7ade45d87d69aaeade09f23d80b | Provenance of the physical closed-body localization and area principle; Sections 1--2 above are complete |
| INNER_PENTAGON_H_OWNED_UNLOADED_END_FIXED_OPPOSITE_RETURN_VERTICES.md | bc1b08bc93401e25891f1307139c465409e4a3e260670513087b658c210e0f8c | Literal full H4/D3 chart, strict HA/HC signs, actual exterior D and 0<p<1 |
| INNER_PENTAGON_FOUR_SPOKE_SHARED_UNLOADED_END_EXCLUSION.md | ab1882057cc4d5bc0be2929c0c926543a92fbbbc4f8f74598c2238707d17f9f6 | Complete degree-free opposite-strict-corner contact obstruction |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 | Actual physical triangle obstruction for a hub-owned axis, with all shared means |

No selected normal, original source bytes, ledger, gate count, roadmap or
handoff is changed. No containing-radius or origin-clearance premise is
introduced, and no completion unit is removed.

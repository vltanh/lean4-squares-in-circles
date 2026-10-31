# High-radius triangle-tip pressure and simultaneous rooted-block exclusions

**Status: complete hand assembly. Root and independent full saved-source and
direct-prerequisite review passed on October 25, 2026; see
REVIEW_HIGH_RADIUS_2026_10_25.md. The two existing HIGH upper-left diamond
leaves close. No new gate ID or coarse-cell closure is claimed.**

New analytic input: NEGATIVE_TRIANGLE_UPPER_LEFT_UNIFORM_HIGH_RADIUS.md,
committed at `0f36bd1e86b828913dbef878585c39f701c00086`.
Earlier inputs are pinned at `87d2684e0e58afbc2b43424a254ab9436a739054`.

Throughout this manuscript keep the original nine physical units and the
common compatible selected certificate, with
\[
                       17/4\le q=R^2\le1105/256.
\]
All original shared means, individual zero circle weights, extra physical
contacts and completion squares remain. No square or force is replaced by an
artificial body. All degree requirements below are the genuine positive degrees.

## 1. Every loaded degree-two triangle tip has nonnegative root pressure

**Theorem A.** Suppose H,A,K are pairwise physically touching. A has exactly
the two positive pair neighbors H,K and positive total circle load. K is
physically circle-touching. H and K may have arbitrary additional positive
forces; HK itself may have zero stress. Then
\[
                              c_H\cdot F_A\ge0.                 \tag{1}
\]
If A has two physical circle corners, the inequality is strict.

**Proof.** For physically radial A, RADIAL_BOUNDARY_NEIGHBOR_PRESSURE.md
applies to each original circle atom separately and gives strict positivity,
even when one atom has zero weight.

Otherwise write F_A=lambda z_A, lambda>0, at its unique physical circle
corner. Suppose c_H dot z_A<0. The full HA owner cover is as follows.

* If A owns HA, including every shared HA interval and mean endpoint,
  NEGATIVE_UNIQUE_ENDPOINT_TIP_OWNED_HIGH_RADIUS.md excludes it. Its actual
  scope permits arbitrary H/K forces and needs no HK stress equation.
* If HA is free, NEGATIVE_UNIQUE_TRIANGLE_FREE_ENDPOINT_HIGH_RADIUS.md
  excludes it in the same fixed-tip selected certificate. Its physical
  triangle premise is exactly the real HK contact; HK need not be positive.
* The remaining HA is an H-owned singleton. Section 1 of
  NEGATIVE_H_OWNED_ENDPOINT_RADIAL_MIDDLE_DOMAIN.md gives its ordered frame
  A=[a-1,a] x [b-1,b], P=(a-1,b-1), n=(u,v), j=(-v,u),
  H=P+[-1,0]n+[-(1-r),r]j, with a>b>3/5, 0<u<=v and 0<r<1.
  It gives exactly three possible outgoing A-to-K normal features.

For the left normal -e_x, the complete whole-orientation theorem
NEGATIVE_H_OWNED_LEFT_HIGH_RADIUS_EXCLUSION.md excludes every singleton and
shared outgoing mean. Its small-coordinate input is included in its stated
whole-domain assembly; no K2 or H equilibrium is used.

For the upper normal +e_y, K lies in y>=b. But every point of H has
\[
                   y\le b-1+ru<b,
\]
since u<1 and r<1. Thus H and K are physically disjoint, contrary to the
triangle premise. This includes every upper side mean and shared interval.

For a strictly upper-left normal g=(-c,s), c,s>0, A's outgoing application
is its fixed vertex T=(a-1,b), distinct from P. Both A applications are fixed
singletons. GENERAL_FIXED_TIP_NORMAL_SELECTION.md excludes free AK in the
already common certificate. The normal is not an A axis, so K owns AK.
PHYSICAL_CONTACT_STRESS.md's singleton convention puts T in the relative
interior of the actual K side; a vertex/vertex singleton instead has a strict
free normal. The new uniform theorem therefore applies, for either physical
K mask and every physical HK feature. Its positive pressure contradiction
excludes this last feature.

The HA and outgoing feature covers are exhaustive, with every actual mean
retained. No negative unique circle atom exists, which proves (1). The proof
establishes nonnegativity for a unique tip, not a claim of strict positivity
at every possible zero-pressure configuration. QED.

All generic selections used above were already stated for actual degree-two
tips with arbitrary neighbor degrees. They can be imposed simultaneously for
the finitely many physical tips before extraction. No new normal is selected
in the argument, and no mean is frozen after extraction.

## 2. One pressure inequality covers both a diamond and a physically chorded C4

**Theorem B.** Let A,K,B be a physical circle-touching path A--K--B, with
positive total circle loads F_A,F_K,F_B. Suppose H touches all three bodies,
and A and B have exactly the respective positive pair neighbors H,K. K may
have arbitrary additional positive neighbors. HK may have positive or zero
stress. Then
\[
                    c_H\cdot(F_A+F_K+F_B)\ge0.                  \tag{2}
\]

Indeed Theorem A gives c_H dot F_A>=0 and c_H dot F_B>=0. The full physical
boundary-path cone theorem BOUNDARY_THREE_PATH_RESULTANT_CONE.md gives
\[
 F_K=\alpha F_A+\beta F_B,\qquad\alpha,\beta>0.
\]
It uses no equation at K and retains its actual unequal radial weights.
Consequently
\[
 c_H\cdot(F_A+F_K+F_B)
       =(1+\alpha)c_H\cdot F_A+(1+\beta)c_H\cdot F_B\ge0.
\]
This proves (2). The identity is a comparison of the original resultants,
not a decomposition of K into fictitious degree-two tips.

**External-pressure corollary.** Suppose H is physically clear and all other
loads in the same positive component have their actual sum M, with
\[
                      c_H\cdot M>0.
\]
Summing all genuine body equations gives
\(F_A+F_K+F_B+M=0\). Its scalar product with c_H contradicts (2).
Every extra force at H or K cancels only in this legitimate whole-component
sum. No local force or physical obstacle is discarded.

This single corollary applies simultaneously to:

| Actual positive graph / geometry | Consequence at q>=17/4 |
|---|---|
| Diamond HK,HA,HB,KA,KB, with an intact HXY petal | Entire diamond-hub KAB family is excluded, with true H5/K3 |
| Diamond with two genuine leaves at H | Entire high-radius SS, SD and DD leaf assignments are excluded, with true H5/K3 |
| C4 H--A--K--B--H with actual zero-stress HK contact and an HXY petal | Entire high-radius physical-chord family is excluded, with true H4/K2 |
| The same physically chorded C4 with any independently proved positive-pressure attachments at H | The same exclusion holds at the actual enlarged root degree |
| Any larger selected component satisfying the displayed true tip degrees, physical contacts and outside pressure | The same contradiction holds, without an exact smaller-component equation |

In particular a surviving high-radius triangle-attached ABC C4 must have
its clear root physically disjoint from the loaded middle body. This is not
a proof that the root and middle touch, and it does not close the full ABC
family. Its no-contact residue remains in its original gate.

## 3. All same-hub diamond/leaf/petal mixtures in the stated size range

**Theorem C.** Consider a selected positive component formed by s>=1 diamond
blocks sharing only one hub H, k>=0 genuine leaves at H, and t>=0 intact end
triangles at H. There are no other positive edges, and
\[
            k+2t\ge1,\qquad m=1+3s+k+2t\le9.                 \tag{3}
\]
Every nonroot diamond hub has true degree three, its two tips true degree
two, every leaf true degree one, and every petal tip true degree two. H keeps
its full degree 3s+k+2t. All 9-m additional physical squares remain arbitrary.
Then the entire family is impossible throughout the high-radius interval.

**Proof.** Every diamond tip is loaded: an unloaded exact degree-two
transmitter cannot have its two neighbors physically touching. Every other
diamond hub is loaded by NO_UNLOADED_DIAMOND_HUB.md, since its neighbor H
touches both other neighbors. Thus each diamond's three original loads form
the boundary path needed by Theorem B. H is circle-clear: otherwise H, a
diamond tip and its other hub would form a forbidden physical triangle of
three circle-touching units. Each diamond contributes nonnegative pressure
by (2), independently of every other diamond and attachment.

Every intact end triangle contributes strictly positive pressure at its
actual root, by the full end-triangle pressure theorem assembled in
BOWTIE_CELL_CLOSED.md. This theorem retains arbitrary additional root forces.
Every genuine S leaf contributes strictly positive pressure by
RADIAL_BOUNDARY_NEIGHBOR_PRESSURE.md. For a genuine D leaf, the selected
leaf/root theorem makes its radial normal e an actual root side axis, so
\[
                    c_H\cdot e=R-\sqrt2-1/2>0.
\]
Its circle resultant is a positive multiple of e. This is the precise
selected-leaf input used in Section 6 of
POSITIVE_ROOT_PRESSURE_OPPOSITE_C4_EXCLUSION.md, not a claim about an
arbitrary unselected vertex normal at a D leaf.

At least one strict positive attachment is present by (3). Therefore the
scalar product of the sum of **all original component circle forces** with
c_H is positive. The genuine whole-component force balance makes that sum
zero, a contradiction. All force magnitudes, relative leaf/petal placements,
physical masks, individual zero weights, shared means and extras remain.
QED.

For clarity, the size condition has exactly these finite integer profiles:
with s=1, k+2t is 1,2,3,4 or5; with s=2 it is1 or2; no s>=3 fits.
This is 14 (s,k,t) profiles, not 14 newly closed gates. Some were already
excluded, and some are already impossible by the physical boundary count.
The theorem's content is the uniform implication (3), not a new gate list.
For example it applies to the high-radius parts of the existing coarse
cells C1.4.b2, C2.34.b0 and their specified same-hub larger attachments.
Those coarse cells include other radii/layouts and remain open.

## 4. Exact retained limitations and verification

Theorem A requires the tip's true degree two and a real physical triangle.
Theorem B requires the middle body's actual positive circle load and the
real root/middle contact. The external-pressure corollary requires its
strict pressure premise; it cannot be guessed from an arbitrary outside
aggregate. Theorem C supplies that premise only for the genuine attachments
specified in (3).

No conclusion is claimed for a lower-radius packing, a graph with extra
positive edges at the designated tips, different-root attachments, an
unchorded physical ABC C4, either remaining alternating C6 family, or the
unrestricted n=9 theorem/equality classification.

The new geometric theorem and complete assembly have passed root and
independent saved-source/direct-prerequisite review. The separate review
reconstructed the support fan and checked the full owner cover, all genuine
degrees, every whole-component sum, 18 exact algebraic identities and seven
rational reserves. See REVIEW_HIGH_RADIUS_2026_10_25.md for the performed
checks and their scope. Earlier author arithmetic is recorded in
UNIFORM_TRIANGLE_HIGH_RADIUS_CHECK.py. No full older dependency-chain or Lean
verification is claimed; no Lean compilation or CI was run.

The exact local construction in LOW_RADIUS_TRIANGLE_TIP_PRESSURE_OBSTRUCTION.md
shows that Theorem A cannot be extended to the entire LOW interval using
these same local hypotheses. The genuine K3/H5 block-pressure and completion
obligations remain. See JOINT_CLOSURE_ROADMAP_2026_10_25.md for the accepted
existing-gate mapping and precise continuation boundary.

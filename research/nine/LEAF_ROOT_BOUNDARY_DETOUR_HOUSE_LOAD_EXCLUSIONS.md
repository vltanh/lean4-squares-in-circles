# A leaf-root boundary detour excludes two complete rooted-house load orbits

Date: October 26, 2026.

**Status: accepted complete hand assembly after independent full-source
and original-gate reviews in
REVIEW_LEAF_ROOT_HOUSE_DETOURS_ROOT_2026_10_26.md and
REVIEW_LEAF_ROOT_BOUNDARY_DETOUR_HOUSE_C6_2026_10_26.md.**
This manuscript applies the already independently accepted, degree-free
central-channel theorem to the original five-body-block-plus-leaf cover.
It excludes the entire house-hub load orbit TDC and the entire
house-lower load orbit TA, each with both genuine leaf types. It adds no
computational certificate and makes no new contact-normal selection.

Work with the common selected physical certificate for the original
nine-square packing and

\[
 \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16},\qquad
 d=\sqrt{R^2-\frac14}-1,\qquad
 \varepsilon=\max(d-1,0)<\frac1{60}.
\tag{1}
\]

All positive magnitudes, actual support points and shared-side means,
physical one- and two-circle-corner masks, individual zero corner
weights, additional zero-stress contacts and the three completion
squares remain unchanged.

## 1. The inherited theorem has no endpoint-degree restriction

Theorem 4.1 of FOUR_CYCLE_ADJACENT_LOAD_EXCLUSION.md states the
following physical implication. Let an arbitrary contained unit square
P meet the closed disk of radius epsilon. Suppose a genuine normal
channel from P to a distinct unit square Q has total reserve w at least
one. For its actual unit direction n and support value alpha,

\[
 \begin{split}
  P&\subseteq\{x:n\cdot x\le\alpha\},\\
  Q&\subseteq\{x:n\cdot x\ge\alpha+w\},
       \qquad w\ge1.
 \end{split}
\tag{2}
\]

Then no physical circle-touching unit square Z can touch both P and Q.
The theorem uses no force equation at P, Q or Z. Their actual degrees
and other positive forces are unrestricted, and either of the contacts
PZ,QZ may have zero stress.

The channel premise is supplied by the unchanged equations at its
internal bodies. In particular, if U is a true unloaded degree-two
body with its two positive neighbors P,Q, then its actual force and
torque equations give (2), with w equal to one or sqrt(2). The actual
applications obey p_Q-p_P=w n; they are not replaced by side midpoints.
The far endpoint Q need not itself carry circle load or physically
touch the circle.

For reference, the inherited contradiction is uniform in the full
radius interval. Containment gives

\[
 |c_Q|\le d+\frac12,
 \qquad \alpha+w+\frac12\le n\cdot c_Q,
 \qquad \alpha\le d-1.
\tag{3}
\]

The central-disk premise gives alpha at least -epsilon. If d<1,
these inequalities already contradict alpha at least zero. If d>=1,
the support lies in [-epsilon,epsilon]. The entire Q then lies in the
n-cap with projection greater than 59/60 and angular shadow within
arctan(13/20) of n. A genuine contact q in P intersect Z has norm
greater than 3/5 and n-projection at most epsilon, so its angle from n
is greater than arccos(1/36). The angular shadow of the boundary
square Z has width less than arctan(23/16). Its other contact with Q
would require

\[
 \arccos\frac1{36}
 <\arctan\frac{13}{20}+\arctan\frac{23}{16}.
\tag{4}
\]

The sum on the right is less than pi/2, and its cosine is

\[
 \frac{21}{\sqrt{446665}}>\frac1{36},
 \qquad 756^2=571536>446665,
\tag{5}
\]

which reverses (4). All cap and angular-shadow statements here are the
complete proved lemmas of the cited source. No circle force at Z or
extra degree premise is introduced by this summary.

## 2. Every genuine leaf root supplies the central-disk premise

Let L be a genuine positive degree-one body with sole neighbor P.
The selected radial-leaf theorem gives either the full S or full D
physical leaf. Lemma 2.1 of FOUR_CYCLE_ADJACENT_LOAD_EXCLUSION.md
then gives

\[
                         \operatorname{dist}(0,P)\le\varepsilon.
\tag{6}
\]

This lemma uses only the actual leaf edge; P may have any other
positive neighbors and forces. In the D case the true radial
application is side-interior on P and the origin lies in P's open
interior. In the S case the full aligned slider and both tilted
families meet the disk in (6), including their allowed endpoints.
The leaf itself remains an occupied physical square throughout.

Combining Sections 1 and 2 gives a useful general propagation rule:

**Leaf-root detour theorem.** Suppose a physical positive component
contains a genuine leaf at P, a true unloaded normal-transmitter
channel from P to Q, and a circle-touching physical common neighbor Z
of P,Q. Then that entire component is impossible in (1).

No edge is deleted to create the channel, and no root force is
omitted. This rule therefore applies unchanged to larger components
whenever those actual premises have been proved.

## 3. House hub A with the entire positive block-load set TDC

Use the exact house graph and names from
FIVE_BODY_BLOCK_LEAF_GRAPH_LOAD_COVER.md:

\[
                  AT,\ DT,\ AD,\ AB,\ BC,\ CD.
\tag{7}
\]

There is the additional genuine leaf edge AL. The root A has true
positive degree four and is physically circle-clear. The block load
set is exactly T,D,C; hence B is unloaded. The complete local join is:

| Role in Sections 1--2 | Actual original house body or edge |
| --- | --- |
| Genuine leaf root P | A, with its original additional positive force on AL |
| True unloaded channel body U | B, whose only two positive neighbors are A,C |
| Far endpoint Q | C, with all its original forces and circle mask |
| Boundary detour body Z | D, loaded and therefore physically circle-touching |
| Both physical detour contacts | AD and DC, both original positive edges |

Thus the unchanged B equations give the actual channel A--B--C,
and the loaded square D touches both channel endpoints. Sections 1--2
give a contradiction. The roof T remains a loaded degree-two body;
its forces and geometry have not been deleted. In particular A is
never assigned the degree-three equation of an isolated house hub.

This excludes the entire TDC load orbit for both S and D leaves,
every physical mask at T,D,C and every channel mean. Reflection of
the house transports the conclusion to the corresponding hub root
under the original rooted-type symmetry; no additional gate is created.

## 4. House lower vertex B with the entire positive block-load set TA

Keep graph (7), now with genuine leaf edge BL. The root B has true
positive degree three and is physically circle-clear. The positive
block-load set is exactly T,A. Both C and D are unloaded, but only C
is used as a transmitter:

| Role in Sections 1--2 | Actual original house body or edge |
| --- | --- |
| Genuine leaf root P | B, with its unchanged force on BL |
| True unloaded channel body U | C, whose only two positive neighbors are B,D |
| Far endpoint Q | D, retaining its true degree three and all three positive pair forces |
| Boundary detour body Z | A, loaded and therefore physically circle-touching |
| Both physical detour contacts | BA and AD, both original positive edges |

The genuine channel is B--C--D. Loaded A touches both endpoints, so
Sections 1--2 again give a contradiction. The far endpoint D is not
treated as a transmitter: its edges to T,A,C all remain. Its zero
circle load is harmless because the inherited detour theorem requires
no circle contact at the far endpoint.

This excludes the entire TA load orbit for both genuine leaf types,
with every physical mask at T,A and all actual means. The reflected
lower-root placement is already included in the original root orbit.

## 5. Exact pre-existing gate joins and retained scope

The following four original gates have whole-domain contradictions:

| Original gate | Complete source join |
| --- | --- |
| M6.B5L.HOUSE.HUB.LTDC.S | Section 3 and the full S-leaf central-disk theorem |
| M6.B5L.HOUSE.HUB.LTDC.D | Section 3 and the full D-leaf central-disk theorem |
| M6.B5L.HOUSE.LOWER.LTA.S | Section 4 and the full S-leaf central-disk theorem |
| M6.B5L.HOUSE.LOWER.LTA.D | Section 4 and the full D-leaf central-disk theorem |

These are two complete block-load orbits among the seven remaining
rooted five-body types: the house-hub and house-lower rooted types
themselves still have other load orbits. Their previous load covers
already exclude the distinct hub TD orbit and the lower TC orbit.
Neither of those earlier exits is counted again here. In particular
the present lower TA family has loaded hub A, whereas the previous
lower TC exclusion concerns two unloaded hubs. The present TDC family
also differs from the hub TDCB family, in which B is loaded and cannot
be used as the true transmitter.

No C5 or fan gate, whole rooted type, complete C1.5.b1 cell, larger
seven-to-nine-body gate or global sharp bound is inferred merely from
the existence of the propagation rule. Each such application must
identify its own genuine leaf, unchanged transmitter, actual boundary
detour and complete load/owner cover. All three original extra squares
remain fixed; the contradiction excludes the core itself, so it needs
no completion capacity estimate.

No finite sign packet, pose sampling, Lean compilation or CI is used.

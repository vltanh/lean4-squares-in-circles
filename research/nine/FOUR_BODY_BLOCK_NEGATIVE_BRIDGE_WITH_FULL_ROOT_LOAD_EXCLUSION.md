# A four-body block cannot lie beyond a negative bridge from an origin unit

Date: October 27, 2026.

**Status: complete corrected hand local theorem, resubmitted for full
root and separate independent review.** An independent audit caught
an incorrect G_H sign in the first draft. The full equation below
has the correct outward-circle sign. Every load mask obtains its
forbidden ray separately, and Section 4's new correction-loop lemma
needs no positive-M point. The invalid convex-combination argument
has been removed. No shared metadata is changed.

Keep all nine original physical unit squares and the same compatible
selected certificate in

    79/40<=R<=sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1<61/60,
    r=R-sqrt(2)>1/2.

Let B be an actual four-body cyclic block and H one of its bodies.
Each private body has exactly its original block neighbors: true
degree two in C4, true degree three at a private diamond hub, and
true degree two at a private diamond tip. The only positive pair
edge from this block to its complement is the actual bridge H--U.
Its normal from H to U is n, its magnitude is beta>0, and its
unchanged real application is

    P=rho n,       rho<0.                              (1)

Suppose the distinct actual unit U contains O closed. All original
forces, actual means, physical circle masks, individual zero weights
and other packing squares remain. H keeps its full circle resultant.
No degree, load or outside subtree shape is prescribed at U.

**Theorem.** This complete original situation is impossible.

This extends the local proof in
FOUR_BODY_BLOCK_SHORT_ARM_NEGATIVE_APPLICATION_EXCLUSION.md.
The old arm supplied root clearance, a forbidden private-resultant
ray, a positive-resultant point, and the origin unit. Here every
full load mask supplies the forbidden ray either after genuine
clearance or from boundary-force acuteness. A two-triangle winding
argument removes the positive-point premise entirely. All masks
omitted by the old arm's load count are explicitly included.

## 1. Correct full balance and the genuinely unloaded-root ray

Write H's full actual outward circle resultant as

    G_H=sum_z 2 lambda_z z,       lambda_z>=0,

over its original physical circle corners. Every individual zero
weight remains. Let M be the sum of the full circle resultants at
the three private block bodies. Summing their unchanged equations
shows that M is the sum of all actual block forces pointing out of
H, and that those forces have zero total origin moment at their
unchanged applications. The actual full H equation is

    M+beta n+G_H=0,
    M=-G_H-beta n.                                     (2)

The true support for the bridge is

    H subset {x:n.x<=rho},       rho<0.                 (3)

In particular H avoids O. If the actual G_H=0, then M=-beta n,
and (3) immediately gives

    M!=0,
    H intersect {-t M:t>=0} is empty.                   (4)

No sign of n.M is inferred directly from (2) when G_H is nonzero.
The complete mask cover below proves genuine clearance wherever
needed, except for the loaded opposite-private C4 mask, where
Section 4 supplies (4) from the actual boundary forces.

## 2. All zero- and one-private-load C4 masks

Write the actual cycle H--A--C--B--H. Its three private bodies
have true degree two. Their original positive-load subsets have
eight possibilities before reflection A<->B.

### 2.1. No private load

Then A,C,B are three consecutive true unloaded transmitters on
H--A--C--B--H. Their unchanged force and torque equations propagate
one common direction; the three actual normal widths each belong
to {1,sqrt(2)}. The two actual H applications would differ by a
vector of length at least three, greater than H's diameter sqrt(2).
This is impossible independently of G_H.

### 2.2. A sole load adjacent to H

If only A is loaded, the actual path H--B--C--A has two true
unloaded transmitters. Their common directed normal and their
actual widths separate H and A by a positive normal gap of at
least two. This contradicts the original positive H--A contact.
The sole-B case is its reflection. No artificial bypass or root
load assumption is used.

### 2.3. A sole opposite load C

A,B are the two genuine unloaded transmitters with endpoints H,C.
TWO_PARALLEL_TRANSMITTERS_NO_THIRD_BYPASS.md, Sections 1--2,
makes both channels side-normal of width one, in the same direction
e from H to C, with both endpoints owning that common axis.
The two original transverse means remain independent.

Let their actual positive magnitudes be mu_1,mu_2. Then

    M=(mu_1+mu_2)e.

At C both true contact forces have the same sign -e. The complete
loaded parallel-star theorem in
PARALLEL_TRANSMISSION_AND_FOUR_CYCLES.md, Lemma N.4, gives radial
S/D geometry and the actual weighted-average application

    pbar_C=r_C e,       r_C in {d,r}.

Each channel's two actual endpoints differ by exactly e. Their
original positive weighted average on H is consequently

    pbar_H=(r_C-1)e in H.                               (5)

This is only an average; neither individual channel mean is
replaced by a radial point. Since H owns the common side axis,
its exact longitudinal interval is [r_C-2,r_C-1] and its transverse
unit interval contains zero. The bounds 1/2<r_C<=d<61/60 make
every H point satisfy

    |x|^2<(3/2)^2+1=13/4<(79/40)^2<=R^2.

Thus H is physically clear, its actual G_H=0, and (4) applies.
The real inward unit segment from (5) also contains
(r_C-2)e, a strictly negative multiple of M. This contradicts (4).
All original shared-side endpoint means and both parallel-star
geometries have been included.

The remaining masks are two adjacent private loads (AC or CB),
two opposite private loads (AB), and all three (ACB).

## 3. Two adjacent private loads: genuine zero root load before the ray step

Suppose A,C are loaded and B is the true unloaded transmitter.
Use Sections 1--4 of
ROOTED_C4_ADJACENT_LOAD_ORIGIN_TRIANGLE_EXCLUSION.md at their
stated local scope. They use the unchanged private equations and
moments, the actual unit bypass A for B's width-one channel, and
the complete root normal/mean cover. They allow an arbitrary H
circle load until Section 4 proves its actual value zero. That
zero-load proof uses the real boundary-path cone, actual circle-
corner ratios, and the original support-width contradiction; it
occurs before the old source invokes its middle triangle. The
same-nine NINE_RADIUS_TWO_MEASURE_LOWER_BOUND.md supplies its
original R>2 premise.

Thus the actual G_H=0 and (4) holds. In the resulting real channel
frame the H support coordinate is a<=0 and M_x>0. The complete
local root cover has exactly these two alternatives.

* Both root normals are the same H-owned axis e_x. Their unchanged
  applications have strictly opposite transverse signs, so (a,0)
  lies in H. Since M is a positive multiple of e_x and a<=0,
  this contradicts (4).
* The root normals are nonparallel. Their actual intersection is
  q=-tM, t>0, with both H ports proper. Premise (4) makes both
  proper coefficients b,c strictly positive. If the force
  magnitudes are mu,nu, the weighted mean of the real ports
  with weights mu/b,nu/c equals (1/Z-t)M in H, where
  Z=mu/b+nu/c>0. Premise (4) forces 1/Z-t>0, so this point has
  positive x coordinate, contrary to H_x<=a<=0.

This is the exact ray step recorded in Section 3 of
FOUR_BODY_BLOCK_SHORT_ARM_NEGATIVE_APPLICATION_EXCLUSION.md,
after the actual root load is proved zero. Every physical mask,
zero individual weight, root owner and endpoint mean is retained.
Reflection covers CB.

## 4. Opposite private loads: the full loaded-root case and a corrected winding lemma

### 4.1. The forbidden ray with the actual G_H retained

Now A,B are loaded and C is the true unloaded transmitter. If
G_H=0, Section 1 gives (4). Otherwise H is a physical boundary
unit touching both physical boundary units A,B. The complete
physical boundary-contact acuteness theorem gives

    G_H.F_A>0,       G_H.F_B>0,
    G_H.M>0,       M=F_A+F_B.                          (6)

Moreover every point x of H has G_H.x>0. For each original
positive-weight H circle corner z,

    z.x>=R^2-R sqrt(2)>0,

and the actual nonnegative weighted sum preserves strictness.
Every nonpositive M-ray point instead has G_H dot product at
most zero by (6). This proves (4), with every original H circle
weight retained. It does not use an incorrect sign in (2), a
new force, or a path-cone decomposition.

### 4.2. The one-improper root correction needs no positive-M point

The complete local opposite-mask theorem gives q=-tM, t>0.
Its surviving one-improper alternative writes the original ports

    P_i=q+b_i n_i,       b_1 b_2<0,
    M=mu_1 n_1+mu_2 n_2,       mu_1,mu_2>0,

where the normals are nonparallel and both b_i are nonzero.
Direct calculation gives

    det(M,P_1)=-b_1 mu_2 det(n_1,n_2),
    det(M,P_2)= b_2 mu_1 det(n_1,n_2).

These determinants have the same strict sign. Thus the triangle
conv(q,P_1,P_2) meets the M line only at q, which is not O.
That entire triangle avoids O and its boundary has winding zero.

Choose any actual D in H, for example its center. The triangle
conv(D,P_1,P_2) lies in the convex H and avoids O by (4), so
its boundary also has winding zero. With the appropriate opposite
orientations, the two triangle boundaries sum exactly to

    D--P_1--q--P_2--D.

Hence the full actual root correction has winding zero. All its
edges avoid O. No point of H on the positive M ray is required,
and no actual port or side mean has been changed.

The same elementary correction applies to the three-private-load
C4, whose remaining root pair has the identical one-improper form.

### 4.3. The actual opposite-load ring encloses U

Apply the complete local portions of
ROOTED_C4_OPPOSITE_LOAD_ORIGIN_TRIANGLE_COMPLETE_EXCLUSION.md,
as exported in Section 4 of
FOUR_BODY_BLOCK_SHORT_ARM_NEGATIVE_APPLICATION_EXCLUSION.md.
Here is their full unchanged premise cover.

The actual C channel has width one because H physically bypasses
it. The original loaded-parallel endpoint alternatives are excluded
using the other endpoint's actual boundary status. Thus the true
A2/B2 stars have positive radial concurrences and genuine proper
ports; no boundary-neighbor premise is invented. Their full sum
is this same M. Under (4), every parallel root pair and every zero
root proper length is excluded. The exact geometric cap and
nearest-point uniqueness leave precisely the one-improper pair.
The actual auxiliary triangle has winding one about O.

Section 4.2 supplies the zero-winding root correction. Thus the
original H--A--C--B--H ring has winding one about O. Each strand
avoids O: H does so by (3), A,B by their physical boundary-point
distance, and the C channel and its center-to-channel homotopy
have the same nonzero transverse height. This is the complete
closed-origin treatment in Section 4.1 of the negative-application
source, retaining every endpoint mean.

The actual U contains O closed. Some points of int(U) therefore
lie in the ring's winding-one neighborhood of O. Its connected
interior avoids the occupied ring strands, so the whole unit
lies on the bounded side, with the established compact-inner-
square convention at weak junctions.

The physical four-ring equality theorem forces the exact aligned
cross with U its central unit. The two opposite physical boundary
members A,B and containment of the other ring members force
R^2=5/2, exactly as in Section 8 of the opposite-load source.
This contradicts the original radius window. In the loaded-H
subcase the ring in fact has three physical boundary members,
so FOUR_CYCLE_THREE_BOUNDARY_HOLE_EMPTY.md is also an immediate
complete exit.

The entire loaded opposite-mask case has therefore been covered
without removing G_H or asserting a positive-M point in H.

## 5. Three private loads

If A,C,B are all loaded, H cannot physically touch the circle:
all four actual units would form a forbidden physical boundary
four-cycle, by CIRCLE_CONTACT_ANGULAR_ORDER.md, Section 5. Thus
H is physically clear, G_H=0, and Section 1 gives (4).

Use ROOTED_C4_THREE_BOUNDARY_NEGATIVE_CONCURRENCE.md and
ROOTED_C4_THREE_LOAD_ORIGIN_TRIANGLE_COMPLETE_EXCLUSION.md,
with the exact private-equation lift in Section 5 of the
negative-application source. The real boundary path gives the
strict full-resultant cone, the three genuine radial proper
concurrences and the winding-one auxiliary polygon. Premise (4)
gives the complete root cover. Section 4.2 gives the zero-winding
root correction in its remaining one-improper case.

The resulting actual ring encloses the unchanged U, including
closed-origin limits. Its three real boundary members are exactly
the domain of FOUR_CYCLE_THREE_BOUNDARY_HOLE_EMPTY.md. The middle
body's full circle load remains in both the cone and the winding.
This closes the last C4 mask.

## 6. Every diamond root orbit and K4

For a hub-rooted diamond H,K,A,B, the private hub K is truly
loaded by NO_UNLOADED_DIAMOND_HUB.md. Each private true-degree-two
tip is loaded because its two physical neighbors touch. These
local obstructions allow all original forces at H. The entire
private mask is therefore KAB.

If H physically touched the circle, H,K and either tip would
form a forbidden physical boundary triangle. Hence H is physically
clear; the actual G_H=0 and (4) follows from the real bridge.

Sections 2--8 of
ROOTED_HUB_DIAMOND_ORIGIN_TRIANGLE_COMPLETE_EXCLUSION.md now
apply at the exact local scope explained in Section 6 of the
negative-application source. The full K3 equation and real HK
chord remain. The complete physical-triangle coefficient lemma,
including its coincident and parallel alternatives, orders all
three actual root forces. The genuine private boundary path
supplies the proper tip concurrences and angular interval.

Premise (4) excludes the parallel root cap. In the nonparallel
case the full correction-triangle split either gives the exact
two-neighbor proper-port cap contradiction, or gives a winding-one
outer ring with three physical boundary members enclosing U.
The same physical four-ring theorem excludes the latter. H
avoids O by (3), so every original homotopy and closed-origin
limit is retained. No artificial degree-two equation is imposed
on K and no diamond force is split into separate triangles.

If H is a diamond tip, both private hubs have true degree three
and are loaded by NO_UNLOADED_DIAMOND_HUB.md. The other private
tip is loaded by its true degree-two touching-neighbor obstruction.
Those three private bodies already form a forbidden physical
boundary triangle. This covers the tip-root orbit independently
of H's circle force.

Finally NO_POSITIVE_K4_SUBGRAPH.md excludes the selected positive
K4 profile with arbitrary original external edges. These are all
four-body biconnected profiles, completing the theorem.

## 7. Scope of the corrected result

The full equation is always (2) with the outward-circle plus sign.
Every use of (4) has been supplied at its actual load mask:
genuine zero load or proved physical clearance, except for the
opposite mask's complete acute-circle argument. Section 4.2 has
removed the positive-M-point requirement rather than manufacturing
such a point from the wrong-signed root equation.

U need not be a leaf, transmitter, or origin-interior unit. The
single external block bridge and strict rho<0 are still required;
no zero-support case is added by a limit. All nine physical bodies,
every original mask and weight, and every actual mean remain.
No Lean compilation or CI is claimed.

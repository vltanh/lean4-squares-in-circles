# The complete three-loaded C4-with-leaf branch is excluded

**Status: complete whole-branch hand assembly; root and two separate independent
assembly audits passed.** Throughout,
\[
                  \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16}.
 \tag{1}
\]

**Theorem.** A selected positive component cannot have pair graph
\[
                    A-B-U-C-A,\qquad A-L,
 \tag{2}
\]
where L is a leaf and all three non-articulation cycle bodies B,U,C
carry positive circle load. Both radial leaf types, every articulation
frame, every physical circle-corner mask, every genuine point or shared
side contact, and all four arbitrary other packing squares are retained.

This is a core exclusion. It needs no secondary minimizing choice and
moves no square. The canonical secondary choice is needed only for the
separate opposite-loaded-pair C4 theorem; it is not an unstated premise
of the present three-loaded theorem.

## 1. Exact graph and geometric prerequisites

The radial bridge/leaf theorem makes L a radial S or radial D unit,
and makes A physically circle-clear. In particular A has zero circle
weight. Each of B,U,C has exactly two positive pair neighbors and a
positive total circle load. Every such body has a boundary neighbor,
so the proper positive radial concurrence theorem in
`TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md`, Lemma 2.1, applies when
used below. Its actual applications include all shared-side means.

A physical two-circle-corner square remains in that physical mask even
if one of its individual circle weights is zero. No argument changes
its physical frame on the basis of that zero weight.

The physical boundary contact and corner-order theorems apply to BU
and UC independently of their contact owners. The leaf supplies the
separate eastern boundary port after normalization. No physical AU
contact is assumed and no positive AU multiplier is introduced.

## 2. The entire S-leaf family is excluded

Normalize the S leaf as
\[
 L=[h,h+1]\times[-1/2,1/2],\qquad
 h=\sqrt{R^2-1/4}-1.
\]
Its inner midpoint `(h,0)` is A's right support. The following two
geometric families exhaust A.

| Articulation frame | Complete source and scope |
| --- | --- |
| Aligned | `FOUR_CYCLE_ALIGNED_S_ARTICULATION_EXCLUSION.md` retains the full slider `A=[h-1,h] x [t-1/2,t+1/2]`, `-1/2<=t<=1/2`. Its force-feature and boundary-center argument excludes every normal and every actual mean. |
| Tilted | `FOUR_CYCLE_TILTED_S_ARTICULATION_EXCLUSION.md` retains the full right-vertex family, including the diagonal endpoint and both reflected orientations. The exact corner-radius dichotomy removes an entire rounded-rectangle center quadrant and forces a B-to-C western gap larger than the two physical boundary contacts can span. |

The tilted source uses the actual distance from a boundary center to
its shared point in A, not a replacement disk-packing assumption.
Both sources keep all physical masks of B,U,C. They exclude the entire
S-leaf branch without a contact-owner selection beyond the existing
necessary certificate.

## 3. The entire nonparallel D-leaf family is excluded

For a D leaf normalize
\[
 r=R-\sqrt2,\quad s=1-r,\quad
 A=[-s,r]\times[-v,H],\quad H+v=1,\quad H,v>0.
 \tag{3}
\]
Its leaf force is horizontal and has zero origin moment.

`D_FOUR_CYCLE_NONPARALLEL_SINGLETON_EXCLUSION.md`, Lemma 2.1,
first proves that every nonparallel pair of A cycle forces, with
arbitrary actual means, concurs at `(q_A,0)` with `q_A>0`.
The proof uses proper boundary concurrences and the actual circular
order B,U,C cut at the eastern D leaf. This positivity is established
before any remaining contact-feature restriction.

If both A-cycle intersections are singletons, the complete alternatives
are:

* Both normals have negative first coordinate: the two A applications
  are its left vertices, and `D_FOUR_CYCLE_LEFT_VERTEX_EXCLUSION.md`
  excludes the full branch, including every BU/UC owner and U mask.
* One normal has positive first coordinate: Section 4 of the
  nonparallel-singleton source excludes its entire right-vertex branch.
* One normal has zero first coordinate: Section 5 of that source
  excludes the full vertical-singleton branch.

Positive leaf balance excludes the missing all-vertical pair. The
fixed-application normal selections are used only where both physical
A applications are fixed singletons.

If an A-cycle intersection has positive length, its normal is an A
side axis. A nonparallel pair cannot contain a horizontal normal:
vertical equilibrium would make the other normal horizontal as well.
Thus the shared contact is on A's top or bottom side. These are
precisely the complete reflected families excluded by
`D_FOUR_CYCLE_SHARED_VERTICAL_EXCLUSION.md`.

That shared-side proof never fixes its application mean. It first uses
the actual interval `0<q_A<=r`. At a free opposite A-corner contact,
an admissible vertex-normal interval has an A-axis endpoint. A strict
normal sufficiently near that endpoint forces either `q_A<0` or
`q_A>r`, eliminating the free contact before multiplier extraction.
The resulting owned-tip height estimate gives `H<1/4`; actual D-leaf
avoidance then puts all four corners of the aligned shared neighbor
strictly inside squared radius `41/16<R^2`.

These alternatives exhaust all nonparallel A reactions. Shared means
on BU and UC remain arbitrary throughout.

## 4. The entire parallel D-leaf family is excluded

The full reduction and aligned-tip theorem are in
`D_FOUR_CYCLE_PARALLEL_ALIGNED_TIP_SIGN.md`. Its Section 1 first
handles the signs of the parallel normals. They are horizontal, but
force balance alone would permit opposite signs. In that alternative,
A torque makes the two application heights have the same strict
sign. Proper boundary concurrences and the ordered circle intervals
then give the same vertical sign to all three non-leaf circle
resultants, contradicting global force balance with a horizontal
leaf. Thus both A cycle normals are `-e_x`.

Their actual wall means have the full form
\[
 P_B=(-s,y),\qquad P_C=(-s,-w),\qquad
 y,w>0,\quad y+w\le1.
\]
The boundary-point distance and actual wall interval yield
\[
 \frac38\le s<\frac49,\qquad
 \frac13<y,w<\frac23,\qquad
 |P_B|,|P_C|<\frac56.
 \tag{4}
\]
Consequently both tips are physically unique-corner, with their circle
corners strictly northwest and southwest. Their actual A applications
may still be arbitrary shared-side means.

For each aligned tip, the aligned-sign source excludes every negative
first component of its outward normal toward U. Its proof uses that
actual mean in the radial concurrence, and screens the only possible
negative-x support vertex by a support value strictly greater than
`R-1`. Other endpoints and all harmless nonnegative-x normals remain.

For each tilted tip,
`D_FOUR_CYCLE_TILTED_WALL_TIP_EXCLUSION.md` proves the stronger
strictly positive first-component conclusion. Its complete argument
includes the following global steps, independent of the U mask.

1. Both wall tips have western open-interior tails longer than
   `22.5 degrees` on the same radius-`5/4` circle. The boundary U
   occupies a connected open arc longer than `45 degrees` between
   them. Therefore the western B-to-C center gap exceeds `90 degrees`.
2. For a tilted upper tip with inward axes `(-a,b),(-b,-a)`, proper
   concurrence gives `a<=b`. The preceding gap forces `b-a>7/10`:
   otherwise the actual B/C center dot product is greater than
   `27/3200`, making that gap acute.
3. This full tilt range screens the lower mixed-normal vertex by
   support greater than `227/225>1`, and screens the outer lower
   side by support greater than `1+41/225`. Here (4) gives
   `R^2<17/4`, while any unit beyond support greater than one needs
   squared containing radius greater than `17/4`.
4. Vertical force balance and the remaining exact square features
   leave only normals with strictly positive first coordinate.

Let `g_B,g_C` denote the actual outward normals from the tips toward
U. The two complete tip theorems give
\[
                          (g_B)_x,(g_C)_x\ge0.
 \tag{5}
\]
Every physical circle corner of U is acute to both the northwest B
corner and the southwest C corner, because U physically touches both
bodies. A vector with nonnegative first coordinate cannot be acute to
both. Thus U's circle resultant `m_U` has strictly negative first
coordinate, including every physical two-corner weight split.

The outward pair normals at U are `-g_B,-g_C`. Its actual balance is
\[
                    2m_U-\mu_B g_B-\mu_C g_C=0,
                    \qquad\mu_B,\mu_C>0.
 \tag{6}
\]
The first coordinate of (6) is strictly negative by (5), a
contradiction. This excludes the entire parallel family. No side
owner, coincident endpoint, free point normal, U frame or U physical
mask remains outside the two tip theorems.

## 5. Certificate compatibility and exact conclusion

All normal choices precede multiplier extraction. The nonparallel
singleton arguments use the established finite fixed-application
conditions. The shared vertical argument uses strict endpoint
neighborhoods within the same admissible point-normal intervals,
never the axis endpoints themselves. Its simultaneous-choice proof
retains the mirrored four-junction convention and the actual shared
mean. The parallel sources make no additional normal selection.

Uncrossing preserves every surviving point-edge normal and adds only
actual shared-side forces; conic thinning deletes atoms. The source
theorems explicitly retain the resulting side means and endpoint
means. They do not rotate any obtained force after a certificate has
been extracted.

The full S articulation frame cover and the full D nonparallel/parallel
cover are now exhausted. Thus no selected component of the form (2)
with all three non-articulation cycle bodies loaded survives anywhere
in (1). All contradictions are strict at the upper endpoint as well.

This theorem closes the last load branch of the C4-with-leaf graph.
Combining it with the older adjacent-load and canonical opposite-load
assemblies closes that graph in the radius-lower-bound proof. The
entire four-body-block-plus-leaf cell also requires the independently
completed diamond and K4 exclusions. This source does not claim an
unrestricted classification of larger positive components or of all
original equality packings.

No numerical optimization, arithmetic pose cover, Lean compilation,
or CI is a premise of this hand assembly.

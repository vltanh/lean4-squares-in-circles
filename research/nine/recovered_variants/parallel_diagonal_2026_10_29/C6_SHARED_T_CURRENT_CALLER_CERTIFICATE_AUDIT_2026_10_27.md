# Current-caller audit of the 1080 shared-T comparisons

Date: October 27, 2026.

**Status: complete dependency audit for the whole bare-C6 assembly;
pending independent acceptance.** Every current source cited below was
read at the pinned PR11 head
`8680a4b9204c0d6fb82a8d052ece5bb52aa9b6c8`.
The conclusion is caller-scoped. It does not assert that every
historical or rooted-component use of the underlying local results has
been removed.

## 1. Exact certificate identity and old scope

`C6_SHARED_T_SIDE_ARC_CERTIFICATES.md`, Sections 1--5, proves four
inequalities on its complete shared-T parameter triangle
\[
 \alpha,\beta\ge\pi/4,\qquad \alpha+\beta\le3\pi/4.
\]
The triangle is rationally parametrized by one closed unit rectangle.
The source keeps the exact normalization
\[
 F=S[A-(1-\ell)B]+\ell CA,
\]
and the physical shared-T torque is precisely \(F=0\). In particular
the certificate is not reused with \(F/S\).

Its four targets and counts are:

| Target | Polynomial degree | Exact coefficient comparisons |
| --- | --- | ---: |
| \(h_B-21/50+F/4>0\) | \((18,10)\) | 209 |
| \(h_C-21/50>0\) | \((12,6)\) | 91 |
| \(4c_T\cdot c_B+3\det(c_T,c_B)>0\) | \((24,14)\) | 375 |
| \(4c_C\cdot c_T+3\det(c_C,c_T)>0\) | \((26,14)\) | 405 |
| **One shared packet** | | **1080** |

The preserved data and derivation are
`C6_SIDE_ARC_CERTIFICATES.json` and
`C6_SIDE_ARC_CERTIFICATES.js`.
This packet is counted once, even when more than one mask-specific
caller uses it. Its 209-entry first polynomial is not identified with
a different historical packet merely because the counts agree.

The physical geometric assembly
`SIX_CYCLE_ONE_DIAGONAL_SIDE_CAPACITIES.md`
requires the entire selected positive component to be the alternating
six-cycle
\[
 B-W-C-U_C-T-U_B-B,
\]
with three unique physical circle corners and exactly one diagonal
transmitter W. It establishes the actual channel heights, center-angle
branches, complete endpoint arcs and whole exterior-pocket routing.
The four scalar inequalities are used together with those geometric
facts to give capacity at most one in each side pocket. This is a
specific complete family, not a purely formal inference from the four
polynomial signs.

## 2. The two audited older bare-C6 callers

The old all-mask parent
`SIX_CYCLE_ONE_DIAGONAL_ALL_MASKS_EXCLUSION.md`
has two uses of this same packet.

| Original physical subfamily | Actual dependency path |
| --- | --- |
| UUU, all three diagonal-cycle loads physically unique | Section 2 invokes SIX_CYCLE_ONE_DIAGONAL_SIDE_CAPACITIES, whose Sections 2--5 invoke the four shared-T scalar inequalities and the full actual-pocket arc argument. |
| SUU or its reflected USU image, unique C, nonaxis C return, high angular sector \(\alpha\ge\pi/4\) | Section 5 invokes SIX_CYCLE_ONE_DIAGONAL_RADIAL_INCIDENT_NONAXIS_EXCLUSION. Its high-angle argument transfers the actual radial B corner and the unchanged unique-T torque to the same original rectangle, and then transfers the complete side-capacity routing. |

The second transfer includes the physical endpoint \(\alpha=\pi/4\);
it does not equalize the radial B corner weights. Its low-angle and
owned-feature subcases have other original arguments, including
separately counted coefficient obligations. Those are not part of
the 1080 packet audited here.

Thus removing only the all-unique side-capacity call would be
insufficient: the incident-radial transfer must also be bypassed.
The present whole-C6 caller does bypass both.

## 3. Exact current replacement caller

The accepted current source
`GENERAL_SIDE_CHANNEL_CAP_CENTRAL_INJECTION_BOUND.md`
already gives a complete theorem for an entire simple positive cycle
with at least three loads and at most one actual unloaded degree-two
transmitter between consecutive loaded bodies. The same nine-square
measure theorem supplies \(R>2\) for its complete nine-unit caller;
it does not assign this bound to an isolated six-unit core.

The replacement preserves every actual mask, circle weight, force,
normal, shared mean, core body, extra square and weak junction. Its
proof needs the following complete physical chain:

1. Actual pocket routing assigns every extra to the central free union
   or one original exterior channel. Direct loaded-loaded pair pockets
   and radial endpoint caps are empty.
2. Every actual diagonal-transmitter exterior pocket is empty, by the
   full-mask local theorem
   `FOUR_C6_DIAGONAL_CHANNEL_CAP_EMPTY.md`.
3. An actual side-transmitter exterior pocket has capacity at most one,
   by `GENERAL_SIDE_CHANNEL_EXTERIOR_CAPACITY_ONE.md`.
   Its proof handles unique endpoints analytically; its physical-radial
   endpoint input is
   `RADIAL_LOAD_SIDE_CHANNEL_POCKET_CAPACITY.md`.
   Neither invokes the shared-T 1080 packet.
4. Every occupied side pocket supplies its own unchanged transmitter U
   with \(\operatorname{dist}(O,U)<1/60\), by
   `FOUR_C6_SIDE_OCCUPIED_CAP_TRANSMITTER_PROXIMITY.md`.
   Its actual vertices lie outside radius \(7/100\), by
   `SIDE_CHANNEL_PORT_MARGIN_AND_NEAR_ORIGIN_THREE_UNIT_EXCLUSION.md`.
5. Each central extra itself meets the disk of radius \(1/40\), while
   all its actual vertices lie outside radius \(3/50\), by the arbitrary
   finite-ring restriction in
   `C7_INNER_SIDE_CORNER_RESTRICTIONS.md`.
6. Assign a central extra to itself, and an exterior extra to its
   actual channel transmitter. This assignment is injective into actual
   pairwise interior-disjoint units. The same near-origin angular
   theorem gives at most two such units, hence at most two extras.

The complete bare-C6 application in Section 4 of the injection source
retains the full six loaded-vertex orbits. The two longer-channel
orbits use their existing complete core contradictions. The alternating
three-load orbit, the two remaining four-load orbits and the five-load
orbit use the uniform at-most-two-extra theorem. In particular the
alternating orbit is treated for every physical mask at once.

This replacement makes no use of the old all-unique/one-radial/
two-radial alternating classification. Accordingly neither of the two
1080-dependent old calls in Section 2 lies on the current bare-C6 proof
path. The whole six-cycle conclusion is obtained with the same three
original extras, so no residual allocation or mask case is omitted.

## 4. Radial leaves: checked distinction and no unsupported extension

The injection theorem requires the entire positive component to be
the stated simple cycle. A true root carrying a genuine radial leaf
has degree three, and its original external force cannot be deleted
to manufacture this hypothesis. Zero origin moment of that genuine
leaf alone does not prove every pocket-routing, proper-concurrence or
whole-component hypothesis in Sections 1--3 of the injection theorem.

A relevant current rooted example was checked directly:
`S_LEAF_C5_RADIAL_BC_POCKET_CAPACITY.md`.
Its whole original component is
\[
 A-B-V-C-U-A
\]
with an actual S leaf at A. It proves that the actual B--V--C pocket
has capacity at most one, and is empty if B is radial. Its Sections
1--3 explicitly account for the root leaf, prove that its branch and
the other cycle applications lie below the channel, and identify the
physical outward crosscut before transferring the local radial arc
bounds. Its Section 4 then invokes Sections 3--6 of
`RADIAL_LOAD_SIDE_CHANNEL_POCKET_CAPACITY.md`, not the
shared-T packet. The current aligned and tilted far-endpoint sources
supply the actual radial C and reserve-one channel premises.

That checked rooted caller therefore does not require a fictional
simple-cycle reduction and does not revive the 1080 packet. This
observation is confined to that actual local caller. No claim of a
complete repository-wide dependency scan, and no general
leaf-attached-cycle extension of the injection theorem, is made here.

## 5. Precise accounting and files retained

For the current **whole bare-C6 caller**, the 1080 packet has zero
required coefficient comparisons. This is a retirement of one shared
packet from that caller, not two retirements of 1080 for its two old
mask-specific uses, and not a new graph closure beyond the current
entire-C6 theorem.

The following distinct dependencies remain:

| Proof input | Current scoped status |
| --- | --- |
| Shared-T 1080 packet | Bypassed by the entire bare-C6 caller; no global-use claim. |
| Balanced diagonal-cap original 202 packet | Still on the current diagonal-cap path. The separate three-inequality analytic replacement removes 76 upon acceptance, leaving Certificate IV's 126 entries active. |
| Same-nine-square \(R>2\) theorem | Five fixed mass charges and one fixed derivative enclosure remain explicitly required. |
| Older packets of sizes 1559, 45, 209 and 288, and 12 earlier matrix certificates | Previously retired under their own established scopes; not recounted here. |
| Any other historical non-C6 or unfinished rooted/attached caller | Unchanged unless a separate full current-caller audit proves replacement. |

Every historical source, scalar certificate, script, coefficient-data
file and review remains intact. The proof-count statement concerns
which inputs the indicated current theorem needs. It asserts no
unrestricted sharp bound, equality classification or new graph gate,
and it uses no Lean run, CI, numerical sample or remote mutation.

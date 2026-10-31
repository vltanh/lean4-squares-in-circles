# Combined marked-cycle budget and the eight-body five-load side reduction

**Date:** October 30, 2026 UTC. **Status:** complete literal join of
frozen geometric inputs, awaiting independent full review. No earlier
source or original case flag is changed.

## 1. Exact same-certificate setting and inputs

Work in the radius window `79/40<=R<=sqrt(1105)/16` with actual
interior-disjoint unit squares. Let a simple cycle of m actual bodies
have at least two marked physical circle-touching bodies. Each
marked-to-marked run has one common signed actual support normal.
The same actual graph has the compatible physical embedding and
preserved marked boundary spokes of the base theorem below.

Every run has zero, one or two internal bodies. Write

* k_0 for the number of direct runs;
* k_1 for the number of all one-internal-body runs;
* d for the subset of those runs whose actual internal support width
  is sqrt(2), so `0<=d<=k_1`;
* ell for the number of two-internal-body runs.

Thus the total body count and mark count t are

    m=k_0+2*k_1+3*ell,
    t=k_0+k_1+ell=m-k_1-2*ell.                          (1)

The literal inputs are:

| Input | SHA256 |
| --- | --- |
| `UNIFORM_MARKED_CYCLE_ANGULAR_BUDGET_AND_NINE_BODY_CYCLE_EXCLUSION_2026_10_30.md` | `b5d9f55141ca2ab2c4f4195de68a714340fa2de607b8b9e81bb484578e4b16be` |
| `SHARP_LONG_AND_DIAGONAL_RUN_ANGLE_BUDGET_2026_10_30.md` | `614382093c6c976e7767855c5234419fe3a3c477bafc8c4465e46d86446e56fc` |
| `BOUNDARY_UNIT_GAP_FORCES_OBTUSE_CENTER_ANGLE_AND_FOUR_LOAD_EIGHT_CYCLE_EXCLUSION_2026_10_30.md` | `fa63e0ef4a0d94d47ff05e848b46792ac2861d0504b8369bc109beb3fd7d5e5a` |

The first supplies the actual cyclic center order and strict
forty-degree direct-run bound. The second supplies strict bounds
of 105 degrees for diagonal-width single runs and 175 degrees for
long runs. The third improves every single run to more than ninety
degrees, regardless of its actual internal orientation.

## 2. Combined exact integer inequality

The successive positive center angular gaps sum to 360 degrees.
Each is at least its endpoint minor angle. Thus the four run classes
give

    360>40*k_0+90*(k_1-d)+105*d+175*ell
       =40*m+10*k_1+15*d+55*ell.

Dividing by five and using integrality proves the uniform statement

    8*m+2*k_1+3*d+11*ell<=71.                           (2)

All inequalities used in this sum are strict; no equality boundary
case is lost at an integer threshold. The actual marked angular
order comes from the frozen compatible-embedding proof, not from a
new force polygon or an assumed origin-containing cycle.

## 3. The entire eight-body marked-cycle remainder

If m=8, equation (2) first forces ell=0, since `64+11>71`.
Then k_1=8-t by (1), and (2) becomes

    2*k_1+3*d<=7,
    3*d<=2*t-9.                                         (3)

At most four singleton runs are possible when ell=0 and m=8,
because k_0>=0. Hence t>=4, and t=4 contradicts (3).
The complete surviving count restrictions are therefore:

| Marks t | Singleton runs k_1 | Diagonal-width singleton runs d |
| --- | --- | --- |
| 5 | 3 | 0 |
| 6 | 2 | at most 1 |
| 7 | 1 | at most 1 |
| 8 | 0 | 0 |

Every marked body is a physical boundary body. The table permits
arbitrary cyclic placements of the direct and singleton runs,
arbitrary endpoint true degrees and all other physical squares.
It is a necessary restriction, not an existence claim for a row.

In particular every compatible eight-body cycle with five marked
boundary bodies has three singleton runs and no diagonal-width
singleton. One such diagonal would require

    8*8+2*3+3=73<=71,

which is impossible. This excludes the entire five-mark diagonal
feature, across every cyclic placement, in one inequality.

## 4. Complete force and moment callers

For a full translational stress, each unmarked cycle body must be
unloaded and have true positive degree two in the same retained
graph. Its complete two-force equation propagates the signed
support normal through the run. Marked bodies may have arbitrary
other positive contacts, attachments or chords, all retained.
This is sufficient for (2) when d is read from actual support widths.

If the same retained certificate also satisfies the original full
moment equations, the exact one-body classification from the
diagonal input applies: opposite physical support means and zero
moment give a width-one side-normal transmitter or a width-sqrt(2)
diagonal transmitter. Thus d=0 means all singleton transmitters
are side-normal in this full force-and-torque caller.

For an entire simple positive component with five positive-circle-
weight bodies and eight total bodies, marking those five yields
the first row of the table. All three actual internal transmitters
must therefore be side-normal. This conclusion is uniform in
their cyclic placement, original side means and physical circle
masks. It does not presume the same discrete classification for
a merely translational certificate.

The geometric theorem also permits marked zero-load physical
boundary bodies and additional positive edges at marks. Every
predicate and the compatible embedding must refer to the same
actual certificate; full degrees cannot be imported from a
different stress selection.

## 5. Retained families and verification boundary

Equation (2) retains the side-short seven-body record orbit
`(2,0,1,0)`, whose values are `m=7`, `k_1=1`, `d=0`, `ell=1`
and whose left side is 69. The four-load seven-body diagonal-short
variant has left side 72 and remains excluded. The combined
inequality does not close the five-mark all-side eight-body family
or the other surviving rows of the table.

This source is an exact literal join: it adds no geometric
normalization, orientation table, stress selection, numerical
search, Lean compilation or CI premise. Earlier frozen sources,
original ledger flags and repository metadata are unchanged.

# Root physical review: coupled three-square energy conversion

The root reviewed the complete hand argument and both Python implementations on
4 November 2026. This is an independent mathematical/source review, not human
or proof-kernel verification. The imported geometric premise remains the accepted
three-physical-square energy bound 7/2, bound below by its immutable source hash.

## Reviewed mathematical points

1. The two projection differences are formed from the same three original centers.
   The third difference is their sum. The polygon therefore retains the exact
   relation that the older three independent secants discarded.
2. Rectangle clipping by the two sum halfplanes preserves the entire closed
   domain, including contact, segments and points. The explicit sum-interval
   emptiness test is necessary and sufficient. No positive clearance is assumed.
3. The displayed convexity identity is a sum of three squares. Checking an
   affine majorant at every vertex proves it throughout the polygon. The
   literal checker recomputes the minimum permitted intercept from all vertices;
   it does not trust producer facet indices or a numerical optimizer.
4. The perpendicular projections have common squared norm p^2+q^2. Their energy
   sum is exactly that norm times the physical center energy. The (1,1) direction
   therefore uses threshold 7, while (1,0) uses 7/2.
5. Expanding the negative affine term gives coefficients A*e, (B-A)*e, -B*e
   on the three centers. Their sum is zero. The independent checker recovers
   A and B by orthogonal projection and rejects coefficients on other originals.
6. Cartesian and diagonal enclosures describe the same physical difference.
   Their intersection can only restrict the necessary domain. An empty
   intersection is used only with a strict rational contradiction.
7. Every accepted row is necessary for the original nine-square witness; no
   replacement frame or altered marked bit is introduced. A caller must still
   reconstruct the interval antecedents, pay every rational coefficient residual,
   and cover its full parent before claiming an original-cell closure.

## Reproduction and observed scope

Run `python -B check_coupled_three_energy.py --report ROOT_RELOCATED_REPLAY.json`
from this directory. The fresh root replay compares the separate intersection
and clipping constructions on 3,375 rational domains, compares and literally
validates 2,568 representative rows, and rejects three damaged controls.
The hand proof supplies the general argument; the finite fixtures check these
implementations and do not stand in for the theorem.

The arithmetic fixture is explicitly not an independently established physical
caller. Separately, an unreleased D6c5 bound-induction replay in this working
session checked 72 occurrences of these literal rows against the full original
ancestry; that state remains OPEN. No original-cell or mask closure is claimed.
The public ledgers remain 219/231 original cells and 8/32 masks CLOSED.
No Lean compilation, Lake or CI was run.

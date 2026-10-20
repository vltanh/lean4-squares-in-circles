module

public import SquaresInCircles.Eight.TableFree.CentralForbiddenWidths

/-!
# The central forbidden-width interface

Uncompiled table-free replacement. The public `bandA_forbidden` and
`bandB_forbidden` declarations now follow from connected rectangle geometry,
three intrinsic calculus regimes, and a single monotone polynomial.

The previous 1,800-plus-line dyadic rectangle cover and its `Row` certificates
are no longer imported. Their source remains available in Git history.
No compiler, native evaluation, or external certificate run is required by
this source transcription. Acceptance by Lean is still unverified.
-/

@[expose] public section
# Independent B review of original-corner disk support rows

Reviewed the producer, independent literal checker, numerical direction selector,
and hand proof supplied in `d_work/adaptive_corner_disk`. Exact source hashes are
recorded in `ADAPTIVE_CORNER_DISK_B_REVIEW.json`; the copied source bytes are unchanged.

For an original center `(x,y)` and its independent unit frame `u=(α,β)`,
`Ju=(-β,α)`, the corner indexed by `ε,τ∈{−1,1}` is
`(x+(εα−τβ)/2, y+(εβ+τα)/2)`. Expanding its scalar product with `(a,b)`
gives coefficients `a,b,(εa+τb)/2,(εb−τa)/2` on the existing center and
signed frame variables. The producer and independent checker both have these
signs and indices correctly. In particular, the second frame coefficient uses
the signed β variable, not the separately stored absolute value.

The caller's original corner predicate is `||z||²≤1105/256`. Cauchy–Schwarz
therefore gives `(a,b)·z≤sqrt((a²+b²)1105/256)`. A nonnegative rational upper
bound `U` is sufficient. The independent condition
`256U²≥1105(a²+b²)` is exactly the needed condition; it is valid at equality
and for either sign of each direction coordinate. There is no division by a
direction coordinate and no loss of an axis direction or corner sign.

The producer takes an integer square root after flooring the scaled rational,
then increments once exactly when its square is too small. This yields the
least multiple of `2^−40` above the target square root. The checker does not
share that algorithm: it directly validates the displayed squared inequality,
nonnegativity, literal coefficients and all original/sign labels. Allowing a
larger valid rational `U` is sound and can only weaken the support row.

The numerical separator merely chooses rational directions from an LP point.
Its tolerances and rounded direction do not participate in validity. Every row
is global for the unchanged original corner, so rows can be retained across
different closed descendants without any interval or SAT ownership premise.
The surrounding proof still has to retain all nine original frames, all corners
and pair predicates, and the original marked conditions. This lemma supplies no
original-cell or mask conclusion by itself.

As an additional independent implementation review, 144 rows covering every
original and corner sign and four rational/axis directions passed independent
literal reconstruction. Direct substitution of four rational frame/center
fixtures per row gave 576 exact coordinate expansions. The broader producer
control suite is separate. No mathematical or code defect was found.

For B discovery, `b_objective_corner_runtime.py` appends these rows in the same
active LP row list as the accepted Gram rows. Appending never renumbers existing
rows, and the exact B adapter reconstructs every weighted corner literal from
the independent checker. Neither floating-point feasibility nor a numerical
infeasibility report constitutes proof.

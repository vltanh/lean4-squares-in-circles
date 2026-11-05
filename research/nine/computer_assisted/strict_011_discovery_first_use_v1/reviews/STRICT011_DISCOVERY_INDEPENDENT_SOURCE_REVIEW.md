# Independent review of the fresh strict-011 discovery entry

The discovery source passes review of its proof boundary and complete
frontier updates. The reviewed versions are v1 `365d87c7...` and v2
`58a85d79...`; v2 adds only the solver option `threads=1`. Removing exactly
that keyword reproduces the complete v1 AST. This is source review, not a
numerical run or another arithmetic replay. The first actual LP gate remains
a separate obligation.

## Exact residual payment

The numerical phase and objective solves only propose row weights. Each
retained weight is a positive integer divided by 2^40. Non-finite values
fail; negative suggested multipliers are clipped to zero. No dual
feasibility status, primal point, objective value, or floating tolerance
enters the mathematical acceptance decision.

For weighted physical rows A_j x<=b_j, let c=sum(lambda_j A_j) and
r=sum(lambda_j b_j). Every column, including selected physical product
auxiliaries, has an independently reconstructed absolute bound B_i.
The proposed contradiction reserve is -r-sum(B_i*abs(c_i)). If positive,
the weighted physical inequalities are impossible. For an objective l*x,
the code instead subtracts l from c and proves
l*x<=r+sum(B_i*abs(c_i-l_i)). It rounds this rational upper bound upward
on the frozen 2^-20 grid. A lower bound is represented by an upper bound
on the negated objective, with the matching sign conversion on insertion.
All objectives use the same certified propagated state for their round.

The frozen independent core reconstructs every weighted literal, all
absolute bounds, exact sums, residuals, rounded bounds and resulting state
before the record is stored. The set of printed rows is exactly the set
used by at least one proposal. Interval and analytic-frame contradictions
must match the existing terminal witnesses. The fresh adapter has an
identity angle-inference function, so the driver's empty frame-inference
list and unchanged slopes agree with that exact contract.

The recorded hand-selected dual controls are valid exact checks but do
not constitute a real LP test. Their bound fixture has zero residual; the
actual LP gate will additionally exercise whatever rationalization
residual its genuine numerical dual produces. This distinction does not
change the correctness of the inspected exact residual formula.

## Complete physical covers

Initialization independently replays the full incoming representative
frontier before creating an output. The root and every physical formula
are pinned to the reviewed full strict-011 checkpoint, with no legacy
001 V/K initializer or registered-original normalization.

Each split reconstructs its parent through the exact core. Proxy splits
retain four axis/sign choices, physical SAT splits retain all eight
owner/axis/sign choices, and angle splits retain both closed halves at a
strictly interior rational cut. The physical children are independently
constructed and compared with the producer. Every pending child starts
as an explicit zero-round OPEN record. Budget limits or an inconclusive
LP leave such domains OPEN; they do not remove alternatives. A final
fresh `python -B -S` replay traverses the complete tree, including all
OPEN leaves, and is the only full-tree acceptance gate.

## Atomic proof pointer

Records are immutable and named by the SHA256 of their serialized bytes.
A changed leaf writes a new record after its full exact check. The old
manifest and its referenced record bytes remain available until a new
manifest is installed. A split writes all four/eight/two children before
adding their entries and the parent split together in one atomic manifest
replacement. An existing nonleaf cannot be updated, preventing its
already attached children's initial states from becoming stale.

Before replacing the manifest, the driver rehashes every record it will
reference. The accepted atomic writer fsyncs new record bytes and their
directory, then applies the corresponding file/directory protocol for the
manifest. An exception escapes the driver. Before the manifest swap the
old complete cover is retained; after a swap followed by an fsync error,
the new manifest still refers to a complete set of written records and
the process stops. Unreferenced new records are retained. This is a
single atomic proof pointer, not a multi-file transaction or a stronger
hardware durability claim.

The five recorded interruption controls replay the last installed full
cover at each tested failure window. Separate recorded controls replay
all eight H/I owned children and both D-angle children. Source review
found no interval, physical-domain, residual-payment or complete-cover
gap. The paired receipt binds these exact sources and recorded controls.
No solver, root model, proof record, mask ledger or running worker was
changed by this review.

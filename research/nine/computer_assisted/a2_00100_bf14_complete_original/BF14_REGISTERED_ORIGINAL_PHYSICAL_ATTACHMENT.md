# Physical attachment for the complete Bf14 original

## Frozen caller and scope

The original is `negative-f14f5bc4eafdf50d`, negative baseline frontier
index 59, in the unchanged 231-original register for mask `001/00`.
Its exact path is

```json
[["angle",3,0],["angle_cut",[0,"0"],0],
 ["position_cut",[11,"1/2"],0],["f_side_escape",[5,7],[1]]]
```

The original definition source has SHA256
`ea000e84c04675fe22424e5c20d3df9d735d659065349800aef2699170bff604`.
The independently reconstructed whole-original initial record has SHA256
`63bf1a0fd1511857846e821eff14d452d68c5236205ccbb20a745005f3ffe00d`.
Both exact replays reconstruct this root from the immutable definition;
they do not promote a restricted descendant to an original.

The accepted target is the strict-radius caller `q < Q = 1105/256`.
Its corners satisfy the closed inequalities at Q used by the relaxation.
The use of those necessary closed inequalities does not change the claimed
scope: this publication asserts no global exclusion at equality, no global
equality classification and no whole-mask closure.

The original labels are A=0 through I=8. The canonical slope of square i
is `t_i=beta_i/alpha_i`, with `alpha_i>0`. The first three path entries
retain `t_D in [-1,0]`, `t_A in [-1,0]` and `y_F <= 1/2`.
The literal `f_side_escape_rows((5,7),1,3/5)` implementation gives

\[
x_H-x_F\le0,\qquad
-y_A+2y_H-y_F\le-3/5,\qquad
y_A-y_F\le3/5.
\]

The third inequality is the closed complement of the preceding height
alternative. It is retained, including equality; it is not inferred from
the exclusion of a sibling.

The caller keeps all nine distinct physical unit squares, their unit
frames, and all 36 original corners

\[
\left(x_i+\frac{\epsilon\alpha_i-\tau\beta_i}{2},
      y_i+\frac{\epsilon\beta_i+\tau\alpha_i}{2}\right),
\qquad \epsilon,\tau\in\{-1,1\}.
\]

All 36 original pair-disjointness predicates, the five center-cone
comparisons, actual AB/BC/EF/FG and strict weak CD remain in force.
All inset and product variables have meanings in these same physical
squares. No original frame is substituted or removed.

## Complete finite cover

The final tree has 679 nodes and 461 terminal domains. Its internal
unions are 64 four-member Cartesian inset covers, 19 eight-member physical
separating-axis covers and 135 two-member closed slope covers.
The counts satisfy `679 = 1 + 64*4 + 19*8 + 135*2`.

The retained 537-node original cover had two unfinished ancestral domains,
209 and 214. Existing independently decoded support rows close all eleven
remaining terminal descendants of 214 without adding a split. Domain 209
is replaced by its entire 143-node conditional cover, attached by exact
equality between the old leaf's certified final state and the new root's
initial state. All old root rounds, every sibling and every conditional
descendant are retained. The final graft changes no original definition.

Within domain 209, the last finite extensions enumerate all eight C/H
owner/axis/sign alternatives at each of three retained leaves, followed by
all eight B/F alternatives at each of the two surviving leaves. A floating
overlap diagnostic chooses which physical pair to split; it contributes
no premise or exclusion. Every alternative, including each sign and owner,
is replayed. Shared slope-cut faces belong to both children.

Each inset cover follows from disjoint interiors of the physical squares
and their contained Cartesian insets. Each physical cover follows from
the separating-axis theorem applied to the two original convex squares:
two possible owners, two owner-frame axes and two signs give eight
necessary alternatives. The exact half-supports remain those of the
original squares. A rational slope cut covers both closed subintervals.

The independent checker reconstructs every child from its certified
parent state, checks the complete alternative set, and visits every node
exactly once. Excluding all 461 leaves therefore excludes the original
root by finite induction.

## Exact bound and terminal rules

The full bound and finite-cover derivation is preserved in
`REGISTERED_B_COMPLETE_TREE_HAND_PROOF.md`, the center-difference hand
proof and all source-bound physical row packages. These generic documents
describe available rules; the concrete terminal table and replay report
identify the rules actually used in this instance.

For certified inequalities `c_k dot z <= b_k` and rational nonnegative
multipliers `w_k`, let `C=sum w_k c_k`, `B=sum w_k b_k`.
With certified absolute bounds `|z_j|<=M_j`, every objective satisfies

\[
a\mathbin{\cdot}z\le B+\sum_j M_j|C_j-a_j|.
\]

Every coefficient residual is paid. A terminal reserve
`-B-sum M_j*abs(C_j)>0` is an exact contradiction. Other terminal kinds
require their separately decoded interval, frame or accepted physical
guard. A numerical infeasibility flag is never sufficient.

The relative-support chord rows introduce no new square or separator
premise. In the signed case, exact frame products give `C>=0`,
`C^2+S^2=1` and original support `h=(1+C+|S|)/2`. Disjoint physical
squares imply that the distance between their centers is at least h.
On a certified normalized transverse interval in `[-1,1]`, concavity of
`sqrt(1-u^2)` supplies a rational lower chord `m*u+b`, with `b>=0`.
The certified nonnegative longitudinal difference therefore satisfies
`d >= m*t+b*h`. The decoder checks every sign, endpoint, support bound,
product rectangle and rational chord coefficient. Lower bounds for h
and the original products give valid linear consequences on the same
caller. The separately bound folded-frame argument uses a support no
larger than the true original support and preserves the implication.

The signed and folded derivations, including all guards, are retained in
`relative_support_chords/RELATIVE_SUPPORT_CHORD_HAND_PROOF.md` and
`relative_support_chords/OWNER_FREE_RELATIVE_SUPPORT_HAND_PROOF.md`.
The independent decoder imports no numerical producer. Exact propagation
uses previously certified intervals only, never bounds from another
unproved sibling.

## Concrete acceptance

The full native replay must report
`PASS_COMPLETE_ORIGINAL_PHYSICAL_TREE`, `complete=true`,
`whole_original_proved=true`,
`entire_registered_original_domain_retained=true`, and zero OPEN leaves.
The complete terminal
table lists every excluded leaf, its original parent and last choice,
round and deduction counts, and either an exact positive reserve lower
bound or its independently checked terminal kind. The literal records
retain all coefficients and multipliers.

The portable builder compares every ID/sign/baseline-index/path tuple
against the live 231-cell register while this original is still OPEN.
The dedicated portable replay reads only the packet and its pinned
published prior, reconstructs every bound and union with standard-library
exact rational arithmetic, forbids old-workspace reads and imports no
numerical optimizer. All frozen inputs are rehashed at completion.

Only after the native replay, complete hand/table review, fresh portable
replay and archive/member checks pass may this one original change to
CLOSED. Partial component proofs, assembler status labels and numerical
candidate counts carry no original or mask credit. Lean, Lake,
compilation and CI are not used.

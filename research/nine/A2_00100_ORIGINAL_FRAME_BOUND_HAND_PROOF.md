# Complete original-cell proofs by certified physical frame bounds

November 3, 2026. This is the exact hand/table rule used for the additional
whole original cells identified in the accompanying continuation manifest.
The fixed original-nine `001/00` predicate and all 231 path identities are
unchanged. The construction proves finite original domains; an unfinished
iteration or subtree leaves its original parent OPEN. No Lean, Lake or CI.

## 1. The same nine physical frames throughout

For each original unit square, the accepted canonical frame uses its
original slope `t` in `[-1,1]` and the exact variables

    alpha = 1/sqrt(1+t²),   beta = t/sqrt(1+t²),
    b = |beta|,             g = 1/[2(alpha+b)].

Thus `alpha>0`, `alpha²+beta²=1`, and `t=beta/alpha`.
This slope is the tangent of the original side angle; it is not the
rational half-angle used to encode an auxiliary octagon rotation.
All nine original frames are independent. Every corner and all 36 physical
pairs remain in the original caller.

The first eighteen scalar variables are the original center coordinates.
The next thirty-six are the nine alphas, nine betas, nine absolute betas,
and nine inset halfwidths. Auxiliary product variables, when present,
retain the frozen physical interpretations and rigorous variable bounds.
The exact row generator is the unchanged version14 verifier with SHA256
`ec1b7de7b15bcc9d89d12087bff974c68e6d056bdaae26b482d514027ec97993`.

## 2. Proving a scalar bound before using it

Begin with the original path's decoded angle and position intervals.
Any inherited coordinate-prefix certificate is first replayed from this
original state. None of its suggested numerical boxes is assumed.

At one subsequent round, let all already justified scalar rows be
`a_j.z<=b_j` and let `|z_k|<=M_k` be valid absolute variable bounds.
For nonnegative rational weights lambda_j and signed coordinate objective
`c=s*e_k`, with `s` equal to `1` or `-1`, set

    r = sum_j lambda_j*a_j - c,
    B = sum_j lambda_j*b_j.

The row sum and variable bounds give the exact implication

    s*z_k <= B + sum_l M_l*|r_l|.                     (1)

The checker computes this rational value directly and proves that it
does not exceed the recorded upper bound U. Equation (1) then justifies
intersecting the corresponding scalar interval with `s*z_k<=U`.
Rational rounding is outward. A numerical optimizer merely proposes
weights; no feasibility status, tolerance or suggested interval is a
premise of (1).

Every proposal in a round uses the same intervals from the beginning of
that round. All proposed bounds are installed only after their separate
exact sums pass. A later row may use these bounds because the preceding
induction already proved them. In particular the upper and lower bounds
of each original alpha, beta, absolute beta and inset variable are added
as necessary scalar rows in the next round. This is a finite acyclic
induction, including when a coordinate is bounded more than once.

The guarded unique-penultimate rows may be added only when the original
path proves their complete cone hypotheses. No such extra row is used
for the original B-family closures described below: their guard set is
empty. Their rows consist of the frozen physical rows and previously
proved scalar bounds.

## 3. Translating proved frame bounds back to the original angle

These translations use the physical unit-frame identities in Section 1,
not a norm equality assumed for an LP proposal.

If `alpha>=L>0`, then

    |t|² = 1/alpha²-1 <= 1/L²-1.                    (2)

An outward rational upper enclosure of the square root therefore gives
an upper bound on `|t|`. If a proved lower bound L exceeds one, the
physical unit frame is already impossible.

The inverse relation

    t = beta/sqrt(1-beta²)                           (3)

is strictly increasing for `-1<beta<1`: its derivative is
`(1-beta²)^(-3/2)>0`. The original canonical frame has
`|beta|<=1/sqrt(2)`, so its denominator is positive. Apply (3) to the
proved lower and upper beta bounds, with outward rational enclosures.
For negative beta the lower and upper denominator choices exchange;
the checker evaluates this sign explicitly.

An upper bound `|beta|<=U<1` similarly gives
`|t|<=U/sqrt(1-U²)`. A lower bound `|beta|>=L` gives a lower bound on
`|t|`, and an upper bound `alpha<=U<1` gives

    |t| >= sqrt(1/U²-1).                             (4)

The lower absolute bounds are converted into a single slope interval
only when the current interval has one sign. On a nonnegative interval
they raise its lower endpoint; on a nonpositive interval they lower its
upper endpoint. An interval straddling zero retains both signs. No
connected interval is silently substituted for a disconnected exclusion.

All square-root enclosures are certified by integer and rational
arithmetic in the frozen source. Every interval remains closed. After
these deductions, intersect with the analytic alpha, beta, absolute-beta
and inset ranges for the newly proved slope interval. Those analytic
ranges refer to the same original unit frame. If an interval becomes
empty, its original caller is contradictory.

Only the following round regenerates physical rows on the narrower
proved angle and position domains. This makes, for example, a narrower
McCormick enclosure valid without adding an orientation assumption.
The angle is constrained by an already proved implication from the
original parent, rather than chosen from a numerical pose.

## 4. Complete physical trees after the parent induction

The final parent bounds hold at every physical point of its unchanged
original predicate. Any child of that predicate inherits them.
Decode a child's original path in the original intervals first, then
intersect its decoded angle and position intervals with the certified
parent intervals. This order matters: an old midpoint split is never
reinterpreted as a midpoint of a newer, narrower interval.

Intersect its original-frame scalar bounds with the analytic ranges of
the resulting child angle intervals. Regenerate the frozen physical
rows, retain any correctly guarded additional rows, and append the
certified original-scalar bounds. A positive exact row-sum reserve

    -sum_j lambda_j*b_j
      -sum_k M_k*|sum_j lambda_j*a_jk| > 0            (5)

contradicts the child domain. A directly verified empty interval or an
accepted original analytic terminal is also a contradiction.

Every physical split retains all four signed inset alternatives or all
eight original owned-axis alternatives. The independent checker rebuilds
the full original-parent trie and requires every child, with closed
contact faces retained. No leaf may be another leaf's ancestor, and no
leaf is counted twice. Complete terminal coverage and (5), together with
the proved parent induction, exclude the entire original parent.

## 5. Three concrete complete original parents

For `negative-547e512df0c949e9`, the inherited coordinate prefix has 99
deductions. Two further rounds prove 128 bounds on original center or
frame variables. The resulting full parent has a direct exact
contradiction, with positive reserve

    226415574570133772664353882784071142146705142806257192201
    / 46158931341152937891180285882639622904728650584376213504000.

There is no remaining subtree in that original cell.

For `negative-685477c369fdc445`, the inherited prefix has 32 coordinate
deductions. Sixteen rounds prove 615 further original-variable bounds.
Two complete four-child inset splits, first HI and then FI under one HI
child, give seven terminal leaves. Five are directly checked propagation
or interval contradictions. The other two contain nine and seven printed
rational rows respectively and satisfy (5). Their reserves are

    602540075334441430892066167332703918254220196230917601
    / 9361524484389063512677373339963334982069518711474094080,

and

    1099043101934087227306582828423763170726921
    / 9800132167323027747745188694034924489932800.

Both are positive. The full parent union has zero unresolved leaves.

For `negative-4b5e7ea05e82b9ac`, the inherited prefix has 37 coordinate
deductions and sixteen parent rounds prove 173 further bounds. The
preserved physical tree has 106 proved leaves and seventeen pending
children. All seventeen are now closed on their exact old paths:
fourteen admit immediate exact terminals, while three require one local
bound round each, with 55, 84 and 77 deductions respectively. Each local
round starts from that child's certified inherited state and obeys the
same acyclic rule as Section 2. No further physical split is introduced.

The complete composition has 426 bound deductions and 123 terminal
paths: 82 positive rational contradictions and 41 exact interval or
analytic terminals. The reviewer checks that the seventeen replacements
are exactly the old frontier, with no repeated or missing index; replays
all 106 retained leaves; verifies every local induction; and checks the
complete trie from the immutable original parent. Thus this is a full
parent proof, not a conclusion drawn from a partial tree's leaf count.

Every original ID and full ancestor path is checked against the accepted
register. None of these certificates is a replacement domain or a
sampled pose. The three B-family certificates use no new guarded
alternative-chain rows: their required original cone guards do not
occur, so the guarded collector contributes zero such rows.

The delivered tables print every used scalar row, rational weight,
residual, proved interval update, physical frame inversion and terminal
reserve. The independent reviewer imports no producer or numerical
optimizer and reconstructs the entire induction from the original path.
Separate printed arithmetic checks recompute the row sums. No unchanged
baseline forest is represented as freshly replayed; no human or
proof-kernel verification is claimed.

These are whole original-cell closures. The complete `001/00` and
`100/00` mask obligations remain governed by all remaining original
paths in the unchanged fixed register.

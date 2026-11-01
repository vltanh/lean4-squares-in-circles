# An exact strict-Q cut from the sharp local theorem

Let P be the original strict-Q physical formula, optionally including one
fixed positional root, and let G be the conjunction of the 49 chart guards.
The model equivalence theorem and (T) of `WIDE_SLIDE_SHARP_TERMINAL.md` prove
that P AND G is impossible. Consequently

    P is equivalent to P AND NOT G.                         (8)

`build_pruned` and the command-line `--cut` option emit the right-hand side.
Every weak guard a>=b is negated to a<b and every a<=b to a>b; their disjunction
is exactly NOT G. All original predicates remain byte-for-byte identical as
expression trees. Thus one has an exhaustive two-branch cover: the chart
branch is closed by (T), and its exact complement remains a search obligation.
Shared boundary faces satisfy G when all weak guards hold and are handled by
the sharp theorem; no boundary is silently omitted.

This use of the local theorem does NOT require first proving that every root
lies in G. It safely removes the proved subdomain from every strict-Q search
where the chosen seven labels/frame are used. It also does NOT prove the
remaining complement empty. The global caller may use a finite collection of
such cuts, but all remaining assignments must still be excluded.

The cut is deliberately restricted to strict-Q mode. At q=Q a real attaining
packing can satisfy G, so imposing NOT G on the closed-Q equality problem
would discard a valid packing. The CLI rejects that combination. The exact
emitted-text tests check the complete 49-term complement, preservation of every
original predicate, and forty varied assignment controls; these assignments
are not asserted to be subcritical physical packings.

Example:

```sh
python emit_sharp_terminal.py --radius strict --cut --output /tmp/n9-with-sharp-cut.smt2
```

For a fixed positional root, the selected IDs must refer to that root's original
square labeling. No gauge is imposed on its hex cells, and no global relabeling
or common-frame premise is inserted without its explicit guard.

## Verification and remaining scope

The new 49-guard interface is derived in `WIDE_SLIDE_SHARP_TERMINAL.md`. The
cut builder retains those named polynomial definitions but replaces the guard
assertions by their exact disjunctive negation. It adds no independent real
variable and retains every original frame, corner, pair and optional cell
constraint. The unfixed-root strict model has 82 assertions; the fixed-cell
version has 138. All polynomials remain quadratic.

Run `python test_sharp_terminal_emitter.py` to reproduce the original 120
physical witness controls, 14 vertical guard endpoints, schema checks, and
40 additional complement evaluations. Invalid label choices and forbidden
closed-Q cut requests are rejected. These finite tests supplement the
propositional implication (8) and the proved geometric terminal; they are not
an exhaustive proof by sampling. No general solver UNSAT result is claimed.

This is a sound usable reduction of the original strict search, not a global
extraction theorem and not closure of A.2. No full positional root is newly
counted excluded from this interface alone. Global optimality, full equality
classification and the final complete hand/table proof remain OPEN.

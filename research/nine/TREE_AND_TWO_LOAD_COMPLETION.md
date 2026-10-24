# Complete exclusion of positive tree components and two-loaded components

The physical capacity theorems `P_ALL_COMPLETION.md` and
`Y_ALL_COMPLETION.md` now close the two continuous completion families
that remained after the tree classification. The same P theorem also
closes the entire two-loaded component class, including cyclic graphs.

The following are conditional structural consequences in the repository's
declared working radius window. They do not supply the lower endpoint
of that window or claim an unrestricted cyclic classification.

## 1. Exact common hypotheses

Consider a hypothetical physical packing of nine unit squares at a
minimizing radius \(R\), equipped with the selected positive physical
stress certificate of `PHYSICAL_CONTACT_STRESS.md`. Retain the selected
strictly exposing common normals at point-only vertex/vertex contacts,
and the earlier nonradial-normal choice at off-origin such contacts
used by the tree localization theorem. Assume explicitly

\[
\boxed{\qquad \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16}.
       \qquad}                                             \tag{1}
\]

The lower inequality in (1) is supplied by the explicit prior-theorem
import in LOWER_WINDOW_FROM_EIGHT.md: delete one square and apply the
existing n=8 theorem. That import retains the n=8 arithmetic-table
dependencies. The lower bound is not proved by the completion theorems
or by this corollary note.

Only components of the nontrivial positive stress support are considered.
Every physical square outside such a component, and every zero-weight
physical contact, remains in all the completion premises.

## 2. Every selected positive tree component is excluded

**Corollary T.** Under the hypotheses above, the selected positive graph
has no tree component.

`TREE_BODY_LOCALIZATION.md` and `TREE_RADIUS_QUANTIZATION.md` put any
such component at squared radius \(17/4\) and into one of the six
origin-incidence profiles used in
`REMAINING_TREE_TWO_FAMILY_REDUCTION.md`. The latter manuscript exhausts
all six profiles, including their shared-edge and nonaligned boundaries.
Its whole remaining-tree theorem says that a nine-square packing with
any selected positive tree component contains either:

- an actual four-square family-P skeleton and five other physical
  squares; or
- an actual five-square family-Y skeleton and four other physical
  squares.

`P_ALL_COMPLETION.md` excludes the first possibility for every pair of
slider parameters in \([-1/2,1/2]^2\).
`Y_ALL_COMPLETION.md` excludes the second for every
\((\alpha,\theta)\in(0,1)\times(0,\pi/2)\).
The complete tree reduction therefore has no surviving completion.
\(\square\)

This excludes a tree component even when other selected components
contain cycles. It is not restricted to a certificate whose entire
positive graph is a forest.

## 3. Every exactly-two-loaded component is excluded, including cycles

**Corollary TL.** Under the hypotheses above, no selected connected
positive component has exactly two circle-loaded bodies.

The arbitrary-component rigidity theorem
`TWO_LOAD_RECIPROCAL_RIGIDITY.md`, Sections 6--7, applies without a tree
assumption. It forces squared radius \(17/4\), two antipodal aligned
radial terminals, and aligned internal layers at horizontal coordinates
\(-1/2\) and \(1/2\). The strict point-contact normal selection puts
every internal center height in \((-1,1)\), so each layer has one or
two members. Thus the component has exactly four, five, or six bodies.

For four bodies, the terminal force-and-torque balance puts both internal
heights in \([-1/2,1/2]\). This is precisely family P, whose completion
to nine is impossible by `P_ALL_COMPLETION.md`.

For five bodies, `FIVE_BODY_TWO_LOAD_REDUCTION.md` proves that either
the core contains an actual family-P skeleton or the entire five-body
core admits at most three further squares. The first alternative is
excluded by P.ALL, and the second has total capacity at most eight.

For six bodies, `SIX_BODY_TWO_LOAD_COMPLETION.md` proves that the entire
parallel-layer family admits at most two further squares, again giving
total capacity at most eight.

These three cases exhaust the rigidity theorem's conclusion. They
exclude every two-loaded selected positive component, whether its
undirected graph is a path, a cycle with attachments, a simple six-cycle,
or a more connected allowed two-column graph. \(\square\)

The common orientation in this argument belongs only to the component
supplied by the rigidity theorem. The physical completion theorems keep
all other squares independently oriented, so no common separating frame
for all nine squares has been introduced.

## 4. Remaining scope

Corollaries T and TL close their entire structural classes in (1).
Components with cycles and three or more circle-loaded bodies remain a
separate global obligation. The prior lower-radius input is now explicitly assembled in
LOWER_WINDOW_FROM_EIGHT.md. Global assembly and equality analysis, and
Lean/kernel integration remain distinct from these completed physical
capacity arguments.

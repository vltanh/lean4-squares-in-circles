# The k=7, central-two-contact, m=6 stress path forces a circle-contact endpoint

**2026-10-12. Complete exact actual-contact graph reduction**, not
the sharp global n=8 radius inequality. This closes the supposed
m=6 subcase where *both* central stressed-path endpoints are
circle-free and C has only its two stressed actual neighbors.

## Theorem

Take an attained least-radius packing of eight genuine unit squares
under \(R^2\le9789/2500\), chosen among all radius minimizers
to have **the fewest actual square-square contacting pairs**.
Suppose:

1. All seven noncentral squares have **outer** centers (norm >=1).
2. The **actual outer-contact graph is not the full seven-cycle**.
3. C has **exactly two positive-stress neighbors** in some
   normalized physical stress, and its *actual* square-contact
   degree is **exactly two**.
4. The unique nontrivial positive-stress cycle is
   \[
   C-S_1-S_2-S_3-S_4-S_5-S_6-C
   \]
   with six **consecutive outer-center-ray** labels. The
   seventh actual exterior square is denoted T.

Then the following full-geometry structural conclusions hold:

* **The two positive central normals are aligned with a true
  central side frame**, not diagonal; C is a genuine
  circle-free **actual-degree-two transmitter** with its
  two opposite contact axes on its own opposite sides.
* In the outer-induced actual-contact graph, the **only**
  extra possible contacts beyond the five consecutive
  path edges \(S_i-S_{i+1}\) are
  \(T-S_1\) and \(T-S_6\), and **at most one** of
  those two contacts may actually occur.
* The stressed path endpoint not touching T
  must touch the **containing circle**:
  \[
  \boxed{
  T\not\sim S_1\ \Longrightarrow S_1
  \text{ has a true circle vertex},\qquad
  T\not\sim S_6\ \Longrightarrow S_6
  \text{ has a true circle vertex}.
  }                                                       \tag{1}
  \]
  In particular **at least one** of \(S_1,S_6\)
  has a true circle contact. If T touches neither,
  **both** stressed endpoints must touch the circle.
* There are exactly **three possible outer actual-contact
  edge sets for each fixed stressed path**: no T edge,
  T-S_1 only, or T-S_6 only. With seven cyclic placements
  of the six-outer stressed path, this is **21
  combinatorial actual-outer-graph templates**,
  prior to testing continuous feasibility and additional
  possible zero-weight contacts with C (which are
  excluded here by actual-degree-two assumption).

Every claim concerns **actual squares and true contacts**.
No assertion is made that all 21 templates are realizable,
or that the entire m=6 case is impossible.

## Proof

### 1. The outer geometry admits only two possible spectator edges

By the all-frame outer-center visibility theorem
[HUMAN_OUTER_GRAPH_REDUCTION.md](HUMAN_OUTER_GRAPH_REDUCTION.md),
each actual outer-square contact joins **circular
neighboring outer center rays**. The six stressed outer
labels \(S_1,\ldots,S_6\) are consecutive by the earlier
[HUMAN_SEVEN_OUTER_STRESS_CYCLE_NORMAL_FORM.md](HUMAN_SEVEN_OUTER_STRESS_CYCLE_NORMAL_FORM.md).
The only seventh outer ray is T, in the complementary
gap between \(S_6\) and \(S_1\).

The five edges \(S_i-S_{i+1}\), \(i=1,\ldots,5\),
are genuine actual contacts (they carry positive
stress). There are exactly two remaining edges of
the seven-outer angular-neighbor cycle:
\(S_6-T\) and \(T-S_1\). Any other actual outer
contact is forbidden by outer-center visibility.

If both remaining edges occurred, the actual
outer-induced graph would be the *full seven-cycle*,
contrary to the hypothesis. Thus at most one is
present. This proves the exact three-edge-set split.

### 2. C is a circle-free side-aligned actual transmitter

The central square C contains zero in its open
interior and lies **strictly inside D_R**,
because its furthest point from zero is
less than its diameter \(\sqrt2\), whereas
the established radius lower bound exceeds
\(\sqrt2+1/2\).

By hypothesis C has exactly two **actual**
neighbors, S_1 and S_6.
Section 8 of
[HUMAN_CYCLE_ANALYSIS.md](HUMAN_CYCLE_ANALYSIS.md)
proves, in the contact-minimal radius representative,
that any strictly circle-free square with exactly two
actual square contacts has *opposite contact
separating normals aligned with an actual side
of the square*. Thus C is a true
side-mode transmitter, and its two contact normals
cannot be diagonal. This also agrees with the
finite central force-axis theorem
[HUMAN_TWO_CENTRAL_FORCE_AXES.md](HUMAN_TWO_CENTRAL_FORCE_AXES.md).
No conclusion is drawn about S_1/S_6 square frames.

### 3. A free endpoint would be an impossible second adjacent interior transmitter

Suppose T does not contact S_1. In the outer
actual graph S_1 has only its positive-path
outer neighbor S_2. Because C has exactly
two actual neighbors, S_1 also touches C
and no other **central** neighbor exists.
All seven exterior squares are outer, so
there is no other inner exterior square.
Thus S_1 has **exactly two actual square
neighbors**: C and S_2.

If S_1 were strictly circle-free, section 8
of HUMAN_CYCLE_ANALYSIS.md would force it
to be a genuine actual-degree-two aligned
transmitter. But C is already a **circle-free
actual-degree-two transmitter** and C-S_1 is
an actual contact. The corollary "two
interior transmitters cannot be adjacent
below radius two" in that same note forbids
this situation. Therefore S_1 must
**touch the containing circle**, with
a true vertex on |x|=R (the square is
contained in the disk).

The symmetric argument gives the conclusion
for S_6 if it does not contact T.
At most one endpoint can contact T, so
at least one cannot and must touch the circle.
If T contacts neither, both must circle-touch.
This proves (1).

### 4. Finite graph-template count

With a fixed six-consecutive-outer
positive path, the optional actual outer edges
can only be one of
\[
\varnothing,\qquad \{T-S_1\},\qquad\{T-S_6\}.
\]
There are seven cyclic choices for which
outer square is the spectator T.
Each yields three distinct labeled
outer-actual-edge sets, giving exactly 21
**graph templates consistent with these
necessary contact restrictions**.

The simple independent combinatorial audit
[verify_m6_spectator_endpoints.py](verify_m6_spectator_endpoints.py)
enumerates the seven placements and checks
every one of these 21 templates, in each
case identifying at least one endpoint
with no spectator contact.

This finite check only validates the
graph combinatorics. The true geometry and
circle-contact conclusion are proved in
sections 1–3. QED.

## Remaining m=6 structural subbranches

The actual six-outer stressed-path root
has now a useful **three-way central-contact
mode split**:

1. **Exactly two actual C neighbors:** C
   must be a side-aligned transmitter, and
   at least one stressed outer path endpoint
   must be a true circle-contact square
   (both if T attaches to neither endpoint).
   This theorem provides 21 optional
   outer-contact graph templates.
2. **Side-stressed C with at least three
   actual neighbors:** there are additional
   **zero-positive-stress C contacts**;
   no degree-two transmitter conclusion for C
   may be used without analyzing those contacts.
3. **Diagonally stressed C:** the separate
   [HUMAN_DIAGONAL_CENTRAL_TANGENTIAL_BRACING.md](HUMAN_DIAGONAL_CENTRAL_TANGENTIAL_BRACING.md)
   forces at least **four actual C neighbors**
   with two extra zero-stress contacts
   having **opposing tangential normals**.

All three retain *all* square frames,
the spectator's true disk/space constraints,
and any actual zero-weight contacts.
The last two are **not** ruled out.
The strict global \(R_8\ge\widehat R\),
equality classification, and Lean handoff
remain OPEN.


## Stronger later result: the pure C-actual-degree-two root admits NO spectator edges

**The earlier three optional m6 outer-contact
edge sets in this note were necessary
*combinatorial possibilities*, but
the nonempty ones are now completely
excluded by true minimum-contact
leaf rigidity.**

[HUMAN_B2_PURE_CENTRAL_CONTACT_ISOLATES_SPECTATORS.md](HUMAN_B2_PURE_CENTRAL_CONTACT_ISOLATES_SPECTATORS.md)
proves that if C has **exactly its
two positive-stress actual neighbors**,
the unique m6 spectator T **must
be completely isolated** in the
*full actual contact graph*.
Otherwise T would have exactly one
actual contact to a noncentral
outer square, contrary to the
actual-leaf theorem, unless T
touched both stressed endpoints
and closed the separately excluded
seven-outer full contact ring.
Thus **both** stressed path
endpoints S1,S6 actually touch
the containing circle, not
merely at least one.

[HUMAN_B2_INTERNAL_PATH_VERTEX_COVER.md](HUMAN_B2_INTERNAL_PATH_VERTEX_COVER.md)
further forces at least two
internal stressed squares S2..S5
to touch the disk circle, so
pure m6 has **at least FOUR
different circle-contact
stressed outer-square labels**.

The other (non-pure) m6
spectator actual contacts are
globally classified by
[HUMAN_M6_SPECTATOR_CONTACT_TRICHOTOMY.md](HUMAN_M6_SPECTATOR_CONTACT_TRICHOTOMY.md):
T is isolated, an actual
C-leaf, or a circle-anchored
C--T--S1/S6 actual contact
triangle. No outer-only leaf
T is ever allowed. Extra
true zero-weight central
contact chords remain in
mode K.

This later result is the
**current** actual-contact
classification; the earlier
21 graph-only m6 supertemplates
should not be treated as 21
genuinely still-open pure-mode
packings.

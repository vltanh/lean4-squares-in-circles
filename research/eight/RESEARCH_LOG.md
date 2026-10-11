# Eight-square mathematical research log

Scope: PR #9, branch `research/eight-proof`; all work stays under `research/eight/`.
Production baseline: `35c72e0aa740b17f012584e625bd13367c9726ff`.

## Method and status

### 2026-10-10 continuation

The current user request is to proceed with a pen-and-paper proof and frequent
`[skip ci]` commits, without writing Lean. The new orientation and dependency
audit are in [PEN_AND_PAPER_ROADMAP.md](PEN_AND_PAPER_ROADMAP.md). New work aims
to replace certificate-only arguments by analytic ones and close the global
structural gap. The previous paragraph below records the earlier session's
method; it is not an instruction to substitute new interval searches for the
present pen-and-paper task.

### Earlier session method

The current instruction permits a rigorously checked computational certificate as an intermediate proof, to be made analytical later. This supersedes the initial tracker's restriction against developing such a certificate. An unverified numerical optimization or a sampled minimum is not a proof. No Lean formalization is to be started before a complete mathematical proof exists.

Record positive results, counterexamples to proposed reductions, and unsuccessful experiments separately. Do not infer global optimality from a construction, a stationary point, a local stress, or convergence of numerical runs. Keep CI skipped on research commits.

## Starting evidence

- Friedman's Squares in Circles page lists Cantrell's March 2002 eight-square construction at radius 1.97877+, without an optimality claim for eight squares: https://erich-friedman.github.io/packing/squincir/
- The publicly displayed MinMax Arena solution supplies decimal centers and half-edge vectors for an independently submitted near-matching construction: https://minmaxarena.com/en/problems/tilted-squares-in-circle/p05-n8-v2 . Those decimals are discovery data, not exact candidate equations or lower-bound evidence.
- The existing six/seven proofs are available in the production baseline. Their radius-specific normalization conclusions cannot simply be applied at the larger eight-square radius.

At the beginning of the earlier session there was no mathematical
deliverable beyond the existing general lower bounds; the first task was
candidate reconstruction. This is a historical starting point, not the
current state.

## Analytical continuation: proved results

The 2026-10-10 continuation supplies the following written arguments:

1. **Exact construction.** A fully rational packing gives
   $R_8\le\sqrt{9789}/50=1.9787875\ldots$. Its proof has seven explicit
   farthest-vertex comparisons and shared separating lines accounting for
   all 28 square pairs. The actual coordinates and all printed rational
   identities were independently checked.
2. **Conditional optimization.** The five-corner radical domain is an
   explicit compact interval. At every tilt its position minimizer is unique.
   Global modified tilt curvature, endpoint arguments, and an exact
   zero-tilt comparison prove that the true family optimum is the least
   admissible root of a stated polynomial stationary system. The equality
   of this least root with the previously isolated candidate remains an
   analytic identification problem. Further inequalities prove monotonicity
   of the feasible minimizing position and $u,v<1$ at every feasible
   simultaneous stationary point, giving the construction's column order.
3. **Arbitrary minimizers.** Compactness, exact center support, balanced
   separator stresses, and normal multipliers with full angle derivatives
   are proved directly. Sliders and zero-force squares are retained.
4. **Local geometry.** Relative to any square, each exceptional corner
   serves at most one neighbor without a separator on that square's axes.
   Outward disk caps have capacity two. A straight chain of k squares needs
   radius $\sqrt{k^2+1}/2$.
5. **Orientation from contacts.** In a minimizer with the fewest actual
   contacts, a strictly interior square of degree two aligns with its
   opposite supports. Two such squares sharing their two neighbors force
   all four frames to be parallel. This proves the orientation consequence
   of a candidate contact pattern; forcing the pattern remains open.
6. **Odd-walk combinatorics.** A symmetric four-type closed seven-step walk
   has minimum weight $\min(\tau+4m,L)$. No enumeration is needed. The
   continuous pair inequalities needed for a sharp geometric application
   are still unproved.
7. **Graph restrictions.** Every actual leaf in a minimum-contact minimizer
   is radial and has the same central neighbor as any other leaf. There are
   at most two leaves, in perpendicular central directions. Consequently
   every nontrivial actual-contact component contains a cycle.
8. **Actual-point equilibrium.** A strict infinitesimal motion argument at
   parallel support edges supplies normal forces at actual common contact
   points, with force and moment equilibrium. A positive-stress bridge has
   a radial force line; every stress-tree component contains a square
   through the disk center. These statements distinguish positive-stress
   edges from additional actual contacts of weight zero. The stronger final
   theorem excludes every fully radial nontrivial stress component when
   $\sqrt2+1/2<R<2$, so every such component has a cycle with nonzero contact
   moment. Applying that lower-radius hypothesis to $R_8$ using the earlier
   computational lower bound keeps that certificate dependency explicit.

Proofs and the concrete remaining dependency chain are indexed in
[PEN_AND_PAPER_ROADMAP.md](PEN_AND_PAPER_ROADMAP.md). Every continuation commit
uses [skip ci]. The changes are research Markdown and an illustrative SVG
of the rational construction; no Lean proof or new continuous certificate
program is written.

The unrestricted sharp n=8 theorem remains open at this stage. In particular,
no argument above silently assumes the five-corner scaffold, identifies
distinctly defined algebraic roots, or promotes computational evidence to an
analytic proof.

## Further continuation: enclosure of the least family root

The instruction to proceed through the roadmap continues from PR head
5f386b7afb956d046e206013df6998745b9a2cce. The next checked results are:

- HUMAN_FAMILY_CLOSURE.md proves that every feasible simultaneous
  stationary point in the relevant radius range has $1/2<v<u<1$,
  $1/2<p<1$, and $r<w$. The proof uses a quadratic sign argument and the
  previously established decreasing function $\Phi$.
- HUMAN_FAMILY_ENCLOSURE.md proves that every feasible projected chain
  with $q\le9789/2500$ has $R>79/40$ and $\tan t<1/5$. Five rational
  choices of support weights give concave functions of the entire tilt
  interval; ten fixed endpoint square comparisons settle their signs.

The enclosure covers all positions and does not assume stationarity.
It is intended to close the full-square construction at the globally
selected family root and to reduce the remaining envelope problem. The
unrestricted sharp lower bound is a separate obligation.

### Analytic central-square theorem

HUMAN_GLOBAL_GEOMETRY_CLOSURE.md replaces the central-existence
certificate dependency with a complete proof for $q\le98/25$.
For any square whose open interior avoids the disk center, its total
angular lengths on radii $1$ and $5/4$ satisfy
$3L_1+L_{5/4}\ge\pi$. A single factored derivative comparison controls
both curved boundary cases. The complete equality family has
$L_1=\pi/3$ and $L_{5/4}=0$.

If eight squares all avoided the center, summing both circular capacities
would force equality for every square, but then their unit-circle arcs
would total $8\pi/3>2\pi$. This proves a unique open central square.
The argument includes all canonical states and disconnected circular
intersections. Two independent derivations checked the derivative
factorization, arc branches, equality cases, and rational trigonometric
comparisons before this commit.

This theorem does not yet prove a fixed central core, the seven marker
gap bounds, or the sharp five-corner obstruction.

### Exact construction at the least family radius: closed

ANALYTIC_EXACT_CONSTRUCTION.md proves $R_8\le\widehat R$, where
$\widehat R$ is the least radius selected analytically by the stationary
polynomial system. The root is not replaced by a numerical approximation.
The coordinate order and support enclosure imply
$u>7/10$, $r<93/50$, $w<48/25$, and the tilted top bound
$Y_G<-41/260$. These bounds leave room for both middle squares.

The note checks every farthest-vertex comparison and all 28 pairs, in
groups of 15, 1, 4, and 8. Explicit independent intervals of radius
$10^{-5}$ are given for the two middle heights and the transverse position
of the second tilted square. They preserve strict disk and non-contact
margins while retaining the required exact contact identities.
An independent audit rederived the projection identities, horizontal and
vertical gaps, concavity argument used in the enclosure, and displayed
fractions. No correction remained before the commit.

The sharp construction work package is therefore complete at the exact
least family root. The unrestricted reverse inequality remains to be
proved; the construction does not assert it.

### Global conditional optimization and unique root: closed

HUMAN_FAMILY_CLOSURE.md now proves that the stationary polynomial system
has a unique admissible solution in $(79/40)^2\le q\le9789/2500$, and
that it gives the sharp radius of the complete projected five-corner
family. All feasible chains are first enclosed by the analytical support
argument. On the remaining strip, the position minimum is unique and
interior, and every critical point of its tilt envelope has positive
second derivative. The determinant estimate is strict by the explicit
margin $237/20000$ after the displayed normalization.

The critical-point estimates do not assume that the defect is nonpositive.
This matters: a positive local maximum between two feasible minima would
otherwise escape the argument. Excluding every critical maximum proves a
unique tilt minimum whenever one exists. Strict radius monotonicity then
selects one stationary root. Existence follows from the earlier attained
family optimum and rational construction, so no tiny root-isolation box
is a hidden premise.

Two independent audits checked the full chain, including the off-feasible
critical points, the normalized Hessian identity, the trial-position bound,
and the rational margins. The conditional optimization and exact
construction work packages are complete. The remaining sharp step is
the unrestricted geometric lower bound.

### Analytical radius range for nonzero contact-moment cycles

HUMAN_ANALYTIC_LOWER_BOUND.md proves the unconditional strict bound
$R_8>\sqrt2+1/2$. Its only structural input is the new analytical
central-square theorem. If the central square contains the open
radius-$1/12$ disk, each exterior square occupies more than $2\pi/7$
on the circle of radius $13/12$. Otherwise choose the auxiliary radius
to equal the distance to the opposite central side; the central square
occupies at least $\pi/3$ and each exterior square more than $3/4$.
Both cases exceed the full circular budget.

The single-square arc estimates cover clipped and disconnected states.
Their curved-boundary derivatives share the positive factor
$(s-R)^2+[r^2-(R-1)^2]s$, which extends the earlier angular comparison
below radius one. The remaining endpoint trigonometric comparisons are
fixed rational square checks. Two independent audits verified all arc
branches and the central-depth split before this commit.

This result removes the earlier computational lower-bound premise from
the theorem that every nontrivial physical stress component of an
eight-square minimizer has nonzero moment circulation. The sharp
unrestricted contact-pattern reduction is still to be proved.

### Angular order for all exterior contact-moment cycles

HUMAN_GLOBAL_CYCLE_CLOSURE.md proves two uniform contact bounds,
$|n\cdot z|\le R-1$ and $|z|^2\le R^2-1$, and uses the first to
order incoming and outgoing contact moments around the nearest-point
ray of every exterior square. Concatenating paths through those nearest
points turns each directed exterior cycle into a closed curve with
positive winding around the central square. The proof treats both
nearest-corner and nearest-side states, arbitrary available contact
normals, and the possible zero-angle degeneracies. A winding exterior
cycle has at least four squares by an elementary area argument.

This removes a degree-two assumption from the angular-order step. It
does not force the positive-stress cycle to avoid the central square.
An exact four-square example in the note also shows that force and
moment balance at one circle-free exterior square alone allow a
three-force branch. Accordingly the remaining argument must use
global minimality, the other squares, or collective deformations.
The full note passed two independent audits before this commit.

### Geometry forced by the twin scaffold

HUMAN_SCAFFOLD_CLOSURE.md proves that, under the explicit hypothesis of
two strictly interior degree-two squares sharing their neighbors, one
twin is the central square. Minimum actual contact count makes all four
side contacts overlap in positive length. The gap between the twins is
a bounded complementary rectangle of height less than one, which no
other unit square can enter. Their entire convex hull therefore excludes
the other squares, and the twins can be made into a vertical domino
without increasing the radius.

The solid-rectangle argument eliminates the two upper corner exceptions
relative to the central square, even for arbitrarily rotated remaining
squares. A separate exact projection lemma shows that a unit square
disjoint from an axis-parallel unit square with horizontal center offset
at most $7/8$ has total vertical span at least two, with equality only
for parallel frames. The disk and scaffold bounds place every remaining
outer-column center within this range. This removes an orientation
assumption from the first and third projected-chain inequalities.

The note states the twin hypothesis and its remaining joint-occupancy
obligation explicitly. Neither the existence of the twins nor the full
five-corner reduction is asserted. An independent audit checked the
endpoint-contact deformation, gap topology, projection polynomial, and
rectangle separating-axis argument before this commit.

### Sharp two-square cap capacity and the local jamming obstruction

HUMAN_SHARP_CAPACITY_BOUND.md proves the exact inequality
$R^2\ge(h+1)^2+1$ for two unit squares in the cap
$D_R\cap\{x\ge h\}$ when $2/3\le h\le1$. Both squares may
rotate arbitrarily. At the critical radius, two disk tangents and the cap
line enclose an isosceles triangle. The proof shows that every unit square
in this triangle contains the same point. All nonparallel orientations
contain it in their open interior. The only boundary cases are the two
parallel stacked units, which establishes the sharp bound and complete
equality description. The whole orientation interval is handled by
elementary monotonicity and concavity, with explicit strict rational
comparisons. Two independent audits rederived the center triangle,
all support extrema, and the disk-to-triangle implication.

As one conditional consequence, a parallel three-square column with two
squares forced into the opposite central cap needs
$q\ge2257/576$. The exact geometric hypotheses and parameter range are
stated; this does not yet classify the eight-square occupancy.

HUMAN_LOCAL_JAM_OBSTRUCTION.md gives a separate exact four-square
counterexample to reducing a strictly contained exterior square to
degree two by local jamming alone. The three-contact square is an
isolated feasible position with its three neighbors fixed; the argument
checks every alternative separating-axis branch. The containing squared
radius is strictly below $39/10$, and the central offset is $23/100$.
This rules out the proposed universal $1/4$ offset consequence and
directs the remaining reduction toward full occupancy or collective
deformations. The example and its first-order isolation argument were
independently checked before this commit.


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


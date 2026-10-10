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


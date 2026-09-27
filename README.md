# Formalization of "Squares in Circles" in Lean 4

[![Lean build](https://github.com/vltanh/lean4-squares-in-circles/actions/workflows/lean.yml/badge.svg)](https://github.com/vltanh/lean4-squares-in-circles/actions/workflows/lean.yml)
[![Doc links](https://github.com/vltanh/lean4-squares-in-circles/actions/workflows/docs.yml/badge.svg)](https://github.com/vltanh/lean4-squares-in-circles/actions/workflows/docs.yml)

Machine-checked proofs, for `n = 1, …, 5` and `n = 7`, of the least radius of
a disk holding `n` non-overlapping unit squares, and of every packing that
attains it, up to rotation about the disk centre and relabelling: exactly one
for `n ≤ 5`, and for `n = 7` a family in which each of the three middle squares
slides along the middle column.

| n | optimal radius | ≈ | an optimal packing |
| :-: | :-: | :-: | :-: |
| 1 | `√2 / 2` | 0.7071 | <img src="https://erich-friedman.github.io/packing/squincir/1.gif" width="100" alt="one unit square in a circle"><br>the square |
| 2 | `√5 / 2` | 1.1180 | <img src="https://erich-friedman.github.io/packing/squincir/2.gif" width="100" alt="two unit squares in a circle"><br>a 2×1 rectangle |
| 3 | `5√17 / 16` | 1.2885 | <img src="https://erich-friedman.github.io/packing/squincir/3.gif" width="100" alt="three unit squares in a circle"><br>the T |
| 4 | `√2` | 1.4142 | <img src="https://erich-friedman.github.io/packing/squincir/4.gif" width="100" alt="four unit squares in a circle"><br>the 2×2 block |
| 5 | `√(5/2)` | 1.5811 | <img src="https://erich-friedman.github.io/packing/squincir/5.gif" width="100" alt="five unit squares in a circle"><br>the plus |
| 7 | `√13 / 2` | 1.8028 | <img src="https://erich-friedman.github.io/packing/squincir/7.gif" width="100" alt="seven unit squares in a circle"><br>three in a line between two pairs; not unique, each square of the line can move along it |

Pictures by Erich Friedman, from the [Squares in Circles](https://erich-friedman.github.io/packing/squincir/)
page of Erich's Packing Center.

## Definitions

More on each definition: [docs/definitions.md](docs/definitions.md).

Read these before trusting the results: the kernel checks the proofs, not that
the statements mean what you intend. All of them are in
`SquaresInCircles/Geometry.lean`, which `Challenge.lean` restates with the main
theorems ([Palomar registry](#palomar-registry)).

### Squares

A point is a pair of reals, and a unit square is a centre with an orthonormal
frame `(cosine, sine)`, so every square is placed and rotated independently:

```lean
abbrev Point := ℝ × ℝ

structure UnitSquare where
  center : Point
  cosine : ℝ
  sine : ℝ
  unit : cosine ^ 2 + sine ^ 2 = 1
```

`localX S p` and `localY S p` are the coordinates of `p` in the frame of `S`.
In those coordinates the square is `[-1/2, 1/2]²`, closed or open:

```lean
def localX (S : UnitSquare) (p : Point) : ℝ :=
  S.cosine * (p.1 - S.center.1) + S.sine * (p.2 - S.center.2)

def localY (S : UnitSquare) (p : Point) : ℝ :=
  -S.sine * (p.1 - S.center.1) + S.cosine * (p.2 - S.center.2)

def closedSquare (S : UnitSquare) (p : Point) : Prop :=
  |localX S p| ≤ 1 / 2 ∧ |localY S p| ≤ 1 / 2

def openSquare (S : UnitSquare) (p : Point) : Prop :=
  |localX S p| < 1 / 2 ∧ |localY S p| < 1 / 2
```

### Packing

A packing of `n` squares in the closed disk of centre `o` and radius `R` asks
only that every closed square lie in the disk and that no point be interior to
two squares. The disk is described with the squared length `normSq`:

```lean
def normSq (p : Point) : ℝ := p.1 ^ 2 + p.2 ^ 2
def sub (p q : Point) : Point := (p.1 - q.1, p.2 - q.2)

def inDisk (o : Point) (R : ℝ) (p : Point) : Prop :=
  normSq (sub p o) ≤ R ^ 2

def Packing {n : ℕ} (S : Fin n → UnitSquare) (o : Point) (R : ℝ) : Prop :=
  0 ≤ R ∧
  (∀ i p, closedSquare (S i) p → inDisk o R p) ∧
  (∀ i j, i ≠ j → ∀ p, ¬ (openSquare (S i) p ∧ openSquare (S j) p))
```

### Congruence

The optimal packings are given as models: configurations of axis-parallel
squares with the disk centre at the origin. `Congruent S o M` says that the
configuration `S` is the model `M`, placed at `o`, turned by one angle about
`o`, and relabelled. It compares point sets, since a quarter turn of a frame
describes the same square. `pointInDirection o φ x y` is the point with
coordinates `(x, y)` in the frame at `o` rotated by `φ : Direction`, a
`Real.Angle`:

```lean
def pointInDirection (o : Point) (phase : Direction) (x y : ℝ) : Point :=
  (o.1 + phase.cos * x - phase.sin * y, o.2 + phase.sin * x + phase.cos * y)

def axisSquare (c : Point) : UnitSquare where
  center := c
  cosine := 1
  sine := 0
  unit := by norm_num

def Congruent {n : ℕ} (S : Fin n → UnitSquare) (o : Point) (M : Fin n → UnitSquare) : Prop :=
  ∃ (φ : Direction) (σ : Equiv.Perm (Fin n)), ∀ i p,
    (openSquare (S (σ i)) (pointInDirection o φ p.1 p.2) ↔ openSquare (M i) p) ∧
    (closedSquare (S (σ i)) (pointInDirection o φ p.1 p.2) ↔ closedSquare (M i) p)
```

For seven squares the optimal packings form a family: two columns of two
squares, and between them a column of three whose heights can each vary. A
`Seven.Column` records the three heights, and `Seven.columnModel` is its model:

```lean
def Seven.columnLimit : ℝ := Real.sqrt 3 - 1 / 2

structure Seven.Column where
  bottom : ℝ
  middle : ℝ
  top : ℝ
  lower : -columnLimit ≤ bottom
  gap_lower : bottom + 1 ≤ middle
  gap_upper : middle + 1 ≤ top
  upper : top ≤ columnLimit

def Seven.columnCenters (c : Column) : Fin 7 → Point :=
  ![(1, -1/2), (1, 1/2), (-1, -1/2), (-1, 1/2),
    (0, c.bottom), (0, c.middle), (0, c.top)]

def Seven.columnModel (c : Column) : Fin 7 → UnitSquare :=
  fun i => axisSquare (columnCenters c i)
```

## Results

More on each theorem: [docs/results.md](docs/results.md).

For `1 ≤ n ≤ 5` and `n = 7`, the root file `SquaresInCircles.lean` proves, in
namespace `SquaresInCircles`:

```lean
theorem optimal_radius (n : ℕ) (hn : 1 ≤ n ∧ n ≤ 5 ∨ n = 7) :
    IsLeast {R | ∃ (S : Fin n → UnitSquare) (o : Point), Packing S o R} (optimalRadius n)

theorem optimal_packings (n : ℕ) (hn : 1 ≤ n ∧ n ≤ 5 ∨ n = 7)
    (S : Fin n → UnitSquare) (o : Point) :
    Packing S o (optimalRadius n) ↔ ∃ M ∈ optimalPackings n, Congruent S o M
```

`optimal_radius`: `optimalRadius n` is the least radius of a disk holding `n`
unit squares; some packing attains it, and none fits in a smaller disk.
`optimal_packings`: the packings of that radius are exactly the configurations
congruent to a model in `optimalPackings n`, which holds one model for `n ≤ 5`
and every column packing for `n = 7`:

```lean
def optimalPackings : (n : ℕ) → Set (Fin n → UnitSquare)
  | 1 => {One.model}
  | 2 => {Two.model}
  | 3 => {Three.model}
  | 4 => {Four.model}
  | 5 => {Five.model}
  | 7 => Set.range Seven.columnModel
  | _ => ∅
```

Each of `One.model`, …, `Five.model` is `fun i => axisSquare (centers i)`,
the axis-parallel squares at the `centers` of its case:

| n | `optimalRadius n` | centres of the optimal models |
| :-: | --- | --- |
| 1 | `Real.sqrt 2 / 2` | `![(0,0)]` |
| 2 | `Real.sqrt 5 / 2` | `![(-1/2,0),(1/2,0)]` |
| 3 | `5 * Real.sqrt 17 / 16` | `![(-1/2,-5/16),(1/2,-5/16),(0,11/16)]` |
| 4 | `Real.sqrt 2` | `![(1/2,1/2),(-1/2,1/2),(-1/2,-1/2),(1/2,-1/2)]` |
| 5 | `Real.sqrt (5 / 2)` | `![(0,0),(1,0),(0,1),(-1,0),(0,-1)]` |
| 7 | `Real.sqrt 13 / 2` | `Seven.columnCenters c` for every `c : Seven.Column` |

Every case proves one `Optimum` (`Common/Optimum.lean`): the radius, the
models, that they pack the disk (`model_packing`; for seven squares
`column_packing`), a point of each model on the circle, and `uniqueness`, that
every packing at that radius is congruent to a model. The lower bound and the
converse of uniqueness then follow once for all cases. The root file also
proves `optimal_packings_rigid`, uniqueness with an explicit isometry of the
plane.

## Proof outline

The proofs are written out as an illustrated, self-contained textbook, every
numbered result linked to its Lean declarations: [docs/proof/](docs/proof/README.md),
with the [preliminaries](docs/proof/preliminaries.md), the shared
[tools](docs/proof/common.md), one chapter per case ([one](docs/proof/one.md),
[two](docs/proof/two.md), [three](docs/proof/three.md),
[four](docs/proof/four.md), [five](docs/proof/five.md),
[seven](docs/proof/seven.md)), and four appendices of computations for seven
squares.

- **One and two squares.** The farthest corner of a square is at least half a
  diagonal from the disk centre, so in the disk of radius `√2 / 2` the square
  is centred at the disk centre. In the disk of radius `√5 / 2` both centres
  of two squares are within `1/2` of the disk centre, and centres of disjoint
  unit squares are at least 1 apart, so both are exactly `1/2` from it; each
  square then holds half of a small circle about the disk centre, and the two
  halves are opposite.
- **Three to five squares.** At the optimal radius every square's centre lies
  in a contact polygon, and each square occupies an arc of a small circle
  around the disk centre. The arcs cannot take up more than the whole circle,
  so every inequality is tight, and the tight configurations are rebuilt into
  the optimal packing. A square containing the disk centre needs a separate
  argument, which for three squares is the hardest part of the proof.
- **Seven squares.** Each square that avoids the disk centre gets a marker, a
  direction from the disk centre. In the disk of radius `√13 / 2`, two
  disjoint such squares have markers at least `π/3` apart, and exactly `π/3`
  apart only if they touch as in the optimal packing. The pair theorem behind
  this is by far the longest proof in the library. Seven directions cannot be
  pairwise at least `π/3` apart, so one square contains the disk centre, and
  the markers of the other six form a regular hexagon, which rebuilds the
  packing up to the heights of the three middle squares.
- **The lower bound** is shared by all cases: a packing in a smaller disk also
  packs the optimal one, so it is congruent to a model, whose outer corners
  reach the circle of the optimal radius.

## Prior work

More on each earlier result, with references:
[docs/prior-work.md](docs/prior-work.md).

- **One and two squares** are folklore; Erich Friedman's page lists them as
  trivial.
- **Three squares.** Montanher, Neumaier, Markót, Domes and Schichl (2019)
  enclosed the optimal radius in an interval of width `6·10⁻¹⁴` containing
  `5√17/16`, and every optimal arrangement in small boxes near the T, by a
  computer-assisted interval branch-and-bound search. The enclosure trusts
  C++ code and interval rounding, and gives neither the exact radius nor exact
  uniqueness.
- **Four squares** are reported on Friedman's page as proved at the
  International Math Summer Camp in 2026; we found no publication.
- **Five squares.** We found no earlier proof; the plus is listed only as the
  best known packing.
- **Seven squares.** We found no earlier proof; Friedman's page lists the
  packing, found by him in 1997, as the best known one.

We found no proof-assistant verification of any optimal square or circle
packing. Here every case is proved exactly, uniqueness included (for `n = 7`,
up to the heights of the middle squares), and checked by Lean's kernel.

## Layout

More on each file: [docs/layout.md](docs/layout.md).

```text
SquaresInCircles.lean      the main theorems, for all six cases
Challenge.lean             the statement alone, for the Palomar registry
SquaresInCircles/
├── Geometry.lean          the statement: squares, disks, Packing, Congruent,
│                          the optimal radii and models
├── Common/                tools shared by several cases
├── One/  Two/             Construction, Uniqueness
├── Three/ Five/           Construction, Exterior, Containing, Uniqueness
├── Four/                  Construction, Exterior, Uniqueness
└── Seven/                 Construction, the pair theorem, Uniqueness, and
                           Uniqueness/ for the ring and the middle square
```

Each case imports only `Common/` and its own folder.

## Verification

More on each check: [docs/verification.md](docs/verification.md).

```sh
lake exe cache get
lake build
lake env lean AxiomAudit.lean
lake env lean SanityChecks.lean
scripts/verify-comparator.sh
```

The build uses Lean and mathlib `v4.35.0-rc3`, pinned by `lean-toolchain` and
`lake-manifest.json`. `lake build` must succeed without warnings, and every
`#print axioms` line must read `[propext, Classical.choice, Quot.sound]`. The
last command (Linux, `bwrap`) checks the proofs against `Challenge.lean`
([Palomar registry](#palomar-registry)). The trusted base is Lean, Lake and
mathlib. GitHub Actions runs all five steps on every push and audits the axioms
of every declaration; a second workflow checks the links from the proof pages
to the Lean declarations.

## Palomar registry

The repository is set up for the [Palomar](https://palomar-registry.org/)
registry. `Challenge.lean` is the statement to audit: it imports only mathlib,
restates `SquaresInCircles/Geometry.lean` word for word, and states
`optimal_radius` and `optimal_packings` with `sorry`.
[`comparator.json`](comparator.json) pairs it with the root module
`SquaresInCircles`, which proves them, and `scripts/verify-comparator.sh` runs
`lake comparator` as Palomar does: the same statements over identical
definitions, only the three standard axioms, and the proofs replayed through
the NanoDa and con-ron kernels as well as Lean's. Edit the definitions in
`Geometry.lean` only; `--write` copies them into `Challenge.lean`.
[`formalization.yaml`](formalization.yaml) records provenance, sources,
authorship, AI use and review status. The
[preflight](.github/workflows/palomar.yml) workflow, run by hand, runs
Palomar's mechanical check on a commit; submissions go through
<https://submit.palomar-registry.org/>.

## License

Apache-2.0, matching mathlib and the Lean ecosystem.

## Contributors

The proofs and the Lean code were written by AI models, ChatGPT 6 Pro and
Claude Opus 5 and 5.5, with the repository owner directing and reviewing the
work. Who did what, and when: [docs/contributors.md](docs/contributors.md).

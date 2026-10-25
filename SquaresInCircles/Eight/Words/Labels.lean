module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Data.Rat.Star
public import SquaresInCircles.Eight.Arithmetic.AffineArc
public import SquaresInCircles.Eight.Arithmetic.Interval
public import SquaresInCircles.Eight.Arithmetic.ScalarExpr
public import SquaresInCircles.Eight.Words.Basic

/-!
# Eight squares: the labels and the targets of the quarter words

The admissible quarter words other than the candidate word are excluded by lower bounds on the
costs of the edges of a boundary cycle at `Q0`. The cost of the edge `i`, with quarter increment
`k` and frame difference `d`, is `k π / 2 + d` plus the label of its source minus the label of
its target; the label of a vertex depends on its radial kind, its sign `σ` and its state
`(a, b)`. This module gives the targets and the labels of these bounds.

The words with a digit `2` are excluded together by the common increment costs, with the labels
`σ (-9/100 + (13/200) a + (203/200) b)` on the outer circle and
`σ ((73/10)(7/12 - a) + (291/250) b)` on the core (`QuarterWordGeometry.commonMarker`) and a
target for each increment `k = 0, 1, 2` (`commonGamma`). The two words without a `2`, `0010111`
and `0011011` (`WrongWord`), have labels that depend on the role of the vertex in the word:
`c + p a + σ q b` for the first and `σ (c + p a + q b + r b² + s a b)` for the second, with
integer coefficients over `10⁵` by role, radial kind and sign (`shortCoefficients`,
`secondCoefficients`), and the targets `wrongGamma`. On these words the vertex `0` has the sign
`+1`, the vertex `2` the sign `-1`, and no zero edge goes from a vertex of sign `-1` to one of
sign `+1` (`allowed`, proved for boundary cycles in `QuarterWordGeometry.actual_allowed`).
`CoreSeparatorExcluded` lists the radial kinds, signs and separating axes of an edge that no
feasible separator has.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.WordProblems

/-- The sign `1` or `-1` of a vertex, as a rational. -/
def sign (positive : Bool) : ℚ := if positive then 1 else -1

/-- The targets of the common increment costs, for the quarter increments `0`, `1` and `2`. -/
def commonGamma (k : Fin 3) : ℚ := ![391/400,157/200,163/200] k

/-- The two admissible quarter words without a digit `2` other than the candidate word:
`0010111` (`short`) and `0011011` (`second`). -/
inductive WrongWord | short | second
  deriving DecidableEq

/-- The digits of a wrong word. -/
def wrongWord : WrongWord→ QuarterWord
  | .short => ![0,0,1,0,1,1,1]
  | .second => ![0,0,1,1,0,1,1]

/-- The signs `σ`, `τ` of the ends of the edge `i` of a wrong word that can occur: the vertex `0`
has the sign `+1`, the vertex `2` the sign `-1`, and a zero edge does not go from the sign `-1`
to the sign `+1`. -/
def allowed (w : WrongWord) (i : Vertex) (σ τ : Bool) : Prop :=
  (i=0→σ=true) ∧ (i=2→σ=false) ∧
  (next i=0→τ=true) ∧ (next i=2→τ=false) ∧
  (wrongWord w i=0→¬(σ=false ∧ τ=true))
instance (w : WrongWord) (i : Vertex) (σ τ : Bool) : Decidable (allowed w i σ τ) := by
  unfold allowed; infer_instance

/-- The labels `c + p a + σ q b` of the word `0010111`: the integers `10⁵ c`, `10⁵ p` and `10⁵ q`
by role, radial index and sign index. The entries of the signs that `allowed` excludes at the
roles `0` and `2` are zero and never used. -/
def shortCoefficients : Vertex→ Fin 2→ Fin 2→ Fin 3→ℤ :=
  ![![![![0,0,0],![0,0,94766]],![![0,0,0],![3177,0,108816]]],![![![24463,-13422,103828],![6130,0,99940]],![![-14041,0,62095],![25648,0,62095]]],![![![-2623,9133,88074],![0,0,0]],![![11680,0,113855],![0,0,0]]],![![![50866,-33147,113360],![-68803,51554,119909]],![![-15540,0,62750],![4149,0,104729]]],![![![-23483,19335,76744],![6294,0,71553]],![![3897,0,104073],![25812,0,58829]]],![![![29579,-20967,83048],![2448,0,86884]],![![1027,0,95269],![2448,0,99195]]],![![![-18660,18602,80996],![-20704,21826,83472]],![![7651,0,99173],![9072,0,95324]]]]

/-- The labels `σ (c + p a + q b + r b² + s a b)` of the word `0011011`: the integers `10⁵ c`,
`10⁵ p`, `10⁵ q`, `10⁵ r` and `10⁵ s` by role, radial index and sign index. -/
def secondCoefficients : Vertex→ Fin 2→ Fin 2→ Fin 5→ℤ :=
  ![![![![394,0,33945,0,39635],![2478,0,93015,2363,-11055]],![![19911,0,63607,0,0],![125,0,103981,0,0]]],![![![0,-26,83194,-11864,17627],![0,-26,83194,-11864,17627]],![![19555,0,63132,0,0],![19555,0,63132,0,0]]],![![![2478,0,93015,2363,-11055],![394,0,33945,0,39635]],![![125,0,103981,0,0],![19911,0,63607,0,0]]],![![![1670,0,242322,-91744,-95769],![0,-1025,16031,0,63457]],![![22042,-34492,98439,-5334,0],![-1449,0,104240,0,0]]],![![![0,-2112,29090,0,44642],![3965,0,385510,-149748,-189442]],![![16823,0,62312,0,0],![4970,0,94831,0,0]]],![![![3965,0,385510,-149748,-189442],![0,-2112,29090,0,44642]],![![4970,0,94831,0,0],![16823,0,62312,0,0]]],![![![0,-1025,16031,0,63457],![1670,0,242322,-91744,-95769]],![![-1449,0,104240,0,0],![22042,-34492,98439,-5334,0]]]]

/-- The index `0` of the outer circle and `1` of the core. -/
def radialIndex (kind : RadialKind) : Fin 2 := if kind=.outer then 0 else 1
/-- The index `1` of the sign `+1` and `0` of the sign `-1`. -/
def signIndex (σ : Bool) : Fin 2 := if σ then 1 else 0

/-- The targets of the edges of the wrong words: `359/400` on the edge `2` of `0010111`,
`17953/20000` on the others. -/
def wrongGamma (w : WrongWord) (i : Vertex) : ℚ :=
  if w=.short ∧ i=2 then 359/400 else 17953/20000

/-- The radial kinds, signs and separating axes `j` of an edge with quarter increment `k` that no
feasible separator has: on a zero edge, axis two against a core target or axis four against a
core source; on any edge, axis one against a core target with a source of sign `-1`, or axis
three against a core source with a target of sign `+1`; on a quarter edge, every axis from a core
source of sign `+1` to a core target of sign `-1`. -/
def CoreSeparatorExcluded (k : Fin 3) (ks kt : RadialKind) (σ τ : Bool) (j : Fin 4) : Prop :=
  (k=0 ∧ ((j=1 ∧ kt≠.outer) ∨ (j=3 ∧ ks≠.outer))) ∨
    (j=0 ∧ σ=false ∧ kt≠.outer) ∨ (j=2 ∧ τ=true ∧ ks≠.outer) ∨
    (k=1 ∧ ks≠.outer ∧ kt≠.outer ∧ σ=true ∧ τ=false)

instance (k : Fin 3) (ks kt : RadialKind) (σ τ : Bool) (j : Fin 4) :
    Decidable (CoreSeparatorExcluded k ks kt σ τ j) := by
  unfold CoreSeparatorExcluded; infer_instance

end SquaresInCircles.Eight.WordProblems

module

public import SquaresInCircles.Eight.Arithmetic.PairCover
public import SquaresInCircles.Eight.QuarterWords

/-!
# The labels and targets of the six wrong quarter words

The three common increment costs and the two role-label systems are kept
separate. The first wrong word uses `c+p*a+sigma*q*b`; the second uses
`sigma*(c+p*a+q*b+r*b^2+s*a*b)`.

The core side and corner are separate closed source and target branches.
The pair tables of `WordGeometry` prove the pair inequalities of these labels.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.WordProblems
open Arithmetic

def sign (positive : Bool) : ℚ := if positive then 1 else -1

def transverseBox : RadialKind→ QInterval
  | .outer => ⟨0,9/10⟩
  | .coreSide => ⟨0,1/2⟩
  | .coreCorner => ⟨1/2,14/25⟩

noncomputable def primaryValue (kind : RadialKind) (b : ℝ) : ℝ :=
  match kind with
  | .outer => Real.sqrt ((9789/2500)-(b+1/2)^2)-1/2
  | .coreSide => 7/12
  | .coreCorner => 1/2+Real.sqrt ((1/144)-(b-1/2)^2)

lemma actual_primary {a b : ℝ} (k : RadialKind) (ha : 1/2<a)
    (hb : 0≤b) (hba : b≤a) (hs : BoundaryState Q0 k a b) :
    a=primaryValue k b ∧ (transverseBox k).Mem b := by
  cases k with
  | outer =>
      have he : (a+1/2)^2+(b+1/2)^2=9789/2500 := by
        simpa [BoundaryState,SquaresInCircles.phi,Q0] using hs
      have hnon : 0≤(9789/2500:ℝ)-(b+1/2)^2 := by linarith [sq_nonneg (a+1/2)]
      have hroot := Real.sq_sqrt hnon
      have hroot0 := Real.sqrt_nonneg ((9789/2500:ℝ)-(b+1/2)^2)
      have hbu : b<9/10 := by nlinarith only [sq_nonneg (a-b), hba, he, ha]
      exact ⟨by dsimp [primaryValue]; nlinarith only [he, hroot, ha, hroot0],
        by norm_num [transverseBox,QInterval.Mem]; exact ⟨hb,hbu.le⟩⟩
  | coreSide =>
      obtain ⟨hA,hB⟩ := hs
      exact ⟨hA,by norm_num [transverseBox,QInterval.Mem]; exact ⟨hb,hB⟩⟩
  | coreCorner =>
      obtain ⟨hB,he⟩ := hs
      have hnon : 0≤(1/144:ℝ)-(b-1/2)^2 := by linarith [sq_nonneg (a-1/2)]
      have hroot := Real.sq_sqrt hnon
      have hroot0 := Real.sqrt_nonneg ((1/144:ℝ)-(b-1/2)^2)
      have hbu : b<14/25 := by nlinarith only [sq_nonneg (a-b), hba, he, ha]
      exact ⟨by dsimp [primaryValue]; nlinarith only [he, hroot, ha, hroot0],
        by norm_num [transverseBox,QInterval.Mem]; exact ⟨hB,hbu.le⟩⟩

def commonGamma (k : Fin 3) : ℚ := ![391/400,157/200,163/200] k

inductive WrongWord | short | second
  deriving DecidableEq

def wrongWord : WrongWord→ QuarterWord
  | .short => ![0,0,1,0,1,1,1]
  | .second => ![0,0,1,1,0,1,1]

def allowed (w : WrongWord) (i : Vertex) (σ τ : Bool) : Prop :=
  (i=0→σ=true) ∧ (i=2→σ=false) ∧
  (next i=0→τ=true) ∧ (next i=2→τ=false) ∧
  (wrongWord w i=0→¬(σ=false ∧ τ=true))
instance (w : WrongWord) (i : Vertex) (σ τ : Bool) : Decidable (allowed w i σ τ) := by
  unfold allowed; infer_instance

/-- Exact coefficients from `short_hand_labels.json`, denominator 100000.
The missing signs at roles 0 and 2 are unreachable by `allowed`; zeros keep
the lookup total and do not certify either excluded sign. -/
def shortCoefficients : Vertex→ Fin 2→ Fin 2→ Fin 3→ℤ :=
  ![![![![0,0,0],![0,0,94766]],![![0,0,0],![3177,0,108816]]],![![![24463,-13422,103828],![6130,0,99940]],![![-14041,0,62095],![25648,0,62095]]],![![![-2623,9133,88074],![0,0,0]],![![11680,0,113855],![0,0,0]]],![![![50866,-33147,113360],![-68803,51554,119909]],![![-15540,0,62750],![4149,0,104729]]],![![![-23483,19335,76744],![6294,0,71553]],![![3897,0,104073],![25812,0,58829]]],![![![29579,-20967,83048],![2448,0,86884]],![![1027,0,95269],![2448,0,99195]]],![![![-18660,18602,80996],![-20704,21826,83472]],![![7651,0,99173],![9072,0,95324]]]]

/-- Exact quadratic coefficients with the source reflection identity expanded.
The entire signed polynomial is multiplied by sigma for this label system. -/
def secondCoefficients : Vertex→ Fin 2→ Fin 2→ Fin 5→ℤ :=
  ![![![![394,0,33945,0,39635],![2478,0,93015,2363,-11055]],![![19911,0,63607,0,0],![125,0,103981,0,0]]],![![![0,-26,83194,-11864,17627],![0,-26,83194,-11864,17627]],![![19555,0,63132,0,0],![19555,0,63132,0,0]]],![![![2478,0,93015,2363,-11055],![394,0,33945,0,39635]],![![125,0,103981,0,0],![19911,0,63607,0,0]]],![![![1670,0,242322,-91744,-95769],![0,-1025,16031,0,63457]],![![22042,-34492,98439,-5334,0],![-1449,0,104240,0,0]]],![![![0,-2112,29090,0,44642],![3965,0,385510,-149748,-189442]],![![16823,0,62312,0,0],![4970,0,94831,0,0]]],![![![3965,0,385510,-149748,-189442],![0,-2112,29090,0,44642]],![![4970,0,94831,0,0],![16823,0,62312,0,0]]],![![![0,-1025,16031,0,63457],![1670,0,242322,-91744,-95769]],![![-1449,0,104240,0,0],![22042,-34492,98439,-5334,0]]]]

def radialIndex (kind : RadialKind) : Fin 2 := if kind=.outer then 0 else 1
def signIndex (σ : Bool) : Fin 2 := if σ then 1 else 0

def wrongGamma (w : WrongWord) (i : Vertex) : ℚ :=
  if w=.short ∧ i=2 then 359/400 else 17953/20000

/-- The radial kinds, signs and original axes `j` of an edge with quarter increment `k` that no
feasible separator has (`WordGeometry.original_not_core_excluded`): on a zero edge, axis two
against a core target or axis four against a core source; on any edge, axis one against a core
target with a source of sign `-1`, or axis three against a core source with a target of sign
`+1`; on a quarter edge, every axis from a core source of sign `+1` to a core target of sign
`-1`. -/
def CoreSeparatorExcluded (k : Fin 3) (ks kt : RadialKind) (σ τ : Bool) (j : Fin 4) : Prop :=
  (k=0 ∧ ((j=1 ∧ kt≠.outer) ∨ (j=3 ∧ ks≠.outer))) ∨
    (j=0 ∧ σ=false ∧ kt≠.outer) ∨ (j=2 ∧ τ=true ∧ ks≠.outer) ∨
    (k=1 ∧ ks≠.outer ∧ kt≠.outer ∧ σ=true ∧ τ=false)

instance (k : Fin 3) (ks kt : RadialKind) (σ τ : Bool) (j : Fin 4) :
    Decidable (CoreSeparatorExcluded k ks kt σ τ j) := by
  unfold CoreSeparatorExcluded; infer_instance

end SquaresInCircles.Eight.WordProblems

/-! ### The problems of the word pair tables

The pair problem of an edge (`commonPairProblem`, `wrongPairProblem`) carries the actual radial
charts, signs and labels of its ends. The pair tables of `WordGeometry` (`Generated/Pairs`) define
their problems as the images of their cases (`commonCases`, `wrongCases`) under these functions,
so `WordGeometry` finds each problem in its table without comparing rationals. -/

namespace SquaresInCircles.Eight.WordGeometry
open Arithmetic Arithmetic.PairCover WordProblems

/-- The tangent range of a radial kind. -/
def kindRange : RadialKind → QInterval
  | .outer => ⟨0, 1⟩
  | .coreSide => ⟨0, 6/7⟩
  | .coreCorner => ⟨6/7, 1⟩

/-- The end of a pair at a vertex of radial kind `kind`, sign `σ` and label `L`. -/
def kindEnd (kind : RadialKind) (σ : Bool) (L : QuadLabel) : PairEnd :=
  ⟨decide (kind = .outer), decide (kind = .coreSide), σ, kindRange kind, L⟩

/-- The common label of a radial kind with the sign `σ`. -/
def commonQuad (kind : RadialKind) (σ : Bool) : QuadLabel :=
  (if kind = .outer then (⟨-9/100, -9/100, 13/200, 203/200, 0, 0⟩ : QuadLabel)
    else ⟨73/10*(7/12), 73/10*(7/12), -(73/10), 291/250, 0, 0⟩).signed σ

/-- The label of a wrong word at a role, for a radial kind and the sign `σ`. -/
def wrongQuad (w : WrongWord) (i : Vertex) (kind : RadialKind) (σ : Bool) : QuadLabel :=
  match w with
  | .short =>
      let v := shortCoefficients i (radialIndex kind) (signIndex σ)
      ⟨v 0/100000, v 0/100000, v 1/100000, sign σ*v 2/100000, 0, 0⟩
  | .second =>
      let v := secondCoefficients i (radialIndex kind) (signIndex σ)
      (⟨v 0/100000, v 0/100000, v 1/100000, v 2/100000, v 3/100000, v 4/100000⟩ : QuadLabel).signed σ

/-- The two halves `(k, ±, 7/10)` of the frame difference, with `u⁺` over `10⁸`. -/
def wordHalves (k : ℕ) : List (ℕ × Bool × ℕ) := [(k, true, 70000000), (k, false, 70000000)]

/-- The pair problem of a common increment `k`. -/
def commonPairProblem (k : Fin 3) (ks kt : RadialKind) (σ τ : Bool) (j : Fin 4) : PairProblem :=
  ⟨kindEnd ks σ (commonQuad ks σ), kindEnd kt τ (commonQuad kt τ), axisOf (j.val + 1), 0,
    commonGamma k, wordHalves k.val⟩

/-- The pair problem of the edge `i` of a wrong word. -/
def wrongPairProblem (w : WrongWord) (i : Vertex) (ks kt : RadialKind) (σ τ : Bool) (j : Fin 4) :
    PairProblem :=
  ⟨kindEnd ks σ (wrongQuad w i ks σ), kindEnd kt τ (wrongQuad w (next i) kt τ),
    axisOf (j.val + 1), 0, wrongGamma w i, wordHalves (wrongWord w i).val⟩

/-- The source kind, target kind, signs and original axis `j` of a word pair problem, in the
order of the tables. -/
def wordCases : List (RadialKind × RadialKind × Bool × Bool × Fin 4) :=
  [.outer, .coreSide, .coreCorner] ×ˢ [.outer, .coreSide, .coreCorner] ×ˢ [false, true] ×ˢ
    [false, true] ×ˢ [0, 1, 2, 3]

theorem mem_wordCases (c : RadialKind × RadialKind × Bool × Bool × Fin 4) : c ∈ wordCases := by
  obtain ⟨ks, kt, σ, τ, j⟩ := c
  simp only [wordCases, List.mem_product]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · cases ks <;> decide
  · cases kt <;> decide
  · cases σ <;> decide
  · cases τ <;> decide
  · fin_cases j <;> decide

/-- The cases of the common table of the increment `k`: an outer end, and an axis that a feasible
separator can have (`CoreSeparatorExcluded`). -/
def commonCases (k : Fin 3) : List (RadialKind × RadialKind × Bool × Bool × Fin 4) :=
  wordCases.filter fun c => decide ((c.1 = .outer ∨ c.2.1 = .outer) ∧
    ¬ CoreSeparatorExcluded k c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2)

/-- The cases of the table of the edge `i` of the wrong word `w`: allowed signs, and an axis that
a feasible separator can have. -/
def wrongCases (w : WrongWord) (i : Vertex) :
    List (RadialKind × RadialKind × Bool × Bool × Fin 4) :=
  wordCases.filter fun c => decide (allowed w i c.2.2.1 c.2.2.2.1 ∧
    ¬ CoreSeparatorExcluded (wrongWord w i) c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2)

theorem mem_commonCases {k : Fin 3} {ks kt : RadialKind} {σ τ : Bool} {j : Fin 4}
    (h : ks = .outer ∨ kt = .outer) (h' : ¬ CoreSeparatorExcluded k ks kt σ τ j) :
    (ks, kt, σ, τ, j) ∈ commonCases k :=
  List.mem_filter.mpr ⟨mem_wordCases _, decide_eq_true ⟨h, h'⟩⟩

theorem mem_wrongCases {w : WrongWord} {i : Vertex} {ks kt : RadialKind} {σ τ : Bool}
    {j : Fin 4} (h : allowed w i σ τ) (h' : ¬ CoreSeparatorExcluded (wrongWord w i) ks kt σ τ j) :
    (ks, kt, σ, τ, j) ∈ wrongCases w i :=
  List.mem_filter.mpr ⟨mem_wordCases _, decide_eq_true ⟨h, h'⟩⟩

end SquaresInCircles.Eight.WordGeometry

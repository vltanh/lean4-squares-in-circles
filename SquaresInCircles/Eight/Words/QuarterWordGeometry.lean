module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Data.Rat.Star
public import SquaresInCircles.Eight.Arithmetic.AffineArc
public import SquaresInCircles.Eight.Arithmetic.Interval
public import SquaresInCircles.Eight.Arithmetic.ScalarExpr
public import SquaresInCircles.Eight.Boundary.CycleActions
public import SquaresInCircles.Eight.Boundary.Realization
public import SquaresInCircles.Eight.Words.Basic

/-!
# Eight squares: original physical data for the quarter-word inequalities

The original signed centers, frame lift (`difference`, `phaseValue`), positive gaps and feasible
separating axes (`original_margin`) enter the word argument here. A label (`commonMarker`,
`wrongMarker`) is evaluated once at each original vertex and cancels with the same value on the
next edge (`marker_budget`). The integer/sign classification and the physical dihedral action
(`normalize_word`) keep all weak contacts and both nearest-axis representations at a tie. The
wrong-word labels take their coefficients from `shortCoefficients` and `secondCoefficients` of
`WordProblems`.
-/

section
/-!
## The labels and the targets of the quarter words

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
end
end
end

section
@[expose] public section
noncomputable section
open scoped BigOperators

namespace SquaresInCircles.Eight.QuarterWordGeometry

open Arithmetic WordProblems

def positiveOf (C : BoundaryCycle Q0) (i : Vertex) : Bool :=
  if C.sigma i=1 then true else false

lemma positiveOf_spec (C : BoundaryCycle Q0) (i : Vertex) :
    (WordProblems.sign (positiveOf C i) : ℝ)=C.sigma i := by
  rcases C.sigma_sign i with h | h <;> norm_num [positiveOf,WordProblems.sign,h]

lemma alpha_formula (C : BoundaryCycle Q0) (i : Vertex) :
    C.alpha i=(WordProblems.sign (positiveOf C i):ℝ)*Real.arctan (C.b i/C.a i) := by
  rw [positiveOf_spec]
  rcases C.sigma_sign i with h | h <;>
    simp [BoundaryCycle.alpha,BoundaryCycle.tangent,h,neg_div,Real.arctan_neg]

lemma unsigned_angle_nonneg (C : BoundaryCycle Q0) (i : Vertex) :
    0 ≤ Real.arctan (C.b i/C.a i) := by
  have h := Real.arctan_mono (div_nonneg (C.b_nonneg i) (C.a_pos i).le)
  simpa using h

lemma alpha_nonpos (C : BoundaryCycle Q0) (i : Vertex) (h : positiveOf C i=false) :
    C.alpha i ≤ 0 := by
  rw [alpha_formula,h]
  simp only [WordProblems.sign,Bool.false_eq_true,ite_false,Rat.cast_neg,Rat.cast_one,neg_one_mul]
  exact neg_nonpos.mpr (unsigned_angle_nonneg C i)

lemma alpha_nonneg (C : BoundaryCycle Q0) (i : Vertex) (h : positiveOf C i=true) :
    0 ≤ C.alpha i := by
  rw [alpha_formula,h]
  simpa [WordProblems.sign] using unsigned_angle_nonneg C i

lemma positiveOf_of_alpha_pos (C : BoundaryCycle Q0) (i : Vertex) (h : 0<C.alpha i) :
    positiveOf C i=true := by
  cases hp : positiveOf C i
  · exact (not_lt_of_ge (alpha_nonpos C i hp) h).elim
  · rfl

lemma positiveOf_of_alpha_neg (C : BoundaryCycle Q0) (i : Vertex) (h : C.alpha i<0) :
    positiveOf C i=false := by
  cases hp : positiveOf C i
  · rfl
  · exact (not_lt_of_ge (alpha_nonneg C i hp) h).elim

def difference {C : BoundaryCycle Q0} (F : QuarterLift C) (i : Vertex) : ℝ :=
  F.theta (next i)-F.theta i

def phaseValue {C : BoundaryCycle Q0} (F : QuarterLift C)
    (hgap : ∀ i,19/25<angleGap C.beta i) (i : Vertex) : ℝ :=
  difference F i+((F.word hgap pi_lt_22_over_7 i).val:ℝ)*Real.pi/2

lemma theta_spread {C : BoundaryCycle Q0} (F : QuarterLift C) (i j : Vertex) :
    |F.theta j-F.theta i|<7/10 := by
  apply abs_lt.mpr
  constructor <;> linarith [(F.theta_range i).1,(F.theta_range i).2,
    (F.theta_range j).1,(F.theta_range j).2,F.small]

lemma difference_small {C : BoundaryCycle Q0} (F : QuarterLift C) (i : Vertex) :
    |difference F i|<7/10 := theta_spread F i (next i)

lemma phase_gap (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀ i,19/25<angleGap C.beta i) (i : Vertex) :
    phaseValue F hgap i+C.alpha i-C.alpha (next i)=angleGap C.beta i := by
  have hk : ((F.word hgap pi_lt_22_over_7 i).val:ℝ)=
      (integerQuarterIncrement F.quarter i:ℝ) := by
    exact_mod_cast F.word_cast hgap pi_lt_22_over_7 i
  rw [phaseValue,hk]
  have hh := F.edge_identity i
  dsimp [difference]
  linarith

lemma phase_sum (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀ i,19/25<angleGap C.beta i) :
    (∑ i,phaseValue F hgap i)=2*Real.pi := by
  have he (i : Vertex) : phaseValue F hgap i=
      angleGap C.beta i-C.alpha i+C.alpha (next i) := by
    linarith [phase_gap C F hgap i]
  simp_rw [he]
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,sum_next,angleGap_sum]
  ring

lemma canonical_phase (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀ i,19/25<angleGap C.beta i) (i : Vertex) :
    C.canonicalAngle (next i)-C.canonicalAngle i=
      phaseValue F hgap i-if i=6 then 2*Real.pi else 0 := by
  have h := phase_gap C F hgap i
  by_cases hi : i=6 <;>
    simp [BoundaryCycle.canonicalAngle,angleGap,hi] at * <;> linarith

lemma relative_phase (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀ i,19/25<angleGap C.beta i) (i : Vertex) :
    relativeC (C.square i) (C.square (next i))=Real.cos (phaseValue F hgap i) ∧
    relativeS (C.square i) (C.square (next i))=Real.sin (phaseValue F hgap i) := by
  have hci : (C.square i).cosine=Real.cos (C.canonicalAngle i) := C.frame_cos i
  have hsi : (C.square i).sine=Real.sin (C.canonicalAngle i) := C.frame_sin i
  have hcj : (C.square (next i)).cosine=Real.cos (C.canonicalAngle (next i)) := C.frame_cos _
  have hsj : (C.square (next i)).sine=Real.sin (C.canonicalAngle (next i)) := C.frame_sin _
  have hc : relativeC (C.square i) (C.square (next i))=
      Real.cos (C.canonicalAngle (next i)-C.canonicalAngle i) := by
    simp [relativeC,hci,hsi,hcj,hsj,Real.cos_sub]
    ring
  have hs : relativeS (C.square i) (C.square (next i))=
      Real.sin (C.canonicalAngle (next i)-C.canonicalAngle i) := by
    simp [relativeS,hci,hsi,hcj,hsj,Real.sin_sub]
    ring
  rw [canonical_phase C F hgap i] at hc hs
  by_cases hi : i=6 <;>
    simpa [hi,Real.cos_sub,Real.sin_sub] using And.intro hc hs

lemma original_margin (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀ i,19/25<angleGap C.beta i) (i : Vertex) (j : Fin 4)
    (hj : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    0 ≤ forwardMargin j (C.a i) (C.b i) (C.a (next i)) (C.b (next i))
      (WordProblems.sign (positiveOf C i)) (WordProblems.sign (positiveOf C (next i)))
      (phaseValue F hgap i) := by
  rw [positiveOf_spec,positiveOf_spec]
  have he := canonical_margin_identity j _ _ _ _ _ _ _ _ (phaseValue F hgap i)
    (C.center_eq i) (C.center_eq (next i)) (relative_phase C F hgap i).1
    (relative_phase C F hgap i).2
  rw [← he]
  exact sub_nonneg.mpr hj

/-- Common label on the original primary and transverse coordinates. -/
def commonValue (kind : RadialKind) (σ : Bool) (a b : ℝ) : ℝ :=
  (WordProblems.sign σ:ℝ)*(if kind=.outer then -9/100+(13/200)*a+(203/200)*b
    else (73/10)*(7/12-a)+(291/250)*b)

def commonMarker (C : BoundaryCycle Q0) (i : Vertex) : ℝ :=
  commonValue (C.kind i) (positiveOf C i) (C.a i) (C.b i)

/-- Both wrong-word label polynomials, evaluated at the primary and transverse coordinates
themselves. -/
def wrongValue (w : WrongWord) (i : Vertex) (kind : RadialKind)
    (σ : Bool) (a b : ℝ) : ℝ :=
  match w with
  | .short =>
      let v := shortCoefficients i (radialIndex kind) (signIndex σ)
      (v 0:ℝ)/100000+(v 1:ℝ)/100000*a+
        (WordProblems.sign σ:ℝ)*(v 2:ℝ)/100000*b
  | .second =>
      let v := secondCoefficients i (radialIndex kind) (signIndex σ)
      (WordProblems.sign σ:ℝ)*((v 0:ℝ)/100000+(v 1:ℝ)/100000*a+
        (v 2:ℝ)/100000*b+(v 3:ℝ)/100000*b^2+(v 4:ℝ)/100000*a*b)

def wrongMarker (C : BoundaryCycle Q0) (w : WrongWord) (i : Vertex) : ℝ :=
  wrongValue w i (C.kind i) (positiveOf C i) (C.a i) (C.b i)

/-- One original vertex value occurs with each sign in the cyclic sum. -/
lemma marker_budget (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i) (marker : Vertex→ℝ) :
    (∑i,(phaseValue F hgap i+marker i-marker (next i)))=2*Real.pi := by
  rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,sum_next,phase_sum C F hgap]
  ring

lemma zero_not_negative_positive (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀ i,19/25<angleGap C.beta i) (i : Vertex)
    (hz : F.word hgap pi_lt_22_over_7 i=0) :
    ¬ (positiveOf C i=false ∧ positiveOf C (next i)=true) := by
  rintro ⟨hs,ht⟩
  have hs' := alpha_nonpos C i hs
  have ht' := alpha_nonneg C (next i) ht
  have hd := (abs_lt.mp (difference_small F i)).2
  have he := phase_gap C F hgap i
  simp only [phaseValue,hz,Fin.val_zero,Nat.cast_zero,zero_mul,zero_div,add_zero] at he
  linarith [hgap i]

/-- The two initial zero increments force strictly positive alpha at role
0 and strictly negative alpha at role 2. -/
lemma initial_signs (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀ i,19/25<angleGap C.beta i) (w : WrongWord)
    (hw : F.word hgap pi_lt_22_over_7=wrongWord w) :
    positiveOf C 0=true ∧ positiveOf C 2=false := by
  have hz0 : F.word hgap pi_lt_22_over_7 0=0 := by cases w <;> simp [hw,wrongWord]
  have hz1 : F.word hgap pi_lt_22_over_7 1=0 := by cases w <;> simp [hw,wrongWord]
  have h0 := phase_gap C F hgap 0
  have h1 := phase_gap C F hgap 1
  simp only [phaseValue,hz0,Fin.val_zero,Nat.cast_zero,zero_mul,zero_div,add_zero] at h0
  simp only [phaseValue,hz1,Fin.val_zero,Nat.cast_zero,zero_mul,zero_div,add_zero] at h1
  norm_num [difference,next] at h0 h1
  have ht := (abs_lt.mp (theta_spread F 0 2)).2
  have hd : 41/50<C.alpha 0-C.alpha 2 := by linarith [hgap 0,hgap 1]
  have ha := C.alpha_range 0
  have hb := C.alpha_range 2
  have hapos : 0<C.alpha 0 := by linarith [pi_lt_22_over_7]
  have hbneg : C.alpha 2<0 := by linarith [pi_lt_22_over_7]
  exact ⟨positiveOf_of_alpha_pos C 0 hapos,positiveOf_of_alpha_neg C 2 hbneg⟩

lemma actual_allowed (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀ i,19/25<angleGap C.beta i) (w : WrongWord)
    (hw : F.word hgap pi_lt_22_over_7=wrongWord w) (i : Vertex) :
    allowed w i (positiveOf C i) (positiveOf C (next i)) := by
  obtain ⟨h0,h2⟩ := initial_signs C F hgap w hw
  refine ⟨?_,?_,?_,?_,?_⟩
  · rintro rfl
    exact h0
  · rintro rfl
    exact h2
  · intro hi
    simpa [hi] using h0
  · intro hi
    simpa [hi] using h2
  · intro hz
    exact zero_not_negative_positive C F hgap i (by simpa [hw] using hz)

/-- Normalizing the EDGE word requires an extra vertex shift in the reflected case. The
physical action is the shared action on the squares, with its signed-axis transport. -/
def normalizingAction (shift : Vertex) (reversed : Bool) : CycleAction where
  shift := if reversed then shift+1 else -shift
  reversed := reversed
  rotation := 0

lemma normalizing_edge (shift : Vertex) (reversed : Bool) (i : Vertex) :
    (if reversed then shift-(normalizingAction shift reversed).edge i
      else (normalizingAction shift reversed).edge i+shift)=i := by
  cases reversed <;>
    simp [normalizingAction,CycleAction.edge,CycleAction.index,next]

lemma word_act (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀ i,19/25<angleGap C.beta i) (G : CycleAction) :
    (F.act G).word (boundary_gap_lower (G.boundary C) le_rfl) pi_lt_22_over_7=
      fun i => F.word hgap pi_lt_22_over_7 (G.edge i) := by
  funext i
  apply Fin.ext
  change (integerQuarterIncrement (G.quarter F.quarter) i).toNat=
    (integerQuarterIncrement F.quarter (G.edge i)).toNat
  rw [G.quarter_increment]

lemma normalize_word (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀ i,19/25<angleGap C.beta i) (v : QuarterWord)
    (hv : (F.word hgap pi_lt_22_over_7).DihedralEquivalent v) :
    ∃ G : CycleAction,
      (F.act G).word (boundary_gap_lower (G.boundary C) le_rfl) pi_lt_22_over_7=v := by
  obtain ⟨shift,reversed,hword⟩ := hv
  refine ⟨normalizingAction shift reversed,?_⟩
  rw [word_act C F hgap]
  funext i
  rw [hword]
  change v (if reversed then shift-(normalizingAction shift reversed).edge i
    else (normalizingAction shift reversed).edge i+shift)=v i
  rw [normalizing_edge]


end SquaresInCircles.Eight.QuarterWordGeometry
end
end
end

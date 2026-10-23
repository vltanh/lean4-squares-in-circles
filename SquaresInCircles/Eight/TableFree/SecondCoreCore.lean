module

public import SquaresInCircles.Eight.TableFree.SecondWordData

/-!
# All core/core edges of the second wrong word

Uncompiled transcription of `WRONG_0011011_ALL_CORE_CORE_HAND_PROOF.md`.
The core-angle endpoint theorem is applied to each literal affine label.
The single nonaffine label keeps its written error bounds. The original
center-distance gap and the finite role/sign comparisons then cover all
nineteen directed core/core cases. The positive/negative edge-three row
uses the direct quarter-angle lower bound, exactly as in the hand proof.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.CoreCore
open CommonQuarter CorePairGeometry Arithmetic TableFreeWordGeometry

abbrev d : ℝ := CoreAngleEndpoint.diagonal

def base (i : Vertex) (σ : Bool) : ℝ :=
  (coefficients i .coreSide σ).c+(7/12)*(coefficients i .coreSide σ).p
def slope (i : Vertex) (σ : Bool) : ℝ := (coefficients i .coreSide σ).q
def exceptional (i : Vertex) (σ : Bool) : Prop :=
  (i=3 ∧ σ=false) ∨ (i=6 ∧ σ=true)
instance (i : Vertex) (σ : Bool) : Decidable (exceptional i σ) := by
  unfold exceptional
  infer_instance

def errorFloor (i : Vertex) (σ : Bool) : ℝ :=
  if exceptional i σ then -(5334/100000)*d^2 else 0

def unsignedUpper (i : Vertex) (σ : Bool) : ℝ :=
  Real.pi/4-base i σ-slope i σ*d-errorFloor i σ

def lower (i : Vertex) (σ : Bool) : ℝ :=
  if σ then -base i σ else -unsignedUpper i σ
def upper (i : Vertex) (σ : Bool) : ℝ :=
  if σ then unsignedUpper i σ else base i σ

lemma core_coefficients (i : Vertex) (σ : Bool) {kind : RadialKind}
    (hk : kind≠.outer) : coefficients i kind σ=coefficients i .coreSide σ := by
  cases kind <;> simp_all [coefficients,WordProblems.radialIndex]

lemma slope_range (i : Vertex) (σ : Bool) : 0≤slope i σ ∧ slope i σ≤8/7 := by
  fin_cases i <;> cases σ <;>
    norm_num [slope,coefficients,WordProblems.secondCoefficients,
      WordProblems.radialIndex,WordProblems.signIndex]

lemma nonlinear_error {a b : ℝ} (hs : CoreState a b) :
    -(5334/100000)*d^2≤(34492/100000)*(7/12-a)-(5334/100000)*b^2 ∧
      (34492/100000)*(7/12-a)-(5334/100000)*b^2≤0 := by
  have hb := CoreAngleEndpoint.state_bounds hs
  have hsq := pow_le_pow_left₀ hb.2.2.1 hb.2.2.2.2 2
  constructor
  · nlinarith [hb.2.1]
  · rcases hs with ⟨rfl,hb0,hb1⟩ | ⟨hb0,hba,hcircle⟩
    · nlinarith [sq_nonneg b]
    · have ha := (CoreAngleEndpoint.corner_diagonal hb0 hba hcircle).2
      have hd := CoreAngleEndpoint.diagonal_bounds.1
      have hbsq : (1/4:ℝ)≤b^2 := by nlinarith
      nlinarith

lemma label_error (i : Vertex) (σ : Bool) {a b : ℝ} (hs : CoreState a b) :
    errorFloor i σ≤(coefficients i .coreSide σ).eval a b-base i σ-slope i σ*b ∧
      (coefficients i .coreSide σ).eval a b-base i σ-slope i σ*b≤0 := by
  have he := nonlinear_error hs
  fin_cases i <;> cases σ <;>
    norm_num [errorFloor,exceptional,base,slope,coefficients,RoleLabel.eval,
      WordProblems.secondCoefficients,WordProblems.radialIndex,WordProblems.signIndex] <;>
    constructor <;> nlinarith [he.1,he.2]

lemma unsigned_bounds (i : Vertex) (σ : Bool) {a b : ℝ} (hs : CoreState a b) :
    -base i σ≤Real.arctan (b/a)-(coefficients i .coreSide σ).eval a b ∧
      Real.arctan (b/a)-(coefficients i .coreSide σ).eval a b≤unsignedUpper i σ := by
  have ha := CoreAngleEndpoint.angle_endpoint hs (slope_range i σ)
  have he := label_error i σ hs
  dsimp [unsignedUpper]
  constructor <;> linarith [ha.1,ha.2,he.1,he.2]

lemma signed_bounds (i : Vertex) (σ : Bool) {kind : RadialKind}
    (hk : kind≠.outer) {a b : ℝ} (hs : CoreState a b) :
    lower i σ≤(WordProblems.sign σ:ℝ)*Real.arctan (b/a)-label i kind σ a b ∧
      (WordProblems.sign σ:ℝ)*Real.arctan (b/a)-label i kind σ a b≤upper i σ := by
  rw [label_coefficients,core_coefficients i σ hk]
  have hh := unsigned_bounds i σ hs
  cases σ <;> simp only [lower,upper,WordProblems.sign,Bool.false_eq_true,if_false,
    if_true,Rat.cast_neg,Rat.cast_one,one_mul,neg_one_mul] <;>
    constructor <;> linarith [hh.1,hh.2]

lemma ordinary_comparison (i : Vertex) (σ τ : Bool)
    (ha : WordProblems.allowed .second i σ τ)
    (hnot : ¬((i=3 ∨ i=5) ∧ σ=true ∧ τ=false)) :
    (91/100:ℝ)<27/20-upper i σ+lower (next i) τ := by
  have hdL := CoreAngleEndpoint.diagonal_bounds.1
  have hdU := CoreAngleEndpoint.diagonal_bounds.2
  have hdSq := CoreAngleEndpoint.diagonal_sq
  have hpi : Real.pi<(3927/1250:ℝ) := by
    linarith [Real.pi_lt_d4]
  fin_cases i <;> cases σ <;> cases τ <;>
    norm_num [WordProblems.allowed,WordProblems.wrongWord,next] at ha <;>
    norm_num [upper,lower,unsignedUpper,base,slope,errorFloor,exceptional,
      coefficients,WordProblems.secondCoefficients,WordProblems.radialIndex,
      WordProblems.signIndex] at hnot ⊢ <;>
    nlinarith [hdL,hdU,hdSq]

lemma special_label (i : Vertex) (hi : i=3 ∨ i=5)
    {source target : RadialKind} (hs : source≠.outer) (ht : target≠.outer)
    (a b A B φ : ℝ) :
    cost i source target true false a b A B φ=
      φ+15374/100000+
        (if i=3 then (104240/100000)*b+(62312/100000)*B
         else (62312/100000)*b+(104240/100000)*B) := by
  rcases hi with rfl | rfl <;> cases source <;> cases target <;>
    norm_num [cost,label,TableFreeWordGeometry.wrongValue,
      WordProblems.secondCoefficients,WordProblems.radialIndex,
      WordProblems.signIndex,WordProblems.sign,next] at hs ht ⊢ <;> ring

lemma original_marker_bounds (C : BoundaryCycle Q0) (i : Vertex)
    (hk : C.kind i≠.outer) :
    lower i (positiveOf C i)≤C.alpha i-wrongMarker C .second i ∧
      C.alpha i-wrongMarker C .second i≤upper i (positiveOf C i) := by
  have hs : CoreState (C.a i) (C.b i) := boundary_core_state C i hk
  have hh := signed_bounds i (positiveOf C i) hk hs
  simpa only [alpha_formula,label,wrongMarker] using hh

/-- All role/sign cases use the original ray gap and original vertex values. -/
theorem actual (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (i : Vertex) (hs : C.kind i≠.outer) (ht : C.kind (next i)≠.outer) :
    threshold i<phaseValue F hgap i+wrongMarker C .second i-
      wrongMarker C .second (next i) := by
  have ha := actual_allowed C F hgap .second hw i
  rw [threshold_value]
  by_cases hspecial : (i=3 ∨ i=5) ∧ positiveOf C i=true ∧ positiveOf C (next i)=false
  · obtain ⟨hi,hσ,hτ⟩ := hspecial
    have hk : F.word hgap pi_lt_22_over_7 i=1 := by
      rw [hw]
      rcases hi with rfl | rfl <;> norm_num [WordProblems.wrongWord]
    have hφ : (17/20:ℝ)<phaseValue F hgap i := by
      have hd := (abs_lt.mp (difference_small F i)).1
      simp only [phaseValue,hk,Fin.val_one,Nat.cast_one,one_mul]
      linarith [Real.pi_gt_d2]
    have he := special_label i hi hs ht (C.a i) (C.b i)
      (C.a (next i)) (C.b (next i)) (phaseValue F hgap i)
    have hc : cost i (C.kind i) (C.kind (next i)) true false
        (C.a i) (C.b i) (C.a (next i)) (C.b (next i)) (phaseValue F hgap i)=
        phaseValue F hgap i+wrongMarker C .second i-wrongMarker C .second (next i) := by
      simp only [cost,label,wrongMarker,hσ,hτ]
    rw [←hc,he]
    split_ifs <;> nlinarith [C.b_nonneg i,C.b_nonneg (next i)]
  · have hsrc := original_marker_bounds C i hs
    have htar := original_marker_bounds C (next i) ht
    have hscalar := ordinary_comparison i (positiveOf C i) (positiveOf C (next i)) ha hspecial
    have hdelta := CoreAngleEndpoint.core_gap C i hs ht
    have hidentity := phase_gap C F hgap i
    linarith

end SquaresInCircles.Eight.TableFree.SecondWord.CoreCore

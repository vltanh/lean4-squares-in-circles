module

public import SquaresInCircles.Eight.TableFree.CoreAngleEndpoint
public import SquaresInCircles.Eight.TableFree.QuarterWordGeometry

/-!
# Every core/core edge of the two binary wrong words

The exact role coefficients define fixed vertex potentials. One shared
core-angle theorem controls every affine potential; the only quadratic
core potential needs one circle estimate. The remaining finite role/sign
substitutions are arithmetic, not subdivisions of a real domain.

The short word has two direct positive-to-negative quarter cases. The
second word has one such case and its reflected counterpart. Every other
case follows from the original center gap and the fixed vertex bounds.
The final adapters retain the original boundary states and frame lift.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.WrongWordCore

open CorePairGeometry CoreAngleEndpoint WordProblems TableFreeWordGeometry

/-- The actual core label, common to the side and the corner. -/
def label (w : WrongWord) (i : Vertex) (σ : Bool) (a b : ℝ) : ℝ :=
  wrongValue w i .coreSide σ a b

lemma core_label {w : WrongWord} {i : Vertex} {kind : RadialKind}
    {σ : Bool} {a b : ℝ} (hk : kind≠.outer) :
    wrongValue w i kind σ a b=label w i σ a b := by
  cases w <;> simp [wrongValue,label,radialIndex,hk]

def shortC (i : Vertex) (σ : Bool) : ℝ :=
  (shortCoefficients i 1 (signIndex σ) 0:ℝ)/100000

def shortG (i : Vertex) (σ : Bool) : ℝ :=
  (shortCoefficients i 1 (signIndex σ) 2:ℝ)/100000

lemma short_label (i : Vertex) (σ : Bool) (a b : ℝ) :
    label .short i σ a b=shortC i σ+(sign σ:ℝ)*shortG i σ*b := by
  fin_cases i <;> cases σ <;>
    norm_num [label,wrongValue,shortC,shortG,shortCoefficients,radialIndex,signIndex,sign]

lemma shortG_bounds (i : Vertex) (σ : Bool) :
    0≤shortG i σ ∧ shortG i σ≤8/7 := by
  fin_cases i <;> cases σ <;> norm_num [shortG,shortCoefficients,signIndex]

def shortLower (i : Vertex) (σ : Bool) : ℝ :=
  if σ then -shortC i σ else -Real.pi/4+shortG i σ*diagonal-shortC i σ

def shortUpper (i : Vertex) (σ : Bool) : ℝ :=
  if σ then Real.pi/4-shortG i σ*diagonal-shortC i σ else -shortC i σ

lemma short_marker_bounds {a b : ℝ} (hc : CoreState a b)
    (i : Vertex) (σ : Bool) :
    shortLower i σ≤(sign σ:ℝ)*Real.arctan (b/a)-label .short i σ a b ∧
      (sign σ:ℝ)*Real.arctan (b/a)-label .short i σ a b≤shortUpper i σ := by
  have h := angle_endpoint hc (shortG_bounds i σ)
  rw [short_label]
  cases σ <;> simp only [shortLower,shortUpper,sign,Bool.false_eq_true,if_false,
    if_true,Rat.cast_neg,Rat.cast_one,one_mul,neg_one_mul] <;>
    constructor <;> linarith [h.1,h.2]

/-- Intrinsic role/sign arithmetic. The two direct geometric cases are
kept separate because their quarter phase gives a stronger bound. -/
lemma short_ordinary_comparison (i : Vertex) (σ τ : Bool)
    (ha : allowed .short i σ τ)
    (h4 : ¬(i=4 ∧ σ=true ∧ τ=false))
    (h5 : ¬(i=5 ∧ σ=true ∧ τ=false)) :
    (449/500:ℝ)<27/20-shortUpper i σ+shortLower (next i) τ := by
  have hd := diagonal_bounds.1
  have hp := Arithmetic.pi_hand_enclosure.2
  fin_cases i <;> cases σ <;> cases τ <;>
    norm_num [allowed,wrongWord,next,shortUpper,shortLower,shortC,shortG,
      shortCoefficients,signIndex] at ha h4 h5 ⊢ <;> linarith

lemma short_four_opposite {a b A B φ : ℝ}
    (hb : 0≤b) (hB : 0≤B) (hφ : Real.pi/2-7/10≤φ) :
    (449/500:ℝ)<φ+label .short 4 true a b-label .short 5 false A B := by
  norm_num [label,wrongValue,shortCoefficients,radialIndex,signIndex,sign]
  linarith [Real.pi_gt_d2]

/-- In the lower phase branch, the physical ray gap itself forces a
positive transverse sum. This keeps every original separating owner. -/
lemma short_five_opposite {a b A B φ : ℝ}
    (hs : CoreState a b) (ht : CoreState A B)
    (hφ : Real.pi/2-7/10≤φ)
    (hgap : (27/20:ℝ)<φ+Real.arctan (b/a)+Real.arctan (B/A)) :
    (449/500:ℝ)<φ+label .short 5 true a b-label .short 6 false A B := by
  have hb := (state_bounds hs).2.2.1
  have hB := (state_bounds ht).2.2.1
  have hcost : φ+label .short 5 true a b-label .short 6 false A B=
      φ-5203/100000+(19839/20000)*b+(99173/100000)*B := by
    norm_num [label,wrongValue,shortCoefficients,radialIndex,signIndex,sign]
    ring
  rw [hcost]
  by_cases hlarge : (951/1000:ℝ)≤φ
  · linarith
  · have hsum : (1/10:ℝ)<b+B := by
      linarith [angle_le_twice hs,angle_le_twice ht]
    linarith [Real.pi_gt_d2]

/-- All nineteen allowed short-word core/core cases, on their complete
closed state and frame domains. -/
theorem short_cost {a b A B φ : ℝ} (hs : CoreState a b) (ht : CoreState A B)
    (i : Vertex) (σ τ : Bool) (ha : allowed .short i σ τ)
    (hphase : |φ-((wrongWord .short i).val:ℝ)*Real.pi/2|≤7/10)
    (hgap : (27/20:ℝ)<φ+(sign σ:ℝ)*Real.arctan (b/a)-
      (sign τ:ℝ)*Real.arctan (B/A)) :
    (449/500:ℝ)<φ+label .short i σ a b-label .short (next i) τ A B := by
  by_cases h4 : i=4 ∧ σ=true ∧ τ=false
  · rcases h4 with ⟨rfl,rfl,rfl⟩
    have hφ : Real.pi/2-7/10≤φ := by
      norm_num [wrongWord] at hphase
      linarith [(abs_le.mp hphase).1]
    simpa [next] using short_four_opposite (a := a) (A := A)
      (state_bounds hs).2.2.1 (state_bounds ht).2.2.1 hφ
  by_cases h5 : i=5 ∧ σ=true ∧ τ=false
  · rcases h5 with ⟨rfl,rfl,rfl⟩
    have hφ : Real.pi/2-7/10≤φ := by
      norm_num [wrongWord] at hphase
      linarith [(abs_le.mp hphase).1]
    have hgap' : (27/20:ℝ)<φ+Real.arctan (b/a)+Real.arctan (B/A) := by
      simpa [sign] using hgap
    simpa [next] using short_five_opposite hs ht hφ hgap'
  have hcmp := short_ordinary_comparison i σ τ ha h4 h5
  have hi := short_marker_bounds hs i σ
  have hj := short_marker_bounds ht (next i) τ
  linarith [hi.2,hj.1]

/-- Constant and transverse slope after the exceptional primary term is
expanded at the core-side coordinate `7/12`. -/
def secondC (i : Vertex) (σ : Bool) : ℝ :=
  (secondCoefficients i 1 (signIndex σ) 0:ℝ)/100000+
    (secondCoefficients i 1 (signIndex σ) 1:ℝ)/100000*(7/12)

def secondG (i : Vertex) (σ : Bool) : ℝ :=
  (secondCoefficients i 1 (signIndex σ) 2:ℝ)/100000

def nonAffine (i : Vertex) (σ : Bool) : Prop :=
  (i=3 ∧ σ=false) ∨ (i=6 ∧ σ=true)

instance (i : Vertex) (σ : Bool) : Decidable (nonAffine i σ) := by
  unfold nonAffine
  infer_instance

def correction (a b : ℝ) : ℝ := (8623/25000)*(7/12-a)-(2667/50000)*b^2

def secondError (i : Vertex) (σ : Bool) : ℝ :=
  if nonAffine i σ then (2667/50000)*diagonal^2 else 0

lemma second_label (i : Vertex) (σ : Bool) (a b : ℝ) :
    label .second i σ a b=(sign σ:ℝ)*
      (secondC i σ+secondG i σ*b+(if nonAffine i σ then correction a b else 0)) := by
  fin_cases i <;> cases σ <;>
    norm_num [label,wrongValue,secondC,secondG,secondCoefficients,radialIndex,
      signIndex,sign,nonAffine,correction] <;> ring

lemma secondG_bounds (i : Vertex) (σ : Bool) :
    0≤secondG i σ ∧ secondG i σ≤8/7 := by
  fin_cases i <;> cases σ <;> norm_num [secondG,secondCoefficients,signIndex]

/-- The only nonaffine core label has a one-sided error on both closed
core pieces. Its lower bound comes directly from the diagonal endpoint. -/
lemma correction_bounds {a b : ℝ} (hc : CoreState a b) :
    -(2667/50000)*diagonal^2≤correction a b ∧ correction a b≤0 := by
  obtain ⟨ha,hau,hb,hab,hbd⟩ := state_bounds hc
  have hd0 : 0≤diagonal := by linarith [diagonal_bounds.1]
  have hb2 := pow_le_pow_left₀ hb hbd 2
  constructor
  · dsimp [correction]
    nlinarith
  · rcases hc with ⟨rfl,hb,hbu⟩ | ⟨hb,hab,hcircle⟩
    · dsimp [correction]
      nlinarith [sq_nonneg b]
    · have hal := (corner_geometry hb hab hcircle).1
      have hsq := pow_le_pow_left₀ (show (0:ℝ)≤1/2 by norm_num) hb 2
      dsimp [correction]
      nlinarith

def secondLower (i : Vertex) (σ : Bool) : ℝ :=
  if σ then -secondC i σ else
    -Real.pi/4+secondG i σ*diagonal+secondC i σ-secondError i σ

def secondUpper (i : Vertex) (σ : Bool) : ℝ :=
  if σ then Real.pi/4-secondG i σ*diagonal-secondC i σ+secondError i σ
    else secondC i σ

lemma second_marker_bounds {a b : ℝ} (hc : CoreState a b)
    (i : Vertex) (σ : Bool) :
    secondLower i σ≤(sign σ:ℝ)*Real.arctan (b/a)-label .second i σ a b ∧
      (sign σ:ℝ)*Real.arctan (b/a)-label .second i σ a b≤secondUpper i σ := by
  have h := angle_endpoint hc (secondG_bounds i σ)
  have he := correction_bounds hc
  have he' : -secondError i σ≤(if nonAffine i σ then correction a b else 0) ∧
      (if nonAffine i σ then correction a b else 0)≤0 := by
    by_cases hi : nonAffine i σ
    · simpa [secondError,hi] using he
    · simp [secondError,hi]
  rw [second_label]
  cases σ <;> simp only [secondLower,secondUpper,sign,Bool.false_eq_true,
    if_false,if_true,Rat.cast_neg,Rat.cast_one,one_mul,neg_one_mul] <;>
    constructor <;> linarith [h.1,h.2,he'.1,he'.2]

lemma second_ordinary_comparison (i : Vertex) (σ τ : Bool)
    (ha : allowed .second i σ τ)
    (h3 : ¬(i=3 ∧ σ=true ∧ τ=false))
    (h5 : ¬(i=5 ∧ σ=true ∧ τ=false)) :
    (91/100:ℝ)<27/20-secondUpper i σ+secondLower (next i) τ := by
  have hd := diagonal_bounds.1
  have hdu := diagonal_bounds.2
  have hd0 : 0≤diagonal := by linarith
  have hd2 := pow_le_pow_left₀ hd0 hdu.le 2
  have hp := Arithmetic.pi_hand_enclosure.2
  fin_cases i <;> cases σ <;> cases τ <;>
    norm_num [allowed,wrongWord,next,secondUpper,secondLower,secondC,secondG,
      secondCoefficients,signIndex,secondError,nonAffine] at ha h3 h5 ⊢ <;>
      nlinarith

lemma second_three_opposite {a b A B φ : ℝ}
    (hb : 0≤b) (hB : 0≤B) (hφ : Real.pi/2-7/10≤φ) :
    (91/100:ℝ)<φ+label .second 3 true a b-label .second 4 false A B := by
  norm_num [label,wrongValue,secondCoefficients,radialIndex,signIndex,sign]
  linarith [Real.pi_gt_d2]

lemma second_five_opposite {a b A B φ : ℝ}
    (hb : 0≤b) (hB : 0≤B) (hφ : Real.pi/2-7/10≤φ) :
    (91/100:ℝ)<φ+label .second 5 true a b-label .second 6 false A B := by
  norm_num [label,wrongValue,secondCoefficients,radialIndex,signIndex,sign]
  linarith [Real.pi_gt_d2]

/-- Every core/core role and both signs of the original frame error. -/
theorem second_cost {a b A B φ : ℝ} (hs : CoreState a b) (ht : CoreState A B)
    (i : Vertex) (σ τ : Bool) (ha : allowed .second i σ τ)
    (hphase : |φ-((wrongWord .second i).val:ℝ)*Real.pi/2|≤7/10)
    (hgap : (27/20:ℝ)<φ+(sign σ:ℝ)*Real.arctan (b/a)-
      (sign τ:ℝ)*Real.arctan (B/A)) :
    (91/100:ℝ)<φ+label .second i σ a b-label .second (next i) τ A B := by
  by_cases h3 : i=3 ∧ σ=true ∧ τ=false
  · rcases h3 with ⟨rfl,rfl,rfl⟩
    have hφ : Real.pi/2-7/10≤φ := by
      norm_num [wrongWord] at hphase
      linarith [(abs_le.mp hphase).1]
    simpa [next] using second_three_opposite (a := a) (A := A)
      (state_bounds hs).2.2.1 (state_bounds ht).2.2.1 hφ
  by_cases h5 : i=5 ∧ σ=true ∧ τ=false
  · rcases h5 with ⟨rfl,rfl,rfl⟩
    have hφ : Real.pi/2-7/10≤φ := by
      norm_num [wrongWord] at hphase
      linarith [(abs_le.mp hphase).1]
    simpa [next] using second_five_opposite (a := a) (A := A)
      (state_bounds hs).2.2.1 (state_bounds ht).2.2.1 hφ
  have hcmp := second_ordinary_comparison i σ τ ha h3 h5
  have hi := second_marker_bounds hs i σ
  have hj := second_marker_bounds ht (next i) τ
  linarith [hi.2,hj.1]

/-- The complete physical core/core block for either wrong word. The
boundary states, weak feasible owners and lift are the original ones. -/
theorem actual_core_pair (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i) (w : WrongWord)
    (hw : F.word hgap pi_lt_22_over_7=wrongWord w) (i : Vertex)
    (hi : C.kind i≠.outer) (hj : C.kind (next i)≠.outer) :
    (wrongGamma w i:ℝ)<phaseValue F hgap i+
      wrongMarker C w i-wrongMarker C w (next i) := by
  have hs := boundary_core_state C i hi
  have ht := boundary_core_state C (next i) hj
  have ha := actual_allowed C F hgap w hw i
  have he := phase_gap C F hgap i
  rw [alpha_formula,alpha_formula] at he
  have hd : (27/20:ℝ)<phaseValue F hgap i+
      (sign (positiveOf C i):ℝ)*Real.arctan (C.b i/C.a i)-
      (sign (positiveOf C (next i)):ℝ)*Real.arctan (C.b (next i)/C.a (next i)) := by
    rw [he]
    exact CoreAngleEndpoint.core_gap C i hi hj
  have hp : |phaseValue F hgap i-((wrongWord w i).val:ℝ)*Real.pi/2|≤7/10 := by
    simpa [phaseValue,hw] using (difference_small F i).le
  have hlabeli : wrongMarker C w i=label w i (positiveOf C i) (C.a i) (C.b i) :=
    core_label hi
  have hlabelj : wrongMarker C w (next i)=
      label w (next i) (positiveOf C (next i)) (C.a (next i)) (C.b (next i)) :=
    core_label hj
  rw [hlabeli,hlabelj]
  cases w with
  | short =>
      have h := short_cost hs ht i _ _ ha hp hd
      have hg : (wrongGamma .short i:ℝ)≤449/500 := by
        by_cases hi : i=2 <;> norm_num [wrongGamma,hi]
      linarith
  | second =>
      have h := second_cost hs ht i _ _ ha hp hd
      norm_num [wrongGamma]
      linarith

end SquaresInCircles.Eight.WrongWordCore

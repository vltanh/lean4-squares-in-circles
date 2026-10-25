module

public import SquaresInCircles.Eight.TableFree.SecondOuterVBounds
public import SquaresInCircles.Eight.TableFree.SecondOuterKBounds
public import SquaresInCircles.Eight.TableFree.SecondOuterPositiveThreeLowerFourth
public import SquaresInCircles.Eight.TableFree.SecondOuterPointProducts

/-!
# Two whole-arc chords for positive-to-negative outer edge three

The global source chord has slope `0.736` and the global target
chord has slope `0.7`.  Their common slope `0.7` already leaves a
strict reserve, so no short-coordinate derivative subdivisions are
needed.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.PositiveNegativeThree

open CommonQuarter CorePairGeometry Arithmetic

def value (b B φ : ℝ) : ℝ := φ+V b+K B
def base : ℝ := V 0+K 0
def Early (φ : ℝ) : Prop := φ∈Icc PositiveThree.lowerAngle (943/1000)
def scalar (φ : ℝ) : ℝ :=
  φ+base+7/20+(7/20)*Real.cos φ-((7/10)*outerAxial-7/20)*Real.sin φ
def scalarFirst (φ : ℝ) : ℝ :=
  1-(7/20)*Real.sin φ-((7/10)*outerAxial-7/20)*Real.cos φ

lemma cost_identity {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B) :
    SecondWord.cost 3 .outer .outer true false a b A B φ=value b B φ := by
  unfold value
  rw [show V b=VLabel.eval a b from VLabel.outer_actual hs,
    show K B=KLabel.eval A B from KLabel.outer_actual ht]
  norm_num [SecondWord.cost,label,TableFreeWordGeometry.wrongValue,next,
    WordProblems.secondCoefficients,WordProblems.radialIndex,WordProblems.signIndex,
    WordProblems.sign,VLabel,KLabel,RoleLabel.eval]
  ring

lemma base_lower : (-(4439/100000:ℝ))<base := by
  dsimp [base]
  linarith [V_zero_bounds.1,K_zero_bounds.1]

lemma chord {b B φ : ℝ} (hb : b∈Icc 0 outerDiagonal) (hB : B∈Icc 0 outerDiagonal) :
    φ+base+(7/10)*(b+B)≤value b B φ := by
  have hv := V_chord hb
  have hk := K_chord hB
  dsimp [value,base]
  linarith [hb.1]

lemma late_value {b B φ : ℝ} (hb : b∈Icc 0 outerDiagonal) (hB : B∈Icc 0 outerDiagonal)
    (hφ : (943/1000:ℝ)≤φ) : (4493/5000:ℝ)<value b B φ := by
  have hh := chord (φ := φ) hb hB
  nlinarith [base_lower,hb.1,hB.1]

lemma large_sum {b B φ : ℝ} (hb : b∈Icc 0 outerDiagonal) (hB : B∈Icc 0 outerDiagonal)
    (hφ : PositiveThree.lowerAngle≤φ) (hsum : (1/5:ℝ)≤b+B) :
    (483/500:ℝ)<value b B φ := by
  have hh := chord (φ := φ) hb hB
  dsimp [PositiveThree.lowerAngle] at hφ
  linarith [base_lower,pi_hand_enclosure.1]

lemma early_lower {φ : ℝ} (hφ : Early φ) : PositiveThree.Lower φ :=
  ⟨hφ.1,by linarith [hφ.2,pi_hand_enclosure.1]⟩

lemma right_lower : PositiveThree.Lower (943/1000:ℝ) := by
  constructor
  · dsimp [PositiveThree.lowerAngle]
    linarith [pi_hand_enclosure.2]
  · linarith [pi_hand_enclosure.1]

lemma early_cos {φ : ℝ} (hφ : Early φ) : (587/1000:ℝ)<Real.cos φ := by
  have ht := PointProducts.trig (show (0:ℝ)≤943/1000 by norm_num)
  norm_num [ReferenceTrig.sin11,sin9,sin7,ReferenceTrig.cos12,cos10,cos8] at ht
  have href : (587/1000:ℝ)<Real.cos (943/1000) := by linarith [ht.2.1]
  exact href.trans_le (PositiveThree.lower_cos_antitone (early_lower hφ) right_lower hφ.2)

lemma small_primary {a b : ℝ} (hs : OuterState a b) (hb : b≤1/5) : (27/20:ℝ)<a := by
  have ha := NegativeTwo.primary_mem hs
  have hcircle := hs.2.2
  have hsquare : (b+1/2)^2≤(7/10:ℝ)^2 := by nlinarith [hs.1]
  norm_num [Q0] at hcircle
  nlinarith [ha.1,fine_outer_endpoint_bounds.2]

lemma scalar_hasDerivAt (φ : ℝ) : HasDerivAt scalar (scalarFirst φ) φ := by
  exact (((((hasDerivAt_id φ).add_const base).add_const (7/20)).add
    ((Real.hasDerivAt_cos φ).const_mul (7/20))).sub
      ((Real.hasDerivAt_sin φ).const_mul ((7/10)*outerAxial-7/20))).congr_deriv
    (by dsimp only [scalarFirst]; ring)

lemma scalarFirst_positive (φ : ℝ) : 0<scalarFirst φ := by
  have hcoef : 0≤(7/10)*outerAxial-7/20 := by linarith [outer_endpoint_bounds.1]
  have hs := mul_le_mul_of_nonneg_left (Real.sin_le_one φ) (by norm_num : (0:ℝ)≤7/20)
  have hc := mul_le_mul_of_nonneg_left (Real.cos_le_one φ) hcoef
  dsimp [scalarFirst]
  nlinarith [outer_endpoint_bounds.2.1]

lemma scalar_monotone : MonotoneOn scalar (Icc PositiveThree.lowerAngle (943/1000)) :=
  monoOn_of_hasDeriv_nonneg
    (fun φ _ => (scalar_hasDerivAt φ).continuousAt.continuousWithinAt)
    (fun φ _ => scalar_hasDerivAt φ)
    (fun φ _ => (scalarFirst_positive φ).le)

lemma scalar_left : (9119/10000:ℝ)<scalar PositiveThree.lowerAngle := by
  have ht := PointProducts.trig (show (0:ℝ)≤7/10 by norm_num)
  norm_num [ReferenceTrig.sin11,sin9,sin7,ReferenceTrig.cos12,cos10,cos8] at ht
  have hs : (64421/100000:ℝ)<Real.sin (7/10) := by linarith [ht.1.1]
  have hc : Real.cos (7/10)<(15297/20000:ℝ) := by linarith [ht.2.2]
  have hcoef : 0≤(7/10)*outerAxial-7/20 := by linarith [outer_endpoint_bounds.1]
  have hcap : (7/10)*outerAxial-7/20<(1281/2000:ℝ) := by
    linarith [outer_endpoint_bounds.2.1]
  have hcos0 : 0≤Real.cos (7/10) := by linarith [ht.2.1]
  have hp := mul_le_mul hcap.le hc.le hcos0 (by norm_num : (0:ℝ)≤1281/2000)
  simp only [scalar,PositiveThree.lowerAngle,Real.sin_sub,Real.cos_sub,
    Real.sin_pi_div_two,Real.cos_pi_div_two,zero_mul,one_mul,sub_zero,zero_add]
  nlinarith [base_lower,pi_hand_enclosure.1]

lemma scalar_lower {φ : ℝ} (hφ : Early φ) : (9119/10000:ℝ)<scalar φ :=
  scalar_left.trans_le
    (scalar_monotone ⟨le_rfl,right_lower.1⟩ hφ hφ.1)

end SquaresInCircles.Eight.TableFree.SecondWord.PositiveNegativeThree

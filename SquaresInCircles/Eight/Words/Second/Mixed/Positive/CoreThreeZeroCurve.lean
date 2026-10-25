module

public import SquaresInCircles.Eight.Words.Second.Mixed.Positive.CoreThreeData
public import SquaresInCircles.Eight.Words.Second.Mixed.Positive.CoreThreeGrowth
public import SquaresInCircles.Eight.Words.Second.Mixed.Primary.ZeroCurve
public import SquaresInCircles.Eight.Words.Second.Outer.Positive.ThreeLowerFourth

/-!
# Eight squares: the complete early primary zero-contact curve

Both endpoint trigonometric bounds are rational Taylor consequences.
They place the entire harmonic-height curve on the original outer
circle and within the range of the primary T-label growth estimate.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedThree.PositiveCore.Zero
open CommonQuarter CorePairGeometry Arithmetic
open PositiveThree (Lower lowerAngle lower_trig)

abbrev m := PrimaryZero.m
abbrev v := PrimaryZero.v
abbrev U := PrimaryZero.U
abbrev V := PrimaryZero.V
abbrev b := PrimaryZero.b
def a (φ : ℝ) : ℝ := U φ-1/2
def angles : Set ℝ := Icc (57/50) (7/5)
def K (φ : ℝ) : ℝ := φ-c+TPrimaryLabel.outer (a φ)
def KD (φ : ℝ) : ℝ := 1-TPrimaryLabel.d1 (a φ)*v φ
def KDD (φ : ℝ) : ℝ := TPrimaryLabel.d2 (a φ)*(v φ)^2-TPrimaryLabel.d1 (a φ)*m φ

lemma initial_trig :
    (90863349/100000000:ℝ)<Real.sin (57/50) ∧ Real.sin (57/50)<90863350/100000000 ∧
    (41759450/100000000:ℝ)<Real.cos (57/50) ∧ Real.cos (57/50)<41759451/100000000 := by
  have hs := HighOrderTaylor.S15_le_sin (x := (57/50:ℝ)) (by norm_num)
  have hsU := HighOrderTaylor.sin_le_S13 (x := (57/50:ℝ)) (by norm_num)
  have hc := HighOrderTaylor.C14_le_cos (x := (57/50:ℝ)) (by norm_num)
  have hcU := HighOrderTaylor.cos_le_C12 (x := (57/50:ℝ)) (by norm_num)
  norm_num [HighOrderTaylor.S15,HighOrderTaylor.S11,HighOrderTaylor.S13,
    HighOrderTaylor.C14,HighOrderTaylor.C12,sin9,sin7,cos10,cos8] at hs hsU hc hcU
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

lemma lower_mem {φ : ℝ} (hφ : φ∈angles) : Lower φ :=
  ⟨by dsimp [angles] at hφ; dsimp [lowerAngle]; linarith [hφ.1,pi_hand_enclosure.2],
    by dsimp [angles] at hφ; linarith [hφ.2,pi_hand_enclosure.1]⟩

lemma trig {φ : ℝ} (hφ : φ∈angles) :
    (227/250:ℝ)<Real.sin φ ∧ Real.sin φ≤1 ∧ 0≤Real.cos φ ∧ Real.cos φ<(209/500:ℝ) := by
  have hi : (57/50:ℝ)∈angles := by norm_num [angles]
  have hs := PositiveThree.lower_sin_monotone (lower_mem hi) (lower_mem hφ) hφ.1
  have hc := PositiveThree.lower_cos_antitone (lower_mem hi) (lower_mem hφ) hφ.1
  exact ⟨by linarith [initial_trig.1],Real.sin_le_one φ,(lower_trig (lower_mem hφ)).2.2.1,
    by linarith [initial_trig.2.2.2]⟩

lemma harmonic_bounds {φ : ℝ} (hφ : φ∈angles) :
    (169/250:ℝ)< m φ ∧ m φ<(907/1000:ℝ) ∧
    (31/40:ℝ)<v φ ∧ v φ<(983/1000:ℝ) := by
  have hm : AntitoneOn m angles := by
    apply antiOn_of_hasDeriv_nonpos
      (fun φ _ => (PrimaryZero.m_hasDerivAt φ).continuousAt.continuousWithinAt)
      (fun φ _ => PrimaryZero.m_hasDerivAt φ)
    intro φ hφ
    have ht := trig (Ioo_subset_Icc_self hφ)
    dsimp [v,PrimaryZero.v]
    linarith [ht.1,ht.2.2.2]
  have hv : MonotoneOn v angles := by
    apply monoOn_of_hasDeriv_nonneg
      (fun φ _ => (PrimaryZero.v_hasDerivAt φ).continuousAt.continuousWithinAt)
      (fun φ _ => PrimaryZero.v_hasDerivAt φ)
    intro φ hφ
    have ht := trig (Ioo_subset_Icc_self hφ)
    dsimp [m,PrimaryZero.m]
    linarith [ht.1,ht.2.2.1]
  have hi : (57/50:ℝ)∈angles := by norm_num [angles]
  have he : (7/5:ℝ)∈angles := by norm_num [angles]
  have hml := hm hφ he hφ.2
  have hmu := hm hi hφ hφ.1
  have hvl := hv hi hφ hφ.1
  have hvu := hv hφ he hφ.2
  have ht := PrimaryZero.terminal_trig
  dsimp [m,PrimaryZero.m,v,PrimaryZero.v] at hml hmu hvl hvu ⊢
  exact ⟨by linarith [ht.1,ht.2.2.1],by linarith [initial_trig.2.1,initial_trig.2.2.2],
    by linarith [initial_trig.1,initial_trig.2.2.2],by linarith [ht.2.1,ht.2.2.1]⟩

lemma U_bounds {φ : ℝ} (hφ : φ∈angles) : (419/250:ℝ)<U φ ∧ U φ<(1907/1000:ℝ) := by
  dsimp [U,PrimaryZero.U]
  exact ⟨by linarith [(harmonic_bounds hφ).1],by linarith [(harmonic_bounds hφ).2.1]⟩

lemma domain {φ : ℝ} (hφ : φ∈angles) : 0<Q0-(U φ)^2 := by
  have hh := U_bounds hφ
  have hp := pow_le_pow_left₀ (by linarith [hh.1] : 0≤U φ) hh.2.le 2
  norm_num [Q0]
  nlinarith

lemma V_bounds {φ : ℝ} (hφ : φ∈angles) : (1/2:ℝ)<V φ ∧ V φ<(1052/1000:ℝ) := by
  have he : (V φ)^2=Q0-(U φ)^2 := HeightLabel.root_sq (domain hφ)
  have hp : 0<V φ := HeightLabel.root_pos (domain hφ)
  have hh := U_bounds hφ
  have hlo := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤419/250) hh.1.le 2
  have hhi := pow_le_pow_left₀ (by linarith [hh.1] : 0≤U φ) hh.2.le 2
  norm_num [Q0] at he
  constructor <;> nlinarith

lemma physical {φ : ℝ} (hφ : φ∈angles) : OuterState (a φ) (b φ) := by
  have hh := U_bounds hφ
  have hv := V_bounds hφ
  have hc : (V φ)^2=Q0-(U φ)^2 := HeightLabel.root_sq (domain hφ)
  dsimp [OuterState,a,b,PrimaryZero.b]
  exact ⟨by linarith,by linarith,by nlinarith only [hc]⟩

lemma primary_mem {φ : ℝ} (hφ : φ∈angles) : a φ∈Icc (147/125:ℝ) outerAxial :=
  ⟨by dsimp [a]; linarith [(U_bounds hφ).1],(NegativeTwo.primary_mem (physical hφ)).2⟩

lemma source_mem {φ : ℝ} (hφ : φ∈angles) : b φ∈Icc (0:ℝ) (3/5) := by
  have hh := V_bounds hφ
  dsimp [b,PrimaryZero.b]
  exact ⟨by linarith,by linarith⟩

lemma a_hasDerivAt (φ : ℝ) : HasDerivAt a (-v φ) φ :=
  (PrimaryZero.U_hasDerivAt φ).sub_const (1/2)

lemma K_hasDerivAt {φ : ℝ} (hφ : φ∈angles) : HasDerivAt K (KD φ) φ := by
  have hT := TPrimaryLabel.outer_hasDerivAt
    (primary_domain (NegativeTwo.primary_mem (physical hφ)))
  have hc0 := hT.comp φ (a_hasDerivAt φ)
  have hc : HasDerivAt (fun x => TPrimaryLabel.outer (a x)) (TPrimaryLabel.d1 (a φ)*-v φ) φ := hc0
  have h := ((hasDerivAt_id' φ).sub_const c).add hc
  exact h.congr_deriv (by simp only [KD]; ring)

lemma KD_hasDerivAt {φ : ℝ} (hφ : φ∈angles) : HasDerivAt KD (KDD φ) φ := by
  have hD := TPrimaryLabel.d1_hasDerivAt
    (primary_domain (NegativeTwo.primary_mem (physical hφ)))
  have hc0 := hD.comp φ (a_hasDerivAt φ)
  have hc : HasDerivAt (fun x => TPrimaryLabel.d1 (a x)) (TPrimaryLabel.d2 (a φ)*-v φ) φ := hc0
  have h := (hc.mul (PrimaryZero.v_hasDerivAt φ)).const_sub 1
  exact h.congr_deriv (by simp only [KDD]; ring)

lemma KDD_lower {φ : ℝ} (hφ : φ∈angles) : (7/25:ℝ)<KDD φ := by
  have hh := harmonic_bounds hφ
  have hg := primary_growth (primary_mem hφ)
  have hs : (31/40:ℝ)^2<(v φ)^2 := by nlinarith [hh.2.2.1]
  have hp := mul_lt_mul_of_pos_right hg.2 (sq_pos_of_pos (by linarith [hh.2.2.1] : 0<v φ))
  have hq := mul_pos (show 0<TPrimaryLabel.d1 (a φ) by linarith [hg.1])
    (show 0<2*(v φ)^2-m φ-(1177/4000:ℝ) by nlinarith [hh.2.1])
  dsimp [KDD]
  nlinarith [hg.1]

lemma cost_eq {φ : ℝ} (hφ : φ∈angles) : K φ=φ-c-T (b φ) := by
  dsimp [K]
  rw [NegativeThree.primary_actual (physical hφ)]
  ring

end SquaresInCircles.Eight.SecondWord.MixedThree.PositiveCore.Zero

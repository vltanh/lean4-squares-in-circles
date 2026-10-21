module

public import SquaresInCircles.Eight.TableFree.SecondMixedLHeightGrowth
public import SquaresInCircles.Eight.TableFree.SecondMixedPrimaryZeroCurve

/-!
# The shared L-label primary zero-source curve

The same exact harmonic height serves both core signs. On the complete
middle arc its cost has negative third derivative. On the entire late
arc its second derivative is negative directly from the height label;
no quotient-of-radial-derivatives estimate is needed.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.LPrimaryZero
open CommonQuarter CorePairGeometry Arithmetic HeightLabel

abbrev m := PrimaryZero.m
abbrev w := PrimaryZero.v
abbrev U := PrimaryZero.U
abbrev V := PrimaryZero.V
abbrev b := PrimaryZero.b

def angles : Set ℝ := Icc (33/25) (Real.pi/2)
def middle : Set ℝ := Icc (33/25) (37/25)
def late : Set ℝ := Icc (73/50) (Real.pi/2)
def e : ℝ := 11021/50000-(8623/25000)*(7/12)
def K (φ : ℝ) : ℝ := φ-e+LHeight.eval (U φ)
def KD (φ : ℝ) : ℝ := 1-LHeight.d1 (U φ)*w φ
def KDD (φ : ℝ) : ℝ := LHeight.d2 (U φ)*(w φ)^2-LHeight.d1 (U φ)*m φ
def KDDD (φ : ℝ) : ℝ := w φ*(-LHeight.d3 (U φ)*(w φ)^2+
  3*LHeight.d2 (U φ)*m φ+LHeight.d1 (U φ))

lemma initial_trig :
    (96871509/100000000:ℝ)≤Real.sin (33/25) ∧ Real.sin (33/25)≤96871511/100000000 ∧
    (4963509/20000000:ℝ)≤Real.cos (33/25) ∧ Real.cos (33/25)≤12408773/50000000 := by
  have hs := HighOrderTaylor.S11_le_sin (x := (33/25:ℝ)) (by norm_num)
  have hsU := HighOrderTaylor.sin_le_S13 (x := (33/25:ℝ)) (by norm_num)
  have hc := HighOrderTaylor.C14_le_cos (x := (33/25:ℝ)) (by norm_num)
  have hcU := HighOrderTaylor.cos_le_C12 (x := (33/25:ℝ)) (by norm_num)
  norm_num [HighOrderTaylor.S11,HighOrderTaylor.S13,HighOrderTaylor.C14,HighOrderTaylor.C12]
    at hs hsU hc hcU
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

lemma middle_terminal_trig :
    (1244851/1250000:ℝ)≤Real.sin (37/25) ∧ Real.sin (37/25)≤49794043/50000000 ∧
    (4533581/50000000:ℝ)≤Real.cos (37/25) ∧ Real.cos (37/25)≤9067163/100000000 := by
  have hs := HighOrderTaylor.S11_le_sin (x := (37/25:ℝ)) (by norm_num)
  have hsU := HighOrderTaylor.sin_le_S13 (x := (37/25:ℝ)) (by norm_num)
  have hc := HighOrderTaylor.C14_le_cos (x := (37/25:ℝ)) (by norm_num)
  have hcU := HighOrderTaylor.cos_le_C12 (x := (37/25:ℝ)) (by norm_num)
  norm_num [HighOrderTaylor.S11,HighOrderTaylor.S13,HighOrderTaylor.C14,HighOrderTaylor.C12]
    at hs hsU hc hcU
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

lemma middle_subset : middle⊆angles := fun φ hφ =>
  ⟨hφ.1,by linarith [hφ.2,pi_hand_enclosure.1]⟩
lemma late_subset : late⊆angles := fun φ hφ => ⟨by linarith [hφ.1],hφ.2⟩

lemma sine_monotone : MonotoneOn Real.sin angles := by
  intro x hx y hy hxy
  exact Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [hx.1,Real.pi_pos]) hy.2 hxy

lemma cosine_antitone : AntitoneOn Real.cos angles := by
  apply antiOn_of_hasDeriv_nonpos
  · exact fun x _ => Real.continuous_cos.continuousAt.continuousWithinAt
  · exact fun x _ => Real.hasDerivAt_cos x
  · intro x hx
    have hs := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hx.1])
      (by linarith [hx.2,Real.pi_pos])
    linarith

lemma trig {φ : ℝ} (hφ : φ∈angles) :
    (24/25:ℝ)<Real.sin φ ∧ Real.sin φ≤1 ∧ 0≤Real.cos φ ∧ Real.cos φ<1/4 := by
  have hleft : (33/25:ℝ)∈angles := ⟨le_rfl,by linarith [pi_hand_enclosure.1]⟩
  have hright : Real.pi/2∈angles := ⟨by linarith [pi_hand_enclosure.1],le_rfl⟩
  have hs := sine_monotone hleft hφ hφ.1
  have hc := cosine_antitone hleft hφ hφ.1
  have hc0 := cosine_antitone hφ hright hφ.2
  norm_num at hc0
  exact ⟨by linarith [initial_trig.1],Real.sin_le_one φ,hc0,by linarith [initial_trig.2.2.2]⟩

lemma w_positive {φ : ℝ} (hφ : φ∈angles) : 0<w φ := by
  have ht := trig hφ
  dsimp [w,PrimaryZero.v]
  linarith [ht.1,ht.2.2.2]

lemma U_antitone : AntitoneOn U angles :=
  antiOn_of_hasDeriv_nonpos
    (fun φ _ => (PrimaryZero.U_hasDerivAt φ).continuousAt.continuousWithinAt)
    (fun φ _ => PrimaryZero.U_hasDerivAt φ)
    (fun φ hφ => neg_nonpos.mpr (w_positive (Ioo_subset_Icc_self hφ)).le)

lemma U_bounds {φ : ℝ} (hφ : φ∈angles) : (3/2:ℝ)≤U φ ∧ U φ<(44/25:ℝ) := by
  have hl := U_antitone hφ
    (show Real.pi/2∈angles from ⟨by linarith [pi_hand_enclosure.1],le_rfl⟩) hφ.2
  have hu := U_antitone
    (show (33/25:ℝ)∈angles from ⟨le_rfl,by linarith [pi_hand_enclosure.1]⟩) hφ hφ.1
  have hinit : U (33/25)<(44/25:ℝ) := by
    dsimp [U,PrimaryZero.U,PrimaryZero.m]
    linarith [initial_trig.2.1,initial_trig.2.2.2]
  norm_num [U,PrimaryZero.U,PrimaryZero.m] at hl
  exact ⟨hl,hu.trans_lt hinit⟩

lemma height_domain {φ : ℝ} (hφ : φ∈angles) : U φ∈LHeightBounds.heights :=
  ⟨by linarith [(U_bounds hφ).1],by linarith [(U_bounds hφ).2]⟩

lemma middle_height {φ : ℝ} (hφ : φ∈middle) : U φ∈LHeightBounds.zero := by
  have hh := U_antitone (middle_subset hφ)
    (middle_subset (show (37/25:ℝ)∈middle by norm_num [middle])) hφ.2
  have hb : (159/100:ℝ)<U (37/25) := by
    dsimp [U,PrimaryZero.U,PrimaryZero.m]
    linarith [middle_terminal_trig.1,middle_terminal_trig.2.2.1]
  exact ⟨by linarith,(U_bounds (middle_subset hφ)).2.le⟩

lemma late_height {φ : ℝ} (hφ : φ∈late) : U φ∈Icc (3/2) (81/50) := by
  have hh := U_antitone
    (show (73/50:ℝ)∈angles from ⟨by norm_num,by linarith [pi_hand_enclosure.1]⟩)
    (late_subset hφ) hφ.1
  have hc := HighOrderTaylor.cos_le_C12 (x := (73/50:ℝ)) (by norm_num)
  norm_num [HighOrderTaylor.C12] at hc
  have hU : U (73/50)<(81/50:ℝ) := by
    dsimp [U,PrimaryZero.U,PrimaryZero.m]
    linarith [Real.sin_le_one (73/50:ℝ)]
  exact ⟨(U_bounds (late_subset hφ)).1,hh.trans hU.le⟩

lemma harmonic_circle (φ : ℝ) : (m φ)^2+(w φ)^2=(205/144:ℝ) := PrimaryZero.mv_circle φ

lemma K_hasDerivAt {φ : ℝ} (hφ : φ∈angles) : HasDerivAt K (KD φ) φ := by
  convert ((hasDerivAt_id φ).sub_const e).add
    ((LHeight.eval_hasDerivAt (LHeightBounds.domain (height_domain hφ))).comp φ
      (PrimaryZero.U_hasDerivAt φ)) using 1 <;> dsimp [K,KD,w] <;> ring

lemma KD_hasDerivAt {φ : ℝ} (hφ : φ∈angles) : HasDerivAt KD (KDD φ) φ := by
  convert ((((LHeight.d1_hasDerivAt (LHeightBounds.domain (height_domain hφ))).comp φ
    (PrimaryZero.U_hasDerivAt φ)).mul (PrimaryZero.v_hasDerivAt φ)).const_sub 1) using 1 <;>
    dsimp [KD,KDD,m,w] <;> ring

lemma KDD_hasDerivAt {φ : ℝ} (hφ : φ∈angles) : HasDerivAt KDD (KDDD φ) φ := by
  convert (((LHeight.d2_hasDerivAt (LHeightBounds.domain (height_domain hφ))).comp φ
    (PrimaryZero.U_hasDerivAt φ)).mul ((PrimaryZero.v_hasDerivAt φ).pow 2)).sub
      (((LHeight.d1_hasDerivAt (LHeightBounds.domain (height_domain hφ))).comp φ
        (PrimaryZero.U_hasDerivAt φ)).mul (PrimaryZero.m_hasDerivAt φ)) using 1 <;>
    dsimp [KDD,KDDD,m,w] <;> ring

lemma KDDD_negative {φ : ℝ} (hφ : φ∈middle) : KDDD φ<0 := by
  have hu := middle_height hφ
  have hm : m φ=U φ-1 := by dsimp [m,U,PrimaryZero.U]; ring
  have hm0 : 0≤m φ := by rw [hm]; linarith [hu.1]
  have hmU : m φ≤(19/25:ℝ) := by rw [hm]; linarith [hu.2]
  have hs := pow_le_pow_left₀ hm0 hmU 2
  have hc := harmonic_circle φ
  have hw : (1/2:ℝ)<(w φ)^2 := by nlinarith
  have hwm : 3*m φ<5*(w φ)^2 := by nlinarith
  have hd := LHeightBounds.third_dominates hu
  have hf := LHeightBounds.first_lower (LHeightBounds.zero_subset hu)
  have hfirst := mul_pos (show 0<LHeight.d1 (U φ) by linarith)
    (show 0<2*(w φ)^2-1 by linarith)
  have hp := mul_lt_mul_of_pos_right hd (show 0<(w φ)^2 by linarith)
  have hlast : -LHeight.d3 (U φ)*(w φ)^2+3*LHeight.d2 (U φ)*m φ+LHeight.d1 (U φ)<0 := by
    by_cases h2 : 0≤LHeight.d2 (U φ)
    · rw [max_eq_left h2] at hp
      have hsecond := mul_nonneg h2 (show 0≤5*(w φ)^2-3*m φ by linarith)
      nlinarith
    · rw [max_eq_right (not_le.mp h2).le] at hp
      have hsecond := mul_nonpos_of_nonpos_of_nonneg (not_le.mp h2).le hm0
      nlinarith
  exact mul_neg_of_pos_of_neg (w_positive (middle_subset hφ)) hlast

lemma KDD_antitone : AntitoneOn KDD middle :=
  antiOn_of_hasDeriv_nonpos
    (fun φ hφ => (KDD_hasDerivAt (middle_subset hφ)).continuousAt.continuousWithinAt)
    (fun φ hφ => KDD_hasDerivAt (middle_subset (Ioo_subset_Icc_self hφ)))
    (fun φ hφ => (KDDD_negative (Ioo_subset_Icc_self hφ)).le)

lemma KDD_negative_late {φ : ℝ} (hφ : φ∈late) : KDD φ<0 := by
  have hu := late_height hφ
  have hdd := LHeightBounds.second_upper_late hu
  have hd := LHeightBounds.first_lower (height_domain (late_subset hφ))
  have hm : (1/2:ℝ)≤m φ := by dsimp [m,U,PrimaryZero.U] at hu; linarith [hu.1]
  have hc := harmonic_circle φ
  have hs : (w φ)^2≤(205/144:ℝ) := by nlinarith [sq_nonneg (m φ)]
  have hp := mul_le_mul_of_nonneg_right hdd.le (sq_nonneg (w φ))
  have hq := mul_le_mul hd.le hm (by norm_num : (0:ℝ)≤1/2)
    (show 0≤LHeight.d1 (U φ) by linarith)
  dsimp [KDD]
  nlinarith

lemma V_positive {φ : ℝ} (hφ : φ∈angles) : 0<V φ :=
  root_pos (LHeightBounds.domain (height_domain hφ))

lemma physical {φ : ℝ} (hφ : φ∈angles) : OuterState (U φ-1/2) (b φ) := by
  have hu := U_bounds hφ
  have hp := V_positive hφ
  have hc : (V φ)^2=Q0-(U φ)^2 := root_sq (LHeightBounds.domain (height_domain hφ)).le
  have hsqL := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤3/2) hu.1 2
  have hsqU := pow_le_pow_left₀ (by linarith [hu.1] : 0≤U φ) hu.2.le 2
  have hb : 0≤b φ := by dsimp [b,PrimaryZero.b]; norm_num [Q0] at hc; nlinarith
  refine ⟨hb,?_,?_⟩
  · dsimp [b,PrimaryZero.b]
    norm_num [Q0] at hc
    nlinarith
  · dsimp [b,PrimaryZero.b]
    nlinarith only [hc]

lemma cost_eq {A B φ : ℝ} (ht : OuterState A B) (hU : A+1/2=U φ) :
    K φ=φ-e-L B := by
  have hh := LHeight_actual ht
  rw [hU] at hh
  dsimp [K]
  linarith

end SquaresInCircles.Eight.TableFree.SecondWord.LPrimaryZero

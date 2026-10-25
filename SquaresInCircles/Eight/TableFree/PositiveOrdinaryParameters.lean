module

public import SquaresInCircles.Eight.TableFree.OrdinaryNegativeSlope
public import SquaresInCircles.Eight.TableFree.ActualOrdinaryBlocks

/-!
# Concrete coefficient domains for the three nonnegative-T regimes

Uncompiled source draft. These are inequalities for the actual stress
coefficients. The split dependence is retained, and the low- and high-d
conditions are proved from the displayed coefficient polynomials.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.PositiveOrdinaryParameters
open PositiveStressCoefficients SecondaryEStress PositivePrimaryBaselines

structure Bounds (d l n b t : ℝ) : Prop where
  angle : d∈Icc 0 frameCap
  ell_lower : 1/2<l
  ell_upper : l<k
  H_lower : k≤n
  H_upper : n≤1
  B_lower : k≤b
  B_upper : b≤2069/2000
  D_lower : k≤t
  D_upper : t≤2069/2000
  correlated : ratio d*b≤l
  high : 3/10≤d → (2/3)*b≤l
  low : d≤3/10 → b≤1 ∧ t≤1 ∧ lP d≤l ∧ l≤1631/2500

theorem tilted_le_one {η x : ℝ} (hη : η∈Icc 0 (19/50))
    (hx : x∈Icc 0 frameCap) : tiltedWeight k η x≤1 := by
  have hnon : 0≤tiltedWeight k η x :=
    tiltedWeight_nonneg (by norm_num [k]) hη.1 hx
  have hη2 := pow_le_pow_left₀ hη.1 hη.2 2
  have he : (Real.cos x+η*Real.sin x)^2+(η*Real.cos x-Real.sin x)^2=1+η^2 := by
    linear_combination (1+η^2)*(Real.sin_sq_add_cos_sq x)
  have hsquare := sq_nonneg (η*Real.cos x-Real.sin x)
  have hbound := mul_le_mul_of_nonneg_left
    (show (Real.cos x+η*Real.sin x)^2≤1+η^2 by linarith) (sq_nonneg k)
  dsimp [tiltedWeight,k] at *
  nlinarith

theorem P_weight_range {d x : ℝ} (hd : d∈Icc 0 frameCap) (hx : x∈Icc 0 d) :
    k≤tiltedWeight k (etaP d) x ∧ tiltedWeight k (etaP d) x≤1 := by
  have hb := coefficient_bounds hd
  have hη : etaP d∈Icc 0 (19/50) := by
    exact ⟨by linarith [hb.2.2.2.2.2.2.1],by linarith [hb.2.2.2.2.2.2.2.1]⟩
  exact ⟨(tiltedWeight_bounds hd hx).1,tilted_le_one hη ⟨hx.1,hx.2.trans hd.2⟩⟩

theorem N_weight_range {d : ℝ} (hd : d∈Icc 0 frameCap) :
    k≤tiltedWeight k (19/50) d ∧ tiltedWeight k (19/50) d≤1 := by
  have hb := coefficient_bounds hd
  have hη : etaP d≤19/50 := by linarith [hb.2.2.2.2.2.2.2.1]
  have hsin := (transport_trig hd).2.2.1
  have hmul := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hη hsin) (show 0≤k by norm_num [k])
  have hbase := (P_weight_range hd ⟨hd.1,le_rfl⟩).1
  refine ⟨?_,tilted_le_one ⟨by norm_num,le_rfl⟩ hd⟩
  dsimp [tiltedWeight] at *
  nlinarith

theorem high_P {d : ℝ} (hd : d∈Icc 0 frameCap) (hlarge : 3/10≤d) :
    (2/3)*k*(1+d/4)≤lP d := by
  have h2 : d≤7/10 := hd.2
  have hd2 : d^2≤(7/10 : ℝ)*d := by nlinarith [hd.1]
  dsimp [lP,k]
  nlinarith

theorem high_N {d : ℝ} (hd : d∈Icc 0 frameCap) (hlarge : 3/10≤d) :
    (2/3)*cN d≤lN d := by
  have h2 : d≤7/10 := hd.2
  have hd2 : d^2≤(7/10 : ℝ)*d := by nlinarith [hd.1]
  dsimp [lN,cN]
  nlinarith

theorem low_P {d : ℝ} (hd : d∈Icc 0 frameCap) (hsmall : d≤3/10) :
    lP d≤1631/2500 := by dsimp [lP]; nlinarith [sq_nonneg d]

theorem low_N {d : ℝ} (hd : d∈Icc 0 frameCap) (hsmall : d≤3/10) :
    cN d≤1 ∧ lP d≤lN d ∧ lN d≤1631/2500 := by
  have hd2 : d^2≤(3/10 : ℝ)*d := by nlinarith [hd.1,hsmall]
  have hupper := mul_nonneg (show 0≤3/10-d by linarith)
    (show 0≤11/20-(1/5 : ℝ)*(d+3/10) by linarith)
  dsimp [cN,lP,lN]
  constructor
  · nlinarith [sq_nonneg d]
  constructor <;> nlinarith

theorem P_base_ratio {d : ℝ} (hd : d∈Icc 0 frameCap) : ratio d*k≤lP d := by
  have h := (correlated_ratios hd).1
  have hr : 0≤ratio d := by dsimp [ratio]; linarith [hd.1]
  have hnon := mul_nonneg (mul_nonneg hr (show 0≤k by norm_num [k])) hd.1
  nlinarith

theorem familyP_td {d x z : ℝ} (hd : d∈Icc 0 frameCap)
    (hx : x∈Icc 0 d) (hz : z∈Icc 0 d) :
    Bounds d (lP d) (tiltedWeight k (etaP d) x) (tiltedWeight k (etaP d) z) k := by
  have hb := coefficient_bounds hd
  have hn := P_weight_range hd hx
  have hm := P_weight_range hd hz
  refine ⟨hd,hb.1,hb.2.1,hn.1,hn.2,hm.1,by linarith [hm.2],
    le_rfl,by norm_num [k],(varying_B_ratio hd hz).1.le,?_,?_⟩
  · intro hlarge
    have hweight := mul_le_mul_of_nonneg_left (tiltedWeight_bounds hd hz).2
      (by norm_num : (0:ℝ)≤2/3)
    nlinarith [high_P hd hlarge]
  · intro hsmall
    exact ⟨hm.2,by norm_num [k],le_rfl,low_P hd hsmall⟩

theorem familyP_bt {d x z : ℝ} (hd : d∈Icc 0 frameCap)
    (hx : x∈Icc 0 d) (hz : z∈Icc 0 d) :
    Bounds d (lP d) (tiltedWeight k (etaP d) x) k (tiltedWeight k (etaP d) z) := by
  have hb := coefficient_bounds hd
  have hn := P_weight_range hd hx
  have hm := P_weight_range hd hz
  refine ⟨hd,hb.1,hb.2.1,hn.1,hn.2,le_rfl,by norm_num [k],
    hm.1,by linarith [hm.2],P_base_ratio hd,?_,?_⟩
  · intro hlarge
    have hnon := mul_nonneg (show 0≤(2/3 : ℝ)*k by norm_num [k]) hd.1
    nlinarith [high_P hd hlarge]
  · intro hsmall
    exact ⟨by norm_num [k],hm.2,le_rfl,low_P hd hsmall⟩

theorem familyN {d : ℝ} (hd : d∈Icc 0 frameCap) :
    Bounds d (lN d) (tiltedWeight k (19/50) d) (cN d) (cN d) := by
  have hb := coefficient_bounds hd
  have hn := N_weight_range hd
  refine ⟨hd,hb.2.2.1,hb.2.2.2.1,hn.1,hn.2,hb.2.2.2.2.1,
    hb.2.2.2.2.2.1,hb.2.2.2.2.1,hb.2.2.2.2.2.1,
    (varying_B_ratio hd ⟨le_rfl,hd.1⟩).2.le,high_N hd,?_⟩
  intro hsmall
  have h := low_N hd hsmall
  exact ⟨h.1,h.1,h.2.1,h.2.2⟩

end SquaresInCircles.Eight.TableFree.PositiveOrdinaryParameters

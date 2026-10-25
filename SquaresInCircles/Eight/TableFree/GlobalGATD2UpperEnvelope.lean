module

public import SquaresInCircles.Eight.TableFree.GlobalGATD2Coordinate

/-!
# The two-scalar envelope for the upper TD2 coefficient family

All four intrinsic blocks and both concentration alternatives are bounded
on the whole frame interval.  Negative-angle growth absorbs every separated
positive charge, while balanced same-block saturation is bounded by its
pure negative charge.  The B block is compared using its actual sorted
coefficients, including the crossing through one.

Uncompiled source draft; no angular sampling is used.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.PositiveTD
open Secondary PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryAngleConcentration
open OrdinaryNegativeEnvelope OrdinaryNegativeSlope OrdinaryPositiveEnvelope

theorem upper_coefficient_data {k m : ℝ}
    (hk : k∈Icc (2/3:ℝ) (17/20)) (hm : m∈Icc (2/3:ℝ) (6/5)) (i : Fin 4) :
    0<pWeights k 1 m i ∧ pWeights k 1 m i≤qWeights k 1 m i ∧
      (2/3)*qWeights k 1 m i≤pWeights k 1 m i ∧
      1≤qWeights k 1 m i ∧ qWeights k 1 m i≤6/5 := by
  have hk0 : 0<k := by linarith [hk.1]
  fin_cases i
  · change 0<k ∧ k≤1 ∧ (2/3)*1≤k ∧ 1≤1 ∧ (1:ℝ)≤6/5
    exact ⟨hk0,by linarith [hk.2],by linarith [hk.1],le_rfl,by norm_num⟩
  · change 0<k ∧ k≤1 ∧ (2/3)*1≤k ∧ 1≤1 ∧ (1:ℝ)≤6/5
    exact ⟨hk0,by linarith [hk.2],by linarith [hk.1],le_rfl,by norm_num⟩
  · change 0< min 1 m ∧ min 1 m≤ max 1 m ∧
      (2/3)*max 1 m≤ min 1 m ∧ 1≤ max 1 m ∧ max 1 m≤6/5
    rcases le_total m 1 with h | h
    · rw [min_eq_right h,max_eq_left h]
      exact ⟨by linarith [hm.1],h,by linarith [hm.1],le_rfl,by norm_num⟩
    · rw [min_eq_left h,max_eq_right h]
      exact ⟨by norm_num,h,by linarith [hm.2],h,hm.2⟩
  · change 0<k ∧ k≤1 ∧ (2/3)*1≤k ∧ 1≤1 ∧ (1:ℝ)≤6/5
    exact ⟨hk0,by linarith [hk.2],by linarith [hk.1],le_rfl,by norm_num⟩

/-- When m crosses one, homogeneity compares the actual sorted B block
with H; no monotonicity in the larger coefficient is assumed. -/
theorem upper_B_comparison {k m z : ℝ}
    (hk : k∈Icc (2/3:ℝ) (17/20)) (hm : m∈Icc 1 (6/5))
    (hkm : k*m≤1) (hz : z∈Icc 0 frameCap) :
    V R k 1 z≤V R 1 m z := by
  have hm0 : 0< m := by linarith [hm.1]
  have hrL : (1:ℝ)/2≤1/m := (le_div_iff₀ hm0).2 (by linarith [hm.2])
  have hrU : 1/m≤1 := (div_le_iff₀ hm0).2 (by simpa using hm.1)
  have hkr : k≤1/m := (le_div_iff₀ hm0).2 hkm
  have hmono := V_monotone_smaller (R:=R) (q:=1) (t:=z)
    (Real.sqrt_nonneg qCap) (by norm_num) hz
    (show k∈Icc ((1:ℝ)/2) 1 by constructor <;> linarith [hk.1,hk.2])
    ⟨hrL,hrU⟩ hkr
  have hv : 0≤V R (1/m) 1 z :=
    V_nonneg (div_pos (by norm_num) hm0) hrU (by linarith [hrL]) hz
  have hhom : V R 1 m z=m*V R (1/m) 1 z := by
    simpa [hm0.ne'] using V_homogeneous hm0.le R (1/m) 1 z
  calc
    V R k 1 z≤V R (1/m) 1 z := hmono
    _≤ m*V R (1/m) 1 z := by nlinarith [mul_nonneg (sub_nonneg.mpr hm.1) hv]
    _=V R 1 m z := hhom.symm

theorem upper_pure_lower {k c z : ℝ}
    (hk : k∈Icc (2/3:ℝ) (17/20))
    (hm : tilted c z∈Icc (2/3:ℝ) (6/5))
    (hkm : k*tilted c z≤1) (hz : z∈Icc 0 frameCap) (j : Fin 4) :
    min (V R k 1 z) (V R (tilted c z) 1 z)≤
      V R (pWeights k 1 (tilted c z) j) (qWeights k 1 (tilted c z) j) z := by
  fin_cases j
  · exact min_le_left _ _
  · exact min_le_left _ _
  · change min (V R k 1 z) (V R (tilted c z) 1 z)≤
      V R (min 1 (tilted c z)) (max 1 (tilted c z)) z
    rcases le_total (tilted c z) 1 with h | h
    · rw [min_eq_right h,max_eq_left h]
      exact min_le_right _ _
    · rw [min_eq_left h,max_eq_right h]
      exact (min_le_left _ _).trans (upper_B_comparison hk ⟨h,hm.2⟩ hkm hz)
  · exact min_le_left _ _

theorem upper_positive_lower {k c z : ℝ}
    (hk : k∈Icc (2/3:ℝ) (17/20))
    (hm : tilted c z∈Icc (2/3:ℝ) (6/5)) (hz : z∈Icc 0 frameCap) (i : Fin 4) :
    -(327/500)*(frameCap-z)≤
      Hybrid.positive R (GlobalGA.Secondary.diagonal-1/2) (pWeights k 1 (tilted c z))
        (qWeights k 1 (tilted c z)) 3 i (frameCap-z) := by
  have ht : frameCap-z∈Icc 0 frameCap := ⟨by linarith [hz.2],by linarith [hz.1]⟩
  by_cases hi : i=3
  · subst i
    simp only [Hybrid.positive,↓reduceIte]
    have hcoef : GlobalGA.Secondary.diagonal-1/2≤327/500 := by linarith [diagonal_bounds.2]
    have hh := mul_le_mul_of_nonneg_right hcoef ht.1
    generalize frameCap-z=w at hh ⊢
    linarith
  · simp only [Hybrid.positive,hi,↓reduceIte]
    have hd := upper_coefficient_data hk hm i
    have hU : -(109/200)*qWeights k 1 (tilted c z) i*(frameCap-z)≤
        U R (pWeights k 1 (tilted c z) i) (qWeights k 1 (tilted c z) i) (frameCap-z) :=
      U_lower (Real.sqrt_nonneg qCap) radius_sq.le
        hd.1 hd.2.1 (by linarith [hd.2.2.1]) ht
    have hcoef := mul_le_mul_of_nonneg_right hd.2.2.2.2 ht.1
    generalize U R (pWeights k 1 (tilted c z) i) (qWeights k 1 (tilted c z) i) (frameCap-z)=u at hU ⊢
    generalize frameCap-z=w at hU hcoef ht ⊢
    linarith

theorem upper_negative_growth {k c z : ℝ}
    (hk : k∈Icc (2/3:ℝ) (17/20))
    (hm : tilted c z∈Icc (2/3:ℝ) (6/5)) (hz : z∈Icc 0 frameCap) (j : Fin 4) :
    (2/3)*(frameCap-z)≤
      V R (pWeights k 1 (tilted c z) j) (qWeights k 1 (tilted c z) j) frameCap-
        V R (pWeights k 1 (tilted c z) j) (qWeights k 1 (tilted c z) j) z := by
  have hd := upper_coefficient_data hk hm j
  have h : (2/3)*qWeights k 1 (tilted c z) j*(frameCap-z)≤
      V R (pWeights k 1 (tilted c z) j) (qWeights k 1 (tilted c z) j) frameCap-
        V R (pWeights k 1 (tilted c z) j) (qWeights k 1 (tilted c z) j) z :=
    V_growth hd.1 hd.2.1 hd.2.2.1 hz
      (show frameCap∈Icc 0 frameCap by exact ⟨by norm_num [frameCap],le_rfl⟩) hz.2
  have hq := mul_le_mul_of_nonneg_right hd.2.2.2.1 (sub_nonneg.mpr hz.2)
  generalize V R (pWeights k 1 (tilted c z) j) (qWeights k 1 (tilted c z) j) frameCap-
    V R (pWeights k 1 (tilted c z) j) (qWeights k 1 (tilted c z) j) z=v at h ⊢
  generalize frameCap-z=w at h hq ⊢
  linarith

theorem upper_saturated_lower {k c z : ℝ}
    (hk : k∈Icc (2/3:ℝ) (17/20))
    (hm : tilted c z∈Icc (2/3:ℝ) (6/5))
    (hkm : k*tilted c z≤1) (hz : z∈Icc 0 frameCap) (i : Fin 4) :
    min (V R k 1 z) (V R (tilted c z) 1 z)≤
      Hybrid.saturated R (GlobalGA.Secondary.diagonal-1/2) (pWeights k 1 (tilted c z))
        (qWeights k 1 (tilted c z)) 3 i z := by
  have hpure := upper_pure_lower hk hm hkm hz i
  by_cases hi : i=3
  · subst i
    change min (V R k 1 z) (V R (tilted c z) 1 z)≤
      -(GlobalGA.Secondary.diagonal-1/2)*(frameCap-z)+V R k 1 frameCap
    have hg := upper_negative_growth hk hm hz (3:Fin 4)
    change (2/3)*(frameCap-z)≤V R k 1 frameCap-V R k 1 z at hg
    have hcoef : GlobalGA.Secondary.diagonal-1/2≤2/3 := by linarith [diagonal_bounds.2]
    have hprod := mul_le_mul_of_nonneg_right hcoef (sub_nonneg.mpr hz.2)
    change min (V R k 1 z) (V R (tilted c z) 1 z)≤V R k 1 z at hpure
    linarith
  · simp only [Hybrid.saturated,if_neg hi]
    have hd := upper_coefficient_data hk hm i
    exact hpure.trans (M_ge_V hd.1.le (hd.1.trans_le hd.2.1).le
      (by linarith [hd.2.2.1]) hz)

/-- Every concentration alternative lies above the two single-negative
expressions for the full upper coefficient domain. -/
theorem upper_endpoint_lower {k c z : ℝ}
    (hk : k∈Icc (2/3:ℝ) (17/20))
    (hm : tilted c z∈Icc (2/3:ℝ) (6/5))
    (hkm : k*tilted c z≤1) (hz : z∈Icc 0 frameCap) (i j : Fin 4) :
    min (V R k 1 z) (V R (tilted c z) 1 z)≤endpoint k 1 c z i j := by
  unfold endpoint
  apply le_min
  · exact upper_pure_lower hk hm hkm hz j
  · by_cases hij : i=j
    · subst j
      simp only [↓reduceIte]
      exact upper_saturated_lower hk hm hkm hz i
    · simp only [hij,↓reduceIte]
      have hp := upper_positive_lower hk hm hz i
      have hn := upper_negative_growth hk hm hz j
      have hb := upper_pure_lower hk hm hkm hz j
      have ht := sub_nonneg.mpr hz.2
      generalize frameCap-z=w at hp hn ht ⊢
      linarith

theorem upper_scalars_positive {k c z : ℝ}
    (hk : k∈Icc (2/3:ℝ) (17/20))
    (hm : tilted c z∈Icc (2/3:ℝ) (6/5))
    (hkm : k*tilted c z≤1) (hz : z∈Icc 0 frameCap)
    (hH : 0<baseline k 1 c z+V R k 1 z)
    (hB : 0<baseline k 1 c z+V R (tilted c z) 1 z)
    (i j : Fin 4) : 0<baseline k 1 c z+endpoint k 1 c z i j := by
  have hmin : 0<baseline k 1 c z+min (V R k 1 z) (V R (tilted c z) 1 z) := by
    rw [add_min]
    exact lt_min hH hB
  linarith [upper_endpoint_lower hk hm hkm hz i j]

end SquaresInCircles.Eight.TableFree.GlobalGA.PositiveTD

module

public import SquaresInCircles.Eight.ExactFamily.EnvelopePosition

/-!
# Every critical envelope position lies below one

Uncompiled draft.  On the entire remaining interval `[1,11/10]`, direct
circle comparisons give `p*r<w-1`.  All three coefficients of the
position/tilt tangent determinant are then negative.  This excludes a
simultaneous critical point without any condition on the sign of `F`.
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.ExactFamily.FiveCornerGeometry

open Set

theorem right_window_bounds {q u : ℝ} (hql : (79/40:ℝ)^2 ≤ q) (hqu : q ≤ 9789/2500)
    (hul : 1 ≤ u) (huu : u ≤ 11/10) :
    1<lowerRight q u ∧ lowerRight q u<171/100 ∧ 19/10<lowerLeft q u ∧
    0<lowerHeight q u ∧ 0<slopeRatio q u ∧ slopeRatio q u<21/40 ∧
    slopeRatio q u*lowerRight q u<lowerLeft q u-1 := by
  have hw : u∈positionWindow := ⟨by linarith,huu⟩
  have hb := window_bounds hql hqu hw
  have hur := square_mono_nonneg (by norm_num : (0:ℝ) ≤ 1) hul
  have hru : lowerRight q u<171/100 := by
    have hh : (41/25:ℝ)<Real.sqrt (q-u^2) ∧ Real.sqrt (q-u^2)<171/100 := by
      apply sqrt_between (by norm_num) (by norm_num)
      · have hs := square_mono_nonneg (by linarith : 0 ≤ u) huu
        nlinarith
      · nlinarith
    exact hh.2
  have hA : 9/10 ≤ 2-u ∧ 2-u ≤ 1 := by constructor <;> linarith
  have hU : 17/10<topRight q u := by
    have hs := square_mono_nonneg (by linarith : 0 ≤ 2-u) hA.2
    have hh : (17/10:ℝ)<Real.sqrt (q-(2-u)^2) ∧ Real.sqrt (q-(2-u)^2)<2 := by
      apply sqrt_between (by norm_num) (by norm_num)
      · nlinarith
      · nlinarith [sq_nonneg (2-u)]
    exact hh.1
  have hV : topLeft q u<13/10 := by dsimp [topLeft]; linarith
  have hY : 147/100<topHeight q u := by
    have hs := square_mono_nonneg (by linarith [hb.V_lower] : 0 ≤ topLeft q u) hV.le
    have hh : (147/100:ℝ)<Real.sqrt (q-topLeft q u^2) ∧ Real.sqrt (q-topLeft q u^2)<2 := by
      apply sqrt_between (by norm_num) (by norm_num)
      · nlinarith
      · nlinarith [sq_nonneg (topLeft q u)]
    exact hh.1
  have hv : lowerHeight q u<53/100 := by dsimp [lowerHeight]; linarith
  have hwl : 19/10<lowerLeft q u := by
    have hs := square_mono_nonneg hb.v_pos.le hv.le
    have hh : (19/10:ℝ)<Real.sqrt (q-lowerHeight q u^2) ∧ Real.sqrt (q-lowerHeight q u^2)<2 := by
      apply sqrt_between (by norm_num) (by norm_num)
      · nlinarith
      · nlinarith [sq_nonneg (lowerHeight q u)]
    exact hh.1
  have hUp : 0<topRight q u := by linarith
  have hYp : 0<topHeight q u := by linarith
  have hp : 0<slopeRatio q u := by
    dsimp [slopeRatio]
    exact div_pos (mul_pos (by linarith) (by linarith [hb.V_lower])) (mul_pos hUp hYp)
  have hpu : slopeRatio q u<21/40 := by
    have hprod := mul_le_mul hU.le hY.le (by norm_num : (0:ℝ) ≤ 147/100) hUp.le
    have hnum := mul_le_mul hA.2 hV.le (by linarith [hb.V_lower]) (by norm_num : (0:ℝ) ≤ 1)
    dsimp [slopeRatio]
    rw [div_lt_iff₀ (mul_pos hUp hYp)]
    nlinarith
  have hpr : slopeRatio q u*lowerRight q u<lowerLeft q u-1 := by
    have hm := mul_le_mul hpu.le hru.le (by linarith [hb.r_lower]) (by norm_num : (0:ℝ) ≤ 21/40)
    nlinarith
  exact ⟨by linarith [hb.r_lower],hru,hwl,hb.v_pos,hp,hpu,hpr⟩

theorem tangent_cross_identity (r w u v p c s : ℝ) (hr : r≠0) (hw : w≠0) :
    (p*(c+s*v/w))*(s*(r-1)+c*u)-(s+c*u/r)*(c*(w-1)+s*v)=
      c^2*(u/r)*(p*r-w+1)+
      c*s*(p*(r-1)-(w-1)+u*v*(p/w-1/r))+
      s^2*(v/w)*(p*(r-1)-w) := by
  field_simp [hr,hw]
  ring

theorem right_window_cross_negative {q c s u : ℝ}
    (hql : (79/40:ℝ)^2 ≤ q) (hqu : q ≤ 9789/2500)
    (hul : 1 ≤ u) (huu : u ≤ 11/10) (hc : 0<c) (hs : 0 ≤ s) :
    positionb q c s u*firstTilt q c s u+positionA q c s u*secondTilt q c s u<0 := by
  obtain ⟨hr,hru,hw,hv,hp,hpu,hpr⟩ := right_window_bounds hql hqu hul huu
  have hrp : 0<lowerRight q u := by linarith
  have hwp : 0<lowerLeft q u := by linarith
  have hu : 0<u := by linarith
  have hrw : lowerRight q u<lowerLeft q u := by linarith
  have hp₁ : slopeRatio q u<1 := by linarith
  have hP : slopeRatio q u*(lowerRight q u-1)<lowerLeft q u-1 := by
    have hm := mul_lt_mul_of_pos_right hp₁ (by linarith : 0<lowerRight q u-1)
    nlinarith
  have hratio : slopeRatio q u/lowerLeft q u<1/lowerRight q u := by
    apply (div_lt_div_iff₀ hwp hrp).2
    nlinarith
  have hC₀ : (u/lowerRight q u)*(slopeRatio q u*lowerRight q u-lowerLeft q u+1)<0 :=
    mul_neg_of_pos_of_neg (div_pos hu hrp) (by linarith)
  have hC₁ : slopeRatio q u*(lowerRight q u-1)-(lowerLeft q u-1)+
      u*lowerHeight q u*(slopeRatio q u/lowerLeft q u-1/lowerRight q u)<0 := by
    have hm := mul_neg_of_pos_of_neg (mul_pos hu hv) (sub_neg.mpr hratio)
    linarith
  have hC₂ : (lowerHeight q u/lowerLeft q u)*(slopeRatio q u*(lowerRight q u-1)-lowerLeft q u)<0 :=
    mul_neg_of_pos_of_neg (div_pos hv hwp) (by linarith)
  have h₀ := mul_neg_of_pos_of_neg (sq_pos_of_pos hc) hC₀
  have h₁ := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hc.le hs) hC₁.le
  have h₂ := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg s) hC₂.le
  have he := tangent_cross_identity (lowerRight q u) (lowerLeft q u) u (lowerHeight q u)
    (slopeRatio q u) c s (ne_of_gt hrp) (ne_of_gt hwp)
  dsimp [positionb,positionB,positionA,firstTilt,secondTilt]
  nlinarith

theorem window_critical_below_one {q c s u : ℝ}
    (hql : (79/40:ℝ)^2 ≤ q) (hqu : q ≤ 9789/2500)
    (hc : 0<c) (hs : 0 ≤ s) (hunit : c^2+s^2=1) (ht : s/c ≤ 1/5)
    (hu : u∈positionWindow) (hp : positionHalf q c s u=0) (htilt : tiltFirst q c s u=0) :
    u<1 := by
  by_contra! hge
  have hcross := right_window_cross_negative hql hqu hge hu.2 hc hs
  have hb := window_bounds hql hqu hu
  obtain ⟨_,hcu,hsu,_,_⟩ := small_tilt_bounds hc hs hunit ht
  have hk := (components_pos (by linarith : q<4) hb.domain hc hcu hs hsu).1
  have hzero : firstComponent q c s u*
      (positionb q c s u*firstTilt q c s u+positionA q c s u*secondTilt q c s u)=0 := by
    dsimp [positionHalf] at hp
    dsimp [tiltFirst] at htilt
    dsimp [positionA,positionb,positionB]
    linear_combination (slopeRatio q u*(c+s*lowerHeight q u/lowerLeft q u)/2)*htilt+
      secondTilt q c s u*hp
  have hn := mul_neg_of_pos_of_neg hk hcross
  linarith

theorem windowMinimizer_isStripCritical {q c s : ℝ}
    (hql : (79/40:ℝ)^2 ≤ q) (hqu : q ≤ 9789/2500)
    (hc : 0<c) (hs : 0 ≤ s) (hunit : c^2+s^2=1) (ht : s/c ≤ 1/5)
    (hcritical : tiltFirst q c s (windowMinimizer q c s)=0) :
    StripCritical q c s (windowMinimizer q c s) := by
  obtain ⟨hu,hp,_,_⟩ := windowMinimizer_geometric hql hqu hc hs hunit ht
  have hupper := window_critical_below_one hql hqu hc hs hunit ht
    (windowMinimizer_mem q c s) hp hcritical
  exact ⟨⟨hql,hqu,hu.1.le,hupper.le⟩,hc,hs,hunit,ht,hp,hcritical⟩

end SquaresInCircles.Eight.ExactFamily.FiveCornerGeometry

module

public import SquaresInCircles.Eight.ExactFamily.PositionLocalization

/-!
# A global norm bound at every position minimum

Uncompiled draft.  A single trial chain, one cubic chord inequality, and
fixed-tilt convexity prove `k₁²+k₂²<4` at every stationary position in the
small-tilt strip.  The defect is allowed to be positive.  This supplies the
norm estimate required by the envelope critical-Hessian argument without
assuming that an envelope critical point is a stationary zero.
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.ExactFamily.FiveCornerGeometry

def normTrial : ℝ := 15/16

theorem normTrial_bounds {q : ℝ} (hql : (79/40:ℝ)^2 ≤ q) (hqu : q<4) :
    Domain q normTrial ∧ 1738/1000<lowerRight q normTrial ∧
      lowerHeight q normTrial<546/1000 ∧ 1898/1000<lowerLeft q normTrial := by
  have hr : 1738/1000<lowerRight q normTrial ∧ lowerRight q normTrial<2 := by
    apply sqrt_between (by norm_num) (by norm_num) <;>
      dsimp [lowerRight,upper,normTrial] <;> nlinarith
  have hU : 1664/1000<topRight q normTrial ∧ topRight q normTrial<2 := by
    apply sqrt_between (by norm_num) (by norm_num) <;>
      dsimp [topRight,upper,normTrial] <;> nlinarith
  have hV : 0<topLeft q normTrial ∧ topLeft q normTrial<1336/1000 := by
    dsimp [topLeft]
    constructor <;> linarith [hU.1,hU.2]
  have hY : 1454/1000<topHeight q normTrial ∧ topHeight q normTrial<2 := by
    apply sqrt_between (by norm_num) (by norm_num)
    · have hs := square_mono_nonneg hV.1.le hV.2.le
      dsimp [topHeight,upper]
      nlinarith
    · dsimp [topHeight,upper]
      nlinarith [sq_nonneg (topLeft q normTrial)]
  have hv : 0<lowerHeight q normTrial ∧ lowerHeight q normTrial<546/1000 := by
    dsimp [lowerHeight]
    constructor <;> linarith [hY.1,hY.2]
  have hw : 1898/1000<lowerLeft q normTrial ∧ lowerLeft q normTrial<2 := by
    apply sqrt_between (by norm_num) (by norm_num)
    · have hs := square_mono_nonneg hv.1.le hv.2.le
      dsimp [lowerLeft,upper]
      nlinarith
    · dsimp [lowerLeft,upper]
      nlinarith [sq_nonneg (lowerHeight q normTrial)]
  have hdom : Domain q normTrial := by
    refine ⟨by norm_num [normTrial],?_,?_,?_,?_⟩
    · have hh : 0<q-normTrial^2 := Real.sqrt_pos.mp (show 0<lowerRight q normTrial by linarith [hr.1])
      linarith
    · have hh : 0<q-(2-normTrial)^2 := Real.sqrt_pos.mp (show 0<topRight q normTrial by linarith [hU.1])
      linarith
    · have hh : 0<q-topLeft q normTrial^2 := Real.sqrt_pos.mp (show 0<topHeight q normTrial by linarith [hY.1])
      linarith
    · have hh : 0<q-lowerHeight q normTrial^2 := Real.sqrt_pos.mp (show 0<lowerLeft q normTrial by linarith [hw.1])
      linarith
  exact ⟨hdom,hr.1,hv.2,hw.1⟩

theorem cosine_from_tangent_lower {c h : ℝ} (hc : 0<c)
    (hunit : c^2*(1+h^2)=1) : 1-h^2/2 ≤ c := by
  have hc2 : c^2 ≤ 1 := by
    nlinarith [mul_nonneg (sq_nonneg c) (sq_nonneg h)]
  have hcu : c ≤ 1 := by nlinarith [sq_nonneg (c-1)]
  have hfactor : 0 ≤ 1+c-2*c^2 := by
    have hh := mul_nonneg (by linarith : 0 ≤ 1-c) (by linarith : 0 ≤ 2*c+1)
    nlinarith
  have hprod := mul_nonneg (sq_nonneg h) hfactor
  have he : (1+c)*(h^2-2+2*c)=h^2*(1+c-2*c^2)+2*(c^2*(1+h^2)-1) := by ring
  have hnon : 0 ≤ (1+c)*(h^2-2+2*c) := by rw [he,hunit]; nlinarith
  have hd : 0 ≤ h^2-2+2*c := by
    by_contra! hh
    exact (not_lt_of_ge hnon) (mul_neg_of_pos_of_neg (by linarith) hh)
  linarith

def trialPolynomial (h : ℝ) : ℝ :=
  5+2*(1-h^2/2)*(-(93/100)+h*(977/1000))+
    (369/500-h*(15/16))^2+(273/500-h*(449/500))^2

/-- The cubic is below its endpoint chord on the complete tilt interval.
The remaining factor is positive without subdivision. -/
theorem trialPolynomial_chord {h : ℝ} (hh : 0 ≤ h) (hhu : h ≤ 1/5) :
    trialPolynomial h ≤ (1-5*h)*trialPolynomial 0+5*h*trialPolynomial (1/5) := by
  let C : ℝ := 93/100+(15/16)^2+(449/500)^2
  have he : (1-5*h)*trialPolynomial 0+5*h*trialPolynomial (1/5)-trialPolynomial h =
      h*(1/5-h)*(C-(977/1000)*(h+1/5)) := by
    dsimp [trialPolynomial,C]
    ring
  have hC : 0 ≤ C-(977/1000)*(h+1/5) := by
    dsimp [C]
    nlinarith
  have hn := mul_nonneg (mul_nonneg hh (by linarith : 0 ≤ 1/5-h)) hC
  linarith

theorem trialPolynomial_lt_four {h : ℝ} (hh : 0 ≤ h) (hhu : h ≤ 1/5) :
    trialPolynomial h<4 := by
  have hc := trialPolynomial_chord hh hhu
  have he : trialPolynomial 0 ≤ trialPolynomial (1/5) := by norm_num [trialPolynomial]
  have hlast : trialPolynomial (1/5)<4 := by norm_num [trialPolynomial]
  have hp := mul_nonneg (by linarith : 0 ≤ 1-5*h) (sub_nonneg.mpr he)
  nlinarith

theorem trial_upper_norm {c h : ℝ} (hc : 0<c) (hh : 0 ≤ h) (hhu : h ≤ 1/5)
    (hunit : c^2*(1+h^2)=1) :
    (2+c*(-(369/500)+h*(15/16)))^2+
      (1+c*(273/500-h*(449/500)))^2<4 := by
  let L : ℝ := -(93/100)+h*(977/1000)
  let Q : ℝ := (369/500-h*(15/16))^2+(273/500-h*(449/500))^2
  have hL : L<0 := by dsimp [L]; linarith
  have hQ : 0 ≤ Q := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hc2 : c^2 ≤ 1 := by
    nlinarith [mul_nonneg (sq_nonneg c) (sq_nonneg h)]
  have hcl := cosine_from_tangent_lower hc hunit
  have hLc : c*L ≤ (1-h^2/2)*L := mul_le_mul_of_nonpos_right hcl hL.le
  have hQc := mul_le_mul_of_nonneg_right hc2 hQ
  have hnorm : (2+c*(-(369/500)+h*(15/16)))^2+
      (1+c*(273/500-h*(449/500)))^2=5+2*c*L+c^2*Q := by
    dsimp [L,Q]
    ring
  have hbound : 5+2*c*L+c^2*Q ≤ trialPolynomial h := by
    dsimp [trialPolynomial]
    change 5+2*c*L+c^2*Q ≤ 5+2*(1-h^2/2)*L+Q
    nlinarith
  rw [hnorm]
  exact hbound.trans_lt (trialPolynomial_lt_four hh hhu)

theorem normTrial_norm_lt_four {q c s : ℝ}
    (hql : (79/40:ℝ)^2 ≤ q) (hqu : q<4)
    (hc : 0<c) (hs : 0 ≤ s) (ht : s/c ≤ 1/5) (hunit : c^2+s^2=1) :
    firstComponent q c s normTrial^2+secondComponent q c s normTrial^2<4 := by
  obtain ⟨hdom,hr,hv,hw⟩ := normTrial_bounds hql hqu
  have hcu : c ≤ 1 := by nlinarith [sq_nonneg s,sq_nonneg (c-1)]
  have hsu : s ≤ 1 := by nlinarith [sq_nonneg c,sq_nonneg (s-1)]
  obtain ⟨hk₁,hk₂⟩ := components_pos hqu hdom hc hcu hs hsu
  have hcs : c*(s/c)=s := by field_simp [ne_of_gt hc]
  have hh : 0 ≤ s/c := div_nonneg hs hc.le
  have hquarter : c^2*(1+(s/c)^2)=1 := by
    field_simp [ne_of_gt hc]
    nlinarith
  have h₁ : firstComponent q c s normTrial ≤ 2+c*(-(369/500)+(s/c)*(15/16)) := by
    have hm := mul_le_mul_of_nonneg_left hr.le hc.le
    dsimp [firstComponent,normTrial]
    nlinarith
  have h₂ : secondComponent q c s normTrial ≤ 1+c*(273/500-(s/c)*(449/500)) := by
    have hm₁ := mul_le_mul_of_nonneg_left hv.le hc.le
    have hm₂ := mul_le_mul_of_nonneg_left hw.le hs
    dsimp [secondComponent]
    nlinarith
  have hs₁ := square_mono_nonneg hk₁.le h₁
  have hs₂ := square_mono_nonneg hk₂.le h₂
  have htrial := trial_upper_norm hc hh ht hquarter
  linarith

/-- This conclusion does not assume a zero or negative defect.  It applies
at every position minimum, and hence at every envelope critical point. -/
theorem position_minimum_norm_lt_four {q c s u : ℝ}
    (hql : (79/40:ℝ)^2 ≤ q) (hqu : q<4)
    (hc : 0<c) (hs : 0 ≤ s) (ht : s/c ≤ 1/5) (hunit : c^2+s^2=1)
    (hmin : ∀ v, Domain q v → defect q c s u ≤ defect q c s v) :
    firstComponent q c s u^2+secondComponent q c s u^2<4 := by
  have hb := normTrial_norm_lt_four hql hqu hc hs ht hunit
  have hm := hmin normTrial (normTrial_bounds hql hqu).1
  dsimp [defect] at hm
  linarith

theorem position_stationary_norm_lt_four {q c s u : ℝ}
    (hql : (79/40:ℝ)^2 ≤ q) (hqu : q<4)
    (hc : 0<c) (hs : 0 ≤ s) (ht : s/c ≤ 1/5) (hunit : c^2+s^2=1)
    (hu : Domain q u) (hstat : HasDerivAt (defect q c s) 0 u) :
    firstComponent q c s u^2+secondComponent q c s u^2<4 := by
  have hcu : c ≤ 1 := by nlinarith [sq_nonneg s,sq_nonneg (c-1)]
  have hsu : s ≤ 1 := by nlinarith [sq_nonneg c,sq_nonneg (s-1)]
  exact position_minimum_norm_lt_four hql hqu hc hs ht hunit
    (stationary_global_minimum hqu hc hcu hs hsu hu hstat)

end SquaresInCircles.Eight.ExactFamily.FiveCornerGeometry

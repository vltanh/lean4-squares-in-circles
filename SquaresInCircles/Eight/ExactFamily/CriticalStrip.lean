module

public import SquaresInCircles.Eight.ExactFamily.EnvelopeNorm
public import SquaresInCircles.Eight.ExactFamily.TiltCurvature

/-!
# Circle support bounds on the complete critical-position strip

Uncompiled draft.  Every bound below is derived from the actual radicals
on one closed strip.  Rational lines supporting the top circle replace
both numerical subdivision and integration of a precomputed derivative
bound.  In particular `slope_affine_lower` and `left_support_lower` are
the two quantitative geometric inputs to the critical-Hessian argument.
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.ExactFamily.FiveCornerGeometry

structure CriticalStrip (q u : ℝ) : Prop where
  q_lower : (79/40:ℝ)^2 ≤ q
  q_upper : q ≤ 9789/2500
  u_lower : 87/100 ≤ u
  u_upper : u ≤ 1

structure StripBounds (q u : ℝ) : Prop where
  domain : Domain q u
  r_lower : 17/10<lowerRight q u
  r_upper : lowerRight q u<16/9
  U_lower : 1619/1000<topRight q u
  U_upper : topRight q u<1708/1000
  V_lower : 1292/1000<topLeft q u
  V_upper : topLeft q u<1381/1000
  Y_lower : 1411/1000<topHeight q u
  Y_upper : topHeight q u<3/2
  v_lower : 1/2<lowerHeight q u
  v_upper : lowerHeight q u<589/1000
  w_lower : 1885/1000<lowerLeft q u
  w_upper : lowerLeft q u<48/25
  p_lower : 1/2<slopeRatio q u
  p_upper : slopeRatio q u<684/1000

theorem CriticalStrip.bounds {q u : ℝ} (h : CriticalStrip q u) : StripBounds q u := by
  have hu : 0 ≤ u := by linarith [h.u_lower]
  have hA : 1 ≤ 2-u ∧ 2-u ≤ 113/100 := by constructor <;> linarith [h.u_lower,h.u_upper]
  have hr : 17/10<lowerRight q u ∧ lowerRight q u<16/9 := by
    apply sqrt_between (by norm_num) (by norm_num)
    · have hs := square_mono_nonneg hu h.u_upper
      dsimp [lowerRight,upper]
      nlinarith [h.q_lower]
    · have hs := square_mono_nonneg (by norm_num : (0:ℝ) ≤ 87/100) h.u_lower
      dsimp [lowerRight,upper]
      nlinarith [h.q_upper]
  have hU : 1619/1000<topRight q u ∧ topRight q u<1708/1000 := by
    apply sqrt_between (by norm_num) (by norm_num)
    · have hs := square_mono_nonneg (by linarith : 0 ≤ 2-u) hA.2
      dsimp [topRight,upper]
      nlinarith [h.q_lower]
    · have hs := square_mono_nonneg (by norm_num : (0:ℝ) ≤ 1) hA.1
      dsimp [topRight,upper]
      nlinarith [h.q_upper]
  have hV : 1292/1000<topLeft q u ∧ topLeft q u<1381/1000 := by
    dsimp [topLeft]
    constructor <;> linarith [hU.1,hU.2]
  have hY : 1411/1000<topHeight q u ∧ topHeight q u<3/2 := by
    apply sqrt_between (by norm_num) (by norm_num)
    · have hs := square_mono_nonneg (by linarith : 0 ≤ topLeft q u) hV.2.le
      dsimp [topHeight,upper]
      nlinarith [h.q_lower]
    · have hs := square_mono_nonneg (by norm_num : (0:ℝ) ≤ 1292/1000) hV.1.le
      dsimp [topHeight,upper]
      nlinarith [h.q_upper]
  have hv : 1/2<lowerHeight q u ∧ lowerHeight q u<589/1000 := by
    dsimp [lowerHeight]
    constructor <;> linarith [hY.1,hY.2]
  have hw : 1885/1000<lowerLeft q u ∧ lowerLeft q u<48/25 := by
    apply sqrt_between (by norm_num) (by norm_num)
    · have hs := square_mono_nonneg (by linarith : 0 ≤ lowerHeight q u) hv.2.le
      dsimp [lowerLeft,upper]
      nlinarith [h.q_lower]
    · have hs := square_mono_nonneg (by norm_num : (0:ℝ) ≤ 1/2) hv.1.le
      dsimp [lowerLeft,upper]
      nlinarith [h.q_upper]
  have hUp : 0<topRight q u := by linarith [hU.1]
  have hYp : 0<topHeight q u := by linarith [hY.1]
  have hprodL : (1619/1000:ℝ)*(1411/1000) ≤ topRight q u*topHeight q u :=
    mul_le_mul hU.1.le hY.1.le (by norm_num) hUp.le
  have hprodU : topRight q u*topHeight q u ≤ (1708/1000:ℝ)*(3/2) :=
    mul_le_mul hU.2.le hY.2.le hYp.le (by norm_num)
  have hnumL : (1292/1000:ℝ) ≤ (2-u)*topLeft q u := by
    have hh := mul_le_mul hA.1 hV.1.le (by norm_num : (0:ℝ) ≤ 1292/1000)
      (by linarith : 0 ≤ 2-u)
    nlinarith
  have hnumU : (2-u)*topLeft q u ≤ (113/100:ℝ)*(1381/1000) :=
    mul_le_mul hA.2 hV.2.le (by linarith [hV.1]) (by norm_num)
  have hp : 1/2<slopeRatio q u ∧ slopeRatio q u<684/1000 := by
    dsimp [slopeRatio]
    constructor
    · rw [lt_div_iff₀ (mul_pos hUp hYp)]
      nlinarith
    · rw [div_lt_iff₀ (mul_pos hUp hYp)]
      nlinarith
  have hdom : Domain q u := by
    refine ⟨hu,?_,?_,?_,?_⟩
    · have hh : 0<q-u^2 := Real.sqrt_pos.mp (show 0<lowerRight q u by linarith [hr.1])
      linarith
    · have hh : 0<q-(2-u)^2 := Real.sqrt_pos.mp hUp
      linarith
    · have hh : 0<q-topLeft q u^2 := Real.sqrt_pos.mp hYp
      linarith
    · have hh : 0<q-lowerHeight q u^2 := Real.sqrt_pos.mp
        (show 0<lowerLeft q u by linarith [hw.1])
      linarith
  exact ⟨hdom,hr.1,hr.2,hU.1,hU.2,hV.1,hV.2,hY.1,hY.2,hv.1,hv.2,
    hw.1,hw.2,hp.1,hp.2⟩

/-- Two rational upper support lines, with their strict margins supplied
by the circle equations. -/
theorem top_support_upper {q u : ℝ} (h : CriticalStrip q u) :
    topRight q u<141/125+(29/50)*u ∧ topHeight q u<1+u/2 := by
  have hb := h.bounds
  have hUcircle := upper_circle hb.domain.second_radicand
  have hYcircle := upper_circle hb.domain.third_radicand
  let L : ℝ := 141/125+(29/50)*u
  let V : ℝ := 3-L
  have ht : 0 ≤ 1-u ∧ 1-u ≤ 13/100 := by constructor <;> linarith [h.u_lower,h.u_upper]
  have hL : 0<L := by dsimp [L]; linarith [h.u_lower]
  have hgap : q<L^2+(2-u)^2 := by
    have he : L^2+(2-u)^2-9789/2500 =
        26/15625+(117/6250)*(1-u)+(3341/2500)*(1-u)^2 := by dsimp [L]; ring
    nlinarith [h.q_upper,sq_nonneg (1-u)]
  have hUl : topRight q u<L := by
    by_contra! hh
    have hs := square_mono_nonneg hL.le hh
    change topRight q u^2+(2-u)^2=q at hUcircle
    nlinarith
  have hV : 0<V := by dsimp [V,L]; linarith [h.u_upper]
  have hVl : V<topLeft q u := by dsimp [V,topLeft]; linarith
  have hV2 := square_strict_mono_nonneg hV.le hVl
  have hYgap : q<(1+u/2)^2+V^2 := by
    have he : (1+u/2)^2+V^2-9789/2500 =
        229/62500-(4/3125)*(1-u)+(733/1250)*(1-u)^2 := by dsimp [V,L]; ring
    nlinarith [h.q_upper,sq_nonneg (1-u)]
  have hYl : topHeight q u<1+u/2 := by
    by_contra! hh
    have hs := square_mono_nonneg (by linarith [h.u_lower] : 0 ≤ 1+u/2) hh
    change topHeight q u^2+topLeft q u^2=q at hYcircle
    nlinarith
  exact ⟨hUl,hYl⟩

/-- This direct circle comparison replaces the integration of `v''>1`.
The residual numerator is a cubic with three positive terms in `1-u`. -/
theorem slope_affine_lower {q u : ℝ} (h : CriticalStrip q u) :
    3/2-u<slopeRatio q u := by
  have hb := h.bounds
  obtain ⟨hU,hY⟩ := top_support_upper h
  let L : ℝ := 141/125+(29/50)*u
  let V : ℝ := 3-L
  let Y : ℝ := 1+u/2
  have hUp : 0<topRight q u := by linarith [hb.U_lower]
  have hYp : 0<topHeight q u := by linarith [hb.Y_lower]
  have hLp : 0<L := by dsimp [L]; linarith [h.u_lower]
  have hYp' : 0<Y := by dsimp [Y]; linarith [h.u_lower]
  have hprod : topRight q u*topHeight q u ≤ L*Y :=
    mul_le_mul hU.le hY.le hYp.le hLp.le
  have hV : V<topLeft q u := by dsimp [V,L,topLeft]; linarith
  have hn := mul_le_mul_of_nonneg_left hV.le (by linarith [h.u_upper] : 0 ≤ 2-u)
  have hd := mul_le_mul_of_nonneg_left hprod (by linarith [h.u_upper] : 0 ≤ 3/2-u)
  have ht : 0 ≤ 1-u ∧ 1-u ≤ 13/100 := by constructor <;> linarith [h.u_lower,h.u_upper]
  have hrem : 0 ≤ (1-u)^2*(2159/1000-(29/100)*(1-u)) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  have hpoly : (3/2-u)*L*Y<(2-u)*V := by
    have he : (2-u)*V-(3/2-u)*L*Y =
        11/1000+(43/250)*(1-u)+(1-u)^2*(2159/1000-(29/100)*(1-u)) := by
      dsimp [V,L,Y]
      ring
    nlinarith
  dsimp [slopeRatio]
  rw [lt_div_iff₀ (mul_pos hUp hYp)]
  nlinarith

theorem position_slope_product_lower {q u : ℝ} (h : CriticalStrip q u) :
    141/100<u*(1+slopeRatio q u) := by
  have hp := slope_affine_lower h
  have hu : 0<u := by linarith [h.u_lower]
  have hh := mul_pos hu (sub_pos.mpr hp)
  have hc := mul_nonneg (sub_nonneg.mpr h.u_lower)
    (by linarith [h.u_upper] : 0 ≤ 163/100-u)
  nlinarith

theorem top_support_lower {q u : ℝ} (h : CriticalStrip q u) :
    9/10+(4/5)*u<topRight q u ∧ lowerHeight q u<38/25-u := by
  have hb := h.bounds
  have hUcircle := upper_circle hb.domain.second_radicand
  have hYcircle := upper_circle hb.domain.third_radicand
  have ht : 0 ≤ 1-u ∧ 1-u ≤ 13/100 := by constructor <;> linarith [h.u_lower,h.u_upper]
  have hpos : 0 ≤ (1-u)*(18/25-(41/25)*(1-u)) := mul_nonneg ht.1 (by linarith)
  have hUl : 9/10+(4/5)*u<topRight q u := by
    have hg : (9/10+(4/5)*u)^2<topRight q u^2 := by
      change topRight q u^2+(2-u)^2=q at hUcircle
      nlinarith [h.q_lower]
    by_contra! hh
    have hs := square_mono_nonneg (upper_nonneg q (2-u)) hh
    nlinarith
  have hYsq : (u+12/25)^2<topHeight q u^2 := by
    change topRight q u^2+(2-u)^2=q at hUcircle
    change topHeight q u^2+topLeft q u^2=q at hYcircle
    dsimp [topLeft] at hYcircle
    nlinarith [h.u_upper]
  have hY : u+12/25<topHeight q u := by
    by_contra! hh
    have hs := square_mono_nonneg (upper_nonneg q (topLeft q u)) hh
    nlinarith
  refine ⟨hUl,?_⟩
  dsimp [lowerHeight]
  linarith

/-- A lower circle support line with a strict, radius-uniform margin. -/
theorem left_support_lower {q u : ℝ} (h : CriticalStrip q u) :
    3/70<lowerLeft q u-1-(6/7)*u := by
  have hb := h.bounds
  have hv := (top_support_lower h).2
  have hvp : 0 ≤ lowerHeight q u := by linarith [hb.v_lower]
  have hv2 := square_mono_nonneg hvp hv.le
  have hwcircle := upper_circle hb.domain.fourth_radicand
  have ht : 0 ≤ 1-u ∧ 1-u ≤ 13/100 := by constructor <;> linarith [h.u_lower,h.u_upper]
  have hn := mul_nonneg ht.1 (by linarith : 0 ≤ 388/175-(85/49)*(1-u))
  have hw2 : (73/70+(6/7)*u)^2<lowerLeft q u^2 := by
    change lowerLeft q u^2+lowerHeight q u^2=q at hwcircle
    nlinarith [h.q_lower]
  have hw : 73/70+(6/7)*u<lowerLeft q u := by
    by_contra! hh
    have hs := square_mono_nonneg (upper_nonneg q (lowerHeight q u)) hh
    nlinarith
  linarith

def curvatureRatio (q u : ℝ) : ℝ :=
  q/((2-u)*topRight q u^2)+slopeRatio q u*q/(topHeight q u*topLeft q u^2)

/-- Both circle denominators admit the same rational lower curvature
constant.  The first comparison retains the equation `U²+(2-u)²=q`. -/
theorem curvatureRatio_lower {q u : ℝ} (h : CriticalStrip q u) :
    (13/10)*(1+slopeRatio q u)<curvatureRatio q u := by
  have hb := h.bounds
  have hA : 1 ≤ 2-u ∧ 2-u ≤ 113/100 := by constructor <;> linarith [h.u_lower,h.u_upper]
  have hAs := square_mono_nonneg (by linarith : 0 ≤ 2-u) hA.2
  have hAc : 0 ≤ q-((2-u)^2+(113/100)*(2-u)+(113/100)^2) := by
    nlinarith [h.q_lower]
  have hprod := mul_nonneg (by linarith : 0 ≤ 113/100-(2-u)) hAc
  have hUcircle := upper_circle hb.domain.second_radicand
  have hfirstNum : (13/10)*((2-u)*topRight q u^2)<q := by
    change topRight q u^2+(2-u)^2=q at hUcircle
    have he := congrArg (fun x : ℝ => (2-u)*x) hUcircle
    nlinarith [h.q_upper]
  have hUp : 0<topRight q u := by linarith [hb.U_lower]
  have hYp : 0<topHeight q u := by linarith [hb.Y_lower]
  have hVp : 0<topLeft q u := by linarith [hb.V_lower]
  have hfirst : 13/10<q/((2-u)*topRight q u^2) := by
    rw [lt_div_iff₀ (mul_pos (by linarith) (sq_pos_of_pos hUp))]
    exact hfirstNum
  have hVs := square_mono_nonneg hVp.le hb.V_upper.le
  have hden := mul_le_mul hb.Y_upper.le hVs (sq_nonneg _) (by norm_num : (0:ℝ) ≤ 3/2)
  have hsecond : 13/10<q/(topHeight q u*topLeft q u^2) := by
    rw [lt_div_iff₀ (mul_pos hYp (sq_pos_of_pos hVp))]
    nlinarith [h.q_lower]
  have hp : 0<slopeRatio q u := by linarith [hb.p_lower]
  have hh := mul_lt_mul_of_pos_left hsecond hp
  calc
    _ < q/((2-u)*topRight q u^2)+slopeRatio q u*(q/(topHeight q u*topLeft q u^2)) := by
      nlinarith
    _ = curvatureRatio q u := by dsimp [curvatureRatio]; ring

theorem right_curvature_upper {q u : ℝ} (h : CriticalStrip q u) :
    q/lowerRight q u^3<4/5 := by
  have hb := h.bounds
  have hr : 0<lowerRight q u := by linarith [hb.r_lower]
  have hu : 0 ≤ u := by linarith [h.u_lower]
  have hus := square_mono_nonneg hu h.u_upper
  have hrs := square_strict_mono_nonneg (by norm_num : (0:ℝ) ≤ 17/10) hb.r_lower
  have hm := mul_nonneg (by linarith [hb.r_lower] : 0 ≤ (4/5)*lowerRight q u-34/25)
    (sq_nonneg (lowerRight q u))
  have hc := upper_circle hb.domain.first_radicand
  rw [div_lt_iff₀ (pow_pos hr 3)]
  change lowerRight q u^2+u^2=q at hc
  nlinarith

end SquaresInCircles.Eight.ExactFamily.FiveCornerGeometry

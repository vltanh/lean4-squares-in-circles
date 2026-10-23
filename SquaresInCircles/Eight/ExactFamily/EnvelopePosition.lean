module

public import SquaresInCircles.Eight.ExactFamily.CriticalDifferentiation
public import SquaresInCircles.Eight.ExactFamily.RadiusMonotonicity
public import Mathlib.Topology.Order.IntermediateValue

/-!
# An interior minimizing position in a fixed geometric window

Uncompiled draft.  The single window `[87/100,11/10]` stays strictly
inside every radical branch in the radius strip.  Opposite derivative
signs at its two endpoints produce an interior position root.  Whole-domain
strict convexity identifies that root with the unique global position
minimum, avoiding all radical-endpoint regularity questions.
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.ExactFamily.FiveCornerGeometry

open Set

def positionWindow : Set ℝ := Icc (87/100) (11/10)

structure WindowBounds (q u : ℝ) : Prop where
  domain : Domain q u
  r_lower : 41/25<lowerRight q u
  U_lower : 1619/1000<topRight q u
  U_upper : topRight q u<1763/1000
  V_lower : 1237/1000<topLeft q u
  V_upper : topLeft q u<1381/1000
  Y_lower : 1411/1000<topHeight q u
  Y_upper : topHeight q u<2
  v_pos : 0<lowerHeight q u
  v_upper : lowerHeight q u<589/1000
  w_lower : 1885/1000<lowerLeft q u

theorem WindowBounds.smoothDomain {q u : ℝ} (h : WindowBounds q u) (hq : q<4) :
    SmoothDomain q u :=
  ⟨h.domain,hq,by linarith [h.r_lower],by linarith [h.U_lower],
    by linarith [h.Y_lower],by linarith [h.w_lower]⟩

theorem window_bounds {q u : ℝ} (hql : (79/40:ℝ)^2 ≤ q) (hqu : q ≤ 9789/2500)
    (hu : u∈positionWindow) : WindowBounds q u := by
  have hul : 87/100 ≤ u := hu.1
  have huu : u ≤ 11/10 := hu.2
  have hup : 0 ≤ u := by linarith
  have hA : 9/10 ≤ 2-u ∧ 2-u ≤ 113/100 := by constructor <;> linarith
  have hr : 41/25<lowerRight q u ∧ lowerRight q u<2 := by
    apply sqrt_between (by norm_num) (by norm_num)
    · have hs := square_mono_nonneg hup huu
      dsimp [lowerRight,upper]
      nlinarith
    · dsimp [lowerRight,upper]
      nlinarith [sq_nonneg u]
  have hU : 1619/1000<topRight q u ∧ topRight q u<1763/1000 := by
    apply sqrt_between (by norm_num) (by norm_num)
    · have hs := square_mono_nonneg (by linarith : 0 ≤ 2-u) hA.2
      dsimp [topRight,upper]
      nlinarith
    · have hs := square_mono_nonneg (by norm_num : (0:ℝ) ≤ 9/10) hA.1
      dsimp [topRight,upper]
      nlinarith
  have hV : 1237/1000<topLeft q u ∧ topLeft q u<1381/1000 := by
    dsimp [topLeft]
    constructor <;> linarith [hU.1,hU.2]
  have hY : 1411/1000<topHeight q u ∧ topHeight q u<2 := by
    apply sqrt_between (by norm_num) (by norm_num)
    · have hs := square_mono_nonneg (by linarith : 0 ≤ topLeft q u) hV.2.le
      dsimp [topHeight,upper]
      nlinarith
    · dsimp [topHeight,upper]
      nlinarith [sq_nonneg (topLeft q u)]
  have hv : 0<lowerHeight q u ∧ lowerHeight q u<589/1000 := by
    dsimp [lowerHeight]
    constructor <;> linarith [hY.1,hY.2]
  have hw : 1885/1000<lowerLeft q u ∧ lowerLeft q u<2 := by
    apply sqrt_between (by norm_num) (by norm_num)
    · have hs := square_mono_nonneg hv.1.le hv.2.le
      dsimp [lowerLeft,upper]
      nlinarith
    · dsimp [lowerLeft,upper]
      nlinarith [sq_nonneg (lowerHeight q u)]
  have hdom : Domain q u := by
    refine ⟨hup,?_,?_,?_,?_⟩
    · have hh : 0<q-u^2 := Real.sqrt_pos.mp (show 0<lowerRight q u by linarith [hr.1])
      linarith
    · have hh : 0<q-(2-u)^2 := Real.sqrt_pos.mp (show 0<topRight q u by linarith [hU.1])
      linarith
    · have hh : 0<q-topLeft q u^2 := Real.sqrt_pos.mp (show 0<topHeight q u by linarith [hY.1])
      linarith
    · have hh : 0<q-lowerHeight q u^2 := Real.sqrt_pos.mp (show 0<lowerLeft q u by linarith [hw.1])
      linarith
  exact ⟨hdom,hr.1,hU.1,hU.2,hV.1,hV.2,hY.1,hY.2,hv.1,hv.2,hw.1⟩

theorem upper_comparison_bounds {q : ℝ}
    (hql : (79/40:ℝ)^2 ≤ q) (hqu : q ≤ 9789/2500) :
    lowerRight q (11/10)<33/20 ∧ lowerHeight q (11/10)<47/100 ∧
    191/100<lowerLeft q (11/10) ∧ 0<slopeRatio q (11/10) ∧
    slopeRatio q (11/10)<21/50 ∧ 2/3<(11/10)/lowerRight q (11/10) ∧
    0<lowerHeight q (11/10)/lowerLeft q (11/10) ∧
    lowerHeight q (11/10)/lowerLeft q (11/10)<1/4 := by
  have hb := window_bounds hql hqu (u:=11/10) (by norm_num [positionWindow])
  have hr : 0<lowerRight q (11/10) := by linarith [hb.r_lower]
  have hru : lowerRight q (11/10)<33/20 := by
    have hh : (41/25:ℝ)<Real.sqrt (q-(11/10)^2) ∧ Real.sqrt (q-(11/10)^2)<33/20 := by
      apply sqrt_between (by norm_num) (by norm_num) <;> nlinarith
    exact hh.2
  have hU : 1758/1000<topRight q (11/10) := by
    have hh : (1758/1000:ℝ)<Real.sqrt (q-(2-11/10)^2) ∧ Real.sqrt (q-(2-11/10)^2)<2 := by
      apply sqrt_between (by norm_num) (by norm_num) <;> nlinarith
    exact hh.1
  have hV : topLeft q (11/10)<1242/1000 := by dsimp [topLeft]; linarith
  have hY : 153/100<topHeight q (11/10) := by
    have hs := square_mono_nonneg (by linarith [hb.V_lower] : 0 ≤ topLeft q (11/10)) hV.le
    have hh : (153/100:ℝ)<Real.sqrt (q-topLeft q (11/10)^2) ∧
        Real.sqrt (q-topLeft q (11/10)^2)<2 := by
      apply sqrt_between (by norm_num) (by norm_num)
      · nlinarith
      · nlinarith [sq_nonneg (topLeft q (11/10))]
    exact hh.1
  have hv : lowerHeight q (11/10)<47/100 := by dsimp [lowerHeight]; linarith
  have hw : 191/100<lowerLeft q (11/10) := by
    have hs := square_mono_nonneg hb.v_pos.le hv.le
    have hh : (191/100:ℝ)<Real.sqrt (q-lowerHeight q (11/10)^2) ∧
        Real.sqrt (q-lowerHeight q (11/10)^2)<2 := by
      apply sqrt_between (by norm_num) (by norm_num)
      · nlinarith
      · nlinarith [sq_nonneg (lowerHeight q (11/10))]
    exact hh.1
  have hUp : 0<topRight q (11/10) := by linarith
  have hYp : 0<topHeight q (11/10) := by linarith
  have hwp : 0<lowerLeft q (11/10) := by linarith
  have hp : 0<slopeRatio q (11/10) := by
    dsimp [slopeRatio]
    exact div_pos (mul_pos (by norm_num) (by linarith [hb.V_lower])) (mul_pos hUp hYp)
  have hpu : slopeRatio q (11/10)<21/50 := by
    have hprod := mul_le_mul hU.le hY.le (by norm_num : (0:ℝ) ≤ 153/100) hUp.le
    dsimp [slopeRatio]
    rw [div_lt_iff₀ (mul_pos hUp hYp)]
    nlinarith
  have hx : 2/3<(11/10)/lowerRight q (11/10) := by
    rw [lt_div_iff₀ hr]
    nlinarith
  have hyl : 0<lowerHeight q (11/10)/lowerLeft q (11/10) := div_pos hb.v_pos hwp
  have hyu : lowerHeight q (11/10)/lowerLeft q (11/10)<1/4 := by
    rw [div_lt_iff₀ hwp]
    linarith
  exact ⟨hru,hv,hw,hp,hpu,hx,hyl,hyu⟩

/-- The upper endpoint has a broad positive derivative margin throughout
the entire radius and tilt strip. -/
theorem upper_position_positive {q c s : ℝ}
    (hql : (79/40:ℝ)^2 ≤ q) (hqu : q ≤ 9789/2500)
    (hc : 0<c) (hs : 0 ≤ s) (hunit : c^2+s^2=1) (ht : s/c ≤ 1/5) :
    (1/4)*c<positionHalf q c s (11/10) := by
  have hb := window_bounds hql hqu (u:=11/10) (by norm_num [positionWindow])
  obtain ⟨hr,hv,hw,hp,hpu,hx,hy,hyu⟩ := upper_comparison_bounds hql hqu
  obtain ⟨_,hcu,hsu,hsc,_⟩ := small_tilt_bounds hc hs hunit ht
  obtain ⟨hk₁,hk₂⟩ := components_pos (by linarith) hb.domain hc hcu hs hsu
  have hcr := mul_le_mul_of_nonneg_left (show lowerRight q (11/10)-1 ≤ 13/20 by linarith) hc.le
  have hk₁l : 27/20 ≤ firstComponent q c s (11/10) := by
    dsimp [firstComponent]
    nlinarith
  have hcx := mul_lt_mul_of_pos_left hx hc
  have ha : (2/3)*c<positionA q c s (11/10) := by
    dsimp [positionA]
    have he : c*((11/10)/lowerRight q (11/10))=c*(11/10)/lowerRight q (11/10) := by ring
    nlinarith
  have hcv := mul_le_mul_of_nonneg_left hv.le hc.le
  have hsw := mul_nonneg hs (by linarith : 0 ≤ lowerLeft q (11/10)-1)
  have hk₂u : secondComponent q c s (11/10) ≤ 147/100 := by dsimp [secondComponent]; nlinarith
  have hsy := mul_le_mul_of_nonneg_left hyu.le hs
  have hB : positionB q c s (11/10) ≤ (21/20)*c := by
    dsimp [positionB]
    have he : s*(lowerHeight q (11/10)/lowerLeft q (11/10))=
      s*lowerHeight q (11/10)/lowerLeft q (11/10) := by ring
    nlinarith
  have hBp : 0 ≤ positionB q c s (11/10) := by
    have hm := mul_nonneg hs hy.le
    dsimp [positionB]
    nlinarith
  have hbu : positionb q c s (11/10) ≤ (441/1000)*c := by
    have hm := mul_le_mul hpu.le hB hBp (by norm_num : (0:ℝ) ≤ 21/50)
    dsimp [positionb]
    nlinarith
  have hbp : 0 ≤ positionb q c s (11/10) := mul_nonneg hp.le hBp
  have hfirst := mul_lt_mul_of_pos_left ha hk₁
  have hfirst' := mul_le_mul_of_nonneg_right hk₁l (by positivity : 0 ≤ (2/3)*c)
  have hsecond := mul_le_mul hk₂u hbu hbp (by norm_num : (0:ℝ) ≤ 147/100)
  have he : positionHalf q c s (11/10)=
      firstComponent q c s (11/10)*positionA q c s (11/10)-
      secondComponent q c s (11/10)*positionb q c s (11/10) := by
    dsimp [positionHalf,positionA,positionb,positionB]
    ring
  rw [he]
  nlinarith

theorem positionHalf_continuousAt {q c s u : ℝ}
    (hr : 0<lowerRight q u) (hU : 0<topRight q u)
    (hY : 0<topHeight q u) (hw : 0<lowerLeft q u) :
    ContinuousAt (positionHalf q c s) u := by
  have cr : Continuous (lowerRight q) := by dsimp [lowerRight,upper]; fun_prop
  have cU : Continuous (topRight q) := by dsimp [topRight,upper]; fun_prop
  have cV : Continuous (topLeft q) := by dsimp [topLeft,topRight,upper]; fun_prop
  have cY : Continuous (topHeight q) := by dsimp [topHeight,topLeft,topRight,upper]; fun_prop
  have cv : Continuous (lowerHeight q) := by dsimp [lowerHeight,topHeight,topLeft,topRight,upper]; fun_prop
  have cw : Continuous (lowerLeft q) := by dsimp [lowerLeft,lowerHeight,topHeight,topLeft,topRight,upper]; fun_prop
  have ck₁ : Continuous (firstComponent q c s) := by
    dsimp [firstComponent,lowerRight,upper]
    fun_prop
  have ck₂ : Continuous (secondComponent q c s) := by
    dsimp [secondComponent,lowerLeft,lowerHeight,topHeight,topLeft,topRight,upper]
    fun_prop
  have ca : ContinuousAt (fun x : ℝ => s+c*x/lowerRight q x) u :=
    continuousAt_const.add ((continuousAt_const.mul continuousAt_id).div cr.continuousAt (ne_of_gt hr))
  have cp : ContinuousAt (slopeRatio q) u :=
    ((continuousAt_const.sub continuousAt_id).mul cV.continuousAt).div
      (cU.continuousAt.mul cY.continuousAt) (ne_of_gt (mul_pos hU hY))
  have cB : ContinuousAt (fun x : ℝ => c+s*lowerHeight q x/lowerLeft q x) u :=
    continuousAt_const.add ((continuousAt_const.mul cv.continuousAt).div cw.continuousAt (ne_of_gt hw))
  exact (ck₁.continuousAt.mul ca).sub ((ck₂.continuousAt.mul cp).mul cB)

theorem window_stationary_exists {q c s : ℝ}
    (hql : (79/40:ℝ)^2 ≤ q) (hqu : q ≤ 9789/2500)
    (hc : 0<c) (hs : 0 ≤ s) (hunit : c^2+s^2=1) (ht : s/c ≤ 1/5) :
    ∃ u∈Ioo (87/100) (11/10), positionHalf q c s u=0 ∧
      HasDerivAt (defect q c s) 0 u ∧
      ∀ v, Domain q v → defect q c s u ≤ defect q c s v := by
  have hl := comparison_position_negative hql hqu hc hs ht hunit
  change positionHalf q c s (87/100)<0 at hl
  have hr : 0<positionHalf q c s (11/10) := by linarith [upper_position_positive hql hqu hc hs hunit ht]
  have hcont : ContinuousOn (positionHalf q c s) (Icc (87/100) (11/10)) := by
    intro u hu
    have hb := window_bounds hql hqu hu
    exact (positionHalf_continuousAt (by linarith [hb.r_lower]) (by linarith [hb.U_lower])
      (by linarith [hb.Y_lower]) (by linarith [hb.w_lower])).continuousWithinAt
  obtain ⟨u,hu,hzero⟩ := intermediate_value_Icc (by norm_num : (87/100:ℝ) ≤ 11/10)
    hcont ⟨hl.le,hr.le⟩
  have hul : 87/100<u := by
    by_contra! hh
    have he : u=87/100 := le_antisymm hh hu.1
    rw [he] at hzero
    linarith
  have huu : u<11/10 := by
    by_contra! hh
    have he : u=11/10 := le_antisymm hu.2 hh
    rw [he] at hzero
    linarith
  have hb := window_bounds hql hqu hu
  have hd := position_deriv (q:=q) (c:=c) (s:=s) (u:=u)
    (by linarith [hb.r_lower]) (by linarith [hb.U_lower])
    (by linarith [hb.Y_lower]) (by linarith [hb.w_lower])
  rw [hzero,mul_zero] at hd
  obtain ⟨_,hcu,hsu,_,_⟩ := small_tilt_bounds hc hs hunit ht
  exact ⟨u,⟨hul,huu⟩,hzero,hd,
    stationary_global_minimum (by linarith) hc hcu hs hsu hb.domain hd⟩

theorem window_minimum_exists (q c s : ℝ) :
    ∃ u∈positionWindow, ∀ v∈positionWindow, defect q c s u ≤ defect q c s v := by
  obtain ⟨u,hu,hm⟩ := (isCompact_Icc : IsCompact positionWindow).exists_isMinOn
    (show positionWindow.Nonempty from ⟨1,by norm_num [positionWindow]⟩)
    (defect_continuous q c s).continuousOn
  exact ⟨u,hu,fun v hv => hm hv⟩

def windowMinimizer (q c s : ℝ) : ℝ := Classical.choose (window_minimum_exists q c s)

theorem windowMinimizer_mem (q c s : ℝ) : windowMinimizer q c s∈positionWindow :=
  (Classical.choose_spec (window_minimum_exists q c s)).1

theorem windowMinimizer_le (q c s : ℝ) {u : ℝ} (hu : u∈positionWindow) :
    defect q c s (windowMinimizer q c s) ≤ defect q c s u :=
  (Classical.choose_spec (window_minimum_exists q c s)).2 u hu

theorem window_minimizer_unique {q c s u v : ℝ}
    (hql : (79/40:ℝ)^2 ≤ q) (hqu : q ≤ 9789/2500)
    (hc : 0<c) (hs : 0 ≤ s) (hunit : c^2+s^2=1) (ht : s/c ≤ 1/5)
    (hu : u∈positionWindow) (hv : v∈positionWindow)
    (hmu : ∀ w∈positionWindow, defect q c s u ≤ defect q c s w)
    (hmv : ∀ w∈positionWindow, defect q c s v ≤ defect q c s w) : u=v := by
  by_contra hne
  obtain ⟨_,hcu,hsu,_,_⟩ := small_tilt_bounds hc hs hunit ht
  have hm : (1/2)*u+(1/2)*v∈positionWindow := by
    constructor <;> linarith [hu.1,hu.2,hv.1,hv.2]
  have hj := defect_mix_strict (by linarith : q<4) (window_bounds hql hqu hu).domain
    (window_bounds hql hqu hv).domain hne hc hcu hs hsu
    (by norm_num : (0:ℝ)<1/2) (by norm_num : (0:ℝ)<1/2) (by norm_num)
  have h₁ := hmu _ hm
  have h₂ := hmv _ hm
  linarith

theorem windowMinimizer_geometric {q c s : ℝ}
    (hql : (79/40:ℝ)^2 ≤ q) (hqu : q ≤ 9789/2500)
    (hc : 0<c) (hs : 0 ≤ s) (hunit : c^2+s^2=1) (ht : s/c ≤ 1/5) :
    windowMinimizer q c s∈Ioo (87/100) (11/10) ∧
    positionHalf q c s (windowMinimizer q c s)=0 ∧
    HasDerivAt (defect q c s) 0 (windowMinimizer q c s) ∧
    ∀ v, Domain q v → defect q c s (windowMinimizer q c s) ≤ defect q c s v := by
  obtain ⟨u,hu,hzero,hd,hm⟩ := window_stationary_exists hql hqu hc hs hunit ht
  have hu' : u∈positionWindow := ⟨hu.1.le,hu.2.le⟩
  have he : windowMinimizer q c s=u := window_minimizer_unique hql hqu hc hs hunit ht
    (windowMinimizer_mem q c s) hu' (fun v hv => windowMinimizer_le q c s hv)
    (fun v hv => hm v (window_bounds hql hqu hv).domain)
  rw [he]
  exact ⟨hu,hzero,hd,hm⟩

theorem windowMinimizer_eq_of_stationary {q c s u : ℝ}
    (hql : (79/40:ℝ)^2 ≤ q) (hqu : q ≤ 9789/2500)
    (hc : 0<c) (hs : 0 ≤ s) (hunit : c^2+s^2=1) (ht : s/c ≤ 1/5)
    (hu : Domain q u) (hd : HasDerivAt (defect q c s) 0 u) : windowMinimizer q c s=u := by
  obtain ⟨_,_,_,hm⟩ := windowMinimizer_geometric hql hqu hc hs hunit ht
  obtain ⟨_,hcu,hsu,_,_⟩ := small_tilt_bounds hc hs hunit ht
  exact minimizer_unique (by linarith) hc hcu hs hsu
    (window_bounds hql hqu (windowMinimizer_mem q c s)).domain hu hm
    (stationary_global_minimum (by linarith) hc hcu hs hsu hu hd)

def positionEnvelope (q t : ℝ) : ℝ :=
  sInf ((fun u => defect q (Real.cos t) (Real.sin t) u) '' positionWindow)

theorem positionEnvelope_eq (q t : ℝ) :
    positionEnvelope q t=defect q (Real.cos t) (Real.sin t)
      (windowMinimizer q (Real.cos t) (Real.sin t)) := by
  obtain ⟨u,hu,he,hm⟩ := (isCompact_Icc : IsCompact positionWindow).exists_sInf_image_eq_and_le
    (show positionWindow.Nonempty from ⟨1,by norm_num [positionWindow]⟩)
    (defect_continuous q (Real.cos t) (Real.sin t)).continuousOn
  dsimp only [positionEnvelope]
  rw [he]
  exact le_antisymm (hm _ (windowMinimizer_mem _ _ _)) (windowMinimizer_le _ _ _ hu)

theorem positionEnvelope_continuous (q : ℝ) : Continuous (positionEnvelope q) := by
  apply (isCompact_Icc : IsCompact positionWindow).continuous_sInf
  dsimp [defect,firstComponent,secondComponent,lowerRight,lowerLeft,lowerHeight,
    topHeight,topLeft,topRight,upper]
  fun_prop

/-- The actual position envelope inherits the finite radius comparison.
Its definition uses a fixed compact window, so no derivative of a
radius-dependent minimizer is needed. -/
theorem positionEnvelope_radius_decrease {q₀ q₁ t : ℝ}
    (hql : (79/40:ℝ)^2 ≤ q₀) (hqu : q₁ ≤ 9789/2500) (hq : q₀<q₁)
    (hc : 0<Real.cos t) (hs : 0 ≤ Real.sin t) :
    positionEnvelope q₁ t<positionEnvelope q₀ t-(q₁-q₀) := by
  have hu := windowMinimizer_mem q₀ (Real.cos t) (Real.sin t)
  have hdom := (window_bounds hql (by linarith : q₀ ≤ 9789/2500) hu).domain
  have hd := defect_radius_decrease hq (by linarith : q₁<4) hdom
    hc (Real.cos_le_one t) hs (Real.sin_le_one t)
  have hm := windowMinimizer_le q₁ (Real.cos t) (Real.sin t) hu
  rw [positionEnvelope_eq q₁ t,positionEnvelope_eq q₀ t]
  linarith

end SquaresInCircles.Eight.ExactFamily.FiveCornerGeometry

module

public import SquaresInCircles.Eight.TableFree.StationaryIntervalAlgebra

/-!
# Whole-rectangle bounds for the position comparison curves

Uncompiled reconstruction.  These are the two continuous rectangles
used by the affine position comparisons in the hand proof.  The more
precise rectangle is the image range of `u = 1 - (3/5) h`; the other
is the terminal rectangle already used for the force estimates.  Neither
argument subdivides the radius or angle interval.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.StationaryPrimitives
open ExactFamily.FiveCornerGeometry

/-- Successive positive-square comparisons with arbitrary rational
endpoints, used below for an entire rectangle or a single comparison
position.  The square comparisons are conclusions of exact arithmetic
at the displayed endpoints, not values of the sought minimizer. -/
theorem radical_box {q u ql qu a b rl ru Ul Uu Yl Yu wl wu : ℝ}
    (hq : q∈Icc ql qu) (hu : u∈Icc a b)
    (hd : 0≤a ∧ 0≤2-b ∧ 0≤rl ∧ 0≤ru ∧ 0≤Ul ∧ 0≤Uu ∧
      0≤3-Uu ∧ 0≤Yl ∧ 0≤Yu ∧ 0≤2-Yu ∧ 0≤wl ∧ 0≤wu ∧
      rl^2<ql-b^2 ∧ qu-a^2<ru^2 ∧
      Ul^2<ql-(2-a)^2 ∧ qu-(2-b)^2<Uu^2 ∧
      Yl^2<ql-(3-Ul)^2 ∧ qu-(3-Uu)^2<Yu^2 ∧
      wl^2<ql-(2-Yl)^2 ∧ qu-(2-Yu)^2<wu^2) :
    lowerRight q u∈Icc rl ru ∧ topRight q u∈Icc Ul Uu ∧
    topLeft q u∈Icc (3-Uu) (3-Ul) ∧ topHeight q u∈Icc Yl Yu ∧
    lowerHeight q u∈Icc (2-Yu) (2-Yl) ∧ lowerLeft q u∈Icc wl wu := by
  rcases hd with ⟨ha,hl,hrl,hru,hUl,hUu,hV,hYl,hYu,hv,hwl,hwu,
    hrL,hrU,hUL,hUU,hYL,hYU,hwL,hwU⟩
  have hu2 := square_bounds hu ha
  have hlb : 2-u∈Icc (2-b) (2-a) := ⟨by linarith [hu.2],by linarith [hu.1]⟩
  have hl2 := square_bounds hlb hl
  have hr : lowerRight q u∈Ioo rl ru := sqrt_bounds
    (show q-u^2∈Icc (ql-b^2) (qu-a^2) from
      ⟨by linarith [hq.1,hu2.2],by linarith [hq.2,hu2.1]⟩) hrl hru hrL hrU
  have hU : topRight q u∈Ioo Ul Uu := sqrt_bounds
    (show q-(2-u)^2∈Icc (ql-(2-a)^2) (qu-(2-b)^2) from
      ⟨by linarith [hq.1,hl2.2],by linarith [hq.2,hl2.1]⟩) hUl hUu hUL hUU
  have hVb : topLeft q u∈Icc (3-Uu) (3-Ul) := by
    dsimp [topLeft]
    exact ⟨by linarith [hU.2],by linarith [hU.1]⟩
  have hV2 := square_bounds hVb hV
  have hY : topHeight q u∈Ioo Yl Yu := sqrt_bounds
    (show q-topLeft q u^2∈Icc (ql-(3-Ul)^2) (qu-(3-Uu)^2) from
      ⟨by linarith [hq.1,hV2.2],by linarith [hq.2,hV2.1]⟩) hYl hYu hYL hYU
  have hvb : lowerHeight q u∈Icc (2-Yu) (2-Yl) := by
    dsimp [lowerHeight]
    exact ⟨by linarith [hY.2],by linarith [hY.1]⟩
  have hv2 := square_bounds hvb hv
  have hw : lowerLeft q u∈Ioo wl wu := sqrt_bounds
    (show q-lowerHeight q u^2∈Icc (ql-(2-Yl)^2) (qu-(2-Yu)^2) from
      ⟨by linarith [hq.1,hv2.2],by linarith [hq.2,hv2.1]⟩) hwl hwu hwL hwU
  exact ⟨⟨hr.1.le,hr.2.le⟩,⟨hU.1.le,hU.2.le⟩,hVb,
    ⟨hY.1.le,hY.2.le⟩,hvb,⟨hw.1.le,hw.2.le⟩⟩

theorem cosine_box {h a b cl cu : ℝ} (hh : h∈Icc a b)
    (hd : 0≤a ∧ 0<cl ∧ 0<cu ∧ (1/cu)^2<1+a^2 ∧ 1+b^2<(1/cl)^2) :
    cosine h∈Icc cl cu := by
  rcases hd with ⟨ha,hcl,hcu,hL,hU⟩
  have hh2 := square_bounds hh ha
  have hD : 0<Real.sqrt (1+h^2) := Real.sqrt_pos.mpr (by positivity)
  have hb := sqrt_bounds
    (show 1+h^2∈Icc (1+a^2) (1+b^2) from
      ⟨by linarith [hh2.1],by linarith [hh2.2]⟩)
    (by positivity : 0≤1/cu) (by positivity : 0≤1/cl) hL hU
  rw [cosine,Real.cos_arctan]
  constructor
  · apply (le_div_iff₀ hD).2
    have hm := mul_lt_mul_of_pos_left hb.2 hcl
    have he : cl*(1/cl)=1 := by field_simp [hcl.ne']
    linarith
  · apply (div_le_iff₀ hD).2
    have hm := mul_lt_mul_of_pos_left hb.1 hcu
    have he : cu*(1/cu)=1 := by field_simp [hcu.ne']
    linarith

theorem affine_radicals {q u : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hu : u∈Icc (1127/1250:ℝ) (47/50)) :
    lowerRight q u∈Icc (174120647/100000000:ℝ) (176145323/100000000) ∧
    topRight q u∈Icc (164587892/100000000:ℝ) (167092789/100000000) ∧
    topLeft q u∈Icc (132907211/100000000:ℝ) (135412108/100000000) ∧
    topHeight q u∈Icc (144282919/100000000:ℝ) (146600387/100000000) ∧
    lowerHeight q u∈Icc (53399613/100000000:ℝ) (55717081/100000000) ∧
    lowerLeft q u∈Icc (189867339/100000000:ℝ) (190537350/100000000) := by
  have hb := radical_box hq hu
    (rl:=174120647/100000000) (ru:=176145323/100000000)
    (Ul:=164587892/100000000) (Uu:=167092789/100000000)
    (Yl:=144282919/100000000) (Yu:=146600387/100000000)
    (wl:=189867339/100000000) (wu:=190537350/100000000) (by norm_num)
  norm_num at hb ⊢
  exact hb

theorem affine_trig {h : ℝ} (hh : h∈Icc (1/10:ℝ) (41/250)) :
    cosine h∈Icc (986817330/1000000000:ℝ) (995037193/1000000000) ∧
    sine h∈Icc (98681733/1000000000:ℝ) (163186100/1000000000) := by
  have hc := cosine_box hh (cl:=986817330/1000000000) (cu:=995037193/1000000000)
    (by norm_num)
  have hs := product_bounds hh hc (by norm_num) (by norm_num)
  refine ⟨hc,?_⟩
  rw [sine_eq]
  exact ⟨by linarith [hs.1],by linarith [hs.2]⟩

/-- The sharper Hessian bounds on the single range of the upper affine
comparison position. -/
theorem affine_derivatives {q u h : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hu : u∈Icc (1127/1250:ℝ) (47/50))
    (hh : h∈Icc (1/10:ℝ) (41/250)) :
    337/50<positionSecond q (cosine h) (sine h) u ∧
    positionSecond q (cosine h) (sine h) u<17/2 ∧
    429/100<mixedSecond q (cosine h) (sine h) u ∧
    mixedSecond q (cosine h) (sine h) u<529/100 := by
  obtain ⟨hr,hU,hV,hY,hv,hw⟩ := affine_radicals hq hu
  obtain ⟨hc,hs⟩ := affine_trig hh
  let J := differentialIntervals (Interval.of_bounds hq) (Interval.of_bounds hu)
    (Interval.of_bounds hr) (Interval.of_bounds hU) (Interval.of_bounds hV)
    (Interval.of_bounds hY) (Interval.of_bounds hv) (Interval.of_bounds hw)
    (Interval.of_bounds hc) (Interval.of_bounds hs)
    (by norm_num [Interval.of_bounds]) (by norm_num [Interval.of_bounds])
    (by norm_num [Interval.of_bounds]) (by norm_num [Interval.of_bounds])
    (by norm_num [Interval.of_bounds]) (by norm_num [Interval.of_bounds])
  have hp := J.position.mem
  have hm := J.mixed.mem
  norm_num [J,differentialIntervals,Interval.of_bounds,Interval.point,Interval.add,
    Interval.sub,Interval.neg,Interval.mul,Interval.div,Interval.inv,Interval.square,Interval.cube] at hp hm
  exact ⟨by linarith [hp.1],by linarith [hp.2],by linarith [hm.1],by linarith [hm.2]⟩

/-- The slightly wider bounds needed by the lower affine comparison. -/
theorem rectangle_derivatives {q u h : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hu : u∈Icc (179/200:ℝ) (47/50))
    (hh : h∈Icc (1/10:ℝ) (41/250)) :
    33/5<positionSecond q (cosine h) (sine h) u ∧
    positionSecond q (cosine h) (sine h) u<87/10 ∧
    21/5<mixedSecond q (cosine h) (sine h) u ∧
    mixedSecond q (cosine h) (sine h) u<11/2 := by
  have hr := radical_bounds hq hu
  have ht := trig_bounds hh
  let J := differentialIntervals (Interval.of_bounds hq) (Interval.of_bounds hu)
    (Interval.of_bounds hr.r) (Interval.of_bounds hr.U) (Interval.of_bounds hr.V)
    (Interval.of_bounds hr.Y) (Interval.of_bounds hr.v) (Interval.of_bounds hr.w)
    (Interval.of_bounds ht.c) (Interval.of_bounds ht.s)
    (by norm_num [Interval.of_bounds]) (by norm_num [Interval.of_bounds])
    (by norm_num [Interval.of_bounds]) (by norm_num [Interval.of_bounds])
    (by norm_num [Interval.of_bounds]) (by norm_num [Interval.of_bounds])
  have hp := J.position.mem
  have hm := J.mixed.mem
  norm_num [J,differentialIntervals,Interval.of_bounds,Interval.point,Interval.add,
    Interval.sub,Interval.neg,Interval.mul,Interval.div,Interval.inv,Interval.square,Interval.cube] at hp hm
  exact ⟨by linarith [hp.1],by linarith [hp.2],by linarith [hm.1],by linarith [hm.2]⟩

end SquaresInCircles.Eight.TableFree.StationaryPrimitives

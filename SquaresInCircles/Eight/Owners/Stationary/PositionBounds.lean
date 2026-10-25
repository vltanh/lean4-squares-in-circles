module

public import SquaresInCircles.Eight.Frames.Central.ForbiddenWidths
public import SquaresInCircles.Eight.Owners.Stationary.TerminalWeights
public import SquaresInCircles.Eight.Stationary.System

/-!
# Eight squares: localization of the actual varying position minimizer

Strict position convexity on the original
geometric window converts the proved comparison signs into bounds on
`minimizingPosition q t` itself.  Tilt stationarity is never used: the
result applies at every tilt in the complete terminal interval.
-/

section
/-!
## Bounds on whole rectangles for the comparison curves of the position

The two rectangles of the affine comparisons of the position: the finer one is the range of
`u = 1 - (3/5) h` (`affine_radicals`, `affine_trig`, `affine_derivatives`), the other is the
terminal rectangle of the force estimates (`rectangle_derivatives`). Each bound holds on the whole
rectangle of radius and angle, through successive comparisons of positive squares
(`radical_box`, `cosine_box`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.StationaryPrimitives
open Stationary.FiveCornerGeometry

/-- Successive comparisons of positive squares with rational endpoints, for a whole rectangle or a
single comparison position; the comparisons are exact arithmetic at the endpoints. -/
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
    429/100< mixedSecond q (cosine h) (sine h) u ∧
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
    21/5< mixedSecond q (cosine h) (sine h) u ∧
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

end SquaresInCircles.Eight.StationaryPrimitives
end
end
end

section
/-!
## Three exact comparison values for the position localization

Each theorem retains the complete original
radius interval.  Positive squaring gives the four successive circle
roots at the one specified comparison position, and ordered-field
arithmetic then bounds the actual position derivative.  These are the
three comparison values in the continuous affine-curve proof, not a
cover or a search for a stationary root.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.StationaryPrimitives
open Stationary.FiveCornerGeometry

theorem upper_pivot {q : ℝ} (hq : q∈Icc (19577/5000:ℝ) (9789/2500)) :
    183/5000<2*positionHalf q (cosine (13/100)) (sine (13/100)) (461/500) := by
  have hu : (461/500:ℝ)∈Icc (461/500) (461/500) := ⟨le_rfl,le_rfl⟩
  obtain ⟨hr,hU,hV,hY,hv,hw⟩ := radical_box hq hu
    (rl:=175080438/100000000) (ru:=175086151/100000000)
    (Ul:=165931190/100000000) (Uu:=165937218/100000000)
    (Yl:=145531969/100000000) (Yu:=145544394/100000000)
    (wl:=190229423/100000000) (wu:=190238238/100000000) (by norm_num)
  have hh : (13/100:ℝ)∈Icc (13/100) (13/100) := ⟨le_rfl,le_rfl⟩
  have hc := cosine_box hh (cl:=99165561/100000000) (cu:=99165563/100000000) (by norm_num)
  have hs : sine (13/100)∈Icc ((13/100:ℝ)*(99165561/100000000))
      ((13/100:ℝ)*(99165563/100000000)) := by
    rw [sine_eq]
    exact product_bounds hh hc (by norm_num) (by norm_num)
  let J := differentialIntervals (Interval.of_bounds hq) (Interval.of_bounds hu)
    (Interval.of_bounds hr) (Interval.of_bounds hU) (Interval.of_bounds hV)
    (Interval.of_bounds hY) (Interval.of_bounds hv) (Interval.of_bounds hw)
    (Interval.of_bounds hc) (Interval.of_bounds hs)
    (by norm_num [Interval.of_bounds]) (by norm_num [Interval.of_bounds])
    (by norm_num [Interval.of_bounds]) (by norm_num [Interval.of_bounds])
    (by norm_num [Interval.of_bounds]) (by norm_num [Interval.of_bounds])
  have hf := J.first.mem
  norm_num [J,differentialIntervals,Interval.of_bounds,Interval.point,Interval.add,
    Interval.sub,Interval.neg,Interval.mul,Interval.div,Interval.inv,Interval.square,Interval.cube] at hf
  linarith [hf.1]

theorem lower_fixed_endpoint {q : ℝ} (hq : q∈Icc (19577/5000:ℝ) (9789/2500)) :
    2*positionHalf q (cosine (41/250)) (sine (41/250)) (179/200)< -11/1000 := by
  have hu : (179/200:ℝ)∈Icc (179/200) (179/200) := ⟨le_rfl,le_rfl⟩
  obtain ⟨hr,hU,hV,hY,hv,hw⟩ := radical_box hq hu
    (rl:=176475918/100000000) (ru:=176481587/100000000)
    (Ul:=164145514/100000000) (Uu:=164151608/100000000)
    (Yl:=143866460/100000000) (Yu:=143879167/100000000)
    (wl:=189744632/100000000) (wu:=189753663/100000000) (by norm_num)
  have hh : (41/250:ℝ)∈Icc (41/250) (41/250) := ⟨le_rfl,le_rfl⟩
  have hc := cosine_box hh (cl:=98681733/100000000) (cu:=98681734/100000000) (by norm_num)
  have hs : sine (41/250)∈Icc ((41/250:ℝ)*(98681733/100000000))
      ((41/250:ℝ)*(98681734/100000000)) := by
    rw [sine_eq]
    exact product_bounds hh hc (by norm_num) (by norm_num)
  let J := differentialIntervals (Interval.of_bounds hq) (Interval.of_bounds hu)
    (Interval.of_bounds hr) (Interval.of_bounds hU) (Interval.of_bounds hV)
    (Interval.of_bounds hY) (Interval.of_bounds hv) (Interval.of_bounds hw)
    (Interval.of_bounds hc) (Interval.of_bounds hs)
    (by norm_num [Interval.of_bounds]) (by norm_num [Interval.of_bounds])
    (by norm_num [Interval.of_bounds]) (by norm_num [Interval.of_bounds])
    (by norm_num [Interval.of_bounds]) (by norm_num [Interval.of_bounds])
  have hf := J.first.mem
  norm_num [J,differentialIntervals,Interval.of_bounds,Interval.point,Interval.add,
    Interval.sub,Interval.neg,Interval.mul,Interval.div,Interval.inv,Interval.square,Interval.cube] at hf
  linarith [hf.2]

theorem lower_affine_pivot {q : ℝ} (hq : q∈Icc (19577/5000:ℝ) (9789/2500)) :
    2*positionHalf q (cosine (3/25)) (sine (3/25)) (229/250)< -27/500 := by
  have hu : (229/250:ℝ)∈Icc (229/250) (229/250) := ⟨le_rfl,le_rfl⟩
  obtain ⟨hr,hU,hV,hY,hv,hw⟩ := radical_box hq hu
    (rl:=175395096/100000000) (ru:=175400799/100000000)
    (Ul:=165539844/100000000) (Uu:=165545885/100000000)
    (Yl:=145170473/100000000) (Yu:=145182958/100000000)
    (wl:=190125545/100000000) (wu:=190134406/100000000) (by norm_num)
  have hh : (3/25:ℝ)∈Icc (3/25) (3/25) := ⟨le_rfl,le_rfl⟩
  have hc := cosine_box hh (cl:=99287683/100000000) (cu:=99287685/100000000) (by norm_num)
  have hs : sine (3/25)∈Icc ((3/25:ℝ)*(99287683/100000000))
      ((3/25:ℝ)*(99287685/100000000)) := by
    rw [sine_eq]
    exact product_bounds hh hc (by norm_num) (by norm_num)
  let J := differentialIntervals (Interval.of_bounds hq) (Interval.of_bounds hu)
    (Interval.of_bounds hr) (Interval.of_bounds hU) (Interval.of_bounds hV)
    (Interval.of_bounds hY) (Interval.of_bounds hv) (Interval.of_bounds hw)
    (Interval.of_bounds hc) (Interval.of_bounds hs)
    (by norm_num [Interval.of_bounds]) (by norm_num [Interval.of_bounds])
    (by norm_num [Interval.of_bounds]) (by norm_num [Interval.of_bounds])
    (by norm_num [Interval.of_bounds]) (by norm_num [Interval.of_bounds])
  have hf := J.first.mem
  norm_num [J,differentialIntervals,Interval.of_bounds,Interval.point,Interval.add,
    Interval.sub,Interval.neg,Interval.mul,Interval.div,Interval.inv,Interval.square,Interval.cube] at hf
  linarith [hf.2]

end SquaresInCircles.Eight.StationaryPrimitives
end
end
end

section
/-!
## Derivative signs on the complete affine comparison curves

The three exact comparison values are
propagated by the actual chain rule and whole-interval derivative bounds.
The resulting signs hold for every radius and every angle in the stated
rectangle; a minimizer or a stationary tilt is not assumed here.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.StationaryPrimitives
open Stationary.FiveCornerGeometry Stationary.EnvelopeGeometry

def comparison (q a b h : ℝ) : ℝ :=
  2*positionHalf q (cosine h) (sine h) (a-b*h)

def comparisonDerivative (q a b h : ℝ) : ℝ :=
  -b*positionSecond q (cosine h) (sine h) (a-b*h)+
    mixedSecond q (cosine h) (sine h) (a-b*h)/(1+h^2)

/-- The derivative of `arctan`, from that of `sin/cos` (Mathlib's `Real.hasDerivAt_arctan` is
not imported here). -/
private theorem arctan_hasDerivAt (h : ℝ) : HasDerivAt Real.arctan (1+h^2)⁻¹ h := by
  have hc : Real.cos (Real.arctan h)≠0 := (cosine_pos h).ne'
  have htan : HasDerivAt (fun t => Real.sin t/Real.cos t)
      ((Real.cos (Real.arctan h)*Real.cos (Real.arctan h)-
        Real.sin (Real.arctan h)*(-Real.sin (Real.arctan h)))/
          Real.cos (Real.arctan h)^2) (Real.arctan h) :=
    (Real.hasDerivAt_sin _).div (Real.hasDerivAt_cos _) hc
  have h1 : Real.cos (Real.arctan h)*Real.cos (Real.arctan h)-
      Real.sin (Real.arctan h)*(-Real.sin (Real.arctan h))=1 := by
    linear_combination Real.sin_sq_add_cos_sq (Real.arctan h)
  have h2 : Real.cos (Real.arctan h)^2=1/(1+h^2) := by
    rw [Real.cos_arctan,div_pow,one_pow,Real.sq_sqrt (by positivity)]
  rw [h1,h2,one_div_one_div] at htan
  exact HasDerivAt.of_local_left_inverse Real.continuous_arctan.continuousAt htan
    (by positivity) (Filter.Eventually.of_forall fun y => by
      rw [← Real.tan_eq_sin_div_cos,Real.tan_arctan])

theorem comparison_hasDerivAt {q a b h : ℝ} (hd : SmoothDomain q (a-b*h)) :
    HasDerivAt (comparison q a b) (comparisonDerivative q a b h) h := by
  have dh : HasDerivAt (fun x => (Real.arctan x,a-b*x)) ((1+h^2)⁻¹,0-b*1) h :=
    (arctan_hasDerivAt h).prodMk ((hasDerivAt_const h a).sub ((hasDerivAt_id' h).const_mul b))
  have hh := (jointPosition_hasFDerivAt hd (Real.arctan h)).comp_hasDerivAt h dh
  have hfun : comparison q a b=jointPosition q ∘ (fun x => (Real.arctan x,a-b*x)) := by
    funext x
    rfl
  rw [hfun]
  refine hh.congr_deriv ?_
  simp only [pairDerivative_apply,comparisonDerivative,cosine,sine]
  ring

/-- Finite comparison obtained from the two strictly increasing
functions `f-L*x` and `U*x-f`. -/
theorem difference_bounds {f df : ℝ → ℝ} {a b L U : ℝ}
    (hd : ∀x∈Icc a b,HasDerivAt f (df x) x)
    (hb : ∀x∈Icc a b,L<df x ∧ df x<U)
    {x y : ℝ} (hx : x∈Icc a b) (hy : y∈Icc a b) (hxy : x≤y) :
    L*(y-x)≤f y-f x ∧ f y-f x≤U*(y-x) := by
  have hdl : ∀t∈Icc a b,HasDerivAt (fun t => f t-L*t) (df t-L*1) t :=
    fun t ht => (hd t ht).sub ((hasDerivAt_id' t).const_mul L)
  have hdu : ∀t∈Icc a b,HasDerivAt (fun t => U*t-f t) (U*1-df t) t :=
    fun t ht => ((hasDerivAt_id' t).const_mul U).sub (hd t ht)
  have hlow : StrictMonoOn (fun t => f t-L*t) (Icc a b) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc a b)
    · intro t ht
      exact (hdl t ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [(hdl t (interior_subset ht)).deriv]
      linarith [(hb t (interior_subset ht)).1]
  have hupp : StrictMonoOn (fun t => U*t-f t) (Icc a b) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc a b)
    · intro t ht
      exact (hdu t ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [(hdu t (interior_subset ht)).deriv]
      linarith [(hb t (interior_subset ht)).2]
  have hl := hlow.monotoneOn hx hy hxy
  have hu := hupp.monotoneOn hx hy hxy
  constructor <;> linarith

theorem upper_comparison_derivative {q h : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hh : h∈Icc (1/10:ℝ) (41/250)) :
    HasDerivAt (comparison q 1 (3/5)) (comparisonDerivative q 1 (3/5) h) h ∧
      -93/100<comparisonDerivative q 1 (3/5) h ∧
      comparisonDerivative q 1 (3/5) h<6/5 := by
  have hu : 1-(3/5)*h∈Icc (1127/1250:ℝ) (47/50) :=
    ⟨by linarith [hh.2],by linarith [hh.1]⟩
  have hu' : 1-(3/5)*h∈Icc (179/200:ℝ) (47/50) :=
    ⟨by linarith [hu.1],hu.2⟩
  have hdom := (radical_bounds hq hu').smoothDomain
    (by linarith [hq.2]) (by linarith [hu'.1])
  obtain ⟨huuL,huuU,hutL,hutU⟩ := affine_derivatives hq hu hh
  have hh2 := square_bounds hh (by norm_num)
  have hden : 1+h^2∈Icc (101/100:ℝ) (64181/62500) :=
    ⟨by linarith [hh2.1],by linarith [hh2.2]⟩
  have hquot := quotient_bounds ⟨hutL.le,hutU.le⟩ hden (by norm_num) (by norm_num)
  refine ⟨comparison_hasDerivAt hdom,?_,?_⟩ <;>
    dsimp [comparisonDerivative] <;> linarith [hquot.1,hquot.2]

theorem upper_comparison_positive {q h : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hh : h∈Icc (1/10:ℝ) (41/250)) : 0<comparison q 1 (3/5) h := by
  have hp : 183/5000<comparison q 1 (3/5) (13/100) := by
    have he : comparison q 1 (3/5) (13/100)=
        2*positionHalf q (cosine (13/100)) (sine (13/100)) (461/500) := by
      simp only [comparison]
      norm_num
    rw [he]
    exact upper_pivot hq
  have hpm : (13/100:ℝ)∈Icc (1/10) (41/250) := by norm_num
  have hd : ∀x∈Icc (1/10:ℝ) (41/250),
      HasDerivAt (comparison q 1 (3/5)) (comparisonDerivative q 1 (3/5) x) x :=
    fun x hx => (upper_comparison_derivative hq hx).1
  have hb : ∀x∈Icc (1/10:ℝ) (41/250),
      -93/100<comparisonDerivative q 1 (3/5) x ∧ comparisonDerivative q 1 (3/5) x<6/5 :=
    fun x hx => (upper_comparison_derivative hq hx).2
  by_cases hx : h≤13/100
  · have he := difference_bounds hd hb hh hpm hx
    linarith [he.2,hh.1]
  · have he := difference_bounds hd hb hpm hh (le_of_not_ge hx)
    linarith [he.1,hh.2]

theorem lower_fixed_negative {q h : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hh : h∈Icc (1/10:ℝ) (41/250)) : comparison q (179/200) 0 h<0 := by
  have hu : (179/200:ℝ)∈Icc (179/200) (47/50) := by norm_num
  have hdom := (radical_bounds hq hu).smoothDomain (by linarith [hq.2]) (by norm_num)
  have hd : ∀x∈Icc (1/10:ℝ) (41/250),
      HasDerivAt (comparison q (179/200) 0) (comparisonDerivative q (179/200) 0 x) x := by
    intro x hx
    apply comparison_hasDerivAt
    simpa only [zero_mul,sub_zero] using hdom
  have hm : StrictMonoOn (comparison q (179/200) 0) (Icc (1/10:ℝ) (41/250)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [(hd x (interior_subset hx)).deriv]
      have hf := (rectangle_derivatives hq hu (interior_subset hx)).2.2.1
      dsimp [comparisonDerivative]
      simp only [zero_mul,neg_zero,sub_zero,zero_add]
      exact div_pos (by linarith) (by positivity)
  have he := hm.monotoneOn hh (show (41/250:ℝ)∈Icc (1/10) (41/250) by norm_num) hh.2
  have hp := lower_fixed_endpoint hq
  norm_num [comparison] at he ⊢
  linarith

theorem lower_comparison_derivative {q h : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hh : h∈Icc (1/10:ℝ) (3/20)) :
    HasDerivAt (comparison q 1 (7/10)) (comparisonDerivative q 1 (7/10) h) h ∧
      -2<comparisonDerivative q 1 (7/10) h ∧
      comparisonDerivative q 1 (7/10) h<83/100 := by
  have hu : 1-(7/10)*h∈Icc (179/200:ℝ) (47/50) :=
    ⟨by linarith [hh.2],by linarith [hh.1]⟩
  have hdom := (radical_bounds hq hu).smoothDomain
    (by linarith [hq.2]) (by linarith [hu.1])
  obtain ⟨huuL,huuU,hutL,hutU⟩ := rectangle_derivatives hq hu
    (show h∈Icc (1/10:ℝ) (41/250) from ⟨hh.1,by linarith [hh.2]⟩)
  have hh2 := square_bounds hh (by norm_num)
  have hden : 1+h^2∈Icc (101/100:ℝ) (409/400) :=
    ⟨by linarith [hh2.1],by linarith [hh2.2]⟩
  have hquot := quotient_bounds ⟨hutL.le,hutU.le⟩ hden (by norm_num) (by norm_num)
  refine ⟨comparison_hasDerivAt hdom,?_,?_⟩ <;>
    dsimp [comparisonDerivative] <;> linarith [hquot.1,hquot.2]

theorem lower_comparison_negative {q h : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hh : h∈Icc (1/10:ℝ) (3/20)) : comparison q 1 (7/10) h<0 := by
  have hp : comparison q 1 (7/10) (3/25)< -27/500 := by
    have he : comparison q 1 (7/10) (3/25)=
        2*positionHalf q (cosine (3/25)) (sine (3/25)) (229/250) := by
      simp only [comparison]
      norm_num
    rw [he]
    exact lower_affine_pivot hq
  have hpm : (3/25:ℝ)∈Icc (1/10) (3/20) := by norm_num
  have hd : ∀x∈Icc (1/10:ℝ) (3/20),
      HasDerivAt (comparison q 1 (7/10)) (comparisonDerivative q 1 (7/10) x) x :=
    fun x hx => (lower_comparison_derivative hq hx).1
  have hb : ∀x∈Icc (1/10:ℝ) (3/20),
      -2<comparisonDerivative q 1 (7/10) x ∧ comparisonDerivative q 1 (7/10) x<83/100 :=
    fun x hx => (lower_comparison_derivative hq hx).2
  by_cases hx : h≤3/25
  · have he := difference_bounds hd hb hh hpm hx
    linarith [he.1,hh.1]
  · have he := difference_bounds hd hb hpm hh (le_of_not_ge hx)
    linarith [he.2,hh.2]

end SquaresInCircles.Eight.StationaryPrimitives
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.StationaryPrimitives
open Stationary.FiveCornerGeometry

theorem position_gradient_strictMono {q c s : ℝ}
    (hql : (79/40:ℝ)^2≤q) (hqu : q≤9789/2500)
    (hc : 0<c) (hs : 0≤ s) (hunit : c^2+s^2=1) :
    StrictMonoOn (fun u => 2*positionHalf q c s u) positionWindow := by
  apply strictMonoOn_of_deriv_pos (convex_Icc (87/100:ℝ) (11/10))
  · intro u hu
    have hd := (window_bounds hql hqu hu).smoothDomain (by linarith)
    exact (position_second_deriv (c:=c) (s:=s) hd).continuousAt.continuousWithinAt
  · intro u hu
    have hd := (window_bounds hql hqu (interior_subset hu)).smoothDomain (by linarith)
    rw [(position_second_deriv (c:=c) (s:=s) hd).deriv]
    exact hd.positionSecond_pos hc hs hunit

theorem arctan_mem_tiltInterval {h : ℝ} (hh : h∈Icc (1/10:ℝ) (41/250)) :
    Real.arctan h∈tiltInterval := by
  exact ⟨Real.arctan_pos.mpr (by linarith [hh.1]),
    Real.arctan_strictMono (by linarith [hh.2])⟩

/-- The first localization of the actual minimum, with both strict
inequalities obtained from nonstationary comparison positions. -/
theorem minimizingPosition_rectangle {q h : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hh : h∈Icc (1/10:ℝ) (41/250)) :
    179/200< minimizingPosition q (Real.arctan h) ∧
      minimizingPosition q (Real.arctan h)<1-(3/5)*h := by
  have hql : (79/40:ℝ)^2≤q := by nlinarith [hq.1]
  have ht := trig_bounds hh
  have hm := position_gradient_strictMono hql hq.2 (cosine_pos h)
    (by linarith [ht.s_lower] : 0≤ sine h) (unit h)
  have hu := windowMinimizer_mem q (cosine h) (sine h)
  change minimizingPosition q (Real.arctan h)∈positionWindow at hu
  have hz := minimizingPosition_root hql hq.2 (arctan_mem_tiltInterval hh)
  change 2*positionHalf q (cosine h) (sine h) (minimizingPosition q (Real.arctan h))=0 at hz
  have hlow : (179/200:ℝ)∈positionWindow := by norm_num [positionWindow]
  have hupp : 1-(3/5)*h∈positionWindow := by
    constructor <;> linarith [hh.1,hh.2]
  have hn := lower_fixed_negative hq hh
  simp only [comparison,zero_mul,sub_zero] at hn
  have hp := upper_comparison_positive hq hh
  change 0<2*positionHalf q (cosine h) (sine h) (1-(3/5)*h) at hp
  constructor
  · by_contra! hbad
    have he := hm.monotoneOn hu hlow hbad
    linarith
  · by_contra! hbad
    have he := hm.monotoneOn hupp hu hbad
    linarith

/-- The additional affine lower bound uses one further comparison on
`h≤.15`; beyond that endpoint the fixed lower bound is stronger. -/
theorem minimizingPosition_affine {q h : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hh : h∈Icc (1/10:ℝ) (41/250)) :
    1-(7/10)*h< minimizingPosition q (Real.arctan h) ∧
      minimizingPosition q (Real.arctan h)<1-(3/5)*h := by
  have hb := minimizingPosition_rectangle hq hh
  refine ⟨?_,hb.2⟩
  by_cases hcut : h≤3/20
  · have hql : (79/40:ℝ)^2≤q := by nlinarith [hq.1]
    have ht := trig_bounds hh
    have hm := position_gradient_strictMono hql hq.2 (cosine_pos h)
      (by linarith [ht.s_lower] : 0≤ sine h) (unit h)
    have hu := windowMinimizer_mem q (cosine h) (sine h)
    change minimizingPosition q (Real.arctan h)∈positionWindow at hu
    have hz := minimizingPosition_root hql hq.2 (arctan_mem_tiltInterval hh)
    change 2*positionHalf q (cosine h) (sine h) (minimizingPosition q (Real.arctan h))=0 at hz
    have hcmp : 1-(7/10)*h∈positionWindow := by
      constructor <;> linarith [hh.1]
    have hn := lower_comparison_negative hq ⟨hh.1,hcut⟩
    change 2*positionHalf q (cosine h) (sine h) (1-(7/10)*h)<0 at hn
    by_contra! hbad
    have he := hm.monotoneOn hu hcmp hbad
    linarith
  · have he : 1-(7/10)*h≤179/200 := by linarith
    exact he.trans_lt hb.1

theorem terminal_tangent {t : ℝ} (ht : t∈Icc (1/10:ℝ) (4/25)) :
    Real.tan t∈Icc (1/10:ℝ) (41/250) ∧ Real.arctan (Real.tan t)=t := by
  have htm : t∈Ioo (-(Real.pi/2)) (Real.pi/2) := by
    constructor <;> linarith [ht.1,ht.2,Real.pi_gt_three]
  have hc := Real.cos_pos_of_mem_Ioo htm
  have hs := Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.1] : 0<t)
    (by linarith [ht.2,Real.pi_gt_three] : t<Real.pi)
  have htan : 0≤Real.tan t := by
    rw [Real.tan_eq_sin_div_cos]
    exact (div_pos hs hc).le
  have hat := Real.arctan_tan htm.1 htm.2
  have hlow := CentralForbidden.atan_upper htan
  rw [hat] at hlow
  have ht2 := square_bounds ht (by norm_num)
  have hcos : (617/625:ℝ)≤Real.cos t := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := t),ht2.2]
  have hsin := Real.sin_le (show 0≤t by linarith [ht.1])
  have hu : Real.tan t≤41/250 := by
    rw [Real.tan_eq_sin_div_cos]
    apply (div_le_iff₀ hc).2
    nlinarith [ht.2]
  exact ⟨⟨ht.1.trans hlow,hu⟩,hat⟩

/-- The reusable actual-angle API.  The position is the geometric
minimum at this `t`, rather than the position at the stationary tilt. -/
theorem minimizingPosition_terminal {q t : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (ht : t∈Icc (1/10:ℝ) (4/25)) :
    179/200< minimizingPosition q t ∧
    1-(7/10)*Real.tan t< minimizingPosition q t ∧
    minimizingPosition q t<1-(3/5)*Real.tan t ∧
    minimizingPosition q t<47/50 := by
  obtain ⟨hh,hat⟩ := terminal_tangent ht
  have hr := minimizingPosition_rectangle hq hh
  have ha := minimizingPosition_affine hq hh
  rw [hat] at hr ha
  exact ⟨hr.1,ha.1,ha.2,by linarith [ha.2,hh.1]⟩

end SquaresInCircles.Eight.StationaryPrimitives
end
end
end

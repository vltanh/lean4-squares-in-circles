module

public import SquaresInCircles.Eight.Owners.Stationary.ComparisonPivots
public import SquaresInCircles.Eight.Stationary.Envelope

/-!
# Eight squares: derivative signs on the complete affine comparison curves

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

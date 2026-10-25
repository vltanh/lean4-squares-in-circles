module

public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.TotallySplit
public import SquaresInCircles.Eight.Owners.GA.Negative.DEHighLateReserve

/-!
# Eight squares: the complete high-DE shape argument on the actual tangent interval

The early
and late estimates are joined at the original angle .55. The early
split at 3x^2=1 is the sign split of the exact derivative formula.
No subdivision of the original geometric angle domain is introduced.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEHighShape
open Candidate Secondary PositiveAngularEnvelope
open NegativeAPositiveTD.SecantCoordinate

/-- The original coefficient domain sufficient for either high-DE family.
The correlation and the upper ordinary coefficient are needed only when
the original total reaches the late interval. -/
structure Domain (bt3 : Bool) (c p q θ : ℝ) : Prop where
  total : θ∈Icc 0 frameCap
  coefficient : c∈Icc 0 Early.C
  smaller_pos : 0<p
  ordered : p≤q
  ratio : (2/3)*q≤p
  larger_lower : (431/500:ℝ)<q
  late_correlation : (11/20:ℝ)≤θ → c≤863/1000+Late.rate bt3*(frameCap-θ)
  late_larger : (11/20:ℝ)≤θ → q≤1

theorem early_positive {c p q θ x : ℝ} (bt3 : Bool)
    (H : Domain bt3 c p q θ) (hx : x∈Icc 0 (Real.tan θ))
    (hearly : x≤Real.tan (11/20:ℝ)) :
    0<baseThird c x+numerator p q (θ-Real.arctan x) x/(1+x^2)^3 := by
  have hs := arctan_interval H.total hx
  have hd : θ-Real.arctan x∈Icc 0 frameCap :=
    ⟨by linarith [hs.2],by linarith [H.total.2,hs.1]⟩
  have hxmax : x≤307/500 := hearly.trans TrigonometricBounds.transition.2.le
  have hbase := Early.lower H.coefficient
    (show x∈Icc (0:ℝ) (3/4) from ⟨hx.1,by linarith⟩)
  have hden : 0<(1+x^2)^3 := by positivity
  have hq := H.smaller_pos.trans_le H.ordered
  have hqp : q≤2*p := by linarith [H.ratio]
  have hnum : (6/25)*(1+x^2)^3<numerator p q (θ-Real.arctan x) x := by
    by_cases hsign : 3*x^2≤1
    · have hn := numerator_early_low H.smaller_pos H.ordered H.ratio hd hx.1 hsign
      have hD : (1+x^2)^3≤(64/27:ℝ) := by
        have hh := pow_le_pow_left₀ (by positivity : 0≤1+x^2)
          (show 1+x^2≤(4/3:ℝ) by linarith) 3
        norm_num at hh
        exact hh
      nlinarith [H.larger_lower]
    · have hxlower : (577/1000:ℝ)<x := by
        by_contra h
        have h2 : x^2≤(577/1000)^2 := pow_le_pow_left₀ hx.1 (le_of_not_gt h) 2
        linarith
      have hslow : (523/1000:ℝ)≤Real.arctan x := by
        by_contra hh
        have hstan := tan_monotone
          (show Real.arctan x∈Icc 0 frameCap from ⟨hs.1,hs.2.trans H.total.2⟩)
          (show (523/1000:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
          (lt_of_not_ge hh).le
        rw [Real.tan_arctan] at hstan
        linarith [TrigonometricBounds.middle_left]
      have hdshort : θ-Real.arctan x∈Icc (0:ℝ) (177/1000) :=
        ⟨hd.1,by
          have ht2 := H.total.2
          simp only [frameCap] at ht2
          linarith⟩
      have hn := numerator_early_middle H.smaller_pos H.ordered hqp hdshort
        ⟨hx.1,hxmax⟩ (lt_of_not_ge hsign).le
      have hx2 := pow_le_pow_left₀ hx.1 hxmax 2
      have hD := pow_le_pow_left₀ (by positivity : 0≤1+x^2)
        (show 1+x^2≤1+(307/500:ℝ)^2 by linarith) 3
      norm_num at hD
      nlinarith [H.larger_lower]
  have hquot : (6/25:ℝ)<numerator p q (θ-Real.arctan x) x/(1+x^2)^3 :=
    (lt_div_iff₀ hden).2 hnum
  linarith

theorem third_positive {c p q θ x : ℝ} (bt3 : Bool)
    (H : Domain bt3 c p q θ) (hx : x∈Icc 0 (Real.tan θ)) :
    0<pureThird 1 c p q θ x := by
  have hs := arctan_interval H.total hx
  by_cases hearly : x≤Real.tan (11/20:ℝ)
  · simpa only [pureThird,one_mul] using early_positive bt3 H hx hearly
  · have hlate : x∈Icc (Real.tan (11/20:ℝ)) (Real.tan frameCap) :=
      ⟨(lt_of_not_ge hearly).le,hx.2.trans
        (tan_monotone H.total (show frameCap∈Icc 0 frameCap by norm_num [frameCap]) H.total.2)⟩
    have hsd := (Late.domain hlate).2
    have hθlate : (11/20:ℝ)≤θ := hsd.1.trans hs.2
    have hcorrelation : c≤Late.coefficient bt3 x := by
      have hm := mul_le_mul_of_nonneg_left
        (show frameCap-θ≤frameCap-Real.arctan x by linarith [hs.2]) (Late.rate_bounds bt3).1
      dsimp [Late.coefficient]
      linarith [H.late_correlation hθlate]
    have hd : θ-Real.arctan x∈Icc (0:ℝ) (3/20) :=
      ⟨by linarith [hs.2],by
        have ht2 := H.total.2
        simp only [frameCap] at ht2
        linarith [hsd.1]⟩
    have hh := Late.combined_positive bt3 H.smaller_pos H.ordered
      (show q≤2*p by linarith [H.ratio,H.smaller_pos]) (H.late_larger hθlate)
      H.coefficient.1 hcorrelation hd hlate
    simpa only [pureThird,one_mul] using hh

/-- A convex first derivative which is nonpositive at its right endpoint
makes the original function attain its minimum at an endpoint. -/
theorem endpoint_of_convex_first {f u : ℝ→ℝ} {t s : ℝ}
    (ht : 0≤t) (hs : s∈Icc 0 t)
    (hf : ∀x∈Icc 0 t,HasDerivAt f (u x) x)
    (hu : ConcaveOn ℝ (Icc 0 t) (fun x => -u x)) (hut : u t≤0) :
    min (f 0) (f t)≤f s := by
  have hright {a b : ℝ} (ha : a∈Icc 0 t) (hb : b∈Icc a t)
      (hderiv : u a≤0) : u b≤0 := by
    have hh := hu.min_le_of_mem_Icc ha ⟨ht,le_rfl⟩ hb
    have hlo : 0≤ min (-u a) (-u t) := le_min (by linarith) (by linarith)
    linarith
  by_cases hsign : u s≤0
  · have hm : AntitoneOn f (Icc s t) := by
      apply antiOn_of_hasDeriv_nonpos
      · intro x hx
        exact (hf x ⟨hs.1.trans hx.1,hx.2⟩).continuousAt.continuousWithinAt
      · intro x hx
        exact hf x ⟨hs.1.trans hx.1.le,hx.2.le⟩
      · intro x hx
        exact hright hs (Ioo_subset_Icc_self hx) hsign
    exact (min_le_right _ _).trans (hm ⟨le_rfl,hs.2⟩ ⟨hs.2,le_rfl⟩ hs.2)
  · have hm : MonotoneOn f (Icc 0 s) := by
      apply monoOn_of_hasDeriv_nonneg
      · intro x hx
        exact (hf x ⟨hx.1,hx.2.trans hs.2⟩).continuousAt.continuousWithinAt
      · intro x hx
        exact hf x ⟨hx.1.le,hx.2.le.trans hs.2⟩
      · intro x hx
        by_contra hh
        have hnon : u x≤0 := (lt_of_not_ge hh).le
        exact hsign (hright ⟨hx.1.le,hx.2.le.trans hs.2⟩ ⟨hx.2.le,hs.2⟩ hnon)
    exact (min_le_left _ _).trans (hm ⟨le_rfl,hs.1⟩ ⟨hs.1,le_rfl⟩ hs.1)

/-- Both original high-DE coefficient families have the same two intrinsic
secant-coordinate endpoints once their right derivative is nonpositive. -/
theorem pure_endpoint_minimum {B c p q θ x : ℝ} (bt3 : Bool)
    (H : Domain bt3 c p q θ) (hx : x∈Icc 0 (Real.tan θ))
    (hright : pureFirst 1 c p q θ (Real.tan θ)≤0) :
    min (pure B 1 c p q θ 0) (pure B 1 c p q θ (Real.tan θ))≤
      pure B 1 c p q θ x := by
  have hd {x : ℝ} (hx : x∈Icc 0 (Real.tan θ)) : θ-Real.arctan x∈Icc 0 frameCap := by
    have hs := arctan_interval H.total hx
    exact ⟨by linarith [hs.2],by linarith [hs.1,H.total.2]⟩
  have hq := H.smaller_pos.trans_le H.ordered
  have hconvex : ConcaveOn ℝ (Icc 0 (Real.tan θ))
      (fun x => -pureFirst 1 c p q θ x) := by
    apply concave_of_deriv2
      (fun x hx => (pureFirst_hasDerivAt H.smaller_pos hq (hd hx)).neg)
      (fun x hx => (pureSecond_hasDerivAt H.smaller_pos hq (hd hx)).neg)
    intro x hx
    linarith [third_positive bt3 H hx]
  exact endpoint_of_convex_first (tan_nonnegative H.total) hx
    (fun x hx => pure_hasDerivAt H.smaller_pos hq (hd hx)) hconvex hright

end SquaresInCircles.Eight.GlobalGA.NegativeDEHighShape

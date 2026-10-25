module

public import SquaresInCircles.Eight.TableFree.NegativeCoreEEntry

/-!
# The growing flat-core interval for positive DE and negative EH

Uncompiled source. The two original primary separators give lower and
upper bounds on E's tangent. Both bounds move inward with E's frame;
their gap increases on the entire short interval. The explicit endpoint
uses the original D and H and remains contained at the original q.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.NegativeCoreE

def lowerGap (a t : ℝ) : ℝ :=
  1/2-(a-1/2)/Real.cos t-(1/12)*(Real.sin t/Real.cos t)

def upperGap (a t : ℝ) : ℝ :=
  -1/2+(a-1/2)/Real.cos t-(13/12)*(Real.sin t/Real.cos t)

def lowerRate (a t : ℝ) : ℝ :=
  ((a-1/2)*Real.sin t+1/12)/(Real.cos t)^2

def upperRate (a t : ℝ) : ℝ :=
  (13/12-(a-1/2)*Real.sin t)/(Real.cos t)^2

theorem short_trig {t : ℝ} (ht : t∈Icc 0 (1/4 : ℝ)) :
    31/32≤Real.cos t ∧ (Real.cos t)^2≤1 ∧
      93/100<(Real.cos t)^2 ∧ 0≤Real.sin t ∧ Real.sin t≤1/4 := by
  have hc := Real.one_sub_sq_div_two_le_cos (x := t)
  have htu := pow_le_pow_left₀ ht.1 ht.2 2
  have hcL : 31/32≤Real.cos t := by norm_num at htu; linarith
  have hcu := Real.cos_le_one t
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi ht.1
    (by linarith [ht.2,Real.pi_gt_three])
  refine ⟨hcL,?_,?_,hs0,(Real.sin_le ht.1).trans ht.2⟩ <;> nlinarith

theorem lowerGap_derivative {a t : ℝ} (ht : t∈Icc 0 (1/4 : ℝ)) :
    HasDerivAt (lowerGap a) (-lowerRate a t) t := by
  have hc : Real.cos t≠0 := ne_of_gt (by linarith [(short_trig ht).1])
  have hd := (((hasDerivAt_const t (1/2 : ℝ)).sub
    ((hasDerivAt_const t (a-1/2)).div (Real.hasDerivAt_cos t) hc)).sub
    (((Real.hasDerivAt_sin t).div (Real.hasDerivAt_cos t) hc).const_mul (1/12 : ℝ)))
  convert hd using 1
  · rfl
  · dsimp [lowerRate]
    field_simp [hc]
    nlinarith [Real.sin_sq_add_cos_sq t]

theorem upperGap_derivative {a t : ℝ} (ht : t∈Icc 0 (1/4 : ℝ)) :
    HasDerivAt (upperGap a) (-upperRate a t) t := by
  have hc : Real.cos t≠0 := ne_of_gt (by linarith [(short_trig ht).1])
  have hd := (((hasDerivAt_const t (-1/2 : ℝ)).add
    ((hasDerivAt_const t (a-1/2)).div (Real.hasDerivAt_cos t) hc)).sub
    (((Real.hasDerivAt_sin t).div (Real.hasDerivAt_cos t) hc).const_mul (13/12 : ℝ)))
  convert hd using 1
  · rfl
  · dsimp [upperRate]
    field_simp [hc]
    nlinarith [Real.sin_sq_add_cos_sq t]

/-- These rational rate bounds apply to every original contained anchor;
neither anchor is replaced by a diagonal or by the upper-radius circle. -/
theorem rates {a t : ℝ} (ha : 1/2<a ∧ a<283/200)
    (ht : t∈Icc 0 (1/4 : ℝ)) :
    0<lowerRate a t ∧ lowerRate a t<17/50 ∧ 17/20<upperRate a t := by
  obtain ⟨hc,hc2U,hc2L,hs0,hsU⟩ := short_trig ht
  have hcos2 : 0<(Real.cos t)^2 := by linarith
  have hprod0 := mul_nonneg (show 0≤a-1/2 by linarith [ha.1]) hs0
  have hprodU : (a-1/2)*Real.sin t≤183/800 := by
    have hh := mul_le_mul (show a-1/2≤183/200 by linarith [ha.2]) hsU
      hs0 (by norm_num : (0:ℝ)≤183/200)
    norm_num at hh
    exact hh
  refine ⟨div_pos (by linarith) hcos2,?_,?_⟩
  · apply (div_lt_iff₀ hcos2).2
    nlinarith
  · apply (lt_div_iff₀ hcos2).2
    nlinarith

theorem growing_gap {aD aH p n : ℝ}
    (hD : 1/2<aD ∧ aD<283/200) (hH : 1/2<aH ∧ aH<283/200)
    (hp : 0≤p ∧ p≤n) (hn : n≤1/4) :
    MonotoneOn (fun τ : ℝ => upperGap aH (n-τ)) (Icc 0 p) ∧
      MonotoneOn (fun τ : ℝ => upperGap aH (n-τ)-lowerGap aD (p-τ)) (Icc 0 p) := by
  have hparams {τ : ℝ} (hτ : τ∈Icc 0 p) :
      n-τ∈Icc 0 (1/4 : ℝ) ∧ p-τ∈Icc 0 (1/4 : ℝ) := by
    constructor <;> constructor <;> linarith [hτ.1,hτ.2,hp.1,hp.2]
  have hupper {τ : ℝ} (hτ : τ∈Icc 0 p) :
      HasDerivAt (fun x => upperGap aH (n-x)) (upperRate aH (n-τ)) τ := by
    have hd := (upperGap_derivative (a := aH) (hparams hτ).1).comp τ
      ((hasDerivAt_id τ).const_sub n)
    exact hd.congr_deriv (by ring)
  have hgap {τ : ℝ} (hτ : τ∈Icc 0 p) :
      HasDerivAt (fun x => upperGap aH (n-x)-lowerGap aD (p-x))
        (upperRate aH (n-τ)-lowerRate aD (p-τ)) τ := by
    have hd := (lowerGap_derivative (a := aD) (hparams hτ).2).comp τ
      ((hasDerivAt_id τ).const_sub p)
    exact ((hupper hτ).sub hd).congr_deriv (by ring)
  constructor
  · apply StrictMonoOn.monotoneOn
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 p)
    · intro τ hτ
      exact (hupper hτ).continuousAt.continuousWithinAt
    · intro τ hτ
      rw [(hupper (interior_subset hτ)).deriv]
      have hr := (rates hH (hparams (interior_subset hτ)).1).2.2
      linarith
  · apply StrictMonoOn.monotoneOn
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 p)
    · intro τ hτ
      exact (hgap hτ).continuousAt.continuousWithinAt
    · intro τ hτ
      rw [(hgap (interior_subset hτ)).deriv]
      have hru := (rates hH (hparams (interior_subset hτ)).1).2.2
      have hrl := (rates hD (hparams (interior_subset hτ)).2).2.1
      linarith

theorem DE_margin {p b : ℝ} (D : SignedPoint) (hp : p∈Icc 0 (1/4 : ℝ)) :
    quarterProjection D (SignedPoint.flat (-b)) p 3-edgeWidth p=
      (b-lowerGap D.a p)*Real.cos p := by
  have hc : Real.cos p≠0 := ne_of_gt (by linarith [(short_trig hp).1])
  rw [edgeWidth_positive_formula ⟨hp.1,by linarith [hp.2]⟩]
  simp [quarterProjection,SignedPoint.flat]
  dsimp [lowerGap]
  field_simp [hc]
  ring

theorem EH_margin {n b : ℝ} (H : SignedPoint) (hn : n∈Icc 0 (1/4 : ℝ)) :
    quarterProjection (SignedPoint.flat (-b)) H (-n) 1-edgeWidth (-n)=
      (upperGap H.a n-b)*Real.cos n := by
  have hc : Real.cos n≠0 := ne_of_gt (by linarith [(short_trig hn).1])
  rw [edgeWidth_negative_formula ⟨hn.1,by linarith [hn.2]⟩]
  simp only [quarterProjection,Matrix.cons_val_one,SignedPoint.flat,Real.sin_neg,Real.cos_neg]
  dsimp [upperGap]
  field_simp [hc]
  ring

structure NegativeEHEndpoint (q : ℝ) (D E H : SignedPoint) (p n : ℝ) where
  point : SignedPoint
  sorted : point.Sorted
  nonpos : point.y≤0
  core : point.Core
  contained : point.Contained q
  flat : point.a=7/12
  tangent_bound : -point.y<39/250
  negative_remaining : 0<n-p
  DE3 : quarterFeasible D point 0 3
  DE2 : quarterFeasible D point 0 2
  EH1 : quarterFeasible point H (-(n-p)) 1

/-- The actual endpoint has frame theta_D. Its tangent is the maximum
of the old tangent and the aligned DE lower bound; the whole-interval
gap estimate proves EH1 there. Only original-q containment is needed. -/
theorem negative_EH_endpoint {q p n : ℝ} {D E H : SignedPoint}
    (hqL : qLow≤q) (hqU : q≤qCap)
    (hDs : D.Sorted) (hDcore : D.AvoidsCore) (hDo : D.Outer q)
    (hHs : H.Sorted) (hHcore : H.AvoidsCore) (hHy : 0≤H.y) (hHc : H.Contained q)
    (hEs : E.Sorted) (hEy : E.y≤0) (hEc : E.Core)
    (hn : n∈Ioc 0 frameCap) (hp : 0<p ∧ p<n)
    (hDE : quarterFeasible D E p 3) (hEH : quarterFeasible E H (-n) 1)
    (hnot : ¬quarterFeasible E H (-n) 0) :
    Nonempty (NegativeEHEndpoint q D E H p n) := by
  obtain ⟨hflat,hbU,hnU⟩ := genuine_negative_flat hEs hEy hEc hHs hHy hHc hqU hn hEH hnot
  let b := -E.y
  have hb0 : 0≤b := neg_nonneg.mpr hEy
  have hEeq : E=SignedPoint.flat (-b) := by
    apply SignedPoint.ext <;> simp [SignedPoint.flat,b,hflat]
  have hp' : p∈Icc 0 (1/4 : ℝ) := ⟨hp.1.le,hp.2.le.trans hnU.le⟩
  have hn' : n∈Icc 0 (1/4 : ℝ) := ⟨hn.1.le,hnU.le⟩
  have hD : 1/2<D.a ∧ D.a<283/200 :=
    ⟨SignedPoint.primary_gt_half hDs hDcore,
      (SignedPoint.coordinate_bounds hDs hDcore hDo.le hqU).2.1⟩
  have hH : 1/2<H.a ∧ H.a<283/200 :=
    ⟨SignedPoint.primary_gt_half hHs hHcore,
      (SignedPoint.coordinate_bounds hHs hHcore hHc hqU).2.1⟩
  have hL : lowerGap D.a p≤b := by
    have hm := sub_nonneg.mpr (show edgeWidth p≤quarterProjection D (SignedPoint.flat (-b)) p 3 by
      rw [← hEeq]; exact hDE)
    rw [DE_margin D hp'] at hm
    have hc : 0<Real.cos p := by linarith [(short_trig hp').1]
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_right hc).1 hm)
  have hU : b≤upperGap H.a n := by
    have hm := sub_nonneg.mpr (show edgeWidth (-n)≤quarterProjection (SignedPoint.flat (-b)) H (-n) 1 by
      rw [← hEeq]; exact hEH)
    rw [EH_margin H hn'] at hm
    have hc : 0<Real.cos n := by linarith [(short_trig hn').1]
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_right hc).1 hm)
  have hmono := growing_gap hD hH ⟨hp.1.le,hp.2.le⟩ hnU.le
  have hz : (0:ℝ)∈Icc 0 p := ⟨le_rfl,hp.1.le⟩
  have hpI : p∈Icc 0 p := ⟨hp.1.le,le_rfl⟩
  have hUmono : upperGap H.a n≤upperGap H.a (n-p) := by
    simpa using hmono.1 hz hpI hp.1.le
  have hgap : upperGap H.a n-lowerGap D.a p≤
      upperGap H.a (n-p)-lowerGap D.a 0 := by
    simpa using hmono.2 hz hpI hp.1.le
  let b' := max b (lowerGap D.a 0)
  have hb'0 : 0≤b' := hb0.trans (le_max_left _ _)
  have hb'U : b'≤upperGap H.a (n-p) := by
    apply max_le
    · exact hU.trans hUmono
    · linarith
  have hL0 : lowerGap D.a 0=1-D.a := by norm_num [lowerGap]; ring
  have hDlower := (uniform_circle_reserves hqL hqU).1.trans_le
    (SignedPoint.outer_bounds hDs hDo).1
  have hb'cut : b'<39/250 := by
    apply max_lt_iff.mpr
    exact ⟨hbU,by rw [hL0]; linarith⟩
  have habs : |-b'|≤1/2 := by rw [abs_neg,abs_of_nonneg hb'0]; linarith
  have hDEnew : quarterFeasible D (SignedPoint.flat (-b')) 0 3 ∧
      quarterFeasible D (SignedPoint.flat (-b')) 0 2 := by
    have hl : 1-D.a≤b' := by rw [← hL0]; exact le_max_right _ _
    constructor <;>
      simp [quarterFeasible,quarterProjection,SignedPoint.flat,edgeWidth,pairWidth] <;> linarith
  have hEHnew : quarterFeasible (SignedPoint.flat (-b')) H (-(n-p)) 1 := by
    apply sub_nonneg.mp
    rw [EH_margin H (show n-p∈Icc 0 (1/4 : ℝ) by constructor <;> linarith [hnU,hp.1,hp.2])]
    exact mul_nonneg (sub_nonneg.mpr hb'U)
      (by linarith [(short_trig (show n-p∈Icc 0 (1/4 : ℝ) by
        constructor <;> linarith [hnU,hp.1,hp.2])).1])
  exact ⟨{
    point := SignedPoint.flat (-b')
    sorted := SignedPoint.flat_sorted habs
    nonpos := neg_nonpos.mpr hb'0
    core := SignedPoint.flat_on_core habs
    contained := SignedPoint.flat_contained hqL habs
    flat := rfl
    tangent_bound := by simpa [SignedPoint.flat] using hb'cut
    negative_remaining := sub_pos.mpr hp.2
    DE3 := hDEnew.1
    DE2 := hDEnew.2
    EH1 := hEHnew }⟩

end SquaresInCircles.Eight.TableFree.NegativeCoreE

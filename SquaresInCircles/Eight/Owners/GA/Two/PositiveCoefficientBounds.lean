module

public import SquaresInCircles.Eight.Owners.GA.Two.PositiveCoefficientCalculus

/-!
# Eight squares: the low and high coefficient derivative reserves

The
low functions have derivative above -12/25.  On the high interval the
two remaining functions increase; the displayed cubic reserve has a
convex derivative and a negative final derivative, so its minimum is
one of its two positive endpoint values.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalGA.TwoPositive.Coefficient
open Secondary PositiveAngularEnvelope PairNormCalculus OrdinaryCurvatureBounds
open VaryingBFunctions SplitConcavityTools

theorem cap_cosine_lower : (478/625:ℝ)<Real.cos frameCap := by
  have hh := cos_lower_six (show (0:ℝ)≤frameCap by norm_num [frameCap])
  norm_num [frameCap] at hh ⊢
  linarith

theorem affine_low_derivative {l s w m : ℝ}
    (hl : 0<l) (hm : 0< m) (hratio : m≤(3/2)*l) (hs : |s|≤frameCap)
    (hw : Real.cos frameCap-1≤w) (hpos : 0<s→0≤w) :
    -(12/25:ℝ)<affineD l s w m := by
  by_cases hsn : 0<s
  · have hn := mul_le_mul_of_nonneg_left (norm_slope_le_one hl hm hs)
      (Real.sqrt_nonneg qCap)
    have hw0 := hpos hsn
    dsimp [affineD]
    linarith [radius_bounds.2]
  · have ht : -s∈Icc 0 frameCap :=
      ⟨by linarith [le_of_not_gt hsn],by simpa [abs_of_nonpos (le_of_not_gt hsn)] using hs⟩
    have hn := negative_slope_upper hl hm hratio ht
    simp only [neg_neg] at hn
    dsimp [affineD]
    linarith [cap_cosine_lower]

theorem shifted_affine_monotone {l s w b L U : ℝ}
    (hl : 0<l) (hL : 0<L) (hU : U≤(3/2)*l) (hs : |s|≤frameCap)
    (hw : Real.cos frameCap-1≤w) (hpos : 0<s→0≤w) :
    MonotoneOn (fun m => affineBranch l s w b m+(12/25)*m) (Icc L U) := by
  have hd (m : ℝ) (hm : m∈Icc L U) :
      HasDerivAt (fun x => affineBranch l s w b x+(12/25)*x)
        (affineD l s w m+12/25) m := by
    have h := (affine_derivative (w:=w) (b:=b) hl (hL.trans_le hm.1) hs).fun_add
      ((hasDerivAt_id' m).const_mul (12/25:ℝ))
    exact h.congr_deriv (by ring)
  apply monoOn_of_hasDeriv_nonneg
  · intro m hm
    exact (hd m hm).continuousAt.continuousWithinAt
  · intro m hm
    exact hd m (Ioo_subset_Icc_self hm)
  · intro m hm
    have hh := affine_low_derivative hl (hL.trans hm.1) (hm.2.le.trans hU) hs hw hpos
    linarith

theorem H_shifted_low {l s g e L U : ℝ}
    (hl : 0<l) (hL : 0<L) (hU : U≤(3/2)*l) (hs : |s|≤frameCap)
    (hg : 0≤g) (he : e≤0) (heLow : Real.cos frameCap-1≤e)
    (hePos : 0<s→e=0) :
    ConcaveOn ℝ (Icc L U) (fun m => H l s g e m+(12/25)*m) ∧
      MonotoneOn (fun m => H l s g e m+(12/25)*m) (Icc L U) := by
  have hge : e≤g := he.trans hg
  have hgc : Real.cos frameCap-1≤g := by linarith [Real.cos_le_one frameCap]
  have hf := H_concave (U:=U) hl hL hs hge
  constructor
  · have hlin : ConcaveOn ℝ (Icc L U) (fun m : ℝ => (12/25)*m) :=
      concave_of_deriv2 (f':=fun _ => 12/25) (f'':=fun _ => 0)
        (fun x _ => by simpa using (hasDerivAt_id' x).const_mul (12/25:ℝ))
        (fun x _ => hasDerivAt_const x _) (fun _ _ => le_rfl)
    exact hf.add hlin
  · have h₁ := shifted_affine_monotone (b:=e) hl hL hU hs hgc (fun _ => hg)
    have h₂ := shifted_affine_monotone (b:=g) hl hL hU hs heLow
      (fun hh => by rw [hePos hh])
    intro x hx y hy hxy
    show H l s g e x+(12/25)*x≤H l s g e y+(12/25)*y
    rw [H_minimum hge,H_minimum hge,minimum_add,minimum_add]
    exact min_le_min (h₁ hx hy hxy) (h₂ hx hy hxy)

def highP (u : ℝ) : ℝ :=
  11811/250000+(23943/6250)*u-(42803/5000)*u^2+(23/5)*u^3
def highPD (u : ℝ) : ℝ := 23943/6250-(42803/2500)*u+(69/5)*u^2
def highPDD (u : ℝ) : ℝ := -42803/2500+(138/5)*u

theorem highP_derivative (u : ℝ) : HasDerivAt highP (highPD u) u := by
  have h := ((((hasDerivAt_id' u).const_mul (23943/6250:ℝ)).const_add
    (11811/250000:ℝ)).fun_sub ((hasDerivAt_pow 2 u).const_mul (42803/5000:ℝ))).fun_add
      ((hasDerivAt_pow 3 u).const_mul (23/5:ℝ))
  unfold highP
  exact h.congr_deriv (by norm_num [highPD]; ring)

theorem highPD_derivative (u : ℝ) : HasDerivAt highPD (highPDD u) u := by
  have h := (((hasDerivAt_id' u).const_mul (42803/2500:ℝ)).const_sub
    (23943/6250:ℝ)).fun_add ((hasDerivAt_pow 2 u).const_mul (69/5:ℝ))
  unfold highPD
  exact h.congr_deriv (by norm_num [highPDD]; ring)

theorem highPDD_derivative (u : ℝ) : HasDerivAt highPDD (138/5) u := by
  have h := ((hasDerivAt_id' u).const_mul (138/5:ℝ)).const_add (-42803/2500:ℝ)
  unfold highPDD
  exact h.congr_deriv (by ring)

theorem highPD_convex : ConvexOn ℝ (Icc 0 (129/200:ℝ)) highPD := by
  have hh : ConcaveOn ℝ (Icc 0 (129/200:ℝ)) (fun u => -highPD u) :=
    concave_of_deriv2 (fun u _ => (highPD_derivative u).fun_neg)
      (fun u _ => (highPDD_derivative u).fun_neg) (fun _ _ => by norm_num)
  have h2 := hh.neg
  have he : (-fun u => -highPD u)=highPD := by funext u; simp
  rwa [he] at h2

theorem highP_positive {u : ℝ} (hu : u∈Icc 0 (129/200:ℝ)) : 0<highP u := by
  have hmin := minimum_of_convex_derivative (fun u _ => highP_derivative u)
    highPD_convex (by norm_num [highPD]) hu
  have hleft : 0<highP 0 := by norm_num [highP]
  have hright : 0<highP (129/200) := by norm_num [highP]
  exact (lt_min hleft hright).trans_le hmin

theorem high_endpoint_fraction {t : ℝ} (ht : t∈Icc 0 frameCap) :
    R*fraction (23/20) (Real.sin t)<Real.cos t+1/2 := by
  let u : ℝ := Real.sin t
  have hu : u∈Icc 0 (129/200:ℝ) :=
    ⟨(transport_trig ht).2.2.1,by dsimp [u]; linarith [(transport_trig ht).2.2.2.1]⟩
  have hu' : u∈Icc 0 frameCap := sin_mem ht
  have hn := root_pos (23/20) hu'
  have hn2 := root_sq (23/20) hu'
  have hc : 0<Real.cos t := transport_cos_pos (by rw [abs_of_nonneg ht.1]; exact ht.2)
  have hunit : (Real.cos t)^2=1-u^2 := by
    dsimp [u]
    nlinarith [Real.sin_sq_add_cos_sq t]
  have hC : 0≤Real.cos t-1+u^2 := by
    have hh := mul_nonneg hc.le (sub_nonneg.mpr (Real.cos_le_one t))
    nlinarith only [hunit,hh]
  have hid : (Real.cos t+1/2)^2*(root (23/20) u)^2-
      (R*((23/20)-u))^2=highP u+
        (Real.cos t-1+u^2)*(1+(23/20:ℝ)^2-2*(23/20)*u) := by
    rw [hn2,mul_pow,radius_sq]
    have hsq : (Real.cos t+1/2)^2=5/4-u^2+Real.cos t := by nlinarith only [hunit]
    rw [hsq]
    norm_num [highP,qCap]
    ring
  have hproduct := mul_nonneg hC (radicand_pos (23/20) hu').le
  have hreserve := highP_positive hu
  have hsquare : (R*((23/20)-u))^2<
      (Real.cos t+1/2)^2*(root (23/20) u)^2 := by linarith
  have hh := quotient_lt_of_square hn (by linarith : 0<Real.cos t+1/2) hsquare
  dsimp [fraction,u] at hh ⊢
  convert hh using 1 <;> ring

theorem high_negative_slope {l m t : ℝ} (hl : 0<l) (_hm : 0< m)
    (hratio : m≤(23/20)*l) (ht : t∈Icc 0 frameCap) :
    R*normD l (-t) m<Real.cos t+1/2 := by
  have hr : m/l≤23/20 := (div_le_iff₀ hl).mpr hratio
  have hmono := fraction_monotone (L:=m/l) (U:=23/20) (sin_mem ht)
    (show m/l∈Icc (m/l) (23/20) from ⟨le_rfl,hr⟩)
    (show (23/20:ℝ)∈Icc (m/l) (23/20) from ⟨hr,le_rfl⟩) hr
  have hp := mul_le_mul_of_nonneg_left hmono (Real.sqrt_nonneg qCap)
  rw [norm_slope_negative_normalized hl ht]
  exact hp.trans_lt (high_endpoint_fraction ht)

theorem high_affine_monotone {l t w b L U : ℝ}
    (hl : 0<l) (hL : 0<L) (hU : U≤(23/20)*l) (ht : t∈Icc 0 frameCap)
    (hw : Real.cos t-1≤w) : MonotoneOn (affineBranch l (-t) w b) (Icc L U) := by
  have hs : |-t|≤frameCap := by rw [abs_neg,abs_of_nonneg ht.1]; exact ht.2
  apply monoOn_of_hasDeriv_nonneg
  · intro m hm
    exact (affine_derivative hl (hL.trans_le hm.1) hs).continuousAt.continuousWithinAt
  · intro m hm
    exact affine_derivative hl (hL.trans hm.1) hs
  · intro m hm
    have hn := high_negative_slope hl (hL.trans hm.1) (hm.2.le.trans hU) ht
    dsimp [affineD]
    linarith

theorem H_high_monotone {l t g e L U : ℝ}
    (hl : 0<l) (hL : 0<L) (hU : U≤(23/20)*l) (ht : t∈Icc 0 frameCap)
    (hge : e≤g) (he : Real.cos t-1≤e) : MonotoneOn (H l (-t) g e) (Icc L U) := by
  have h₁ := high_affine_monotone (b:=e) hl hL hU ht (he.trans hge)
  have h₂ := high_affine_monotone (b:=g) hl hL hU ht he
  intro x hx y hy hxy
  rw [H_minimum hge,H_minimum hge]
  exact min_le_min (h₁ hx hy hxy) (h₂ hx hy hxy)

end SquaresInCircles.Eight.GlobalGA.TwoPositive.Coefficient

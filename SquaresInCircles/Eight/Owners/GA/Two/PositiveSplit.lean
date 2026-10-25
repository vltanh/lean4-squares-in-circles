module

public import SquaresInCircles.Eight.Owners.GA.Positive.TDScalarBounds
public import SquaresInCircles.Eight.Owners.GA.ChargedPairs
public import SquaresInCircles.Eight.Owners.GA.Two.PositiveASupport
public import SquaresInCircles.Eight.Owners.GA.Two.PositiveHighTransfer
public import SquaresInCircles.Eight.Owners.SplitConcavityTools
public import SquaresInCircles.Eight.Owners.Varying.BComparison

/-!
# Eight squares: concavity in the actual A/TD split

The coefficients are fixed while the nonnegative total is split.  The
low coefficient function is shifted by `12/25`; its compensating term
is kept in the scalar remainder.  The high proof joins the two actual
A support branches with their common value and derivative.  Thus the
coefficient kink and the A support transition retain their closed ties.
-/

section
/-!
## Coefficient derivatives in the fixed-total split

The pair norm is differentiated with respect to its moving coefficient.
The min/max coefficient changes are expressed as the minimum of their
two affine branches, retaining the downward kink at equality.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalGA.TwoPositive.Coefficient
open Secondary PositiveAngularEnvelope PairNormCalculus OrdinaryCurvatureBounds
open VaryingBFunctions VaryingBComparison

def normD (l s m : ℝ) : ℝ := (m+l*Real.sin s)/pairNorm l m s
def normDD (l s m : ℝ) : ℝ := l^2*(Real.cos s)^2/(pairNorm l m s)^3

theorem norm_derivative {l s m : ℝ} (hl : 0<l) (hm : 0< m) (hs : |s|≤frameCap) :
    HasDerivAt (fun x => pairNorm l x s) (normD l s m) m := by
  have hin : HasDerivAt (fun x => l^2+x^2+2*l*x*Real.sin s) (2*m+2*l*Real.sin s) m := by
    have h := (((hasDerivAt_id m).fun_pow 2).const_add (l^2)).fun_add
      (((hasDerivAt_id m).const_mul (2*l)).mul_const (Real.sin s))
    convert h using 1
    · funext x
      simp only [id_eq]
    · simp only [id_eq]
      ring
  have hd := hin.sqrt (pair_radicand_pos hl hm hs).ne'
  have hn := pairNorm_pos hl hm hs
  refine hd.congr_deriv ?_
  change (2*m+2*l*Real.sin s)/(2*pairNorm l m s)=normD l s m
  dsimp only [normD]
  field_simp

theorem norm_second {l s m : ℝ} (hl : 0<l) (hm : 0< m) (hs : |s|≤frameCap) :
    HasDerivAt (normD l s) (normDD l s m) m := by
  have hn := pairNorm_pos hl hm hs
  have hsq := pairNorm_sq hl hm hs
  have hd := ((hasDerivAt_id m).add_const (l*Real.sin s)).div
    (norm_derivative hl hm hs) hn.ne'
  have hcos : (Real.cos s)^2=1-(Real.sin s)^2 := by nlinarith [Real.sin_sq_add_cos_sq s]
  refine hd.congr_deriv ?_
  dsimp only [normD,normDD,id_eq]
  dsimp only [pairEnergy,pairProduct] at hsq
  field_simp
  rw [hcos]
  linear_combination hsq

theorem norm_second_nonneg {l s m : ℝ} (hl : 0<l) (hm : 0< m) (hs : |s|≤frameCap) :
    0≤normDD l s m := by
  dsimp [normDD]
  exact div_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (pow_nonneg (pairNorm_pos hl hm hs).le 3)

theorem norm_slope_le_one {l s m : ℝ} (hl : 0<l) (hm : 0< m) (hs : |s|≤frameCap) :
    normD l s m≤1 := by
  have hn := pairNorm_pos hl hm hs
  have hsq := pairNorm_sq hl hm hs
  have hunit := congrArg (fun v : ℝ => l^2*v) (Real.sin_sq_add_cos_sq s)
  have hsq' : (m+l*Real.sin s)^2≤(pairNorm l m s)^2 := by
    dsimp [pairEnergy,pairProduct] at hsq
    nlinarith [mul_nonneg (sq_nonneg l) (sq_nonneg (Real.cos s))]
  dsimp [normD]
  apply (div_le_one hn).mpr
  nlinarith

def fraction (r u : ℝ) : ℝ := (r-u)/root r u

theorem fraction_derivative_u (r : ℝ) {u : ℝ} (hu : u∈Icc 0 frameCap) :
    HasDerivAt (fraction r) ((r*u-1)/(root r u)^3) u := by
  have hn := root_pos r hu
  have hd := ((hasDerivAt_id u).const_sub r).div (root_hasDerivAt_u r hu) hn.ne'
  have h2 := root_sq r hu
  refine hd.congr_deriv ?_
  dsimp only [id_eq]
  field_simp
  linear_combination (-1:ℝ)*h2

theorem fraction_derivative_r {r u : ℝ} (hu : u∈Icc 0 frameCap) :
    HasDerivAt (fun x => fraction x u) ((1-u^2)/(root r u)^3) r := by
  have hn := root_pos r hu
  have hd := ((hasDerivAt_id r).sub_const u).div (root_hasDerivAt_r hu) hn.ne'
  have h2 := root_sq r hu
  refine hd.congr_deriv ?_
  dsimp only [id_eq]
  field_simp
  linear_combination h2

theorem fraction_antitone {r : ℝ} (hr : r∈Icc 0 (3/2:ℝ)) :
    AntitoneOn (fraction r) (Icc 0 (129/200:ℝ)) := by
  have hdom {u : ℝ} (hu : u∈Icc 0 (129/200:ℝ)) : u∈Icc 0 frameCap :=
    ⟨hu.1,by norm_num [frameCap]; linarith [hu.2]⟩
  apply antiOn_of_hasDeriv_nonpos
  · intro u hu
    exact (fraction_derivative_u r (hdom hu)).continuousAt.continuousWithinAt
  · intro u hu
    exact fraction_derivative_u r (hdom (Ioo_subset_Icc_self hu))
  · intro u hu
    have hp := mul_le_mul_of_nonneg_right hr.2 hu.1.le
    have hnum : r*u-1≤0 := by nlinarith [hu.2]
    exact div_nonpos_of_nonpos_of_nonneg hnum
      (pow_nonneg (root_pos r (hdom (Ioo_subset_Icc_self hu))).le 3)

theorem fraction_monotone {u L U : ℝ} (hu : u∈Icc 0 frameCap) :
    MonotoneOn (fun r => fraction r u) (Icc L U) := by
  apply monoOn_of_hasDeriv_nonneg
  · intro r _
    exact (fraction_derivative_r hu).continuousAt.continuousWithinAt
  · intro r _
    exact fraction_derivative_r hu
  · intro r _
    have hu2 := pow_le_pow_left₀ hu.1 hu.2 2
    have hnum : 0≤1-u^2 := by dsimp [frameCap] at hu2; linarith
    exact div_nonneg hnum (pow_nonneg (root_pos r hu).le 3)

theorem fraction_le_zero {r u : ℝ} (hr : r∈Icc 0 (3/2:ℝ))
    (hu : u∈Icc 0 (129/200:ℝ)) : fraction r u≤r/shape r := by
  have hh := fraction_antitone hr (show (0:ℝ)∈Icc 0 (129/200:ℝ) by norm_num) hu hu.1
  simpa [fraction] using hh

theorem zero_fraction_bound {r : ℝ} (hr : r∈Icc 0 (3/2:ℝ)) :
    r/shape r≤3/Real.sqrt 13 := by
  have hN := shape_pos r
  have hD : 0<Real.sqrt (13:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hD2 : (Real.sqrt (13:ℝ))^2=13 := Real.sq_sqrt (by norm_num)
  have hN2 := shape_sq r
  have hr2 := pow_le_pow_left₀ hr.1 hr.2 2
  apply (div_le_div_iff₀ hN hD).mpr
  have hsquare : (r*Real.sqrt (13:ℝ))^2≤(3*shape r)^2 := by
    rw [mul_pow,mul_pow,hD2,hN2]
    nlinarith only [hr2]
  nlinarith [mul_nonneg hr.1 hD.le]

theorem radius_fraction_bound : 3*R/Real.sqrt 13<(33/20:ℝ) := by
  have hn : 0<Real.sqrt (13:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  apply quotient_lt_of_square hn (by norm_num)
  rw [mul_pow,radius_sq,Real.sq_sqrt (by norm_num : (0:ℝ)≤13)]
  norm_num [qCap]

theorem norm_slope_negative_normalized {l m t : ℝ} (hl : 0<l)
    (ht : t∈Icc 0 frameCap) :
    normD l (-t) m=fraction (m/l) (Real.sin t) := by
  have he : pairNorm l m (-t)=l*root (m/l) (Real.sin t) := by
    rw [pairNorm_symm]
    exact negativeNorm_normalized hl
  dsimp [normD,fraction]
  rw [he,Real.sin_neg]
  field_simp [hl.ne',(root_pos (m/l) (sin_mem ht)).ne']
  ring

theorem negative_slope_upper {l m t : ℝ} (hl : 0<l) (hm : 0< m)
    (hratio : m≤(3/2)*l) (ht : t∈Icc 0 frameCap) :
    R*normD l (-t) m<33/20 := by
  have hr : m/l∈Icc 0 (3/2:ℝ) :=
    ⟨div_nonneg hm.le hl.le,(div_le_iff₀ hl).mpr hratio⟩
  have ht0 := (transport_trig ht).2.2.1
  have ht1 : Real.sin t≤129/200 := by linarith [(transport_trig ht).2.2.2.1]
  have hfrac := (fraction_le_zero hr ⟨ht0,ht1⟩).trans (zero_fraction_bound hr)
  have hp := mul_le_mul_of_nonneg_left hfrac (Real.sqrt_nonneg qCap)
  rw [norm_slope_negative_normalized hl ht]
  have he : R*(3/Real.sqrt (13:ℝ))=3*R/Real.sqrt 13 := by ring
  rw [he] at hp
  exact hp.trans_lt radius_fraction_bound

def affineBranch (l s w b m : ℝ) : ℝ := (3/2+w)*m+b*l-R*pairNorm l m s
def affineD (l s w m : ℝ) : ℝ := 3/2+w-R*normD l s m

def H (l s g e m : ℝ) : ℝ :=
  (3/2)*m+g*min l m+e*max l m-R*pairNorm l m s

theorem H_minimum {l s g e : ℝ} (hge : e≤g) (m : ℝ) :
    H l s g e m=min (affineBranch l s g e m) (affineBranch l s e g m) := by
  rcases le_total m l with hm | hm
  · have hp := mul_nonneg (sub_nonneg.mpr hge) (sub_nonneg.mpr hm)
    have hbranch : affineBranch l s g e m≤affineBranch l s e g m := by
      dsimp [affineBranch]
      nlinarith only [hp]
    rw [min_eq_left hbranch]
    simp only [H,min_eq_right hm,max_eq_left hm,affineBranch]
    ring
  · have hp := mul_nonneg (sub_nonneg.mpr hge) (sub_nonneg.mpr hm)
    have hbranch : affineBranch l s e g m≤affineBranch l s g e m := by
      dsimp [affineBranch]
      nlinarith only [hp]
    rw [min_eq_right hbranch]
    simp only [H,min_eq_left hm,max_eq_right hm,affineBranch]
    ring

theorem affine_derivative {l s w b m : ℝ} (hl : 0<l) (hm : 0< m) (hs : |s|≤frameCap) :
    HasDerivAt (affineBranch l s w b) (affineD l s w m) m := by
  have h := (((hasDerivAt_id m).const_mul (3/2+w)).add_const (b*l)).sub
    ((norm_derivative hl hm hs).const_mul R)
  refine h.congr_deriv ?_
  dsimp only [affineD]
  ring

theorem affine_second {l s w m : ℝ} (hl : 0<l) (hm : 0< m) (hs : |s|≤frameCap) :
    HasDerivAt (affineD l s w) (-R*normDD l s m) m := by
  have h := (hasDerivAt_const m (3/2+w)).sub ((norm_second hl hm hs).const_mul R)
  refine h.congr_deriv ?_
  ring

theorem affine_concave {l s w b L U : ℝ} (hl : 0<l) (hL : 0<L) (hs : |s|≤frameCap) :
    ConcaveOn ℝ (Icc L U) (affineBranch l s w b) := by
  apply concave_of_deriv2
    (fun m hm => affine_derivative hl (hL.trans_le hm.1) hs)
    (fun m hm => affine_second hl (hL.trans_le hm.1) hs)
  intro m hm
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Real.sqrt_nonneg qCap))
    (norm_second_nonneg hl (hL.trans_le hm.1) hs)

theorem H_concave {l s g e L U : ℝ} (hl : 0<l) (hL : 0<L)
    (hs : |s|≤frameCap) (hge : e≤g) : ConcaveOn ℝ (Icc L U) (H l s g e) := by
  have he : H l s g e=fun m => min (affineBranch l s g e m) (affineBranch l s e g m) :=
    funext (H_minimum hge)
  rw [he]
  exact SplitConcavityTools.minimum (affine_concave hl hL hs) (affine_concave hl hL hs)

end SquaresInCircles.Eight.GlobalGA.TwoPositive.Coefficient
end
end
end

section
/-!
## The low and high coefficient derivative reserves

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
  convert hh using 1
  ring

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
end
end
end

section
/-!
## The full-circle form of the six certified A/T endpoint inequalities

These statements expose the
stronger expressions proved by the same six polynomial numerators, so
the positive-A/TD0 proof can use its fourth ordinary circle block.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.TwoPositive.Certificate
open Polynomial Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PositiveTD
open PositiveTD.Certificate

def fullEndpointBase (e : Endpoint) (t : ℝ) : ℝ :=
  endpointBase e t+clippedSupport 1 (cAt t)-fullSupport 1 (cAt t)

theorem full_H_identity (e : Endpoint) (t : ℝ) :
    endpointNonradical e t+Real.cos t-1-
      R*(pairNorm (kAt t) (lAt t) 0+pairNorm (lAt t) (mAt e t) 0+
        pairNorm (kAt t) 1 (-t)+pairNorm (cAt t) 1 0)=
      fullEndpointBase e t+V R (kAt t) 1 t := by
  simp only [fullEndpointBase,endpointNonradical,endpointBase,baseline,fullSupport_pair,mAt,V]
  ring

theorem full_G_identity (e : Endpoint) (t : ℝ) :
    endpointNonradical e t+lAt t*(Real.cos t-1)-
      R*(pairNorm (kAt t) 1 0+pairNorm (lAt t) (mAt e t) 0+
        pairNorm (kAt t) (lAt t) (-t)+pairNorm (cAt t) 1 0)=
      fullEndpointBase e t+V R (kAt t) (lAt t) t := by
  simp only [fullEndpointBase,endpointNonradical,endpointBase,baseline,fullSupport_pair,mAt,V]
  ring

theorem full_B_identity (e : Endpoint) (t : ℝ) :
    endpointNonradical e t+max (lAt t) (mAt e t)*(Real.cos t-1)-
      R*(pairNorm (kAt t) 1 0+pairNorm (kAt t) (lAt t) 0+
        pairNorm (lAt t) (mAt e t) (-t)+pairNorm (cAt t) 1 0)=
      fullEndpointBase e t+
        V R (min (lAt t) (mAt e t)) (max (lAt t) (mAt e t)) t := by
  simp only [V,sorted_pair_norm]
  simp only [fullEndpointBase,endpointNonradical,endpointBase,baseline,fullSupport_pair,mAt]
  ring

theorem high_H_full_positive (e : Endpoint) {t : ℝ} (ht : t∈Icc (1/6:ℝ) frameCap) :
    0<fullEndpointBase e t+V R (kAt t) 1 t := by
  have hn := high_norm_bounds e ht
  have htrig := taylor_bounds (high_frame_domain ht)
  have hA : aeval t (highA e+C10-1)≤endpointNonradical e t+Real.cos t-1 := by
    simp only [map_add,map_sub,map_one]
    linarith [high_nonradical_lower e ht,htrig.2.2.2.2.1]
  have hrG : 0<aeval t highRG := by simpa [mass] using masses_positive e 1 ht
  have hrB : 0<aeval t (highRB e) := by simpa [mass] using masses_positive e 3 ht
  have hrH : 0<aeval t highRHminus := by simpa [mass] using masses_positive e 4 ht
  have hrD : 0<aeval t highRD := by simpa [mass] using masses_positive e 2 ht
  have hp := num4_transfer hrG hrB hrH hrD
    (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _)
    (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _)
    hn.2.1 hn.2.2.2.1 hn.2.2.2.2.1 hn.2.2.1 hA (highNH_positive e ht)
  simpa only [full_H_identity] using hp

theorem high_G_full_positive (e : Endpoint) {t : ℝ} (ht : t∈Icc (1/6:ℝ) frameCap) :
    0<fullEndpointBase e t+V R (kAt t) (lAt t) t := by
  have hn := high_norm_bounds e ht
  have hr := high_ranges ht
  have htrig := taylor_bounds (high_frame_domain ht)
  have hcos := mul_le_mul_of_nonneg_left (sub_le_sub_right htrig.2.2.2.2.1 1)
    (show 0≤lAt t by linarith [hr.2.2.1])
  have hA : aeval t (highA e+highL*(C10-1))≤
      endpointNonradical e t+lAt t*(Real.cos t-1) := by
    simp only [map_add,map_mul,map_sub,map_one]
    linarith [high_nonradical_lower e ht]
  have hrH : 0<aeval t highRH := by simpa [mass] using masses_positive e 0 ht
  have hrB : 0<aeval t (highRB e) := by simpa [mass] using masses_positive e 3 ht
  have hrG : 0<aeval t highRGminus := by simpa [mass] using masses_positive e 5 ht
  have hrD : 0<aeval t highRD := by simpa [mass] using masses_positive e 2 ht
  have hp := num4_transfer hrH hrB hrG hrD
    (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _)
    (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _)
    hn.1 hn.2.2.2.1 hn.2.2.2.2.2.1 hn.2.2.1 hA (highNG_positive e ht)
  simpa only [full_G_identity] using hp

theorem high_B_full_positive (e : Endpoint) {t : ℝ} (ht : t∈Icc (1/6:ℝ) frameCap) :
    0<fullEndpointBase e t+
      V R (min (lAt t) (mAt e t)) (max (lAt t) (mAt e t)) t := by
  have hn := high_norm_bounds e ht
  have hr := high_ranges ht
  have htrig := taylor_bounds (high_frame_domain ht)
  have hQ := high_Q_bound e ht
  have hQ0 : 0≤aeval t highQ := by
    have hlq := (le_max_left (lAt t) (mAt e t)).trans hQ
    linarith [hr.2.2.1]
  have h₁ := mul_le_mul_of_nonneg_left (sub_le_sub_right htrig.2.2.2.2.1 1) hQ0
  have h₂ := mul_le_mul_of_nonpos_right hQ (sub_nonpos.mpr (Real.cos_le_one t))
  have hA : aeval t (highA e+highQ*(C10-1))≤endpointNonradical e t+
      max (lAt t) (mAt e t)*(Real.cos t-1) := by
    simp only [map_add,map_mul,map_sub,map_one]
    linarith [high_nonradical_lower e ht]
  have hrH : 0<aeval t highRH := by simpa [mass] using masses_positive e 0 ht
  have hrG : 0<aeval t highRG := by simpa [mass] using masses_positive e 1 ht
  have hrB : 0<aeval t (highRBminus e) := by simpa [mass] using masses_positive e 6 ht
  have hrD : 0<aeval t highRD := by simpa [mass] using masses_positive e 2 ht
  have hp := num4_transfer hrH hrG hrB hrD
    (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _)
    (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _)
    hn.1 hn.2.1 hn.2.2.2.2.2.2 hn.2.2.1 hA (highNB_positive e ht)
  simpa only [full_B_identity] using hp

/-- All six polynomial certificates apply before the sorted D support
is restored. -/
theorem high_six_full_scalars_positive (e : Endpoint) {t : ℝ}
    (ht : t∈Icc (1/6:ℝ) frameCap) :
    0<fullEndpointBase e t+V R (kAt t) 1 t ∧
    0<fullEndpointBase e t+V R (kAt t) (lAt t) t ∧
    0<fullEndpointBase e t+
      V R (min (lAt t) (mAt e t)) (max (lAt t) (mAt e t)) t :=
  ⟨high_H_full_positive e ht,high_G_full_positive e ht,high_B_full_positive e ht⟩

end SquaresInCircles.Eight.GlobalGA.TwoPositive.Certificate
end
end
end

section
@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalGA.TwoPositive.Split
open Candidate Secondary PositiveTD PositiveAngularEnvelope
open SplitConcavityTools

def mD (c t a : ℝ) : ℝ := c*(Real.sin (t-a)-eta*Real.cos (t-a))

def smooth (c z : ℝ) : ℝ := c*(1+Real.cos z+Real.sin z)/2-c*sigma*Real.sin z

def smoothD (c t a : ℝ) : ℝ :=
  c*(Real.sin (t-a)-Real.cos (t-a))/2+c*sigma*Real.cos (t-a)

def smoothDD (c t a : ℝ) : ℝ :=
  c*(-Real.cos (t-a)/2+(sigma-1/2)*Real.sin (t-a))

def axialRest (r c l t a : ℝ) : ℝ :=
  smooth c (t-a)+l*ASupport.axialCharge a-r*tilted c (t-a)

def circleRest (r c l t a : ℝ) : ℝ :=
  smooth c (t-a)+l*ASupport.circleCharge a-r*tilted c (t-a)

def rest (c l t a : ℝ) : ℝ := smooth c (t-a)+l*ASupport.charge a

theorem split_domain {t a : ℝ} (ht : t∈Icc 0 frameCap) (ha : a∈Icc 0 t) :
    a∈Icc 0 frameCap ∧ t-a∈Icc 0 frameCap := by
  exact ⟨⟨ha.1,ha.2.trans ht.2⟩,⟨by linarith [ha.2],by linarith [ht.2,ha.1]⟩⟩

theorem tilted_derivative (c t a : ℝ) :
    HasDerivAt (fun x => tilted c (t-x)) (mD c t a) a := by
  have hz := (hasDerivAt_id a).const_sub t
  convert (((Real.hasDerivAt_cos (t-a)).comp a hz).add
    (((Real.hasDerivAt_sin (t-a)).comp a hz).const_mul eta)).const_mul c using 1 <;>
    dsimp [tilted,mD]
  ring

theorem tilted_second (c t a : ℝ) :
    HasDerivAt (mD c t) (-tilted c (t-a)) a := by
  have hz : HasDerivAt (fun x : ℝ => t-x) (-1) a := (hasDerivAt_id' a).const_sub t
  have h := ((hz.sin).sub ((hz.cos).const_mul eta)).const_mul c
  refine h.congr_deriv ?_
  simp only [tilted]
  ring

theorem tilted_concave {c t : ℝ} (hc : 0<c) (ht : t∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc 0 t) (fun a => tilted c (t-a)) := by
  apply concave_of_deriv2 (fun a _ => tilted_derivative c t a)
    (fun a _ => tilted_second c t a)
  intro a ha
  exact neg_nonpos.mpr (tilted_pos hc (split_domain ht ha).2).le

theorem smooth_actual {c z : ℝ} (hz : z∈Icc 0 frameCap) :
    smooth c z=c*edgeWidth z-c*sigma*Real.sin z := by
  have hc := transport_cos_pos (by rw [abs_of_nonneg hz.1]; exact hz.2)
  simp only [smooth,edgeWidth,pairWidth,abs_of_pos hc,
    abs_of_nonneg (transport_trig hz).2.2.1]
  ring

theorem smooth_derivative (c t a : ℝ) :
    HasDerivAt (fun x => smooth c (t-x)) (smoothD c t a) a := by
  have hz : HasDerivAt (fun x : ℝ => t-x) (-1) a := (hasDerivAt_id' a).const_sub t
  have h := (((((hz.cos).const_add 1).add hz.sin).const_mul c).div_const 2).sub
    ((hz.sin).const_mul (c*sigma))
  refine h.congr_deriv ?_
  simp only [smoothD]
  ring

theorem smooth_second (c t a : ℝ) :
    HasDerivAt (smoothD c t) (smoothDD c t a) a := by
  have hz : HasDerivAt (fun x : ℝ => t-x) (-1) a := (hasDerivAt_id' a).const_sub t
  have h := ((((hz.sin).sub hz.cos).const_mul c).div_const 2).add
    ((hz.cos).const_mul (c*sigma))
  refine h.congr_deriv ?_
  simp only [smoothDD]
  ring

theorem axial_derivative (r c l t a : ℝ) :
    HasDerivAt (axialRest r c l t)
      (smoothD c t a+l*ASupport.axialD a-r*mD c t a) a := by
  convert ((smooth_derivative c t a).add
    ((ASupport.axial_derivative a).const_mul l)).sub
      ((tilted_derivative c t a).const_mul r) using 1
  rfl

theorem axial_second (r c l t a : ℝ) :
    HasDerivAt (fun x => smoothD c t x+l*ASupport.axialD x-r*mD c t x)
      (smoothDD c t a+l*ASupport.axialDD a+r*tilted c (t-a)) a := by
  convert ((smooth_second c t a).add
    ((ASupport.axial_second a).const_mul l)).sub
      ((tilted_second c t a).const_mul r) using 1
  ring

theorem circle_derivative (r c l t a : ℝ) :
    HasDerivAt (circleRest r c l t)
      (smoothD c t a+l*ASupport.circleD a-r*mD c t a) a := by
  convert ((smooth_derivative c t a).add
    ((ASupport.circle_derivative a).const_mul l)).sub
      ((tilted_derivative c t a).const_mul r) using 1
  rfl

theorem circle_second (r c l t a : ℝ) :
    HasDerivAt (fun x => smoothD c t x+l*ASupport.circleD x-r*mD c t x)
      (smoothDD c t a+l*ASupport.circleDD a+r*tilted c (t-a)) a := by
  convert ((smooth_second c t a).add
    ((ASupport.circle_second a).const_mul l)).sub
      ((tilted_second c t a).const_mul r) using 1
  ring

theorem sigma_bound : sigma≤177/125 := by
  have hh := PositiveTD.Certificate.sigma_le_sigmabar
  norm_num [PositiveTD.Certificate.sigmabar] at hh
  linarith

theorem low_trig {a : ℝ} (ha : a∈Icc 0 (1/6:ℝ)) :
    (71/72:ℝ)≤Real.cos a ∧ 0≤Real.sin a ∧ Real.sin a≤1/6 := by
  have ha2 : a^2≤(1/6:ℝ)^2 := pow_le_pow_left₀ ha.1 ha.2 2
  have hcos := Real.one_sub_sq_div_two_le_cos (x:=a)
  exact ⟨by nlinarith,(transport_trig ⟨ha.1,by norm_num [frameCap]; linarith [ha.2]⟩).2.2.1,
    (Real.sin_le ha.1).trans ha.2⟩

theorem low_rest_curvature {c l t a : ℝ}
    (hc : 0<c) (hl : 0<l) (hcl : c≤(3/2)*l)
    (ht : t∈Icc 0 (1/6:ℝ)) (ha : a∈Icc 0 t) :
    smoothDD c t a+l*ASupport.axialDD a+(12/25)*tilted c (t-a)< -(9/100)*l := by
  have ha' : a∈Icc 0 (1/6:ℝ) := ⟨ha.1,ha.2.trans ht.2⟩
  have hz : t-a∈Icc 0 (1/6:ℝ) := ⟨by linarith [ha.2],by linarith [ht.2,ha.1]⟩
  have hta := low_trig ha'
  have htz := low_trig hz
  have hsig := mul_le_mul_of_nonneg_right
    (show sigma-1/2≤229/250 by linarith [sigma_bound]) htz.2.1
  have hax := mul_le_mul_of_nonneg_right
    (show axial-1/2≤183/200 by linarith [axial_bounds.2]) hta.2.1
  have hzBound : -Real.cos (t-a)/2+(sigma-1/2)*Real.sin (t-a)≤
      -71/144+229/1500 := by linarith [htz.1,htz.2.2]
  have haBound : ASupport.axialDD a≤-71/144+61/400 := by
    dsimp [ASupport.axialDD]
    linarith [hta.1,hta.2.2]
  have hm : tilted c (t-a)≤c*(1+eta/6) := by
    apply mul_le_mul_of_nonneg_left _ hc.le
    have hh := Real.cos_le_one (t-a)
    dsimp [eta]
    linarith [htz.2.2]
  have hcz := mul_le_mul_of_nonneg_left hzBound hc.le
  have hla := mul_le_mul_of_nonneg_left haBound hl.le
  have hcm := mul_le_mul_of_nonneg_left hm (show (0:ℝ)≤12/25 by norm_num)
  have hratio := mul_le_mul_of_nonneg_right hcl
    (show (0:ℝ)≤(12/25)*(1+eta/6)-71/144+229/1500 by norm_num [eta])
  dsimp [smoothDD,eta] at *
  nlinarith only [hcz,hla,hcm,hratio,hl]

theorem low_rest_concave {c l t : ℝ}
    (hc : 0<c) (hl : 0<l) (hcl : c≤(3/2)*l) (ht : t∈Icc 0 (1/6:ℝ)) :
    ConcaveOn ℝ (Icc 0 t) (axialRest (12/25) c l t) := by
  apply concave_of_deriv2 (fun a _ => axial_derivative (12/25) c l t a)
    (fun a _ => axial_second (12/25) c l t a)
  intro a ha
  exact (low_rest_curvature hc hl hcl ht ha).le.trans (by linarith)

theorem low_tilted_lower {c t a : ℝ} (hc : 0<c)
    (ht : t∈Icc 0 (1/6:ℝ)) (ha : a∈Icc 0 t) : c/2≤tilted c (t-a) := by
  have hz : t-a∈Icc 0 (1/6:ℝ) := ⟨by linarith [ha.2],by linarith [ht.2,ha.1]⟩
  have htrig := low_trig hz
  have hf : (1/2:ℝ)≤Real.cos (t-a)+eta*Real.sin (t-a) := by
    have hh := mul_nonneg (show (0:ℝ)≤eta by norm_num [eta]) htrig.2.1
    linarith [htrig.1]
  have hh := mul_le_mul_of_nonneg_left hf hc.le
  simpa [tilted,div_eq_mul_inv,mul_comm] using hh

/-- Every low scalar in equation (24), with its actual coefficient
transition, is concave on the complete fixed-total split. -/
theorem low_scalar_concave {c l t s g e : ℝ}
    (hc : 0<c) (hl : 0<l) (hcl : c≤(3/2)*l)
    (ht : t∈Icc 0 (1/6:ℝ)) (hs : |s|≤frameCap)
    (hg : 0≤g) (he : e≤0) (heLow : Real.cos frameCap-1≤e)
    (hePos : 0<s→e=0)
    (hm : ∀a∈Icc 0 t,tilted c (t-a)≤(3/2)*l) :
    ConcaveOn ℝ (Icc 0 t)
      (fun a => Coefficient.H l s g e (tilted c (t-a))+rest c l t a) := by
  have ht' : t∈Icc 0 frameCap := ⟨ht.1,by norm_num [frameCap]; linarith [ht.2]⟩
  have hH := Coefficient.H_shifted_low (L:=c/2) (U:=(3/2)*l)
    hl (by positivity) le_rfl hs hg he heLow hePos
  have hcomp := compose hH.1 hH.2 (tilted_concave hc ht')
    (fun a ha => ⟨low_tilted_lower hc ht ha,hm a ha⟩)
  have hsum := hcomp.add (low_rest_concave hc hl hcl ht)
  have heq {a : ℝ} (ha : a∈Icc 0 t) :
      Coefficient.H l s g e (tilted c (t-a))+(12/25)*tilted c (t-a)+
        axialRest (12/25) c l t a=
      Coefficient.H l s g e (tilted c (t-a))+rest c l t a := by
    rw [rest,ASupport.charge_low (ha.2.trans ht.2)]
    dsimp [axialRest]
    ring
  refine ⟨hsum.1,?_⟩
  intro x hx y hy r v hr hv hrv
  have hh := hsum.2 hx hy hr hv hrv
  simp only [Pi.add_apply] at hh
  rw [heq hx,heq hy,heq (hsum.1 hx hy hr hv hrv)] at hh
  exact hh

theorem high_rest_curvature {c l t a d : ℝ}
    (hl : 0<l) (hcLow : (9/10)*l≤c) (hcHigh : c≤(11/10)*l)
    (ht : t∈Icc 0 frameCap) (ha : a∈Icc 0 t)
    (hd : d≤-Real.cos a/2+(23/25)*Real.sin a) :
    smoothDD c t a+l*d< -(1/50)*l := by
  have hc : 0<c := by linarith
  have hdom := split_domain ht ha
  have hsa := (transport_trig hdom.1).2.2.1
  have hsz := (transport_trig hdom.2).2.2.1
  have hca : (478/625:ℝ)<Real.cos a :=
    Coefficient.cap_cosine_lower.trans_le
      (Real.cos_le_cos_of_nonneg_of_le_pi hdom.1.1
        (by dsimp [frameCap]; linarith [Real.pi_gt_three]) hdom.1.2)
  have hcz : (478/625:ℝ)<Real.cos (t-a) :=
    Coefficient.cap_cosine_lower.trans_le
      (Real.cos_le_cos_of_nonneg_of_le_pi hdom.2.1
        (by dsimp [frameCap]; linarith [Real.pi_gt_three]) hdom.2.2)
  have hcosA := mul_le_mul_of_nonneg_left hca.le hl.le
  have hcosZ := mul_le_mul_of_nonneg_left hcz.le hc.le
  have hsig := mul_le_mul_of_nonneg_right
    (show sigma-1/2≤229/250 by linarith [sigma_bound]) hsz
  have hsigC := mul_le_mul_of_nonneg_left hsig hc.le
  have hczUpper := mul_le_mul_of_nonneg_right hcHigh hsz
  have hcharge := mul_le_mul_of_nonneg_left hd hl.le
  have hsin : Real.sin a+Real.sin (t-a)≤frameCap := by
    linarith [Real.sin_le ha.1,Real.sin_le hdom.2.1,ht.2]
  have hsinL := mul_le_mul_of_nonneg_left hsin hl.le
  have hsinAL := mul_nonneg hl.le hsa
  dsimp [smoothDD,frameCap] at *
  nlinarith only [hcLow,hcosA,hcosZ,hsigC,hczUpper,hcharge,hsinL,hsinAL,hl]

theorem high_axial_bound {a : ℝ} (ha : a∈Icc 0 frameCap) :
    ASupport.axialDD a≤-Real.cos a/2+(23/25)*Real.sin a := by
  have hh := ASupport.axial_curvature ha
  have hs := (transport_trig ha).2.2.1
  linarith

theorem high_rest_concave {c l t : ℝ}
    (hl : 0<l) (hcLow : (9/10)*l≤c) (hcHigh : c≤(11/10)*l)
    (ht : t∈Icc 0 frameCap) : ConcaveOn ℝ (Icc 0 t) (rest c l t) := by
  have hax {L U : ℝ} (hL : 0≤L) (hU : U≤t) :
      ConcaveOn ℝ (Icc L U) (axialRest 0 c l t) := by
    apply concave_of_deriv2 (fun a _ => axial_derivative 0 c l t a)
      (fun a _ => axial_second 0 c l t a)
    intro a ha
    have ha' : a∈Icc 0 t := ⟨hL.trans ha.1,ha.2.trans hU⟩
    have hh := high_rest_curvature hl hcLow hcHigh ht ha'
      (high_axial_bound (split_domain ht ha').1)
    simpa only [zero_mul,add_zero] using hh.le.trans (by linarith : -(1/50)*l≤0)
  by_cases hcut : t≤ASupport.alpha
  · have hh := hax (L:=0) (U:=t) le_rfl le_rfl
    have heq {a : ℝ} (ha : a∈Icc 0 t) : axialRest 0 c l t a=rest c l t a := by
      simp [axialRest,rest,ASupport.charge,ha.2.trans hcut]
    refine ⟨hh.1,?_⟩
    intro x hx y hy r v hr hv hrv
    have h := hh.2 hx hy hr hv hrv
    rw [heq hx,heq hy,heq (hh.1 hx hy hr hv hrv)] at h
    exact h
  · have halpha : ASupport.alpha∈Icc 0 t :=
      ⟨by linarith [ASupport.alpha_bounds.1],(lt_of_not_ge hcut).le⟩
    have hcirc : ConcaveOn ℝ (Icc ASupport.alpha t) (circleRest 0 c l t) := by
      apply concave_of_deriv2 (fun a _ => circle_derivative 0 c l t a)
        (fun a _ => circle_second 0 c l t a)
      intro a ha
      have ha' : a∈Icc 0 t := ⟨halpha.1.trans ha.1,ha.2⟩
      have haFrame := (split_domain ht ha').1
      have hmajor := ASupport.high_curvature_majorant
        (show a∈Icc (1/2:ℝ) frameCap from
          ⟨by linarith [ha.1,ASupport.alpha_bounds.1],haFrame.2⟩)
      have hd := (ASupport.circle_curvature haFrame).trans hmajor
      have hh := high_rest_curvature hl hcLow hcHigh ht ha' hd
      simpa only [zero_mul,add_zero] using hh.le.trans (by linarith : -(1/50)*l≤0)
    have he : axialRest 0 c l t ASupport.alpha=circleRest 0 c l t ASupport.alpha := by
      simp only [axialRest,circleRest,ASupport.transition_value]
    have hd : smoothD c t ASupport.alpha+l*ASupport.axialD ASupport.alpha=
        smoothD c t ASupport.alpha+l*ASupport.circleD ASupport.alpha := by
      rw [ASupport.transition_derivative]
    have hleft := axial_derivative 0 c l t ASupport.alpha
    have hright := circle_derivative 0 c l t ASupport.alpha
    simp only [zero_mul,sub_zero] at hleft hright
    rw [← hd] at hright
    have hj := join halpha (hax le_rfl halpha.2) hcirc he hleft hright
    have hrest : rest c l t=fun x => if x≤ASupport.alpha then axialRest 0 c l t x
        else circleRest 0 c l t x := by
      funext x
      simp only [rest,ASupport.charge,axialRest,circleRest,zero_mul,sub_zero]
      split_ifs <;> rfl
    rw [hrest]
    exact hj

/-- The balanced single-negative alternatives retain their actual
`min/max` coefficient kink throughout the high split. -/
theorem high_scalar_concave {c l t s g e L U : ℝ}
    (hl : 0<l) (hcLow : (9/10)*l≤c) (hcHigh : c≤(11/10)*l)
    (ht : t∈Icc 0 frameCap) (hs : s∈Icc 0 frameCap)
    (hL : 0<L) (hU : U≤(23/20)*l)
    (hge : e≤g) (he : Real.cos s-1≤e)
    (hm : ∀a∈Icc 0 t,tilted c (t-a)∈Icc L U) :
    ConcaveOn ℝ (Icc 0 t)
      (fun a => Coefficient.H l (-s) g e (tilted c (t-a))+rest c l t a) := by
  have hc : 0<c := by linarith
  have hH := Coefficient.H_concave (U:=U) hl hL
    (show |-s|≤frameCap by rw [abs_neg,abs_of_nonneg hs.1]; exact hs.2) hge
  have hmono := Coefficient.H_high_monotone hl hL hU hs hge he
  exact (compose hH hmono (tilted_concave hc ht) hm).add
    (high_rest_concave hl hcLow hcHigh ht)

end SquaresInCircles.Eight.GlobalGA.TwoPositive.Split
end
end
end

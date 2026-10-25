module

public import SquaresInCircles.Eight.TableFree.GlobalGATwoPositiveEnvelope
public import SquaresInCircles.Eight.TableFree.SplitConcavityTools

/-!
# Coefficient derivatives in the fixed-total split

Uncompiled source following equations (24)--(29) of the split proof.
The pair norm is differentiated with respect to its moving coefficient.
The min/max coefficient changes are expressed as the minimum of their
two affine branches, retaining the downward kink at equality.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalGA.TwoPositive.Coefficient
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

end SquaresInCircles.Eight.TableFree.GlobalGA.TwoPositive.Coefficient

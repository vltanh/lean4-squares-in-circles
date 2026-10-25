module

public import SquaresInCircles.Eight.Owners.Critical.EPosition
public import SquaresInCircles.Eight.Owners.Exceptional.ContactSupport
public import SquaresInCircles.Eight.Owners.Exceptional.PositiveTOrdinaryData
public import SquaresInCircles.Eight.Owners.SecantNormCurvature
public import SquaresInCircles.Eight.Stationary.System

/-!
# Eight squares: actual coefficient bounds on every critical minimizing fibre

All ordinary-envelope coefficients are now the
literal functions of the original common-radius circle chain. Positive
denominator substitution proves the numerical bounds, and position
stationarity gives the correlated l/c and c/k comparisons. The public
entry theorem selects minimizingPosition itself and discharges the
affine-strip and stationary-position premises.
-/

section
/-!
## Coefficient conditions for the sharp critical ordinary envelope

These elementary consequences are separated from
the later construction of the coefficients from the actual minimizer.
The final geometric theorem will instantiate every field from that
construction. The weaker bounds used here also retain a two-angle H
block, so the original EH0 angle need not be zero.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CriticalECoefficients
open ExceptionalContactStress ExceptionalContactSupport

structure Bounds (t k l c eta : ℝ) : Prop where
  angle_lower : 1/10≤t
  angle_upper : t≤4/25
  k_lower : 37/40<k
  k_upper : k<197/200
  c_lower : 37/40<c
  c_upper : c<1
  ell_pos : 0<l
  ell_upper : l<67/100
  ell_k : l<(27/40)*k
  ell_c_lower : (63/100)*c<l
  ell_c_upper : l<(17/25)*c
  difference : c-k<1/50
  eta_lower : 27/100<eta
  eta_upper : eta<31/100

theorem Bounds.angle {t k l c eta : ℝ} (h : Bounds t k l c eta) : t∈Icc 0 frameCap := by
  exact ⟨by linarith [h.angle_lower],by
    show t≤7/10
    linarith [h.angle_upper]⟩

theorem Bounds.short {t k l c eta : ℝ} (h : Bounds t k l c eta) : t∈Icc 0 (9/50:ℝ) :=
  ⟨by linarith [h.angle_lower],by linarith [h.angle_upper]⟩

theorem Bounds.order {t k l c eta : ℝ} (h : Bounds t k l c eta) :
    0<k ∧ l≤k ∧ l≤c ∧ (117/200)*c≤l ∧ c≤2*l ∧ k≤2*l ∧ (1/4:ℝ)≤c-l := by
  have hk := h.k_lower
  have hku := h.k_upper
  have hc := h.c_lower
  have hcu := h.c_upper
  have hlk := h.ell_k
  have hll := h.ell_c_lower
  have hlu := h.ell_c_upper
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩ <;> linarith

theorem Bounds.tilt_bounds {t k l c eta s : ℝ} (h : Bounds t k l c eta)
    (hs : s∈Icc 0 t) : 1≤tilt eta s ∧ tilt eta s<21/20 := by
  exact ⟨SoleLowCoefficientBounds.tilted_lower
    ⟨by linarith [h.eta_lower],by linarith [h.eta_upper]⟩
    ⟨hs.1,by linarith [hs.2,h.angle_upper]⟩,
    SoleLowCoefficientBounds.tilted_upper
      ⟨by linarith [h.eta_lower],by linarith [h.eta_upper]⟩⟩

theorem Bounds.contactScalar_lt {t k l c eta R : ℝ} (h : Bounds t k l c eta)
    (hR : 0≤R) (hQL : Eight.qLow≤R^2) : contactScalar R eta t<3 := by
  have hrad := SoleAngleGrowth.radius_lower hR hQL
  have hs0 := Real.sqrt_nonneg (1+eta^2)
  have hs2 := Real.sq_sqrt (show 0≤1+eta^2 by positivity)
  have hs1 : 1≤Real.sqrt (1+eta^2) := by nlinarith [sq_nonneg eta]
  have hm := mul_le_mul_of_nonneg_left hs1 hR
  have hcoef : 1+2*eta-R*Real.sqrt (1+eta^2)<0 := by linarith [h.eta_upper]
  have hsin : 0<Real.sin t := Real.sin_pos_of_pos_of_lt_pi
    (by linarith [h.angle_lower]) (by linarith [h.angle_upper,Real.pi_gt_three])
  have hp := mul_neg_of_neg_of_pos hcoef hsin
  dsimp [contactScalar]
  linarith [Real.cos_le_one t]

end SquaresInCircles.Eight.CriticalECoefficients
end
end
end

section
/-!
## The supporting family on the critical E strip

The weights `eta`, `lam`, `k`, `ell`, `c` are functions of the four successive circle roots
(`circle_identities`, `positive_weights`). Stationarity of the position aligns the force on B with
its circle point (`aligned_support`). With the pure B charge, the endpoint is exactly the radial
defect of the required D point (`endpoint_identity`); the identity keeps the sharp zero, so the
endpoint is nonnegative (`endpoint_nonnegative`), on every minimizing-position fibre
(`minimizing_endpoint`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CriticalEFamily
open Stationary.FiveCornerGeometry PositiveAngularEnvelope OrdinaryAngleConcavity
open ExceptionalContactSupport ExceptionalContactStress

def eta (q u : ℝ) : ℝ := lowerHeight q u/lowerLeft q u
def lam (q t u : ℝ) : ℝ := Real.cos t+eta q u*Real.sin t
def k (q t u : ℝ) : ℝ := lam q t u*topLeft q u/topHeight q u
def ell (q t u : ℝ) : ℝ := k q t u*(2-u)/topRight q u
def c (q t u : ℝ) : ℝ :=
  firstComponent q (Real.cos t) (Real.sin t) u/
    secondComponent q (Real.cos t) (Real.sin t) u
def requiredNorm (q t u : ℝ) : ℝ :=
  Real.sqrt (firstComponent q (Real.cos t) (Real.sin t) u^2+
    secondComponent q (Real.cos t) (Real.sin t) u^2)

theorem circle_identities {q u : ℝ} (h : SmoothDomain q u) :
    lowerRight q u^2+u^2=q ∧
    topRight q u^2+(2-u)^2=q ∧
    topHeight q u^2+topLeft q u^2=q ∧
    lowerLeft q u^2+lowerHeight q u^2=q :=
  ⟨upper_circle h.first_radicand,upper_circle h.second_radicand,
    upper_circle h.third_radicand,upper_circle h.fourth_radicand⟩

theorem positive_weights {q t u : ℝ} (h : SmoothDomain q u)
    (hc : 0<Real.cos t) (hs : 0≤Real.sin t) :
    0<eta q u ∧ 0<lam q t u ∧ 0<k q t u ∧ 0<ell q t u ∧ 0<c q t u := by
  have hv := h.toDomain.lowerHeight_pos h.radius_lt_four
  have hV := h.toDomain.topLeft_pos h.radius_lt_four
  have ha : 0<2-u := by linarith [h.toDomain.height_lt_two h.radius_lt_four]
  obtain ⟨h1,h2⟩ := components_pos h.radius_lt_four h.toDomain hc
    (Real.cos_le_one t) hs (Real.sin_le_one t)
  have he : 0<eta q u := div_pos hv h.w_pos
  have hl : 0<lam q t u := by dsimp [lam]; nlinarith [mul_nonneg he.le hs]
  have hk : 0<k q t u := div_pos (mul_pos hl hV) h.Y_pos
  exact ⟨he,hl,hk,div_pos (mul_pos hk ha) h.U_pos,div_pos h1 h2⟩

theorem stationary_ratio {q t u : ℝ} (h : SmoothDomain q u)
    (hc : 0<Real.cos t) (hs : 0≤Real.sin t)
    (hposition : positionHalf q (Real.cos t) (Real.sin t) u=0) :
    ell q t u=c q t u*(Real.sin t+Real.cos t*u/lowerRight q u) := by
  have h2 := (components_pos h.radius_lt_four h.toDomain hc
    (Real.cos_le_one t) hs (Real.sin_le_one t)).2
  dsimp [positionHalf,slopeRatio] at hposition
  dsimp [ell,k,lam,eta,c]
  field_simp [h.r_pos.ne',h.U_pos.ne',h.Y_pos.ne',h.w_pos.ne',h2.ne'] at hposition ⊢
  nlinarith [hposition]

/-- An aligned force attains the support of the same circle. -/
theorem aligned_support {R x y a b : ℝ} (hR : 0≤R) (hx : 0<x)
    (hy : 0≤y) (ha : 0≤a) (hcirc : x^2+y^2=R^2)
    (halign : b*x=a*y) :
    R*Real.sqrt (a^2+b^2)=a*x+b*y := by
  have hb : 0≤b := by nlinarith [mul_nonneg ha hy]
  have hn := Real.sqrt_nonneg (a^2+b^2)
  have hn2 := Real.sq_sqrt (show 0≤a^2+b^2 by positivity)
  have hid : (a*x+b*y)^2+(a*y-b*x)^2=(a^2+b^2)*(x^2+y^2) := by ring
  have hprod : (R*Real.sqrt (a^2+b^2))^2=(a^2+b^2)*(x^2+y^2) := by
    rw [mul_pow,hn2,hcirc]
    ring
  have hd := add_nonneg (mul_nonneg ha hx.le) (mul_nonneg hb hy)
  nlinarith [mul_nonneg hR hn]

theorem supports {q R t u : ℝ} (h : SmoothDomain q u)
    (hR : 0≤R) (hR2 : R^2=q) (hc : 0<Real.cos t) (hs : 0≤Real.sin t)
    (hposition : positionHalf q (Real.cos t) (Real.sin t) u=0) :
    R*pairNorm (lam q t u) (k q t u) 0=
      lam q t u*topHeight q u+k q t u*topLeft q u ∧
    R*pairNorm (k q t u) (ell q t u) 0=
      k q t u*topRight q u+ell q t u*(2-u) ∧
    R*pairNorm (ell q t u) (c q t u) (-t)=
      c q t u*Real.cos t*lowerRight q u+
        (ell q t u-c q t u*Real.sin t)*u ∧
    R*Real.sqrt (1+eta q u^2)=lowerLeft q u+eta q u*lowerHeight q u := by
  obtain ⟨hr,hU,hY,hw⟩ := circle_identities h
  obtain ⟨he,hl,hk,hell,hc'⟩ := positive_weights h hc hs
  have hV := h.toDomain.topLeft_pos h.radius_lt_four
  have hv := h.toDomain.lowerHeight_pos h.radius_lt_four
  have ha : 0<2-u := by linarith [h.toDomain.height_lt_two h.radius_lt_four]
  have hratio := stationary_ratio h hc hs hposition
  have hunit := Real.cos_sq_add_sin_sq t
  refine ⟨?_,?_,?_,?_⟩
  · rw [pairNorm_zero]
    apply aligned_support hR h.Y_pos hV.le hl.le (hY.trans hR2.symm)
    dsimp [k]
    field_simp [h.Y_pos.ne']
  · rw [pairNorm_zero]
    apply aligned_support hR h.U_pos ha.le hk.le (hU.trans hR2.symm)
    dsimp [ell]
    field_simp [h.U_pos.ne']
  · have hnorm : pairNorm (ell q t u) (c q t u) (-t)=
        Real.sqrt ((c q t u*Real.cos t)^2+(ell q t u-c q t u*Real.sin t)^2) := by
      apply congrArg Real.sqrt
      simp only [Real.sin_neg]
      linear_combination (-(c q t u)^2)*hunit
    rw [hnorm]
    apply aligned_support hR h.r_pos h.height_nonneg (mul_nonneg hc'.le hc.le)
      (hr.trans hR2.symm)
    rw [hratio]
    field_simp [h.r_pos.ne']
    ring
  · simpa only [one_pow,one_mul] using
      aligned_support hR h.w_pos hv.le (show (0:ℝ)≤1 by norm_num)
        (hw.trans hR2.symm) (show eta q u*lowerLeft q u=1*lowerHeight q u by
          dsimp [eta]; field_simp [h.w_pos.ne'])

theorem D_norm {q t u : ℝ} (h : SmoothDomain q u)
    (hc : 0<Real.cos t) (hs : 0≤Real.sin t) :
    pairNorm 1 (c q t u) 0=
      requiredNorm q t u/secondComponent q (Real.cos t) (Real.sin t) u := by
  have h2 := (components_pos h.radius_lt_four h.toDomain hc
    (Real.cos_le_one t) hs (Real.sin_le_one t)).2
  rw [pairNorm_zero]
  dsimp [c,requiredNorm]
  have hS : Real.sqrt (secondComponent q (Real.cos t) (Real.sin t) u^2)=
      secondComponent q (Real.cos t) (Real.sin t) u := Real.sqrt_sq h2.le
  have hx : (1:ℝ)^2+(firstComponent q (Real.cos t) (Real.sin t) u/
      secondComponent q (Real.cos t) (Real.sin t) u)^2=
      (firstComponent q (Real.cos t) (Real.sin t) u^2+
        secondComponent q (Real.cos t) (Real.sin t) u^2)/
        secondComponent q (Real.cos t) (Real.sin t) u^2 := by
    field_simp
    ring
  rw [hx,Real.sqrt_div' _ (by positivity),hS]

/-- The endpoint identity: at a stationary position the endpoint is
`requiredNorm * (requiredNorm - R) / secondComponent`, the radial defect of the required D point
over its exact denominator. -/
theorem endpoint_identity {q R t u : ℝ} (h : SmoothDomain q u)
    (hR : 0≤R) (hR2 : R^2=q) (hc : 0<Real.cos t) (hs : 0≤Real.sin t)
    (hposition : positionHalf q (Real.cos t) (Real.sin t) u=0) :
    atE R (k q t u) (ell q t u) (c q t u) (eta q u) t+
        V R (ell q t u) (c q t u) t=
      requiredNorm q t u*(requiredNorm q t u-R)/
        secondComponent q (Real.cos t) (Real.sin t) u := by
  obtain ⟨hH,hA,hB,hE⟩ := supports h hR hR2 hc hs hposition
  have hD := D_norm h hc hs
  have h2 := (components_pos h.radius_lt_four h.toDomain hc
    (Real.cos_le_one t) hs (Real.sin_le_one t)).2
  have hN2 : requiredNorm q t u^2=
      firstComponent q (Real.cos t) (Real.sin t) u^2+
        secondComponent q (Real.cos t) (Real.sin t) u^2 := Real.sq_sqrt (by positivity)
  have hV : topLeft q u+topRight q u=3 := by dsimp [topLeft]; ring
  have hv : topHeight q u+lowerHeight q u=2 := by dsimp [lowerHeight]; ring
  have htilt : tilt (eta q u) t=lam q t u := rfl
  have hlin : atE R (k q t u) (ell q t u) (c q t u) (eta q u) t+
      V R (ell q t u) (c q t u) t=
      c q t u*firstComponent q (Real.cos t) (Real.sin t) u+
        secondComponent q (Real.cos t) (Real.sin t) u-
        R*(requiredNorm q t u/secondComponent q (Real.cos t) (Real.sin t) u) := by
    simp only [atE,contactScalar,V]
    rw [htilt]
    simp only [lam,firstComponent,secondComponent] at hH hD ⊢
    linear_combination (-1:ℝ)*hH-hA-hB-Real.sin t*hE-R*hD-k q t u*hV-
      (Real.cos t+eta q u*Real.sin t)*hv
  have hcF : c q t u*secondComponent q (Real.cos t) (Real.sin t) u=
      firstComponent q (Real.cos t) (Real.sin t) u := div_mul_cancel₀ _ h2.ne'
  have hdiv : requiredNorm q t u/secondComponent q (Real.cos t) (Real.sin t) u*
      secondComponent q (Real.cos t) (Real.sin t) u=requiredNorm q t u :=
    div_mul_cancel₀ _ h2.ne'
  rw [hlin,eq_div_iff h2.ne']
  linear_combination firstComponent q (Real.cos t) (Real.sin t) u*hcF-hN2-R*hdiv

theorem endpoint_nonnegative {q R t u : ℝ} (h : SmoothDomain q u)
    (hR : 0≤R) (hR2 : R^2=q) (hc : 0<Real.cos t) (hs : 0≤Real.sin t)
    (hposition : positionHalf q (Real.cos t) (Real.sin t) u=0)
    (hdefect : 0≤defect q (Real.cos t) (Real.sin t) u) :
    0≤atE R (k q t u) (ell q t u) (c q t u) (eta q u) t+
      V R (ell q t u) (c q t u) t := by
  have hN : 0≤requiredNorm q t u := Real.sqrt_nonneg _
  have hN2 : requiredNorm q t u^2=
      firstComponent q (Real.cos t) (Real.sin t) u^2+
        secondComponent q (Real.cos t) (Real.sin t) u^2 := Real.sq_sqrt (by positivity)
  have hNR : R≤requiredNorm q t u := by dsimp [defect] at hdefect; nlinarith
  have h2 := (components_pos h.radius_lt_four h.toDomain hc
    (Real.cos_le_one t) hs (Real.sin_le_one t)).2
  rw [endpoint_identity h hR hR2 hc hs hposition]
  exact div_nonneg (mul_nonneg hN (sub_nonneg.mpr hNR)) h2.le

/-- At a stationary radius the endpoint is nonnegative on the minimizing-position fibre of every
tilt in `tiltInterval`, not only at the stationary tilt. -/
theorem minimizing_endpoint {d : Stationary.Coordinates} (hd : d.IsStationary)
    {t : ℝ} (ht : t∈tiltInterval) :
    0≤atE (Real.sqrt d.q) (k d.q t (minimizingPosition d.q t))
      (ell d.q t (minimizingPosition d.q t)) (c d.q t (minimizingPosition d.q t))
      (eta d.q (minimizingPosition d.q t)) t+
      V (Real.sqrt d.q) (ell d.q t (minimizingPosition d.q t))
        (c d.q t (minimizingPosition d.q t)) t := by
  have h := minimizingPosition_smoothDomain (t:=t) hd.q_lower hd.q_upper
  obtain ⟨hc,hs,_⟩ := tiltInterval_bounds ht
  have hroot := minimizingPosition_root hd.q_lower hd.q_upper ht
  have hzero : positionHalf d.q (Real.cos t) (Real.sin t) (minimizingPosition d.q t)=0 := by
    dsimp [jointPosition] at hroot
    linarith
  have hn := stationary_envelope_nonneg hd ⟨ht.1.le,ht.2.le⟩
  rw [positionEnvelope_eq] at hn
  apply endpoint_nonnegative h (Real.sqrt_nonneg _) (Real.sq_sqrt (by linarith [hd.q_lower])) hc hs.le hzero
  exact hn

end SquaresInCircles.Eight.CriticalEFamily
end
end
end

section
/-!
## Pure ordinary charges for the exact critical family

The comparisons use the actual coefficient bounds
of the supporting chain. Both orders of k and c are included. The
one-angle A coefficient stays l, while H and D admit the stronger
two-angle relaxation needed for an arbitrary original EH0 angle.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CriticalEPureCharges
open CriticalECoefficients SoleNormGain PositiveAngularEnvelope
open OrdinaryAngleConcavity OrdinaryNegativeSlope OrdinaryNegativeEnvelope
open VaryingBFunctions VaryingBComparison SingleAngleConcavity

theorem A_ge_B {R t k l c eta : ℝ} (hR : R∈Icc 0 2)
    (h : Bounds t k l c eta) : V R l c t≤Vnu R l k l t := by
  have ho := h.order
  have hcos0 : 0≤1-Real.cos t := by linarith [Real.cos_le_one t]
  by_cases hck : c≤k
  · have hg := HalfRatioNormGain.larger_monotone hR.1 h.ell_pos ho.2.2.1 hck
      ho.2.2.2.2.2.1 h.angle
    have hp := mul_nonneg (show 0≤c-l by linarith [ho.2.2.1]) hcos0
    dsimp [V,Vnu,normGain] at *
    linarith
  · have hkc : k≤c := le_of_lt (lt_of_not_ge hck)
    have hs : t∈Icc 0 (1/5:ℝ) := ⟨h.angle.1,by linarith [h.angle_upper]⟩
    have hg := coefficient_short hR ho.1 hkc ho.2.2.2.1
      (show l≤(18/25)*k by linarith [h.ell_k]) hs
    have hcos := SoleLowAComparison.cosine_loss_lower hs
    have hck' : c-k≤t/5 := by linarith [h.difference,h.angle_lower]
    have hm := mul_le_mul_of_nonneg_right ho.2.2.2.2.2.2 hcos0
    have hm' := mul_le_mul_of_nonneg_left hcos (by norm_num : (0:ℝ)≤1/4)
    have hkg := mul_le_mul_of_nonneg_left hck' (show 0≤(11/20)*t by linarith [h.angle_lower])
    dsimp [V,Vnu,normGain] at *
    nlinarith [sq_nonneg t]

theorem A_ge_B_at_cap {R t k l c eta : ℝ} (hR : R∈Icc 0 2)
    (h : Bounds t k l c eta) : V R l c frameCap≤Vnu R l k l frameCap := by
  have ho := h.order
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have hcos0 : 0≤1-Real.cos frameCap := by linarith [Real.cos_le_one frameCap]
  by_cases hck : c≤k
  · have hg := HalfRatioNormGain.larger_monotone hR.1 h.ell_pos ho.2.2.1 hck
      ho.2.2.2.2.2.1 hh
    have hp := mul_nonneg (show 0≤c-l by linarith [ho.2.2.1]) hcos0
    dsimp [V,Vnu,normGain] at *
    linarith
  · have hkc : k≤c := le_of_lt (lt_of_not_ge hck)
    have hg := coefficient_cap hR ho.1 hkc ho.2.2.2.1
      (show l≤(18/25)*k by linarith [h.ell_k])
    have hcos := cos_upper_four (show (0:ℝ)≤frameCap by norm_num [frameCap])
    have hc : (117/500:ℝ)≤1-Real.cos frameCap := by norm_num [frameCap] at hcos; linarith
    have hm := mul_le_mul_of_nonneg_right ho.2.2.2.2.2.2 hcos0
    have hm' := mul_le_mul_of_nonneg_left hc (by norm_num : (0:ℝ)≤1/4)
    dsimp [V,Vnu,normGain] at *
    linarith [h.difference]

theorem B_zero_slope {R t k l c eta : ℝ} (hR : R∈Icc 0 2)
    (h : Bounds t k l c eta) : Vd R l c 0≤23/20 := by
  have hc : 0<c := by linarith [h.c_lower]
  have hr0 : 0≤l/c := div_nonneg h.ell_pos.le hc.le
  have hr1 : l/c≤7/10 := (div_le_iff₀ hc).2 (by linarith [h.ell_c_upper])
  have hz : (0:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hfrac := normalized_fraction_mono hr0 hr1 (by norm_num) hz
  have hN := root_pos (7/10) hz
  have hN2 := root_sq (7/10) hz
  have hNlo : (61/50:ℝ)≤root (7/10) 0 := by nlinarith
  have hnum : c*R*(7/10)≤(501/500)*2*(7/10) := by
    have hm := mul_le_mul (show c≤501/500 by linarith [h.c_upper]) hR.2 hR.1
      (by norm_num : (0:ℝ)≤501/500)
    nlinarith
  have hbound : c*R*(7/10)/root (7/10) 0≤23/20 := by
    apply (div_le_iff₀ hN).2
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hfrac (mul_nonneg hc.le hR.1)
  rw [Vd_normalized hc]
  simp only [Real.sin_zero,Real.cos_zero,neg_zero,zero_add,mul_one]
  calc
    c*(R*(l/c)/root (l/c) 0)≤c*R*(7/10)/root (7/10) 0 := by
      simpa only [mul_div_assoc,mul_assoc] using hm
    _≤23/20 := hbound

theorem B_short {R t k l c eta : ℝ} (hR : 0≤R) (hQU : R^2≤Eight.qCap)
    (h : Bounds t k l c eta) : V R l c t≤(23/20)*t := by
  have ho := h.order
  have hc : 0<c := by linarith [h.c_lower]
  have hR2 : R≤2 := by norm_num [Eight.qCap] at hQU; nlinarith
  have hz : (0:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hanti := Vd_antitone hR hQU h.ell_pos ho.2.2.1 ho.2.2.2.2.1
  have hd := derivative_reserve (f := fun x => -V R l c x)
    (df := fun x => -Vd R l c x) (k := -Vd R l c 0)
    (fun x hx => (V_hasDerivAt h.ell_pos hc hx).neg.continuousAt.continuousWithinAt)
    (fun x hx => (V_hasDerivAt h.ell_pos hc (Ioo_subset_Icc_self hx)).neg)
    (fun x hx => neg_le_neg (hanti hz (Ioo_subset_Icc_self hx) hx.1.le))
    hz h.angle h.angle.1
  simp only [V_zero,neg_zero,sub_zero] at hd
  have hm := mul_le_mul_of_nonneg_right (B_zero_slope ⟨hR,hR2⟩ h) h.angle.1
  linarith

theorem B_cap {R t k l c eta : ℝ} (hR : R∈Icc 0 2)
    (h : Bounds t k l c eta) : V R l c frameCap<18/25 := by
  have ho := h.order
  have hc : 0<c := by linarith [h.c_lower]
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have hsmall := normGain_smaller_mono hR.1 hc hh
    ⟨by linarith [ho.2.2.2.2.1],ho.2.2.1⟩
    (show (673/1000:ℝ)∈Icc (c/2) c by constructor <;> linarith [h.c_lower,h.c_upper])
    (show l≤673/1000 by linarith [h.ell_upper])
  have hlarge := normGain_larger_mono hR.1 (by norm_num : (0:ℝ)<673/1000)
    (show (673/1000:ℝ)≤c by linarith [h.c_lower])
    (show c≤501/500 by linarith [h.c_upper]) hh
    (show Real.sin frameCap*(501/500)≤(673/1000:ℝ) by linarith [(transport_trig hh).2.2.2.1])
  have hX2 : (pairNorm (673/1000) (501/500) 0)^2=(673/1000:ℝ)^2+(501/500)^2 := by
    simp only [pairNorm_zero]
    exact Real.sq_sqrt (by positivity)
  have hY2 := SoleLowGap.negative_norm_square (by norm_num : (0:ℝ)<673/1000)
    (by norm_num : (0:ℝ)<501/500) hh
  have hX0 : 0≤pairNorm (673/1000) (501/500) 0 := Real.sqrt_nonneg _
  have hY0 : 0≤pairNorm (673/1000) (501/500) (-frameCap) := Real.sqrt_nonneg _
  have hX : pairNorm (673/1000) (501/500) 0≤151/125 := by nlinarith
  have hY : (383/500:ℝ)≤pairNorm (673/1000) (501/500) (-frameCap) := by
    nlinarith [(transport_trig hh).2.2.2.1]
  have hdiff : pairNorm (673/1000) (501/500) 0-
      pairNorm (673/1000) (501/500) (-frameCap)≤221/500 := by linarith
  have hmul := mul_le_mul_of_nonneg_left hdiff hR.1
  have hcos := cos_upper_four (show (0:ℝ)≤frameCap by norm_num [frameCap])
  have hclo : (117/500:ℝ)≤1-Real.cos frameCap := by norm_num [frameCap] at hcos; linarith
  have hpen := mul_le_mul (show (17253/20000:ℝ)≤c by linarith [h.c_lower])
    hclo (by norm_num : (0:ℝ)≤117/500) hc.le
  dsimp [normGain,V] at *
  nlinarith [hR.2]

theorem wide_dominates {R p q nu t k l c eta : ℝ}
    (hR : 0≤R) (hQL : Eight.qLow≤R^2) (hQU : R^2≤Eight.qCap)
    (hp : SoleLowChargeBounds.base≤p) (hpq : p≤q) (hq : q∈Icc 1 (21/20:ℝ))
    (hnu : nu≤21/20) (h : Bounds t k l c eta) :
    V R l c t≤Vnu R p q nu t ∧ V R l c frameCap≤Vnu R p q nu frameCap := by
  have hq' : q∈Icc 1 (28/25:ℝ) := ⟨hq.1,by linarith [hq.2]⟩
  have hn' : nu≤28/25 := by linarith
  have ht' : t∈SoleECoefficients.domain .low := ⟨h.angle.1,by linarith [h.angle_upper]⟩
  have hR2 : R≤2 := by norm_num [Eight.qCap] at hQU; nlinarith
  constructor
  · have hw := SoleLowChargeBounds.wide_short hR hQL hp hpq hq' hn' ht'
    have hB := B_short hR hQU h
    nlinarith [h.angle.1]
  · linarith [SoleLowChargeBounds.wide_cap hR hQL hp hpq hq' hn',B_cap ⟨hR,hR2⟩ h]

end SquaresInCircles.Eight.CriticalEPureCharges
end
end
end

section
/-!
## The correlated c/k bound for the sharp critical family

Position stationarity expresses c/k as a ratio
which decreases with the actual position. Its denominator increases
by circle monotonicity. The comparison therefore uses the lower affine
chain itself, preserving the correlation lost by an independent box
for k and c. The endpoint polynomial covers the complete tilt strip.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CriticalERatioBounds
open CriticalEPolynomials CriticalERadicals CriticalESubstitution CriticalEPosition
open Stationary.FiveCornerGeometry

def dualRatio (q t u : ℝ) : ℝ :=
  (2-u)/(topRight q u*(Real.sin t+Real.cos t*u/lowerRight q u))

theorem positionA_pos {q t u : ℝ} (h : SmoothDomain q u)
    (hc : 0<Real.cos t) (hs : 0<Real.sin t) :
    0<Real.sin t+Real.cos t*u/lowerRight q u := by
  have hh := div_nonneg (mul_nonneg hc.le h.height_nonneg) h.r_pos.le
  linarith

theorem dualRatio_antitone {q t u₀ u : ℝ}
    (h₀ : SmoothDomain q u₀) (h : SmoothDomain q u) (hu : u₀≤u)
    (hc : 0<Real.cos t) (hs : 0<Real.sin t) : dualRatio q t u≤dualRatio q t u₀ := by
  have hL0 : 0<2-u₀ := by linarith [h₀.toDomain.height_lt_two h₀.radius_lt_four]
  have hL : 0<2-u := by linarith [h.toDomain.height_lt_two h.radius_lt_four]
  have hr : lowerRight q u≤lowerRight q u₀ := upper_antitone h₀.height_nonneg hu
  have hU : topRight q u₀≤topRight q u :=
    upper_antitone hL.le (show 2-u≤2-u₀ by linarith)
  have hright : u₀/lowerRight q u₀≤u/lowerRight q u := by
    apply (div_le_div_iff₀ h₀.r_pos h.r_pos).2
    exact mul_le_mul hu hr h.r_pos.le h.height_nonneg
  have hp : Real.sin t+Real.cos t*u₀/lowerRight q u₀≤
      Real.sin t+Real.cos t*u/lowerRight q u := by
    have hh := mul_le_mul_of_nonneg_left hright hc.le
    rw [mul_div_assoc,mul_div_assoc]
    linarith
  have hp₀ := positionA_pos h₀ hc hs
  have hp₁ := positionA_pos h hc hs
  have hd := mul_le_mul hU hp hp₀.le h.U_pos.le
  dsimp [dualRatio]
  apply (div_le_div_iff₀ (mul_pos h.U_pos hp₁) (mul_pos h₀.U_pos hp₀)).2
  exact mul_le_mul (show 2-u≤2-u₀ by linarith) hd
    (mul_pos h₀.U_pos hp₀).le hL0.le

theorem stationary_ratio {q t u : ℝ} (h : SmoothDomain q u)
    (hc : 0<Real.cos t) (hs : 0<Real.sin t)
    (hposition : positionHalf q (Real.cos t) (Real.sin t) u=0) :
    CriticalEFamily.c q t u/CriticalEFamily.k q t u=dualRatio q t u := by
  have hpos := CriticalEFamily.positive_weights h hc hs.le
  have hp := positionA_pos h hc hs
  have he := CriticalEFamily.stationary_ratio h hc hs.le hposition
  have hid : CriticalEFamily.k q t u*dualRatio q t u=
      CriticalEFamily.ell q t u/(Real.sin t+Real.cos t*u/lowerRight q u) := by
    dsimp [dualRatio,CriticalEFamily.ell]
    field_simp [h.U_pos.ne',hp.ne']
  rw [he,mul_div_cancel_right₀ _ hp.ne'] at hid
  exact (div_eq_iff hpos.2.2.1.ne').2 (by linarith [hid])

theorem lower_comparison_upper {q t : ℝ}
    (hq : q∈Icc (qLower:ℝ) (qUpper:ℝ)) (ht : t∈Icc (1/10:ℝ) (4/25)) :
    dualRatio q t (ev t uMinus)<51/50 := by
  have hu : ev t uMinus∈Icc (ev t (a .lower)) (ev t (b .lower)) := ⟨le_rfl,le_rfl⟩
  have hr := actual_radicals .lower hq ht hu
  let B := boxes ht hu hr
  let X := B.other.mul B.r
  let Y := B.U.mul ((B.sine.mul B.r).add (B.cosine.mul B.height))
  have hY : 0<Y.lo := by
    have hU : 0<B.U.lo := by
      have h1 : 1/2<ev t (ULo .lower) := (polynomial_coordinates .lower 1 ht).1
      rw [B.U_lo]; linarith
    have hC : 0<B.cosine.lo := by rw [B.cosine_lo]; exact (trig_bounds ht).2.2.2
    have hu0 : 0<B.height.lo := by rw [B.height_lo]; linarith [(endpoints ht .lower).1]
    dsimp [Y,PositiveInterval.mul,PositiveInterval.add]
    exact mul_pos hU (add_pos_of_nonneg_of_pos
      (mul_nonneg B.sine.lo_nonneg B.r.lo_nonneg) (mul_pos hC hu0))
  have hpoly : X.hi<(51/50)*Y.lo := by
    have hh := coefficient_positive .cK (local_parameter ht)
    change 0<ev t (cleared .cK) at hh
    have e2 : ev t (2:Polynomial ℚ)=2 := by rw [ev]; exact map_ofNat _ 2
    have hX : X.hi=(2-ev t (a .lower))*ev t (rHi .lower) := by
      simp only [X,PositiveInterval.mul]; rw [B.other_hi,B.r_hi]
    have hY' : Y.lo=ev t (ULo .lower)*(ev t sineLo*ev t (rLo .lower)+
        ev t cosineLo*ev t (a .lower)) := by
      simp only [Y,PositiveInterval.mul,PositiveInterval.add]
      rw [B.U_lo,B.sine_lo,B.r_lo,B.cosine_lo,B.height_lo]
    simp only [cleared,ev_sub,ev_mul,ev_add,ev_C,e2] at hh
    rw [hX,hY']
    push_cast at hh
    linarith
  have hh := PositiveInterval.upper_ratio X Y hY (by norm_num : (0:ℝ)≤51/50) hpoly
  have hd := hr.smoothDomain ht (by rw [ev_minus]; linarith [ht.2])
    (by norm_num [qUpper] at hq; linarith [hq.2])
  obtain ⟨hc,hs,_⟩ := tiltInterval_bounds (angle_mem ht)
  have hp := positionA_pos hd hc hs
  have hnum : 0<Real.sin t*lowerRight q (ev t uMinus)+Real.cos t*ev t uMinus := by
    have hu0 : 0≤ev t uMinus := hd.height_nonneg
    exact add_pos_of_pos_of_nonneg (mul_pos hs hd.r_pos) (mul_nonneg hc.le hu0)
  have hid : (2-ev t uMinus)*lowerRight q (ev t uMinus)/
      (topRight q (ev t uMinus)*(Real.sin t*lowerRight q (ev t uMinus)+Real.cos t*ev t uMinus))=
      dualRatio q t (ev t uMinus) := by
    have hden : topRight q (ev t uMinus)*(Real.sin t*lowerRight q (ev t uMinus)+
        Real.cos t*ev t uMinus)=topRight q (ev t uMinus)*(Real.sin t+
        Real.cos t*ev t uMinus/lowerRight q (ev t uMinus))*lowerRight q (ev t uMinus) := by
      rw [mul_assoc,add_mul,div_mul_cancel₀ _ hd.r_pos.ne']
    rw [hden,mul_div_mul_right _ _ hd.r_pos.ne']
    rfl
  rwa [hid] at hh

theorem original_ratio_upper {q t u : ℝ}
    (hq : q∈Icc (qLower:ℝ) (qUpper:ℝ)) (ht : t∈Icc (1/10:ℝ) (4/25))
    (hu : u∈Icc (ev t uMinus) (ev t uPlus))
    (hposition : positionHalf q (Real.cos t) (Real.sin t) u=0) :
    CriticalEFamily.c q t u/CriticalEFamily.k q t u<51/50 := by
  have hl : ev t uMinus∈Icc (ev t (a .lower)) (ev t (b .lower)) := ⟨le_rfl,le_rfl⟩
  have hrl := actual_radicals .lower hq ht hl
  have hru := actual_radicals .mixed hq ht hu
  have hq4 : q<4 := by norm_num [qUpper] at hq; linarith [hq.2]
  have hm0 : 0≤ev t uMinus := by rw [ev_minus]; linarith [ht.2]
  have hd₀ := hrl.smoothDomain ht hm0 hq4
  have hd := hru.smoothDomain ht (by linarith [hu.1]) hq4
  obtain ⟨hc,hs,_⟩ := tiltInterval_bounds (angle_mem ht)
  rw [stationary_ratio hd hc hs hposition]
  exact (dualRatio_antitone hd₀ hd hu.1 hc hs).trans_lt (lower_comparison_upper hq ht)

end SquaresInCircles.Eight.CriticalERatioBounds
end
end
end

section
/-!
## Adapted exact-dual coefficients in the critical positive-T triangle

The starting coefficients are the actual supporting-chain dual.
The T coefficient decreases with its actual primary error, yielding
the correlated l/m, l/c and m-k bounds used by the ordinary envelope.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CriticalPositiveTCoefficients
open Candidate ExceptionalContactStress PositiveAngularEnvelope OrdinaryNegativeEnvelope

def adaptedK (K z : ℝ) : ℝ := K+3/50*z
def adaptedL (L z : ℝ) : ℝ := L-23/100*z
def adaptedC (C z : ℝ) : ℝ := C-53/100*z
def adaptedM (C eta z : ℝ) : ℝ := adaptedC C z*tilt eta z
def mDerivative (C eta z : ℝ) : ℝ :=
  -(53/100)*tilt eta z+adaptedC C z*(-Real.sin z+eta*Real.cos z)

theorem tilt_bounds {eta s : ℝ} (heta : eta∈Icc (27/100:ℝ) (31/100))
    (hs : s∈Icc 0 (4/25:ℝ)) : 1≤tilt eta s ∧ tilt eta s<26/25 := by
  have heta' : eta∈Icc (1/4:ℝ) (7/10) := ⟨by linarith [heta.1],by linarith [heta.2]⟩
  have hs' : s∈Icc 0 (1/5:ℝ) := ⟨hs.1,by linarith [hs.2]⟩
  have hsin := (transport_trig (show s∈Icc 0 (7/10:ℝ) from ⟨hs.1,by linarith [hs.2]⟩)).2.2.1
  have hη := mul_le_mul heta.2 (Real.sin_le hs.1) hsin (by norm_num : (0:ℝ)≤31/100)
  have hcos := cos_upper_four hs.1
  have h4 : s^4≤(4/25:ℝ)^4 := pow_le_pow_left₀ hs.1 hs.2 4
  have hq := mul_nonneg (show 0≤4/25-s by linarith [hs.2]) (show 0≤23/50-s by linarith [hs.2])
  refine ⟨SoleLowCoefficientBounds.tilted_lower heta' hs',?_⟩
  unfold ExceptionalContactStress.tilt
  nlinarith

theorem tilt_derivative {eta s : ℝ} (heta : eta∈Icc (27/100:ℝ) (31/100))
    (hs : s∈Icc 0 (4/25:ℝ)) :
    53/500< -Real.sin s+eta*Real.cos s ∧ -Real.sin s+eta*Real.cos s≤31/100 := by
  have hc := Real.one_sub_sq_div_two_le_cos (x := s)
  have hs2 : s^2≤(4/25:ℝ)^2 := pow_le_pow_left₀ hs.1 hs.2 2
  have hcl : (617/625:ℝ)≤Real.cos s := by linarith
  have hm := mul_le_mul heta.1 hcl (by norm_num : (0:ℝ)≤617/625)
    (by linarith [heta.1] : 0≤eta)
  have hmu := mul_le_mul_of_nonneg_left (Real.cos_le_one s)
    (by linarith [heta.1] : 0≤eta)
  have hsin := (transport_trig (show s∈Icc 0 (7/10:ℝ) from ⟨hs.1,by linarith [hs.2]⟩)).2.2.1
  constructor <;> linarith [(Real.sin_le hs.1).trans hs.2,heta.2]

theorem m_hasDerivAt (C eta z : ℝ) : HasDerivAt (adaptedM C eta) (mDerivative C eta z) z := by
  have hc : HasDerivAt (fun y => C-53/100*y) (-(53/100*1)) z :=
    ((hasDerivAt_id' z).const_mul (53/100)).const_sub C
  have hf : HasDerivAt (fun y => Real.cos y+eta*Real.sin y) (-Real.sin z+eta*Real.cos z) z :=
    (Real.hasDerivAt_cos z).fun_add ((Real.hasDerivAt_sin z).const_mul eta)
  have h := hc.fun_mul hf
  have he : adaptedM C eta=fun y => (C-53/100*y)*(Real.cos y+eta*Real.sin y) := rfl
  rw [he]
  convert h using 1
  simp only [mDerivative,adaptedC,ExceptionalContactStress.tilt]
  ring

theorem m_decreases {C eta z : ℝ} (hC : C∈Icc (37/40:ℝ) 1)
    (heta : eta∈Icc (27/100:ℝ) (31/100)) (hz : z∈Icc 0 (4/25:ℝ)) :
    adaptedM C eta z≤C-(11/50)*z := by
  have hd (s : ℝ) (hs : s∈Icc 0 (4/25:ℝ)) : mDerivative C eta s≤ -(11/50) := by
    have hf := tilt_bounds heta hs
    have hdf := tilt_derivative heta hs
    have hc : adaptedC C s∈Icc 0 1 := by
      dsimp [adaptedC]
      constructor <;> linarith [hC.1,hC.2,hs.1,hs.2]
    have hm := mul_le_mul hc.2 hdf.2
      (by linarith [hdf.1] : 0≤ -Real.sin s+eta*Real.cos s) (by norm_num : (0:ℝ)≤1)
    dsimp [mDerivative]
    linarith [hf.1]
  have h := derivative_reserve (f:=fun s => -adaptedM C eta s)
    (df:=fun s => -mDerivative C eta s) (k:=11/50)
    (fun s _ => (m_hasDerivAt C eta s).neg.continuousAt.continuousWithinAt)
    (fun s _ => (m_hasDerivAt C eta s).neg)
    (fun s hs => by linarith [hd s (Ioo_subset_Icc_self hs)])
    (show (0:ℝ)∈Icc 0 (4/25:ℝ) by norm_num) hz hz.1
  have h0 : adaptedM C eta 0=C := by
    simp [adaptedM,adaptedC,ExceptionalContactStress.tilt]
  linarith

structure Bounds (t z k l c m eta : ℝ) : Prop where
  angle_lower : 1/10≤t
  angle_upper : t≤4/25
  z_nonneg : 0≤z
  z_le : z≤t
  k_lower : 37/40<k
  k_upper : k<199/200
  c_lower : 4201/5000<c
  c_le_m : c≤ m
  m_upper : m<1
  ell_pos : 0<l
  ell_upper : l<67/100
  ell_k : l<(27/40)*k
  ell_m_lower : (61/100)*m<l
  ell_m_upper : l< m
  ell_c_upper : l<(71/100)*c
  difference : m-k<1/50
  gap : 31/125< m-l
  delta_upper : m-c≤(31/100)*z
  refined_gap : 37/125-(3/10)*z+(m-c)< m-l
  eta_lower : 27/100<eta
  eta_upper : eta<31/100

theorem adapted_bounds {t z K L C eta : ℝ}
    (h : CriticalECoefficients.Bounds t K L C eta) (hz : z∈Icc 0 t) :
    Bounds t z (adaptedK K z) (adaptedL L z) (adaptedC C z) (adaptedM C eta z) eta := by
  have heta : eta∈Icc (27/100:ℝ) (31/100) := ⟨h.eta_lower.le,h.eta_upper.le⟩
  have hz' : z∈Icc 0 (4/25:ℝ) := ⟨hz.1,hz.2.trans h.angle_upper⟩
  have hc : (4201/5000:ℝ)<adaptedC C z := by
    dsimp [adaptedC]
    linarith [h.c_lower,hz'.2]
  have hf := tilt_bounds heta hz'
  have hcm : adaptedC C z≤adaptedM C eta z := by
    have hh := mul_le_mul_of_nonneg_left hf.1 (show 0≤adaptedC C z by linarith)
    simpa [adaptedM] using hh
  have hmd := m_decreases ⟨h.c_lower.le,h.c_upper.le⟩ heta hz'
  have hmu : adaptedM C eta z<1 := by linarith [h.c_upper,hz'.1]
  have hgap0 : (37/125:ℝ)<C-L := by linarith [h.ell_c_upper,h.c_lower]
  have hdelta : adaptedM C eta z-adaptedC C z≤(31/100)*z := by
    have hs := (transport_trig (show z∈Icc 0 (7/10:ℝ) from ⟨hz'.1,by linarith [hz'.2]⟩)).2.2.1
    have hsU := Real.sin_le hz'.1
    have hη := mul_le_mul h.eta_upper.le hsU hs (by norm_num : (0:ℝ)≤31/100)
    have hcU : adaptedC C z≤1 := by dsimp [adaptedC]; linarith [h.c_upper,hz'.1]
    have htilt : 0≤ExceptionalContactStress.tilt eta z-1 := by linarith [hf.1]
    have hcoef : ExceptionalContactStress.tilt eta z-1≤(31/100)*z := by
      dsimp [ExceptionalContactStress.tilt]; linarith [Real.cos_le_one z]
    have hh := mul_le_mul hcU hcoef htilt (by norm_num : (0:ℝ)≤1)
    have he : adaptedM C eta z-adaptedC C z=adaptedC C z*(ExceptionalContactStress.tilt eta z-1) := by
      dsimp [adaptedM]; ring
    rw [he]
    linarith
  refine ⟨h.angle_lower,h.angle_upper,hz.1,hz.2,?_,?_,hc,hcm,hmu,?_,?_,?_,?_,?_,?_,?_,?_,hdelta,?_,
    h.eta_lower,h.eta_upper⟩
  all_goals dsimp only [adaptedK,adaptedL] at *
  all_goals dsimp only [adaptedC] at hc hcm hdelta hmd ⊢
  all_goals linarith [h.k_lower,h.k_upper,h.c_lower,h.c_upper,h.ell_pos,h.ell_upper,
    h.ell_k,h.ell_c_lower,h.ell_c_upper,h.difference,hz'.1,hz'.2]

theorem Bounds.angle {t z k l c m eta : ℝ} (h : Bounds t z k l c m eta) : t∈Icc 0 frameCap :=
  ⟨by linarith [h.angle_lower],by dsimp [frameCap]; linarith [h.angle_upper]⟩
theorem Bounds.tilt {t z k l c m eta s : ℝ} (h : Bounds t z k l c m eta) (hs : s∈Icc 0 t) :
    1≤tilt eta s ∧ tilt eta s<26/25 :=
  tilt_bounds ⟨h.eta_lower.le,h.eta_upper.le⟩ ⟨hs.1,hs.2.trans h.angle_upper⟩
theorem Bounds.order {t z k l c m eta : ℝ} (h : Bounds t z k l c m eta) :
    0<k ∧ l≤k ∧ l≤c ∧ l≤ m ∧ k≤2*l ∧ c≤2*l ∧ m≤2*l := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩ <;> linarith [h.k_lower,h.k_upper,h.c_lower,h.c_le_m,h.ell_pos,
    h.ell_k,h.ell_m_lower,h.ell_m_upper,h.ell_c_upper]

def weights (td : Bool) (k l c m eta x e : ℝ) : ExceptionalPositiveTBlocks.Weights :=
  ⟨k*tilt eta x,k,l,if td then m else c,if td then c else m,tilt eta e⟩

end SquaresInCircles.Eight.CriticalPositiveTCoefficients
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CriticalEWeightBounds
open CriticalEPolynomials CriticalERadicals CriticalESubstitution CriticalEPosition
open CriticalEFamily Stationary.FiveCornerGeometry

theorem weight_formulas {q t u : ℝ} (h : SmoothDomain q u) :
    k q t u=(Real.cos t*lowerLeft q u+Real.sin t*lowerHeight q u)*topLeft q u/
      (lowerLeft q u*topHeight q u) ∧
    ell q t u=(Real.cos t*lowerLeft q u+Real.sin t*lowerHeight q u)*topLeft q u*(2-u)/
      (lowerLeft q u*topHeight q u*topRight q u) := by
  dsimp [k,ell,lam,eta]
  constructor <;> field_simp [h.w_pos.ne',h.Y_pos.ne',h.U_pos.ne']

theorem original_bounds {q t u : ℝ}
    (hq : q∈Icc (qLower:ℝ) (qUpper:ℝ)) (ht : t∈Icc (1/10:ℝ) (4/25))
    (hu : u∈Icc (ev t uMinus) (ev t uPlus))
    (hposition : positionHalf q (Real.cos t) (Real.sin t) u=0) :
    CriticalECoefficients.Bounds t (k q t u) (ell q t u) (c q t u) (eta q u) := by
  have hr := actual_radicals .mixed hq ht hu
  have hu0 : 0≤u := by
    have h1 := hu.1
    rw [ev_minus] at h1
    linarith [ht.2]
  have hd := hr.smoothDomain ht hu0 (by norm_num [qUpper] at hq; linarith [hq.2])
  obtain ⟨hc,hs,_⟩ := tiltInterval_bounds (angle_mem ht)
  have hpos := positive_weights hd hc hs.le
  have hforms := weight_formulas (t := t) hd
  have e2 : ev t (2:Polynomial ℚ)=2 := by rw [ev]; exact map_ofNat _ 2
  let B := boxes ht hu hr
  let L := (B.cosine.mul B.w).add (B.sine.mul B.v)
  let KN := L.mul B.V
  let KD := B.w.mul B.Y
  let EN := KN.mul B.other
  let ED := KD.mul B.U
  let PN := (B.sine.mul B.r).add (B.cosine.mul B.height)
  have hp (i : Fin 6) : 0<ev t (coordinateLower .mixed i) := by
    linarith [(polynomial_coordinates .mixed i ht).1]
  have hrlo : 0<B.r.lo := by rw [B.r_lo]; exact hp 0
  have hUlo : 0<B.U.lo := by rw [B.U_lo]; exact hp 1
  have hYlo : 0<B.Y.lo := by rw [B.Y_lo]; exact hp 3
  have hwlo : 0<B.w.lo := by rw [B.w_lo]; exact hp 5
  have hKDp : 0<KD.lo := mul_pos hwlo hYlo
  have hEDp : 0<ED.lo := mul_pos hKDp hUlo
  have hsecond : 0<B.second.lo := by
    rw [B.second_lo]
    linarith [(auxiliary_bounds .mixed ht).2.2.2]
  have hpoly (i : Coefficient) : 0<ev t (cleared i) := coefficient_positive i (local_parameter ht)
  have helo : (27/100:ℝ)<eta q u := by
    apply PositiveInterval.lower_ratio B.v B.w hwlo (by norm_num)
    rw [B.w_hi,B.v_lo]
    have hh := hpoly .etaLower
    simp only [cleared,ev_sub,ev_mul,ev_C] at hh
    push_cast at hh
    linarith
  have hehi : eta q u<31/100 := by
    apply PositiveInterval.upper_ratio B.v B.w hwlo (by norm_num)
    rw [B.v_hi,B.w_lo]
    have hh := hpoly .etaUpper
    simp only [cleared,ev_sub,ev_mul,ev_C] at hh
    push_cast at hh
    linarith
  have hklo : (37/40:ℝ)<k q t u := by
    rw [hforms.1]
    apply PositiveInterval.lower_ratio KN KD hKDp (by norm_num)
    show (37/40:ℝ)*(B.w.hi*B.Y.hi)<(B.cosine.lo*B.w.lo+B.sine.lo*B.v.lo)*B.V.lo
    rw [B.w_hi,B.Y_hi,B.cosine_lo,B.w_lo,B.sine_lo,B.v_lo,B.V_lo]
    have hh := hpoly .kLower
    simp only [cleared,ev_sub,ev_mul,ev_add,ev_C] at hh
    push_cast at hh
    linarith
  have hkhi : k q t u<197/200 := by
    rw [hforms.1]
    apply PositiveInterval.upper_ratio KN KD hKDp (by norm_num)
    show (B.cosine.hi*B.w.hi+B.sine.hi*B.v.hi)*B.V.hi<(197/200:ℝ)*(B.w.lo*B.Y.lo)
    rw [B.w_hi,B.Y_lo,B.cosine_hi,B.w_lo,B.sine_hi,B.v_hi,B.V_hi]
    have hh := hpoly .kUpper
    simp only [cleared,ev_sub,ev_mul,ev_add,ev_C] at hh
    push_cast at hh
    linarith
  have hello : 0<ell q t u := hpos.2.2.2.1
  have hellhi : ell q t u<67/100 := by
    rw [hforms.2]
    apply PositiveInterval.upper_ratio EN ED hEDp (by norm_num)
    show (B.cosine.hi*B.w.hi+B.sine.hi*B.v.hi)*B.V.hi*B.other.hi<
      (67/100:ℝ)*(B.w.lo*B.Y.lo*B.U.lo)
    rw [B.w_hi,B.Y_lo,B.cosine_hi,B.w_lo,B.sine_hi,B.v_hi,B.V_hi,B.other_hi,B.U_lo]
    have hh := hpoly .ellUpper
    simp only [cleared,ev_sub,ev_mul,ev_add,ev_C,e2] at hh
    push_cast at hh
    linarith
  have helk : ell q t u<(27/40)*k q t u := by
    have hh : (2-u)/topRight q u<(27/40:ℝ) := by
      apply PositiveInterval.upper_ratio B.other B.U hUlo (by norm_num)
      rw [B.other_hi,B.U_lo]
      have hh := hpoly .ellK
      simp only [cleared,ev_sub,ev_mul,ev_C,e2] at hh
      push_cast at hh
      linarith
    have hm := mul_lt_mul_of_pos_left hh hpos.2.2.1
    have he : ell q t u=k q t u*((2-u)/topRight q u) := by
      simp only [ell]
      ring
    rw [he]
    linarith
  have hclo : (37/40:ℝ)<c q t u := by
    apply PositiveInterval.lower_ratio B.first B.second hsecond (by norm_num)
    rw [B.second_hi,B.first_lo]
    have hh := hpoly .cLower
    simp only [cleared,ev_sub,ev_mul,ev_C] at hh
    push_cast at hh
    linarith
  have hchi : c q t u<1 := by
    apply PositiveInterval.upper_ratio B.first B.second hsecond (by norm_num)
    rw [B.first_hi,B.second_lo]
    have hh := hpoly .cUpper
    simp only [cleared,ev_sub] at hh
    linarith
  have hPa : (Real.sin t*lowerRight q u+Real.cos t*u)/lowerRight q u=
      Real.sin t+Real.cos t*u/lowerRight q u := by
    field_simp [hd.r_pos.ne']
  have hpaLo : (63/100:ℝ)<Real.sin t+Real.cos t*u/lowerRight q u := by
    rw [← hPa]
    apply PositiveInterval.lower_ratio PN B.r hrlo (by norm_num)
    show (63/100:ℝ)*B.r.hi<B.sine.lo*B.r.lo+B.cosine.lo*B.height.lo
    rw [B.r_hi,B.sine_lo,B.r_lo,B.cosine_lo,B.height_lo]
    have hh := hpoly .ellCLower
    simp only [cleared,ev_sub,ev_mul,ev_add,ev_C] at hh
    push_cast at hh
    linarith
  have hpaHi : Real.sin t+Real.cos t*u/lowerRight q u<(17/25:ℝ) := by
    rw [← hPa]
    apply PositiveInterval.upper_ratio PN B.r hrlo (by norm_num)
    show B.sine.hi*B.r.hi+B.cosine.hi*B.height.hi<(17/25:ℝ)*B.r.lo
    rw [B.r_hi,B.sine_hi,B.r_lo,B.cosine_hi,B.height_hi]
    have hh := hpoly .ellCUpper
    simp only [cleared,ev_sub,ev_mul,ev_C] at hh
    push_cast at hh
    linarith
  have hel := CriticalEFamily.stationary_ratio hd hc hs.le hposition
  have helcLo : (63/100)*c q t u<ell q t u := by
    rw [hel]
    linarith [mul_lt_mul_of_pos_left hpaLo hpos.2.2.2.2]
  have helcHi : ell q t u<(17/25)*c q t u := by
    rw [hel]
    linarith [mul_lt_mul_of_pos_left hpaHi hpos.2.2.2.2]
  have hck := CriticalERatioBounds.original_ratio_upper hq ht hu hposition
  have hck' : c q t u<(51/50)*k q t u := (div_lt_iff₀ hpos.2.2.1).1 hck
  have hdiff : c q t u-k q t u<1/50 := by linarith [hkhi]
  exact ⟨ht.1,ht.2,hklo,hkhi,hclo,hchi,hello,hellhi,helk,helcLo,helcHi,hdiff,helo,hehi⟩

/-- All coefficient conditions are conclusions about the actual
geometric position minimum, for each tilt in the critical interval. -/
theorem minimizing_bounds {q t : ℝ}
    (hq : q∈Icc (qLower:ℝ) (qUpper:ℝ)) (ht : t∈Icc (1/10:ℝ) (4/25)) :
    CriticalECoefficients.Bounds t (k q t (minimizingPosition q t))
      (ell q t (minimizingPosition q t)) (c q t (minimizingPosition q t))
      (eta q (minimizingPosition q t)) := by
  have hs := minimizingPosition_strip hq ht
  have hql : (79/40:ℝ)^2≤q := by norm_num [qLower] at hq ⊢; linarith [hq.1]
  have hqu : q≤9789/2500 := by norm_num [qUpper] at hq; linarith [hq.2]
  have hz := minimizingPosition_root hql hqu (angle_mem ht)
  apply original_bounds hq ht (by rw [Set.mem_Icc,ev_minus,ev_plus]; exact ⟨hs.1.le,hs.2.le⟩)
  dsimp [jointPosition] at hz
  linarith

end SquaresInCircles.Eight.CriticalEWeightBounds
end
end
end

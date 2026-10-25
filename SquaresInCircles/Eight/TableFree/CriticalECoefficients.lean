module

public import SquaresInCircles.Eight.TableFree.CriticalEFamily
public import SquaresInCircles.Eight.TableFree.ExceptionalECoefficients

/-!
# Coefficient conditions for the sharp critical ordinary envelope

Uncompiled source. These elementary consequences are separated from
the later construction of the coefficients from the actual minimizer.
The final geometric theorem will instantiate every field from that
construction. The weaker bounds used here also retain a two-angle H
block, so the original EH0 angle need not be zero.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.CriticalECoefficients
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
    (hR : 0≤R) (hQL : TableFree.qLow≤R^2) : contactScalar R eta t<3 := by
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

end SquaresInCircles.Eight.TableFree.CriticalECoefficients

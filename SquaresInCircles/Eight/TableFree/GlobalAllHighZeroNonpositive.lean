module

public import SquaresInCircles.Eight.TableFree.GlobalAllHighZeroNorms

/-!
# Original nonpositive-source zero projections

The fixed positive multiplier is applied to the retained owner-2
projection.  Both original corner disks are kept.  The source may be
core or outer: containment suffices for its force bound.  Uncompiled
source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalAllHigh

open Polynomial FramePair FrameCircleArc GlobalZeroSign GlobalOuterAnchor ZeroPolynomial

def zeroHighRaw (z : ℝ) : ℝ := z+kappa*(zeroMu z*(1+Real.sin z)-1-
  R*zeroN1 z-R*(zeroN2 z-Real.sqrt 2))
def zeroLowRaw (z : ℝ) : ℝ := zeroGap+z+kappa*(zeroMu z*Real.sin z+z/250-R*zeroN1 z)

theorem zero_source_force (s : State) {z : ℝ} (hz : z∈Icc 0 frameCap) :
    (zeroMu z*Real.sin z)*s.a+(1-zeroMu z*Real.cos z)*s.b≤
      R*zeroN1 z-(zeroMu z*Real.sin z+1-zeroMu z*Real.cos z)/2 := by
  have hn : 0≤zeroN1 z := Real.sqrt_nonneg _
  have hnorm : (zeroMu z*Real.sin z)^2+(1-zeroMu z*Real.cos z)^2=(zeroN1 z)^2 := by
    have hu := congrArg (fun r : ℝ => (zeroMu z)^2*r) (Real.sin_sq_add_cos_sq z)
    nlinarith [zeroN1_sq hz]
  have hsq : Q0*((zeroMu z*Real.sin z)^2+(1-zeroMu z*Real.cos z)^2)≤
      (R*zeroN1 z)^2 := by
    rw [hnorm,mul_pow,R_sq]
  convert circle_product_support s (mul_nonneg R_pos.le hn) hsq using 1 <;> ring

theorem zero_target_force (t : State) (z : ℝ) :
    t.a+zeroMu z*t.b≤R*zeroN2 z-(1+zeroMu z)/2 := by
  have hn : 0≤zeroN2 z := Real.sqrt_nonneg _
  have hsq : Q0*((1:ℝ)^2+(zeroMu z)^2)≤(R*zeroN2 z)^2 := by
    rw [mul_pow,R_sq,zeroN2_sq]
    norm_num
  simpa only [one_mul] using circle_product_support t (mul_nonneg R_pos.le hn) hsq

theorem high_polynomial_transfer {z : ℝ} (hz : z∈Icc 0 frameCap) :
    aeval z H≤zeroHighRaw z := by
  have hmu : 0≤zeroMu z := by linarith [(zeroMu_bounds hz).1]
  have hs : Arithmetic.sin7 z≤Real.sin z := by
    simpa only [Arithmetic.sin7] using sin_lower_seven hz.1
  have hsin := mul_le_mul_of_nonneg_left hs hmu
  have hnorm1 := radius_norm1_envelope hz
  have hnorm2 := radius_norm2_difference hz
  rw [H_eval]
  dsimp [zeroHighRaw,zeroMu,kappa] at *
  nlinarith only [hsin,hnorm1,hnorm2]

theorem low_polynomial_transfer {z : ℝ} (hz : z∈Icc 0 frameCap) :
    aeval z L≤zeroLowRaw z := by
  have hmu : 0≤zeroMu z := by linarith [(zeroMu_bounds hz).1]
  have hs : Arithmetic.sin7 z≤Real.sin z := by
    simpa only [Arithmetic.sin7] using sin_lower_seven hz.1
  have hsin := mul_le_mul_of_nonneg_left hs hmu
  have hnorm := radius_norm1_envelope hz
  rw [L_eval]
  dsimp [zeroLowRaw,zeroMu,kappa] at *
  nlinarith only [hsin,hnorm]

theorem lower_target_constant_gap : zeroGap<2*kappa*c0-
    ((6/5)*zeroU+(13/25)*(kappa-zeroV)+rho*highConstant) := by
  have hpi := Arithmetic.two_pi_lt_710_over_113
  have hc := diagonal_bounds.1
  dsimp [zeroGap,zeroU,zeroV,highConstant,kappa,rho] at *
  linarith

theorem nonpositive_zero_high_transfer (s t : State) (ht : t.branch=.high)
    (hs : transverse s≤0) {z : ℝ} (hz : z∈Icc 0 frameCap)
    (hm : GlobalOuterAnchor.width z≤ s.a*Real.sin z+transverse s*Real.cos z+t.b) :
    aeval z H≤zeroCharge s t z-gammaZero := by
  have hsy : transverse s= -s.b := transverse_nonpos_eq s hs
  have hmu : 0≤zeroMu z := by linarith [(zeroMu_bounds hz).1]
  have hproj := mul_le_mul_of_nonneg_left hm hmu
  have hsource := zero_source_force s hz
  have htarget := zero_target_force t z
  have hR := radius_sqrt_two
  have hsin := (transport_trig hz).2.2.1
  have hraw : zeroHighRaw z≤zeroCharge s t z-gammaZero := by
    simp only [GlobalOuterAnchor.width,abs_of_nonneg hsin,hsy] at hproj
    rw [zeroCharge,potential_high t ht,hsy]
    dsimp [zeroHighRaw,gammaZero,kappa]
    nlinarith only [hproj,hsource,htarget,hR]
  exact (high_polynomial_transfer hz).trans hraw

theorem nonpositive_zero_lower_transfer (s t : State)
    (ht : t.branch=.low ∨ t.branch=.middle) (hs : transverse s≤0)
    {z : ℝ} (hz : z∈Icc 0 frameCap)
    (hm : GlobalOuterAnchor.width z≤ s.a*Real.sin z+transverse s*Real.cos z+t.b) :
    aeval z L≤zeroCharge s t z-gammaZero := by
  have hsy : transverse s= -s.b := transverse_nonpos_eq s hs
  have hmu := zeroMu_bounds hz
  have hproj := mul_le_mul_of_nonneg_left hm (show 0≤zeroMu z by linarith [hmu.1])
  have hsource := zero_source_force s hz
  have hpotential := potential_upper t
  have htarget := lower_chart_linear_upper t ht
    (by norm_num [zeroU] : 0≤zeroU)
    (show zeroU*(102/169)≤kappa*zeroMu z-zeroV by
      dsimp [zeroU,zeroV,kappa]
      linarith [hmu.1])
  have hgap := lower_target_constant_gap
  have hsin := (transport_trig hz).2.2.1
  have hraw : zeroLowRaw z≤zeroCharge s t z-gammaZero := by
    simp only [GlobalOuterAnchor.width,abs_of_nonneg hsin,hsy] at hproj
    rw [zeroCharge,hsy]
    dsimp [zeroLowRaw,gammaZero,zeroMu,kappa] at hproj hsource htarget hgap ⊢
    nlinarith only [hproj,hsource,htarget,hpotential,hgap]
  exact (low_polynomial_transfer hz).trans hraw

/-- The complete owner-2 row: lower target charts lose nothing; the
high chart loses less than `.007`, and nothing through angle `.35`. -/
theorem nonpositive_zero_charge (s t : State) (ht : t.branch.type≠0)
    (hs : transverse s≤0) {z : ℝ} (hz : z∈Icc 0 frameCap)
    (hm : GlobalOuterAnchor.width z≤ s.a*Real.sin z+transverse s*Real.cos z+t.b) :
    gammaZero-7/1000<zeroCharge s t z ∧
      ((z≤7/20 ∨ t.branch≠.high) → gammaZero≤zeroCharge s t z) := by
  cases hbr : t.branch with
  | coreSide | coreCorner => simp [hbr,Branch.type] at ht
  | low =>
      have htfer := nonpositive_zero_lower_transfer s t (Or.inl hbr) hs hz hm
      have hpos := L_positive hz
      exact ⟨by linarith,fun _ => by linarith⟩
  | middle =>
      have htfer := nonpositive_zero_lower_transfer s t (Or.inr hbr) hs hz hm
      have hpos := L_positive hz
      exact ⟨by linarith,fun _ => by linarith⟩
  | high =>
      have htfer := nonpositive_zero_high_transfer s t hbr hs hz hm
      have hlower := H_lower hz
      refine ⟨by linarith,?_⟩
      intro hshort
      have hzshort : z≤7/20 := hshort.resolve_right (fun hn => hn rfl)
      have hnonneg := H_short_nonnegative ⟨hz.1,hzshort⟩
      linarith

end SquaresInCircles.Eight.TableFree.GlobalAllHigh

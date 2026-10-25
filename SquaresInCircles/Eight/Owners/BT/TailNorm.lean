module

public import SquaresInCircles.Eight.Owners.CircleGeometry
public import SquaresInCircles.Eight.Frames.High.Arc
public import SquaresInCircles.Eight.Owners.TrigonometricReserves

/-!
# Eight squares: one circle-norm concavity theorem for every BT tail multiplier

The original shared-circle force has norm
sqrt(a²+c²−2ac sin z).  Its exact curvature is bounded using its two
unit force components.  The result holds for every positive a,c,
including the larger core-E multiplier, on the full error interval.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalBT

open FramePair FrameCircleArc

def tailNorm (a c z : ℝ) : ℝ := Real.sqrt (a^2+c^2-2*a*c*Real.sin z)
def tailNormD (a c z : ℝ) : ℝ := -a*c*Real.cos z/tailNorm a c z
def tailNormDD (a c z : ℝ) : ℝ :=
  a*c*Real.sin z/tailNorm a c z-a^2*c^2*(Real.cos z)^2/(tailNorm a c z)^3
def normForceU (a c z : ℝ) : ℝ := (a-c*Real.sin z)/tailNorm a c z
def normForceV (a c z : ℝ) : ℝ := c*Real.cos z/tailNorm a c z
def normForceW (a c z : ℝ) : ℝ := c*Real.sin z/tailNorm a c z
def normCos (a c z : ℝ) : ℝ := a*Real.cos z-R*tailNorm a c z
def normCosD (a c z : ℝ) : ℝ := -a*Real.sin z-R*tailNormD a c z
def normCosDD (a c z : ℝ) : ℝ := -a*Real.cos z-R*tailNormDD a c z

theorem tail_energy_positive {a c z : ℝ} (_ha : 0<a) (hc : 0<c)
    (hz : z∈Icc 0 frameCap) : 0<a^2+c^2-2*a*c*Real.sin z := by
  have ht := transport_trig hz
  have hv : 0<c*Real.cos z := mul_pos hc (by linarith [ht.1])
  have hid : a^2+c^2-2*a*c*Real.sin z=
      (a-c*Real.sin z)^2+(c*Real.cos z)^2 := by
    linear_combination -c^2*(Real.sin_sq_add_cos_sq z)
  rw [hid]
  nlinarith [sq_nonneg (a-c*Real.sin z),sq_pos_of_pos hv]

theorem tailNorm_pos {a c z : ℝ} (ha : 0<a) (hc : 0<c)
    (hz : z∈Icc 0 frameCap) : 0<tailNorm a c z :=
  Real.sqrt_pos.mpr (tail_energy_positive ha hc hz)

theorem tailNorm_sq {a c z : ℝ} (ha : 0<a) (hc : 0<c)
    (hz : z∈Icc 0 frameCap) : (tailNorm a c z)^2=a^2+c^2-2*a*c*Real.sin z :=
  Real.sq_sqrt (tail_energy_positive ha hc hz).le

theorem tailNorm_literal {a c z : ℝ} (ha : 0<a) (hc : 0<c)
    (hz : z∈Icc 0 frameCap) :
    (tailNorm a c z)^2=(a-c*Real.sin z)^2+(c*Real.cos z)^2 := by
  rw [tailNorm_sq ha hc hz]
  linear_combination -c^2*(Real.sin_sq_add_cos_sq z)

theorem tailNorm_deriv {a c z : ℝ} (ha : 0<a) (hc : 0<c)
    (hz : z∈Icc 0 frameCap) : HasDerivAt (tailNorm a c) (tailNormD a c z) z := by
  have hd := ((hasDerivAt_const z (a^2+c^2)).sub
    ((Real.hasDerivAt_sin z).const_mul (2*a*c))).sqrt
      (tail_energy_positive ha hc hz).ne'
  convert hd using 1
  · funext y
    rfl
  · simp only [tailNormD,tailNorm,Pi.sub_apply]
    ring

theorem tailNormD_deriv {a c z : ℝ} (ha : 0<a) (hc : 0<c)
    (hz : z∈Icc 0 frameCap) : HasDerivAt (tailNormD a c) (tailNormDD a c z) z := by
  have hn := (tailNorm_pos ha hc hz).ne'
  have hd := ((Real.hasDerivAt_cos z).const_mul (-a*c)).div
    (tailNorm_deriv ha hc hz) hn
  convert hd using 1
  · rfl
  · dsimp [tailNormD,tailNormDD]
    field_simp [hn]

theorem norm_force_unit {a c z : ℝ} (ha : 0<a) (hc : 0<c)
    (hz : z∈Icc 0 frameCap) : (normForceU a c z)^2+(normForceV a c z)^2=1 := by
  have hn := (tailNorm_pos ha hc hz).ne'
  have hh := tailNorm_literal ha hc hz
  dsimp [normForceU,normForceV]
  field_simp [hn]
  nlinarith only [hh]

theorem norm_curvature_force {a c z : ℝ} (ha : 0<a) (hc : 0<c)
    (hz : z∈Icc 0 frameCap) :
    tailNormDD a c z=a*((normForceU a c z)^2*normForceW a c z-
      normForceU a c z*(normForceV a c z)^2) := by
  have hn := (tailNorm_pos ha hc hz).ne'
  have hh := tailNorm_literal ha hc hz
  dsimp [tailNormDD,normForceU,normForceV,normForceW]
  field_simp [hn]
  linear_combination Real.sin z*hh

/-- A rational upper bound on u v² over the complete unit circle. -/
theorem unit_cubic_upper {u v : ℝ} (hu : u^2+v^2=1) :
    u*v^2≤(193/500:ℝ) := by
  by_cases hs : u≤0
  · have hh := mul_nonpos_of_nonpos_of_nonneg hs (sq_nonneg v)
    linarith
  · have hs' : 0≤u := by linarith
    have hlast : 0≤4/3-u^2 := by nlinarith [sq_nonneg v]
    have hprod := mul_nonneg (sq_nonneg (u^2-1/3)) hlast
    have hid : 4/27-(u*v^2)^2=(u^2-1/3)^2*(4/3-u^2) := by
      rw [show v^2=1-u^2 by linarith]
      ring
    have hsq : (u*v^2)^2≤4/27 := by nlinarith only [hprod,hid]
    have hn := mul_nonneg hs' (sq_nonneg v)
    nlinarith only [hsq,hn]

theorem tailNorm_curvature_lower {a c z : ℝ} (ha : 0<a) (hc : 0<c)
    (hz : z∈Icc 0 frameCap) : -(193/500)*a≤tailNormDD a c z := by
  have hu := unit_cubic_upper (norm_force_unit ha hc hz)
  have hw : 0≤normForceW a c z := by
    dsimp [normForceW]
    exact div_nonneg (mul_nonneg hc.le (transport_trig hz).2.2.1)
      (tailNorm_pos ha hc hz).le
  have hnonneg := mul_nonneg (sq_nonneg (normForceU a c z)) hw
  have hm := mul_le_mul_of_nonneg_left hu ha.le
  rw [norm_curvature_force ha hc hz]
  nlinarith only [hm,mul_nonneg ha.le hnonneg]

theorem normCos_deriv {a c z : ℝ} (ha : 0<a) (hc : 0<c)
    (hz : z∈Icc 0 frameCap) : HasDerivAt (normCos a c) (normCosD a c z) z := by
  have hd := ((Real.hasDerivAt_cos z).const_mul a).sub
    ((tailNorm_deriv ha hc hz).const_mul R)
  convert hd using 1
  · rfl
  · simp only [normCosD]
    ring

theorem normCosD_deriv {a c z : ℝ} (ha : 0<a) (hc : 0<c)
    (hz : z∈Icc 0 frameCap) : HasDerivAt (normCosD a c) (normCosDD a c z) z := by
  have hd := ((Real.hasDerivAt_sin z).const_mul (-a)).sub
    ((tailNormD_deriv ha hc hz).const_mul R)
  convert hd using 1
  · rfl
  · simp only [normCosDD]

theorem normCos_curvature {a c z : ℝ} (ha : 0<a) (hc : 0<c)
    (hz : z∈Icc 0 frameCap) : normCosDD a c z<0 := by
  have hn := mul_le_mul_of_nonneg_left (tailNorm_curvature_lower ha hc hz) R_pos.le
  have hR : R<1979/1000 := by
    have hh := FrameHighArc.radius_bound
    dsimp [FrameHighArc.radiusUpper] at hh
    linarith
  have hRprod := mul_lt_mul_of_pos_right hR ha
  have hcos := mul_lt_mul_of_pos_left (transport_trig hz).1 ha
  dsimp [normCosDD]
  nlinarith only [hn,hRprod,hcos,ha]

theorem normCos_concave {a c : ℝ} (ha : 0<a) (hc : 0<c) :
    ConcaveOn ℝ (Icc 0 frameCap) (normCos a c) :=
  concave_of_deriv2 (fun z hz => normCos_deriv ha hc hz)
    (fun z hz => normCosD_deriv ha hc hz)
    (fun z hz => (normCos_curvature ha hc hz).le)

@[simp] theorem tailNorm_comm (a c z : ℝ) : tailNorm a c z=tailNorm c a z := by
  dsimp [tailNorm]
  congr 1
  ring

end SquaresInCircles.Eight.GlobalBT

module

public import SquaresInCircles.Eight.TableFree.CrossedUpperRateInverse

/-!
# The complete upper-tangent crossed cap-rate comparison

Uncompiled source draft.  At the single rational transverse endpoint
the hard cap rate exceeds the inverse-HG cap rate by more than .009.
Their exact derivatives on the complete remaining interval increase
this gap at rate greater than .15.  The original hard contact compares
its actual angle to the proved algebraic endpoint, completing the
physical angular-rate statement at the actual q.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
namespace CrossedUpperRate
open CrossedClampRates

theorem InverseDomain.opposite {q Y t : ℝ} (C : InverseDomain q Y t) :
    EndpointDomain q (2-Y) := by
  refine ⟨C.floor,C.ceiling,⟨?_,?_⟩⟩
  · linarith [(inverse_radicals C).1]
  · linarith [C.Y_mem.1]

theorem InverseDomain.segment {q Y t y : ℝ} (C : InverseDomain q Y t)
    (hy : y∈Icc (26/25 : ℝ) Y) : InverseDomain q y t :=
  ⟨C.floor,C.ceiling,⟨hy.1,hy.2.trans C.Y_mem.2⟩,C.t_mem⟩

theorem complete_gap {q Y t : ℝ} (C : InverseDomain q Y t) :
    9/1000+(3/20)*(Y-26/25)<endpointRate q (2-Y)-inverseRate q Y t := by
  let f : ℝ → ℝ := fun y => endpointRate q (2-y)-inverseRate q y t
  let df : ℝ → ℝ := fun y => -endpointRateD q (2-y)-inverseRateD q y t
  have hd (y : ℝ) (hy : y∈Icc (26/25 : ℝ) Y) : HasDerivAt f (df y) y := by
    let D := C.segment hy
    have hfirst := (endpointRate_hasDerivAt D.opposite).comp y
      ((hasDerivAt_id y).const_sub 2)
    convert hfirst.sub (inverseRate_hasDerivAt D) using 1
    · rfl
    · dsimp [df]
      ring
  have hc : ContinuousOn f (Icc (26/25 : ℝ) Y) := by
    intro y hy
    exact (hd y hy).continuousAt.continuousWithinAt
  have hderiv (y : ℝ) (hy : y∈Ioo (26/25 : ℝ) Y) : 3/20≤df y := by
    let D := C.segment (Ioo_subset_Icc_self hy)
    have hb := endpoint_rate_derivative_upper D.opposite
    have ha := inverse_rate_derivative_upper D
    dsimp [df]
    linarith
  have hreserve := derivative_reserve hc
    (fun y hy => hd y (Ioo_subset_Icc_self hy)) hderiv
    (show (26/25 : ℝ)∈Icc (26/25) Y from ⟨le_rfl,C.Y_mem.1⟩)
    (show Y∈Icc (26/25 : ℝ) Y from ⟨C.Y_mem.1,le_rfl⟩) C.Y_mem.1
  have hb := (base_endpoint_bounds C.floor C.ceiling).2
  have ha := base_inverse_upper C.floor C.ceiling C.t_mem
  have hbase : 9/1000<f (26/25) := by
    dsimp [f]
    rw [show (2 : ℝ)-26/25=24/25 by norm_num]
    linarith
  dsimp [f] at hreserve
  linarith

end CrossedUpperRate

namespace CrossedClampRates

/-- The upper-tangent rate estimate uses only the actual-q cap domain,
the already captured common-frame distance, and the actual normal BT2
contact.  The opposite angle has no extra small-angle assumption. -/
theorem upper_gap {q Y r u : ℝ}
    (hqL : qLow≤q) (hq : q≤qCap)
    (hY : Y∈Icc (26/25 : ℝ) (Real.sqrt (q-9/4)))
    (hr : r∈Icc (0 : ℝ) (1/25)) (hu : u∈Icc 0 frameCap)
    (hBT : (radius q (2-Y)-1)*Real.cos u-(2-Y)*Real.sin u≥1/2) :
    9/1000+(3/20)*(Y-26/25)<
      angularHardRate q (2-Y) u-angularInverseRate q Y r := by
  let C : CrossedUpperRate.InverseDomain q Y (Real.tan r) :=
    ⟨hqL,hq,hY,CrossedUpperRate.tangent_short hr⟩
  have hgap := CrossedUpperRate.complete_gap C
  have hhard := CrossedUpperRate.hard_rate_lower C.opposite hu hBT
  dsimp [angularInverseRate]
  linarith

theorem upper_gap_positive {q Y r u : ℝ}
    (hqL : qLow≤q) (hq : q≤qCap)
    (hY : Y∈Icc (26/25 : ℝ) (Real.sqrt (q-9/4)))
    (hr : r∈Icc (0 : ℝ) (1/25)) (hu : u∈Icc 0 frameCap)
    (hBT : (radius q (2-Y)-1)*Real.cos u-(2-Y)*Real.sin u≥1/2) :
    angularInverseRate q Y r<angularHardRate q (2-Y) u := by
  have hh := upper_gap hqL hq hY hr hu hBT
  linarith [hY.1]

end CrossedClampRates
end SquaresInCircles.Eight.TableFree

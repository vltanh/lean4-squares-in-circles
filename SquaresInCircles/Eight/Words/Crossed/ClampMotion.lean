module

public import Mathlib.Algebra.Order.Star.Real
public import SquaresInCircles.Eight.Owners.StrictBoundaryContinuation
public import SquaresInCircles.Eight.Words.Crossed.SmallWrongSign
public import SquaresInCircles.Eight.Words.Crossed.GACycle
public import SquaresInCircles.Eight.Words.Crossed.ClampBudget
public import SquaresInCircles.Eight.Words.Crossed.WrongEndpointBound
public import SquaresInCircles.Eight.Words.Crossed.LowerInverseRate

/-!
# Eight squares: strict feasibility along the common-frame clamp

Both angular errors decrease by the same
amount.  The inverse HG cap and the unchanged opposite hard cap are
evaluated at the original q throughout.  Their sum starts above the
physical threshold and has a strictly inward derivative whenever it
equals that threshold.  Thus every positive motion has strict middle
slack, up to the first of the two unchanged endpoint frames.
-/

section
/-!
## The upper-tangent crossed cap-rate comparison

At the single rational transverse endpoint the hard cap rate exceeds the inverse-HG cap rate by
more than `.009`. Their exact derivatives on the whole remaining interval increase this gap at a
rate greater than `.15` (`complete_gap`). The original hard contact compares its angle to the
algebraic endpoint, which gives the physical angular-rate statement at the same q
(`upper_gap_positive`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
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

/-- The upper-tangent rate estimate uses only the cap domain at the same q, the captured
common-frame distance and the normal BT2 contact. The opposite angle needs no small-angle
assumption. -/
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
end SquaresInCircles.Eight
end
end
end

section
/-!
## Every active common-frame boundary has a strictly favorable cap rate

The original H/T budget first forces the active transverse corner above `48/49`. Its two
lower-tangent angle captures give a rate gap above `1/500` (`lower_gap_small`,
`lower_gap_medium`); the upper-tangent theorem covers the remaining interval. All cap rates use
the same q, and the only contact hypotheses are the weak bounds of the original source
(`active_boundary_rate`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
namespace CrossedClampRates

theorem lower_gap_small {q Y r u : ℝ} (hqL : qLow≤q) (hq : q≤qCap)
    (hY : Y∈Icc (48/49:ℝ) 1) (hr : r∈Icc (0:ℝ) (1/25))
    (hu : u∈Icc (0:ℝ) (3/50)) :
    1/500<angularHardRate q (2-Y) u-angularInverseRate q Y r := by
  have ha := CrossedLowerRate.angular_inverse_small hqL hq hY hr
  have hB : (2-Y)∈Icc (1:ℝ) EndpointRotationPenalty.charge := by
    dsimp [EndpointRotationPenalty.charge]
    constructor <;> linarith [hY.1,hY.2]
  have hb := CrossedLowerRate.angular_hard_small hqL hq hB hu
  linarith

theorem lower_gap_medium {q Y r u : ℝ} (hqL : qLow≤q) (hq : q≤qCap)
    (hY : Y∈Icc (1:ℝ) (26/25)) (hr : r∈Icc (0:ℝ) (1/25))
    (hu : u∈Icc (0:ℝ) (79/500)) :
    1/500<angularHardRate q (2-Y) u-angularInverseRate q Y r := by
  have ha := CrossedLowerRate.angular_inverse_medium hqL hq hY hr
  have hB : (2-Y)∈Icc (24/25:ℝ) 1 := by constructor <;> linarith [hY.1,hY.2]
  have hb := CrossedLowerRate.angular_hard_medium hqL hq hB hu
  linarith

end CrossedClampRates

namespace CrossedClampBudget
open CrossedClampRates

theorem BoundaryData.lower_gap {q Y r u bH bT : ℝ}
    (C : BoundaryData q Y r u bH bT) (hY : Y≤26/25) :
    1/500<angularHardRate q (2-Y) u-angularInverseRate q Y r := by
  have hfloor := C.Y_gt
  by_cases hY1 : Y≤1
  · exact lower_gap_small C.floor C.ceiling ⟨hfloor.le,hY1⟩ C.r_mem
      ⟨C.u_mem.1,(C.angle_small hY1).le⟩
  · have hYi : Y∈Icc (1:ℝ) (26/25) := ⟨(lt_of_not_ge hY1).le,hY⟩
    exact lower_gap_medium C.floor C.ceiling hYi C.r_mem
      ⟨C.u_mem.1,(C.angle_medium hYi).le⟩

theorem BoundaryData.rate {q Y r u bH bT : ℝ}
    (C : BoundaryData q Y r u bH bT) :
    48/49<Y ∧ angularInverseRate q Y r<angularHardRate q (2-Y) u := by
  refine ⟨C.Y_gt,?_⟩
  by_cases hY : Y≤26/25
  · have hh := C.lower_gap hY
    linarith
  · apply upper_gap_positive C.floor C.ceiling
      ⟨(lt_of_not_ge hY).le,C.Y_mem.2⟩ C.r_mem C.u_mem
    linarith [C.BT,C.T_nonneg]

end CrossedClampBudget

namespace CrossedClampRates

/-- The rate comparison at an active boundary, from the weak bounds of the inverse HG cap and of
the unchanged opposite hard cap. The original tangents `bH` and `bT` occur only in the original
necessary contacts and the budget. -/
theorem active_boundary_rate {q Y r u bH bT : ℝ}
    (hqL : qLow≤q) (hq : q≤qCap)
    (hY : Y∈Icc (23/25:ℝ) (Real.sqrt (q-9/4)))
    (hr : r∈Icc (0:ℝ) (1/25)) (hu : u∈Icc 0 frameCap)
    (hT : 0≤bT)
    (hHG : 1/2+(1-transverse q Y)*Real.cos r-(adjacent q Y-1)*Real.sin r≤bH)
    (hBT : bT+1/2≤(radius q (2-Y)-1)*Real.cos u-(2-Y)*Real.sin u)
    (hbudget : bH-bT+EndpointRotationPenalty.charge*(r-u)<1-EndpointBudgetScalars.S0) :
    48/49<Y ∧ angularInverseRate q Y r<angularHardRate q (2-Y) u :=
  CrossedClampBudget.BoundaryData.rate ⟨hqL,hq,hY,hr,hu,hT,hHG,hBT,hbudget⟩

end CrossedClampRates
end SquaresInCircles.Eight
end
end
end

section
/-!
## Exact cap derivatives and their geometric rate formulas

The derivatives of the explicit inverse HG
cap and unchanged BT cap agree with the shared rational rate functions.
All denominators are positive on their actual physical domains.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight

namespace CrossedClampInverse

def cap1 (q b r : ℝ) : ℝ := -(D q b r+1)*D1 q b r/cap q b r

theorem cap_hasDerivAt {q b r : ℝ} (S : Domain q b) (hr : r∈Icc (0:ℝ) (1/25)) :
    HasDerivAt (cap q b) (cap1 q b r) r := by
  have hc := cap_bounds S hr
  have hr0 : q-(D q b r+1)^2≠0 := by nlinarith [hc.1,hc.2.2.2]
  have hd := ((((D_hasDerivAt S hr).add_const 1).pow 2).const_sub q).sqrt hr0
  convert hd using 1
  · rfl
  · dsimp [cap1,cap]
    field_simp [show Real.sqrt (q-(D q b r+1)^2)≠0 by
      change cap q b r≠0; linarith [hc.1]]

theorem cap_radius {q b r : ℝ} (S : Domain q b) (hr : r∈Icc (0:ℝ) (1/25)) :
    CrossedClampRates.radius q (cap q b r)=D q b r+1 := by
  dsimp [CrossedClampRates.radius]
  rw [show q-(cap q b r)^2=(D q b r+1)^2 by nlinarith [(cap_bounds S hr).2.2.2]]
  exact Real.sqrt_sq (by linarith [(D_bounds S hr).1])

theorem cap_transverse {q b r : ℝ} (S : Domain q b) (hr : r∈Icc (0:ℝ) (1/25)) :
    CrossedClampRates.transverse q (cap q b r)=D q b r := by
  dsimp [CrossedClampRates.transverse]
  rw [cap_radius S hr]
  ring

theorem cap_adjacent {q b r : ℝ} (S : Domain q b) (hr : r∈Icc (0:ℝ) (1/25)) :
    CrossedClampRates.adjacent q (cap q b r)=X q b r := by
  dsimp [CrossedClampRates.adjacent]
  rw [cap_transverse S hr]
  exact radius_eq S hr

theorem cap_rate {q b r : ℝ} (S : Domain q b) (hr : r∈Icc (0:ℝ) (1/25)) :
    cap1 q b r=CrossedClampRates.angularInverseRate q (cap q b r) r := by
  have hc : 0<Real.cos r := by linarith [(trig hr).2.2.2.1]
  have hw : 0<W q b r := by linarith [(W_bounds S hr).1.1]
  have hy : 0<cap q b r := by linarith [(cap_bounds S hr).1]
  have hden : X q b r-D q b r*(Real.sin r/Real.cos r)=W q b r/Real.cos r := by
    field_simp [hc.ne']
    nlinarith [reverse q b r]
  rw [CrossedClampRates.angularInverseRate,CrossedClampRates.inverseRate,
    cap_radius S hr,cap_transverse S hr,cap_adjacent S hr,Real.tan_eq_sin_div_cos,hden]
  dsimp [cap1,D1]
  rw [←reverse q b r]
  field_simp [hc.ne',hy.ne',show X q b r*Real.cos r-D q b r*Real.sin r≠0 by
    rw [reverse]; exact hw.ne']
  ring

theorem cap_angular_hasDerivAt {q b r : ℝ} (S : Domain q b)
    (hr : r∈Icc (0:ℝ) (1/25)) :
    HasDerivAt (cap q b) (CrossedClampRates.angularInverseRate q (cap q b r) r) r := by
  simpa only [cap_rate S hr] using cap_hasDerivAt S hr

theorem source_bound {q b r : ℝ} (S : Domain q b) (hr : r∈Icc (0:ℝ) (1/25)) :
    1/2+(1-CrossedClampRates.transverse q (cap q b r))*Real.cos r-
      (CrossedClampRates.adjacent q (cap q b r)-1)*Real.sin r=b := by
  rw [cap_transverse S hr,cap_adjacent S hr]
  have hh := contact q b r
  dsimp [M] at hh
  nlinarith

end CrossedClampInverse

namespace CrossedClampRates
open HardSplitCap

theorem hard_cap_radius {q d u : ℝ} (S : MiddleHardCap.Feasible q d)
    (hu : u∈Icc 0 frameCap) : radius q (cap q d u)=cornerX q d u := by
  dsimp [radius]
  rw [show q-(cap q d u)^2=(cornerX q d u)^2 by nlinarith [MiddleHardCap.corner_norm S hu]]
  exact Real.sqrt_sq (MiddleHardCap.cornerX_pos S hu).le

theorem hard_cap_rate {q d u : ℝ} (S : MiddleHardCap.Feasible q d)
    (hu : u∈Icc 0 frameCap) : first q d u= -angularHardRate q (cap q d u) u := by
  have hc : 0<Real.cos u := by linarith [(transport_trig hu).1]
  have hw := MiddleHardCap.root_pos S hu
  have hback : cap q d u*Real.cos u+cornerX q d u*Real.sin u=root q d u := by
    dsimp [cap,cornerX]
    linear_combination root q d u*Real.sin_sq_add_cos_sq u
  have hden : cap q d u+cornerX q d u*(Real.sin u/Real.cos u)=root q d u/Real.cos u := by
    field_simp [hc.ne']
    nlinarith
  rw [angularHardRate,hardRate,hard_cap_radius S hu,Real.tan_eq_sin_div_cos,hden]
  dsimp [first,drift]
  rw [←hback]
  field_simp [hc.ne',show cap q d u*Real.cos u+cornerX q d u*Real.sin u≠0 by
    rw [hback]; exact hw.ne']
  ring

theorem hard_cap_angular_hasDerivAt {q d u : ℝ} (S : MiddleHardCap.Feasible q d)
    (hu : u∈Icc 0 frameCap) :
    HasDerivAt (cap q d) (-angularHardRate q (cap q d u) u) u := by
  simpa only [hard_cap_rate S hu] using MiddleHardCap.cap_deriv S hu

theorem hard_cap_contact {q d u : ℝ} (S : MiddleHardCap.Feasible q d)
    (hu : u∈Icc 0 frameCap) :
    (radius q (cap q d u)-1)*Real.cos u-cap q d u*Real.sin u=d := by
  rw [hard_cap_radius S hu]
  exact corner_contact q d u

end CrossedClampRates
end SquaresInCircles.Eight
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CrossedClampMotion
open CrossedClampRates

structure Data (q bH bT r0 u0 : ℝ) : Prop where
  inverse : CrossedClampInverse.Domain q bH
  opposite : MiddleHardCap.Feasible q (1/2+bT)
  r_mem : r0∈Ioc (0:ℝ) (1/25)
  u_mem : u0∈Ioc 0 frameCap
  T_nonneg : 0≤bT
  opposite_floor : 1/2≤HardSplitCap.cap q (1/2+bT) u0
  initial : 2≤CrossedClampInverse.cap q bH r0+HardSplitCap.cap q (1/2+bT) u0
  budget : bH-bT+EndpointRotationPenalty.charge*(r0-u0)<1-EndpointBudgetScalars.S0

def total (q bH bT r0 u0 s : ℝ) : ℝ :=
  CrossedClampInverse.cap q bH (r0-s)+HardSplitCap.cap q (1/2+bT) (u0-s)

def rate (q bH bT r0 u0 s : ℝ) : ℝ :=
  angularHardRate q (HardSplitCap.cap q (1/2+bT) (u0-s)) (u0-s)-
    angularInverseRate q (CrossedClampInverse.cap q bH (r0-s)) (r0-s)

theorem total_continuous (q bH bT r0 u0 : ℝ) :
    Continuous (total q bH bT r0 u0) := by
  unfold total CrossedClampInverse.cap CrossedClampInverse.D
    CrossedClampInverse.W CrossedClampInverse.M HardSplitCap.cap
    HardSplitCap.root HardSplitCap.contact
  fun_prop

theorem Data.remaining_r {q bH bT r0 u0 s : ℝ}
    (C : Data q bH bT r0 u0) (hs : s∈Icc 0 (min r0 u0)) :
    r0-s∈Icc (0:ℝ) (1/25) := by
  have hsr : s≤r0 := hs.2.trans (min_le_left r0 u0)
  constructor <;> linarith [C.r_mem.2,hs.1]

theorem Data.remaining_u {q bH bT r0 u0 s : ℝ}
    (C : Data q bH bT r0 u0) (hs : s∈Icc 0 (min r0 u0)) :
    u0-s∈Icc 0 frameCap := by
  have hsu : s≤u0 := hs.2.trans (min_le_right r0 u0)
  constructor <;> linarith [C.u_mem.2,hs.1]

theorem Data.cap_floor {q bH bT r0 u0 s : ℝ}
    (C : Data q bH bT r0 u0) (hs : s∈Icc 0 (min r0 u0)) :
    1/2≤HardSplitCap.cap q (1/2+bT) (u0-s) := by
  have hh := (MiddleHardCap.cap_strictAnti C.opposite).antitoneOn
    (C.remaining_u hs) (show u0∈Icc 0 frameCap from ⟨C.u_mem.1.le,C.u_mem.2⟩)
    (show u0-s≤u0 by linarith [hs.1])
  exact C.opposite_floor.trans hh

theorem Data.total_hasDerivAt {q bH bT r0 u0 s : ℝ}
    (C : Data q bH bT r0 u0) (hs : s∈Icc 0 (min r0 u0)) :
    HasDerivAt (total q bH bT r0 u0) (rate q bH bT r0 u0 s) s := by
  have hr : HasDerivAt (fun x : ℝ => r0-x) (-1) s := by
    simpa using (hasDerivAt_id s).const_sub r0
  have hu : HasDerivAt (fun x : ℝ => u0-x) (-1) s := by
    simpa using (hasDerivAt_id s).const_sub u0
  have hA := (CrossedClampInverse.cap_angular_hasDerivAt C.inverse
    (C.remaining_r hs)).comp s hr
  have hB := (hard_cap_angular_hasDerivAt C.opposite (C.remaining_u hs)).comp s hu
  convert hA.add hB using 1
  · rfl
  · dsimp [rate]
    ring

theorem Data.boundary_rate {q bH bT r0 u0 s : ℝ}
    (C : Data q bH bT r0 u0) (hs : s∈Icc 0 (min r0 u0))
    (hboundary : total q bH bT r0 u0 s=2) : 0<rate q bH bT r0 u0 s := by
  let Y := CrossedClampInverse.cap q bH (r0-s)
  have hr := C.remaining_r hs
  have hu := C.remaining_u hs
  have hYbounds := CrossedClampInverse.cap_bounds C.inverse hr
  have hY : Y∈Icc (23/25:ℝ) (Real.sqrt (q-9/4)) :=
    ⟨hYbounds.1.le,hYbounds.2.1⟩
  have hB : HardSplitCap.cap q (1/2+bT) (u0-s)=2-Y := by
    dsimp [total] at hboundary
    dsimp [Y]
    linarith
  have hHG := CrossedClampInverse.source_bound C.inverse hr
  have hBT := hard_cap_contact C.opposite hu
  rw [hB] at hBT
  have hbudget : bH-bT+EndpointRotationPenalty.charge*((r0-s)-(u0-s))<1-EndpointBudgetScalars.S0 := by
    convert C.budget using 1
    ring
  have hgap := (active_boundary_rate C.inverse.floor C.inverse.ceiling hY hr hu
    C.T_nonneg (by simpa only [Y] using hHG.le)
    (by linarith) hbudget).2
  dsimp [rate]
  rw [hB]
  exact sub_pos.mpr hgap

theorem Data.strict {q bH bT r0 u0 : ℝ} (C : Data q bH bT r0 u0) :
    ∀s∈Ioc 0 (min r0 u0),2<total q bH bT r0 u0 s := by
  apply strict_boundary_continuation (total_continuous q bH bT r0 u0)
    (fun s hs => C.total_hasDerivAt hs) (fun s hs => C.boundary_rate hs)
  simpa [total] using C.initial

/-- Every positive state has actual G/A/B points, with both rigid
middle anchors strictly inside the unchanged source circle. -/
theorem Data.realize {q r0 u0 s : ℝ} {H T : SignedPoint}
    (C : Data q H.y T.y r0 u0) (hs : s∈Ioc 0 (min r0 u0)) :
    Nonempty (CrossedClampData q H T (r0-s) (u0-s)) := by
  have hsi : s∈Icc 0 (min r0 u0) := ⟨hs.1.le,hs.2⟩
  exact CrossedClampInverse.realize C.inverse (C.remaining_r hsi) C.opposite
    (C.remaining_u hsi) (C.cap_floor hsi) (C.strict s hs)

end SquaresInCircles.Eight.CrossedClampMotion
end
end
end

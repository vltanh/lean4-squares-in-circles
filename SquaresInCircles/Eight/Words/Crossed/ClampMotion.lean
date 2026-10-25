module

public import SquaresInCircles.Eight.Words.Crossed.ClampDerivatives
public import SquaresInCircles.Eight.Words.Crossed.BoundaryRate
public import SquaresInCircles.Eight.Owners.StrictBoundaryContinuation

/-!
# Eight squares: strict feasibility along the common-frame clamp

Both angular errors decrease by the same
amount.  The inverse HG cap and the unchanged opposite hard cap are
evaluated at the original q throughout.  Their sum starts above the
physical threshold and has a strictly inward derivative whenever it
equals that threshold.  Thus every positive motion has strict middle
slack, up to the first of the two unchanged endpoint frames.
-/

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
    convert C.budget using 1 <;> ring
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

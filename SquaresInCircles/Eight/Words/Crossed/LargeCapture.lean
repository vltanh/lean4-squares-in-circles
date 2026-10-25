module

public import SquaresInCircles.Eight.Words.Crossed.LargeCaptureBounds
public import SquaresInCircles.Eight.Words.Crossed.LargeScalar
public import SquaresInCircles.Eight.Owners.Small.PositiveZeroEndpoint

/-!
# Eight squares: capture and GA-alignment reserve for the large crossed cap

Concavity reduces the G interval to GA alignment and the intrinsic zero-transverse contact.
Both endpoints are excluded when the crossing is at least `.04`, by the polynomial budget and
the signed opposite envelope (`crossing_short`). The retained original opposite hard contact and
the unchanged mixed-endpoint budget are the only global inputs.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CrossedLargeCapture
open PositiveSmallScalar CrossedLargeScalar EndpointRotationPenalty EndpointBudgetScalars

theorem zero_budget_lower {q P Y aB t r Z v : ℝ}
    (I : CrossedLargeScalar.CapData q P Y)
    (hr : r∈Icc 0 frameCap) (hZ : Z∈Icc 0 (1/5 : ℝ))
    (heq : V P Y Z=1/2) (hv : v∈Icc 0 frameCap)
    (hB : (aB+1/2)^2+(2-Y)^2≤qCap)
    (hBT : t+1/2≤(aB-1/2)*Real.cos v-(2-Y)*Real.sin v) :
    117/200<demand q P Y r Z-t+charge*(r-v) := by
  have hZi : Z∈Icc 0 frameCap := ⟨hZ.1,by dsimp [frameCap]; linarith [hZ.2]⟩
  have hp := SignedOppositeHardEnvelope.actual_middle_wrong_bound
    (aA := P+1/2) (aB := aB) (b := Y-1/2) (g := 0) (t := t) (z := Z) (v := v)
    ⟨I.tangent_range.1,I.tangent_range.2.trans (by norm_num [SignedOppositeHardEnvelope.pivot])⟩
    (by linarith [I.P_mem.1])
    (by convert I.circle.le.trans I.ceiling using 1; ring)
    (by convert hB using 1; ring) hZi hv (by norm_num)
    (by dsimp [V] at heq; nlinarith)
    (by convert hBT using 1; ring)
  have B := CrossedLargeScalar.point_bounds I hZi heq.ge
  have hhi : r+Z∈Icc 0 (9/10 : ℝ) := by
    dsimp [frameCap] at hr
    constructor <;> linarith [hr.1,hr.2,hZ.1,hZ.2]
  have hf := CrossedAngleReserve.nonnegative (A := (1/2:ℝ))
    (k := W q P Y Z-1) le_rfl (by linarith [B.W_mem.2]) hhi
  have hfloor : 1≤demand q P Y r Z+charge*(r+Z) := by
    dsimp [CrossedAngleReserve.curve] at hf
    dsimp [demand]
    rw [heq]
    linarith
  linarith

theorem crossing_short {q P Y aB t bH r z v : ℝ}
    (I : CrossedLargeScalar.CapData q P Y)
    (hr : r∈Icc 0 frameCap) (hz : z∈Icc 0 frameCap)
    (hGA : 1/2≤V P Y z) (hv : v∈Icc 0 frameCap)
    (hB : (aB+1/2)^2+(2-Y)^2≤qCap)
    (hBT : t+1/2≤(aB-1/2)*Real.cos v-(2-Y)*Real.sin v)
    (hHG : demand q P Y r z≤bH)
    (hbudget : bH-t+charge*(r-v)<1-S0) : r<1/25 := by
  by_contra! hwide
  obtain ⟨Z,hzZ,hZshort,hZE,hZall⟩ := CrossedLargeScalar.contact_endpoint I hz hGA
  have hZi : Z∈Icc 0 (1/5 : ℝ) := ⟨by linarith [hz.1],hZshort.le⟩
  have hW0 : W q P Y 0=Real.sqrt (q-P^2) := by simp [W,V]
  have hrad : 0≤q-P^2 := by nlinarith [I.circle,I.P_mem.1,I.Y_mem.1]
  have hWsq : (W q P Y 0)^2+P^2=q := by
    rw [hW0,Real.sq_sqrt hrad]
    ring
  have hleft := aligned_budget_lower
    (q := q) (R := P+1) (W := W q P Y 0) (b := Y-1/2)
    (aB := aB) (t := t) (r := r) (v := v)
    I.tangent_range (by linarith [I.P_mem.1]) (Real.sqrt_nonneg _)
    (by convert I.circle using 1; ring) I.ceiling
    (by convert hWsq using 1; ring)
    (by convert hB using 1; ring) ⟨hwide,hr.2⟩ hv
    (by convert hBT using 1; ring)
  have hleft' : 117/200<demand q P Y r 0-t+charge*(r-v) := by
    rw [show (2:ℝ)-(P+1)=1-P by ring] at hleft
    simpa [demand,V] using hleft
  have hright := zero_budget_lower I hr hZi hZE hv hB hBT
  have hmin := endpoint_minimum I hr hZi hZall ⟨hz.1,hzZ⟩
  have hboth : 117/200+t-charge*(r-v)<
      min (demand q P Y r 0) (demand q P Y r Z) :=
    lt_min (by linarith) (by linarith)
  have hconstant := SmallPositiveZeroEndpoint.endpoint_constant_lower
  linarith

/-- The original budget that captures the crossing also gives the strict displacement reserve
from which the A loss is constructed. -/
theorem captured_alignment_gain {q P Y aB t bH r z v : ℝ}
    (I : CrossedLargeScalar.CapData q P Y)
    (hr : r∈Icc 0 frameCap) (hz : z∈Icc 0 frameCap)
    (hGA : 1/2≤V P Y z) (hv : v∈Icc 0 frameCap)
    (hB : (aB+1/2)^2+(2-Y)^2≤qCap)
    (hBT : t+1/2≤(aB-1/2)*Real.cos v-(2-Y)*Real.sin v)
    (hHG : demand q P Y r z≤bH)
    (hbudget : bH-t+charge*(r-v)<1-S0) :
    r<1/25 ∧ demand q P Y r 0+z/150≤bH := by
  have hc := crossing_short I hr hz hGA hv hB hBT hHG hbudget
  obtain ⟨Z,hzZ,hZshort,hZE,hZall⟩ := CrossedLargeScalar.contact_endpoint I hz hGA
  have hgain := alignment_gain I ⟨hr.1,hc.le⟩
    ⟨by linarith [hz.1],hZshort.le⟩ hZE hZall ⟨hz.1,hzZ⟩
  exact ⟨hc,by linarith⟩

end SquaresInCircles.Eight.CrossedLargeCapture

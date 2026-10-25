module

public import SquaresInCircles.Eight.Words.Crossed.SmallScalar
public import SquaresInCircles.Eight.Words.Crossed.WrongEndpointBound
public import SquaresInCircles.Eight.Owners.Small.PositiveZeroEndpoint
public import SquaresInCircles.Eight.Owners.Wide.SmallHardEnvelope

/-!
# Eight squares: the small crossed source captures its tangent and crossing

The zero endpoint is excluded by the middle envelope on the whole interval. At the aligned
endpoint one Cauchy square bounds the sum of the two middle radii (`radius_pair`). The opposite
contact has a direct quadratic excess bound (`opposite_excess`), which gives `Y > 48/49` and
`r < .01` at the unchanged source radius (`capture`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CrossedSmallCapture
open PositiveSmallScalar CrossedLargeScalar EndpointRotationPenalty EndpointBudgetScalars

def oppositeRadius (Y : ℝ) : ℝ := Real.sqrt (qCap-(2-Y)^2)

theorem opposite_radius {q P Y : ℝ} (S : CrossedSmallScalar.CapData q P Y) :
    (oppositeRadius Y)^2+(2-Y)^2=qCap ∧
      oppositeRadius Y∈Icc (1557/1000 : ℝ) (427/250) := by
  have hy : 2-Y∈Icc (1:ℝ) (233/200) := by constructor <;> linarith [S.Y_mem.1,S.Y_mem.2]
  have hysq := pow_le_pow_left₀ (show 0≤2-Y by linarith [hy.1]) hy.2 2
  have hr : 0≤qCap-(2-Y)^2 := by norm_num [qCap] at *; nlinarith
  have hw := Real.sq_sqrt hr
  have hw0 := Real.sqrt_nonneg (qCap-(2-Y)^2)
  refine ⟨by dsimp [oppositeRadius]; linarith,?_⟩
  dsimp [oppositeRadius]
  constructor
  · norm_num [qCap] at hw
    nlinarith
  · have hyl := pow_le_pow_left₀ (show (0:ℝ)≤1 by norm_num) hy.1 2
    norm_num [qCap] at hw
    nlinarith

theorem opposite_quadratic {q P Y aB t v : ℝ} (S : CrossedSmallScalar.CapData q P Y)
    (_haB : 0≤aB) (ht : 0≤t) (hv : v∈Icc 0 frameCap)
    (hB : (aB+1/2)^2+(2-Y)^2≤qCap)
    (hBT : t+1/2≤(aB-1/2)*Real.cos v-(2-Y)*Real.sin v) :
    t+charge*v≤oppositeRadius Y-3/2+(charge-(2-Y))*v-v^2/5 := by
  obtain ⟨hRcircle,hR⟩ := opposite_radius S
  have hRa : aB-1/2≤oppositeRadius Y-1 := by
    have h := le_of_pow_le_pow_left₀ (by decide : (2:ℕ)≠0) (by linarith [hR.1] : 0≤oppositeRadius Y)
      (show (aB+1/2)^2≤(oppositeRadius Y)^2 by rw [←hRcircle] at hB; linarith)
    linarith
  have htr := transport_trig hv
  have hm := mul_le_mul_of_nonneg_right hRa (show 0≤Real.cos v by linarith [htr.1])
  have hcontact : 1/2≤(oppositeRadius Y-1)*Real.cos v-(2-Y)*Real.sin v := by linarith
  have hquad := WideSmallHardEnvelope.opposite_quadratic
    (show oppositeRadius Y-1∈Icc (557/1000 : ℝ) (177/250) by
      constructor <;> linarith [hR.1,hR.2])
    (show 2-Y∈Icc (1:ℝ) (61/50) by constructor <;> linarith [S.Y_mem.1,S.Y_mem.2])
    hv hcontact
  linarith

theorem opposite_flat {q P Y aB t v : ℝ} (S : CrossedSmallScalar.CapData q P Y)
    (haB : 0≤aB) (ht : 0≤t) (hv : v∈Icc 0 frameCap)
    (hB : (aB+1/2)^2+(2-Y)^2≤qCap)
    (hBT : t+1/2≤(aB-1/2)*Real.cos v-(2-Y)*Real.sin v)
    (hY : charge≤2-Y) : t+charge*v≤oppositeRadius Y-3/2 := by
  have hh := opposite_quadratic S haB ht hv hB hBT
  have hm := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hY) hv.1
  nlinarith [sq_nonneg v]

theorem opposite_excess {q P Y aB t v : ℝ} (S : CrossedSmallScalar.CapData q P Y)
    (haB : 0≤aB) (ht : 0≤t) (hv : v∈Icc 0 frameCap)
    (hB : (aB+1/2)^2+(2-Y)^2≤qCap)
    (hBT : t+1/2≤(aB-1/2)*Real.cos v-(2-Y)*Real.sin v) :
    t+charge*v≤oppositeRadius Y-3/2+5/9604 := by
  have hh := opposite_quadratic S haB ht hv hB hBT
  have hm := mul_le_mul_of_nonneg_right S.Y_mem.2 hv.1
  dsimp [charge] at *
  nlinarith [sq_nonneg (v-5/98)]

/-- The A radius and the opposite comparison radius obey one two-circle Cauchy bound, because
their transverse corners sum to 2. -/
theorem radius_pair {q P Y : ℝ} (S : CrossedSmallScalar.CapData q P Y) :
    1-S0≤3-P-oppositeRadius Y := by
  obtain ⟨hRcircle,hR⟩ := opposite_radius S
  have hs := Real.sq_sqrt (show 0≤qCap-1 by norm_num [qCap])
  have hs0 := Real.sqrt_nonneg (qCap-1)
  have hsumSq : (P+1+oppositeRadius Y)^2≤4*(qCap-1) := by
    nlinarith [S.circle,S.ceiling,sq_nonneg (P+1-oppositeRadius Y),sq_nonneg (Y-1)]
  have hsum : P+1+oppositeRadius Y≤2*Real.sqrt (qCap-1) := by
    nlinarith [S.P_mem.1,hR.1]
  dsimp [S0]
  linarith

theorem zero_budget_lower {q P Y aB t r Z v : ℝ}
    (S : CrossedSmallScalar.CapData q P Y)
    (hr : r∈Icc 0 frameCap) (hZ : Z∈Ioo (39/200 : ℝ) (2/5))
    (hcontact : V P Y Z=1/2) (ht : 0≤t) (hv : v∈Icc 0 frameCap)
    (hB : (aB+1/2)^2+(2-Y)^2≤qCap)
    (hBT : t+1/2≤(aB-1/2)*Real.cos v-(2-Y)*Real.sin v) :
    117/200<demand q P Y r Z-t+charge*(r-v) := by
  have hZi := CrossedWrongEndpointBound.contact_mem hZ
  have hm := WideSmallHardEnvelope.actual_middle_bound
    (b := Y-1/2) (aA := P+1/2) (aB := aB) (t := t) (z := Z) (v := v)
    (show Y-1/2∈Icc (7/25 : ℝ) (1/2) by constructor <;> linarith [S.Y_mem.1,S.Y_mem.2])
    (by linarith [S.P_mem.1])
    (by convert S.circle.le.trans S.ceiling using 1 <;> ring)
    (by convert hB using 1 <;> ring) hZi hv ht
    (by dsimp [V] at hcontact; nlinarith)
    (by convert hBT using 1 <;> ring)
  have hh : r+Z∈Icc (39/200 : ℝ) (11/10) := by
    dsimp [frameCap] at hr
    constructor <;> linarith [hr.1,hr.2,hZ.1,hZ.2]
  have hf := CrossedWrongEndpointCalculus.zeroDemand_reserve S.floor S.ceiling hh
  have heq : demand q P Y r Z=CrossedWrongEndpointCalculus.zeroDemand q (r+Z) := by
    norm_num [demand,W,CrossedWrongEndpointCalculus.zeroDemand,hcontact] <;> ring
  rw [←heq] at hf
  linarith

theorem capture {q P Y aB t bH r z v : ℝ}
    (S : CrossedSmallScalar.CapData q P Y)
    (hr : r∈Ioc 0 frameCap) (hz : z∈Icc 0 frameCap)
    (hGA : 1/2≤V P Y z) (haB : 0≤aB) (ht : 0≤t) (hv : v∈Icc 0 frameCap)
    (hB : (aB+1/2)^2+(2-Y)^2≤qCap)
    (hBT : t+1/2≤(aB-1/2)*Real.cos v-(2-Y)*Real.sin v)
    (hHG : demand q P Y r z≤bH)
    (hbudget : bH-t+charge*(r-v)<1-S0) :
    48/49<Y ∧ r<1/100 := by
  obtain ⟨Z,hzZ,hZ,hZE,hall⟩ := CrossedSmallScalar.contact_endpoint S hz hGA
  have hzero := zero_budget_lower S ⟨hr.1.le,hr.2⟩ hZ hZE ht hv hB hBT
  have hmin := CrossedSmallScalar.endpoint_minimum S ⟨hr.1.le,hr.2⟩
    ⟨by linarith [hZ.1],hZ.2.le⟩ hall ⟨hz.1,hzZ⟩
  have hconstant := SmallPositiveZeroEndpoint.endpoint_constant_lower
  have hzeroBad : bH<demand q P Y r Z := by linarith
  have hleft : demand q P Y r 0≤bH := by
    by_contra! hbad
    have hh := lt_min hbad hzeroBad
    linarith
  have hgrowth := CrossedSmallScalar.aligned_growth S ⟨hr.1.le,hr.2⟩
  have hradii := radius_pair S
  constructor
  · by_contra! hY
    have hopp := opposite_flat S haB ht hv hB hBT (by dsimp [charge]; linarith)
    have hpos : 0<(charge-9/10)*r := mul_pos (by norm_num [charge]) hr.1
    nlinarith
  · by_contra! hwide
    have hopp := opposite_excess S haB ht hv hB hBT
    dsimp [charge] at hgrowth hbudget hopp
    nlinarith

theorem captured_alignment_gain {q P Y aB t bH r z v : ℝ}
    (S : CrossedSmallScalar.CapData q P Y)
    (hr : r∈Ioc 0 frameCap) (hz : z∈Icc 0 frameCap)
    (hGA : 1/2≤V P Y z) (haB : 0≤aB) (ht : 0≤t) (hv : v∈Icc 0 frameCap)
    (hB : (aB+1/2)^2+(2-Y)^2≤qCap)
    (hBT : t+1/2≤(aB-1/2)*Real.cos v-(2-Y)*Real.sin v)
    (hHG : demand q P Y r z≤bH)
    (hbudget : bH-t+charge*(r-v)<1-S0) :
    48/49<Y ∧ r<1/100 ∧ demand q P Y r 0+z/100≤bH := by
  obtain ⟨hY,hshort⟩ := capture S hr hz hGA haB ht hv hB hBT hHG hbudget
  obtain ⟨Z,hzZ,hZ,hZE,hall⟩ := CrossedSmallScalar.contact_endpoint S hz hGA
  have hZi := CrossedWrongEndpointBound.contact_mem hZ
  have hZtight := CrossedSmallScalar.tight_contact_angle S hY.le hZi hZE.ge
  have hgain := CrossedSmallScalar.alignment_gain S hY.le ⟨hr.1.le,hshort.le⟩
    ⟨hZi.1,hZtight.le⟩ hZE hall ⟨hz.1,hzZ⟩
  exact ⟨hY,hshort,by linarith⟩

end SquaresInCircles.Eight.CrossedSmallCapture

module

public import SquaresInCircles.Eight.TableFree.SmallCancelingEnvelope
public import SquaresInCircles.Eight.TableFree.CrossedCancelingScalar
public import SquaresInCircles.Eight.TableFree.CrossedZeroReserve
public import SquaresInCircles.Eight.TableFree.SignedOppositeHardSigns

/-!
# The small crossed HG2 composite at the original H and A

Uncompiled source draft.  The explicit two-middle envelope and the
retained positive HG2 projection force the full HG angle below one fifth.
On this interval the original H circle gives U_H < .8, whereas the
actual A rotation gives U_A >= .835.  Feasible-contact continuation
therefore supplies the whole decreasing-angle path and a strict reserve.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SmallCancelingScalar
open PositiveSmallScalar CrossedCancelingScalar EndpointRotationPenalty EndpointBudgetScalars

theorem full_error_short {H : SignedPoint} {aA aB Y g t r z v : ℝ}
    (hHs : H.Sorted) (hHc : H.AvoidsCore) (hHq : H.Contained qCap)
    (hHy : 0≤H.y) (hY : Y∈Icc (167/200 : ℝ) 1)
    (haA : 0≤aA) (haB : 0≤aB)
    (hA : (aA+1/2)^2+Y^2≤qCap)
    (hB : (aB+1/2)^2+(2-Y)^2≤qCap)
    (hr : 0≤r) (hz : z∈Icc 0 frameCap) (hv : v∈Icc 0 frameCap)
    (hspan : z+r≤frameCap) (ht : 0≤t)
    (hHG : 1/2≤g+S H (z+r))
    (hGA : g+1/2≤(aA-1/2)*Real.cos z-Y*Real.sin z)
    (hBT : t+1/2≤(aB-1/2)*Real.cos v-(2-Y)*Real.sin v)
    (hbudget : H.y-t+charge*(r-v)<1-S0) : z+r<1/5 := by
  have hmiddle := SmallCancelingEnvelope.actual_middle_bound hY haA haB hA hB hz hv ht hGA hBT
  have hH := SignedPoint.coordinate_bounds hHs hHc hHq le_rfl
  by_contra! hlong
  have hh : z+r∈Icc (39/200 : ℝ) (11/10) := by
    dsimp [frameCap] at hspan
    constructor <;> linarith
  have hreserve := CrossedZeroReserve.strict
    (show H.a-1/2≤183/200 by linarith [hH.2.1]) hh
  have hcos := mul_nonneg hHy (sub_nonneg.mpr (Real.cos_le_one (z+r)))
  have hS0 := SignedOppositeHardEnvelope.budget_reserve
  dsimp [S] at hHG
  nlinarith

theorem rotated_support_upper {H : SignedPoint} {h : ℝ}
    (hHy : 0≤H.y) (hHq : H.Contained qCap)
    (hh : h∈Icc 0 (1/5 : ℝ)) (hS : 103/500≤S H h) : U_H H h<4/5 := by
  have hi : h∈Icc 0 frameCap := ⟨hh.1,by dsimp [frameCap]; linarith [hh.2]⟩
  have ht := transport_trig hi
  have h2 := pow_le_pow_left₀ hh.1 hh.2 2
  have hs := Real.sin_le hh.1
  have hc := Real.one_sub_sq_div_two_le_cos (x := h)
  obtain ⟨m,hm_def⟩ : ∃ m, m=Real.cos h+Real.sin h := ⟨_,rfl⟩
  obtain ⟨n,hn_def⟩ : ∃ n, n=Real.cos h-Real.sin h := ⟨_,rfl⟩
  have hm : 1 ≤ m := by
    have hp := mul_nonneg (show 0≤Real.cos h by linarith [ht.1]) ht.2.2.1
    have hm0 : 0 ≤ m := by rw [hm_def]; linarith [ht.1,ht.2.2.1]
    have hsq : m^2=1+2*(Real.cos h*Real.sin h) := by
      rw [hm_def]
      linear_combination Real.sin_sq_add_cos_sq h
    nlinarith
  have hn : 39/50≤n := by rw [hn_def]; linarith [hh.2]
  have hid : (S H h+m)^2+(U_H H h+n)^2=H.circle := by
    rw [hm_def,hn_def]
    dsimp [S,U_H,SignedPoint.circle]
    rw [abs_of_nonneg hHy]
    linear_combination (((H.a+1/2)^2+(H.y+1/2)^2)*Real.sin_sq_add_cos_sq h)
  by_contra! hbad
  have hs2 := pow_le_pow_left₀ (show (0:ℝ)≤603/500 by norm_num)
    (show 603/500≤S H h+m by linarith) 2
  have hu2 := pow_le_pow_left₀ (show (0:ℝ)≤79/50 by norm_num)
    (show 79/50≤U_H H h+n by linarith) 2
  have hq : H.circle≤9789/2500 := hHq
  linarith

theorem U_lower {q P Y z : ℝ} (C : PositiveSmallScalar.CapData q P Y)
    (hz : z∈Icc 0 frameCap) (hV : 1/2≤V P Y z) : Y≤U P Y z := by
  have ht := transport_trig hz
  have hP : 0≤P := by linarith [C.P_mem.1]
  have hY : 0≤Y := by linarith [C.Y_mem.1]
  have hU : 0≤U P Y z := by
    dsimp [U]
    exact add_nonneg (mul_nonneg hP ht.2.2.1)
      (mul_nonneg hY (by linarith [ht.1]))
  have hv := PositiveSmallScalar.V_upper C hz
  have hv2 := pow_le_pow_left₀ (show 0≤V P Y z by linarith) hv 2
  nlinarith [PositiveSmallScalar.rotation_identity P Y z]

theorem alignment_reserve {q P Y r z : ℝ} {H : SignedPoint}
    (C : PositiveSmallScalar.CapData q P Y)
    (hHy : 0≤H.y) (hHq : H.Contained q)
    (hr : 0≤r) (hz : 0≤z) (hspan : z+r≤1/5)
    (hV : 1/2≤V P Y z) (hpair : 1≤composite H P Y r z) :
    ∀x∈Icc 0 z, 1≤composite H P Y r x ∧
      (7/200)*(z-x)≤composite H P Y r x-composite H P Y r z := by
  apply feasible_left_reserve hz (by norm_num : (0:ℝ)<7/200)
  · exact (continuous_iff_continuousAt.2 fun x =>
      (composite_hasDerivAt H P Y r x).continuousAt).continuousOn
  · intro x _
    exact composite_hasDerivAt H P Y r x
  · intro x hx hfeasible
    have hxi : x∈Icc 0 frameCap := ⟨hx.1,by dsimp [frameCap]; linarith [hx.2]⟩
    have hzi : z∈Icc 0 frameCap := ⟨hz,by dsimp [frameCap]; linarith⟩
    have hhi : x+r∈Icc 0 (1/5 : ℝ) := ⟨by linarith [hx.1],by linarith [hx.2]⟩
    have hxV : 1/2≤V P Y x :=
      hV.trans (PositiveSmallScalar.V_antitone C hxi hzi hx.2)
    have hxU := U_lower C hxi hxV
    have hxupper := (PositiveSmallScalar.V_upper C hxi).trans C.P_mem.2
    have hxS : 103/500≤S H (x+r) := by dsimp [composite] at hfeasible; linarith
    have hhU := rotated_support_upper hHy (hHq.trans C.ceiling) hhi hxS
    dsimp [compositeD]
    linarith [C.Y_mem.1]
  · exact hpair

theorem actual_cap {q z : ℝ} {G A : SignedPoint}
    (hq : q≤qCap) (hAs : A.Sorted) (hAc : A.AvoidsCore)
    (hAq : A.Contained q) (hAy : A.y∈Icc (67/200 : ℝ) (1/2))
    (hGy : G.y≤0) (hz : z∈Icc 0 frameCap)
    (hGA : quarterFeasible G A (-z) 0) :
    PositiveSmallScalar.CapData q (A.a-1/2) (A.y+1/2) ∧
      1/2≤V (A.a-1/2) (A.y+1/2) z := by
  have ha := SignedPoint.primary_gt_half hAs hAc
  have hcontact := SignedOppositeHardEnvelope.negative_hard_contact hz hGA
  have ht := transport_trig hz
  have hp := mul_le_mul_of_nonneg_left ht.2.1 (show 0≤A.a-1/2 by linarith)
  have hy := mul_nonneg (show 0≤A.y+1/2 by linarith [hAy.1]) ht.2.2.1
  have ha1 : 1≤A.a := by linarith
  have hcircle : (A.a-1/2+1)^2+(A.y+1/2)^2≤q := by
    have h : A.circle≤q := hAq
    simp only [SignedPoint.circle,abs_of_nonneg (show 0≤A.y by linarith [hAy.1])] at h
    have he : A.a-1/2+1=A.a+1/2 := by ring
    rw [he]
    exact h
  have hupper : A.a-1/2≤397/500 := by
    have hc := hcircle.trans hq
    dsimp [qCap] at hc
    nlinarith [hAy.1]
  refine ⟨⟨⟨by linarith,hupper⟩,⟨by linarith [hAy.1],by linarith [hAy.2]⟩,
    hcircle,hq⟩,?_⟩
  dsimp [V]
  linarith

/-- The endpoint tangent is below the original H tangent.  This uses
the captured full angle and the retained canceling projection only. -/
theorem tangent_order {H : SignedPoint} {r g : ℝ}
    (hHy : 0≤H.y) (hHa : H.a≤283/200)
    (hr : r∈Icc 0 (1/5 : ℝ)) (hg : g∈Icc (0:ℝ) (147/500))
    (hHG : 1/2≤g+S H r) : g<H.y := by
  have hi : r∈Icc 0 frameCap := ⟨hr.1,by dsimp [frameCap]; linarith [hr.2]⟩
  have ht := transport_trig hi
  have hsin := Real.sin_le hr.1
  have hcos := Real.one_sub_sq_div_two_le_cos (x := r)
  have h2 := pow_le_pow_left₀ hr.1 hr.2 2
  have hc98 : 49/50≤Real.cos r := by linarith
  by_contra! hbad
  have hprimary := mul_le_mul_of_nonneg_right
    (show H.a-1/2≤183/200 by linarith) ht.2.2.1
  have hminor := mul_le_mul_of_nonneg_right
    (show H.y-1/2≤g-1/2 by linarith) (show 0≤Real.cos r by linarith [ht.1])
  have hgcos := mul_le_mul_of_nonpos_left hc98
    (show g-1/2≤0 by linarith [hg.2])
  dsimp [S] at hHG
  linarith [hr.2,hg.2]

end SquaresInCircles.Eight.TableFree.SmallCancelingScalar

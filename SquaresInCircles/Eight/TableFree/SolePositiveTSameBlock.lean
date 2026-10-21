module

public import SquaresInCircles.Eight.TableFree.SolePositiveTGrowth

/-!
# Same-anchor alternatives for every positive-T family

Uncompiled source. The original norm cancels in the comparison. The
low EH ratio dominates the existing correlated whole-interval ratio.
The two remaining low ratios follow from one half-angle inequality.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SolePositiveTSameBlock
open PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryAngleConcentration

theorem from_bracket {R p q r t : ℝ} (hq : 0≤q) (hr : r*q≤p)
    (ht : t∈Icc 0 frameCap)
    (hbracket : 0≤r*(phi (frameCap-t)-1)+Real.cos frameCap-Real.cos t) :
    V R p q t≤M R p q t := by
  have ha : frameCap-t∈Icc 0 frameCap := ⟨by linarith [ht.2],by linarith [ht.1]⟩
  have hphi := sub_nonneg.mpr (CorrelatedSameBlock.one_le_phi ha)
  have hm := mul_le_mul_of_nonneg_right hr hphi
  have hb := mul_nonneg hq hbracket
  dsimp [V,M]
  nlinarith

theorem half_angle_bracket {r t : ℝ} (ht : t∈Icc 0 frameCap)
    (hr : r≤Real.cos frameCap)
    (hreserve : 0≤r-Real.sin frameCap+
      (Real.cos frameCap-r)*(frameCap-t)/2) :
    0≤r*(phi (frameCap-t)-1)+Real.cos frameCap-Real.cos t := by
  let a := frameCap-t
  have ha : a∈Icc 0 frameCap := ⟨by dsimp [a]; linarith [ht.2],
    by dsimp [a]; linarith [ht.1]⟩
  have hh := mul_le_mul_of_nonneg_left (CorrelatedSameBlock.half_angle_lower ha)
    (sub_nonneg.mpr hr)
  have hs := mul_nonneg (transport_trig ha).2.2.1 hreserve
  have hid : Real.cos t=Real.cos frameCap*Real.cos a+Real.sin frameCap*Real.sin a := by
    rw [← Real.cos_sub]
    congr 1
    dsimp [a]
    ring
  rw [hid]
  dsimp [phi,a] at *
  nlinarith

theorem EH_low {R p q t : ℝ} (hq : 0≤q)
    (hr : (117/200+3/10*t)*q≤p) (ht : t∈Icc 0 frameCap) :
    V R p q t≤M R p q t := by
  have hcor : PositiveStressCoefficients.ratio t*q≤p := by
    have hh := mul_nonneg ht.1 hq
    dsimp [PositiveStressCoefficients.ratio]
    nlinarith
  have hh := CorrelatedSameBlock.negative_surplus (R:=R) hq hcor ht
    (show (0:ℝ)∈Icc 0 t from ⟨le_rfl,ht.1⟩)
  have hid : mixedBlock R p q (frameCap-t) frameCap=M R p q t := by
    simpa only [show t+(frameCap-t)=frameCap by ring] using mixedBlock_saturated R p q t
  simpa only [sub_zero,hid] using hh

theorem EH_middle {R p q t : ℝ} (hq : 0≤q)
    (hr : (13/20)*q≤p) (ht : t∈Icc 0 frameCap) :
    V R p q t≤M R p q t := by
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have hc := (transport_trig hh).1
  have hs := (transport_trig hh).2.2.2.1
  apply from_bracket hq hr ht
  apply half_angle_bracket ht (by linarith)
  have hm := mul_nonneg (show 0≤Real.cos frameCap-13/20 by linarith)
    (show 0≤frameCap-t by linarith [ht.2])
  linarith

theorem DE_low_B {R p q t : ℝ} (hq : 0≤q)
    (hr : (5/8)*q≤p) (ht : t∈Icc 0 (7/20:ℝ)) :
    V R p q t≤M R p q t := by
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have hc := (transport_trig hh).1
  have hs := (transport_trig hh).2.2.2.1
  have ht' : t∈Icc 0 frameCap := ⟨ht.1,by norm_num [frameCap]; linarith [ht.2]⟩
  apply from_bracket hq hr ht'
  apply half_angle_bracket ht' (by linarith)
  have hlen : (7/20:ℝ)≤frameCap-t := by norm_num [frameCap]; linarith [ht.2]
  have hm := mul_le_mul (by linarith : (699/5000:ℝ)≤Real.cos frameCap-5/8)
    hlen (by norm_num) (by linarith)
  linarith

end SquaresInCircles.Eight.TableFree.SolePositiveTSameBlock

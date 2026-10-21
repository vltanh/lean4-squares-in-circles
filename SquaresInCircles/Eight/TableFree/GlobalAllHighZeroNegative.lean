module

public import SquaresInCircles.Eight.TableFree.GlobalAllHighZeroPositive
public import SquaresInCircles.Eight.TableFree.ZeroSignedCharge

/-!
# Nonpositive errors of the original zero edges

The original weak projection itself forces a positive source tangent.
The previously proved signed `.98` charge then strengthens to the
common `1.03` charge, and the same target-potential gap closes the row.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalAllHigh

open FramePair ZeroPrimary GlobalZeroSign GlobalOuterAnchor

theorem zero_nonpositive_error_source (s t : State) {d : ℝ}
    (hd : |d|≤frameCap) (hd0 : d≤0)
    (hm : width d≤transverse s+t.a*Real.sin d+t.b*Real.cos d ∨
      width d≤s.a*Real.sin d+transverse s*Real.cos d+t.b) :
    0<transverse s := by
  have hw := width_ge_one hd
  have hsin := sine_nonpos hd hd0
  have hcos : 0≤Real.cos d := by linarith [(signed_trig hd).1]
  have htarget := (coordinates t).2.2.2.2
  by_contra! hy
  rcases hm with hm | hm
  · have hA := mul_nonpos_of_nonneg_of_nonpos t.a_pos.le hsin
    have hB := mul_le_mul_of_nonneg_left (Real.cos_le_one d) t.b_nonneg
    linarith
  · have ha := mul_nonpos_of_nonneg_of_nonpos s.a_pos.le hsin
    have hyc := mul_nonpos_of_nonpos_of_nonneg hy hcos
    linarith

theorem zero_nonpositive_error (s t : State) (ht : t.branch.type≠0)
    {d : ℝ} (hd : |d|≤frameCap) (hd0 : d≤0)
    (hm : width d≤transverse s+t.a*Real.sin d+t.b*Real.cos d ∨
      width d≤s.a*Real.sin d+transverse s*Real.cos d+t.b) :
    gammaZero≤zeroCharge s t d := by
  have hy := (zero_nonpositive_error_source s t hd hd0 hm).le
  have hsy := transverse_of_nonneg s hy
  have hsc := coordinates s
  have htc := coordinates t
  have hw : edgeWidth d=width d := by
    exact CommonQuarter.signed_width (by simpa only [frameCap] using hd)
  have hproj : edgeWidth d≤s.b+t.a*Real.sin d+t.b*Real.cos d ∨
      edgeWidth d≤s.a*Real.sin d+s.b*Real.cos d+t.b := by
    simpa only [hw,hsy] using hm
  have hzero := ZeroSignedCharge.nonnegative_zero
    ⟨hsc.1.le,hsc.2.1.le⟩ ⟨htc.1.le,htc.2.1.le⟩
    ⟨s.b_nonneg,hsc.2.2.2.2.le⟩ ⟨t.b_nonneg,htc.2.2.2.2.le⟩ hd hproj
  have hD : 0≤s.b+t.b-1 := by
    dsimp [ZeroSignedCharge.kappa] at hzero
    linarith
  have hgap := target_gap t ht
  rw [zeroCharge,hsy]
  dsimp [gammaZero,kappa,ZeroSignedCharge.kappa] at *
  linarith

/-- Every original zero with nonnegative source has no loss, for all
errors, radial kinds, and outer target charts. -/
theorem zero_nonnegative_source (s t : State) (ht : t.branch.type≠0)
    (hy : 0≤transverse s) {d : ℝ} (hd : |d|≤frameCap)
    (hm : width d≤transverse s+t.a*Real.sin d+t.b*Real.cos d ∨
      width d≤s.a*Real.sin d+transverse s*Real.cos d+t.b) :
    gammaZero≤zeroCharge s t d := by
  rcases le_total 0 d with hd0 | hd0
  · exact positive_zero_nonnegative s t ht hy ⟨hd0,(le_abs_self d).trans hd⟩ hm
  · exact zero_nonpositive_error s t ht hd hd0 hm

end SquaresInCircles.Eight.TableFree.GlobalAllHigh

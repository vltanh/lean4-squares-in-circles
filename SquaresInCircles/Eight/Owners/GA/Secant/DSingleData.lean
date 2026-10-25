module

public import SquaresInCircles.Eight.Owners.GA.Positive.BT3DEnvelopeGeometry
public import SquaresInCircles.Eight.Frames.Ordinary.PositiveEnvelope

/-!
# Eight squares: one signed D angle with its secant coefficient

The support is the sorted outer-circle support. The positive branch keeps its coefficient
`max q c`; neither the secant coefficient nor the remaining angle of the cycle changes
(`positive_lower`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.SecantD
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PositiveBT3

abbrev slope : ℝ := 109/200
abbrev qUpper : ℝ := 327/250
abbrev cLower : ℝ := 7/10
abbrev cUpper : ℝ := 7/5

def increment (q c t : ℝ) : ℝ :=
  c*(edgeWidth t-1)+sortedSupport q c-
    sortedSupport (q+c*Real.sin t) (c*Real.cos t)

def actualIncrement (q c t : ℝ) (P : SignedPoint) : ℝ :=
  c*(edgeWidth t-1)+sortedSupport q c-
    ((q+c*Real.sin t)*P.a+(c*Real.cos t)*(-P.y))

theorem coefficient_pos {q c : ℝ} (hq : q∈Icc 1 qUpper)
    (hc : c∈Icc cLower cUpper) : 0<q ∧ 0<c ∧ q≤2*c := by
  dsimp [qUpper,cLower,cUpper] at *
  exact ⟨by linarith [hq.1],by linarith [hc.1],by linarith [hq.2,hc.1]⟩

theorem forces_positive {q c t : ℝ} (hq : q∈Icc 1 qUpper)
    (hc : c∈Icc cLower cUpper) (ht : |t|≤frameCap) :
    0<q+c*Real.sin t ∧ 0<c*Real.cos t := by
  have htrig := signed_trig ht
  have hs : -(6443/10000:ℝ)<Real.sin t := neg_lt_of_abs_lt htrig.2
  have hp := coefficient_pos hq hc
  have hm := mul_lt_mul_of_pos_left hs hp.2.1
  have hu := mul_le_mul_of_nonneg_right hc.2 (by norm_num : (0:ℝ)≤6443/10000)
  dsimp [cUpper] at hu
  exact ⟨by linarith [hq.1],mul_pos hp.2.1 (by linarith [htrig.1])⟩

theorem baseline_no_axis {q c : ℝ} (hq : q∈Icc 1 qUpper)
    (hc : c∈Icc cLower cUpper) : q/2<(axial+1/2)*c := by
  have hp := coefficient_pos hq hc
  have hm := mul_le_mul_of_nonneg_left hc.1
    (show 0≤axial+1/2 by linarith [axial_bounds.1])
  dsimp [qUpper,cLower] at *
  nlinarith [axial_bounds.1,hq.2]

theorem baseline_clipped {q c : ℝ} (hq : q∈Icc 1 qUpper)
    (hc : c∈Icc cLower cUpper) : sortedSupport q c=clippedSupport q c := by
  have hn := not_le.mpr (baseline_no_axis hq hc)
  simp only [sortedSupport,clippedSupport,hn,↓reduceIte]

theorem baseline_full {q c : ℝ} (hq : q∈Icc 1 qUpper)
    (hc : c∈Icc cLower cUpper) (hcq : c≤q) :
    sortedSupport q c=fullSupport q c := by
  have hp := coefficient_pos hq hc
  exact sortedSupport_full_of_between hp.1 hp.2.1 hcq (baseline_no_axis hq hc).le

theorem force_norm (q c t : ℝ) :
    Real.sqrt ((q+c*Real.sin t)^2+(c*Real.cos t)^2)=pairNorm c q t := by
  unfold pairNorm
  congr 1
  linear_combination c^2*Real.sin_sq_add_cos_sq t

theorem full_increment_positive {q c t : ℝ} (ht : t∈Icc 0 frameCap) :
    c*(edgeWidth t-1)+fullSupport q c-
      fullSupport (q+c*Real.sin t) (c*Real.cos t)=U R c q t := by
  rw [edgeWidth_positive_formula ht]
  have hzero : Real.sqrt (q^2+c^2)=pairNorm c q 0 := by
    simp [pairNorm,add_comm]
  dsimp [fullSupport,U,PositiveAngularEnvelope.phi]
  rw [force_norm,hzero]
  ring

theorem positive_below {q c t : ℝ} (hq : q∈Icc 1 qUpper)
    (hc : c∈Icc cLower cUpper) (ht : t∈Icc 0 frameCap) (hcq : c≤q) :
    -slope*q*t≤ increment q c t := by
  have hp := coefficient_pos hq hc
  have hU := OrdinaryPositiveEnvelope.U_lower (Real.sqrt_nonneg qCap)
    radius_sq.le hp.2.1 hcq hp.2.2 ht
  have hs := sortedSupport_le_full (f:=q+c*Real.sin t) (g:=c*Real.cos t)
  have he := full_increment_positive (q:=q) (c:=c) ht
  dsimp [increment,slope]
  rw [baseline_full hq hc hcq]
  linarith

/-- The support point selected by the final force has primary coordinate at least the diagonal
coordinate; this is the integrated form of the nonpositive derivative in `q/c`. -/
theorem positive_above {q c t : ℝ} (hq : q∈Icc 1 qUpper)
    (hc : c∈Icc cLower cUpper) (ht : t∈Icc 0 frameCap) (hqc : q≤c) :
    -slope*c*t≤ increment q c t := by
  have hp := coefficient_pos hq hc
  have hf := forces_positive hq hc (by rw [abs_of_nonneg ht.1]; exact ht.2)
  obtain ⟨a,b,ha,hb,hab,hcircle,hsupport⟩ := sortedSupport_attained hf.1 hf.2
  have hda : GlobalGA.Secondary.diagonal≤a := by
    nlinarith [diagonal_circle,diagonal_bounds.1]
  have hbase := raw_full_support (a:=a) (b:=b) (f:=1+Real.sin t)
    (g:=Real.cos t) hcircle.le
  have hm := mul_le_mul_of_nonneg_left hbase hp.2.1.le
  have hd := mul_le_mul_of_nonpos_left hda (sub_nonpos.mpr hqc)
  have hnorm : (2:ℝ)*GlobalGA.Secondary.diagonal=fullSupport 1 1 := by
    have hh := full_at_diagonal (f:=1) (g:=1) rfl (by norm_num)
    simp only [diagonalSupport] at hh
    rw [hh]; ring
  have he := full_increment_positive (q:=1) (c:=1) ht
  norm_num only [one_mul] at he
  have hU := OrdinaryPositiveEnvelope.U_lower (p:=1) (q:=1)
    (Real.sqrt_nonneg qCap) radius_sq.le (by norm_num) le_rfl (by norm_num) ht
  have hUc := mul_le_mul_of_nonneg_left hU hp.2.1.le
  dsimp [increment,slope]
  rw [sortedSupport_diagonal hqc,hsupport]
  dsimp [diagonalSupport]
  rw [←hnorm] at he
  nlinarith

theorem positive_lower {q c t : ℝ} (hq : q∈Icc 1 qUpper)
    (hc : c∈Icc cLower cUpper) (ht : t∈Icc 0 frameCap) :
    -slope*max q c*t≤ increment q c t := by
  by_cases hqc : q≤c
  · simpa [max_eq_right hqc] using positive_above hq hc ht hqc
  · have hcq := (lt_of_not_ge hqc).le
    simpa [max_eq_left hcq] using positive_below hq hc ht hcq

end SquaresInCircles.Eight.GlobalGA.SecantD

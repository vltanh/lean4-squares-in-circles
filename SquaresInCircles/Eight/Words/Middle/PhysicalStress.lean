module

public import SquaresInCircles.Eight.Owners.Positive.AngularEnvelope

/-!
# Eight squares: the original AB--BT inequalities as a two-circle stress

A lower bound for the unchanged A radial coordinate is added to a positive multiple of the AB
witness and of the hard BT2 witness. Both AB owners are covered (`raw_zero`, `raw_two`). Only A
and B are supported by their circles; the T contribution is its unchanged signed tangent, with no
sign premise and no circle relaxation.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.MiddlePhysicalStress
open Candidate SignedStress SecondaryEStress PositiveAngularEnvelope

theorem positive_rotated_support {P : SignedPoint} {R : ℝ}
    (hR : 0≤R) (hc : P.Contained (R^2)) (hy : 0≤P.y)
    (p r u v : ℝ) :
    work (rotatedPair p r u v) P≤
      R*pairNorm p r (u+v)-(p*PositiveAngularEnvelope.phi v+r*PositiveAngularEnvelope.phi u)/2 := by
  have h := work_le_signed_support hR hc (Or.inl rfl)
    (by simpa [abs_of_nonneg hy] : (1:ℝ)*P.y=|P.y|)
    (rotatedPair p r u v)
  change work (rotatedPair p r u v) P≤ signedSupport R 1 (rotatedPair p r u v) at h
  rw [rotatedPair_signedSupport] at h
  exact h

theorem negative_rotated_support {P : SignedPoint} {R : ℝ}
    (hR : 0≤R) (hc : P.Contained (R^2)) (hy : P.y≤0)
    (p r u v : ℝ) :
    work ((rotatedPair p r u v).1,-(rotatedPair p r u v).2) P≤
      R*pairNorm p r (u+v)-(p*PositiveAngularEnvelope.phi v+r*PositiveAngularEnvelope.phi u)/2 := by
  have h := work_le_signed_support hR hc (Or.inr rfl)
    (by simp [abs_of_nonpos hy] : (-1:ℝ)*P.y=|P.y|)
    ((rotatedPair p r u v).1,-(rotatedPair p r u v).2)
  change work ((rotatedPair p r u v).1,-(rotatedPair p r u v).2) P≤
    signedSupport R (-1) ((rotatedPair p r u v).1,-(rotatedPair p r u v).2) at h
  rw [reflected_rotatedPair_signedSupport] at h
  exact h

/-- Exact original AB0 stress, before its angular width is minimized. -/
theorem raw_zero {A B T : SignedPoint} {R l f d v : ℝ}
    (hR : 0≤R) (hA : A.Contained (R^2)) (hB : B.Contained (R^2))
    (hyA : 0≤A.y) (hyB : B.y≤0) (hl : 0≤l) (hf : f≤A.a)
    (hd : |d|≤frameCap) (hv : |v|≤frameCap)
    (hAB : zeroFeasible A B d 0) (hBT : quarterFeasible B T v 2) :
    f+2+2*l-2*R*pairNorm l 1 0+
      (l*psi d+psi v-R*(pairNorm l 1 (d+v)-pairNorm l 1 0))+T.y≤0 := by
  have hsupA := positive_rotated_support hR hA hyA 1 l 0 0
  have hsupB := negative_rotated_support hR hB hyB 1 l d v
  simp only [work,rotatedPair,Real.sin_zero,Real.cos_zero,phi_zero,
    zero_add,add_zero,mul_zero,mul_one,one_mul,pairNorm_symm 1 l] at hsupA hsupB
  have hAB' : edgeWidth d≤A.y+B.a*Real.sin d-B.y*Real.cos d := by
    simpa [zeroFeasible,zeroProjection] using hAB
  have hBT' : edgeWidth v≤B.a*Real.cos v-B.y*Real.sin v-T.y := by
    simpa [quarterFeasible,quarterProjection] using hBT
  have hweighted := mul_le_mul_of_nonneg_left hAB' hl
  have hwd := width_add_half_phi hd
  have hwv := width_add_half_phi hv
  have hwld := congrArg (fun z : ℝ => l*z) hwd
  dsimp [PositiveAngularEnvelope.phi] at hwd hwv hwld hsupA hsupB
  nlinarith

/-- Exact original AB2 stress. Its two separate norms keep the AB and BT angles, of either sign
and with weak owner ties. -/
theorem raw_two {A B T : SignedPoint} {R l f d v : ℝ}
    (hR : 0≤R) (hA : A.Contained (R^2)) (hB : B.Contained (R^2))
    (hyA : 0≤A.y) (hyB : B.y≤0) (hl : 0≤l) (hf : f≤A.a)
    (hd : |d|≤frameCap) (hv : |v|≤frameCap)
    (hAB : zeroFeasible A B d 2) (hBT : quarterFeasible B T v 2) :
    f+2+2*l-2*R*pairNorm l 1 0+
      (l*psi d-R*(pairNorm l 1 d-pairNorm l 1 0))+
      (psi v-R*(pairNorm l 1 v-pairNorm l 1 0))+T.y≤0 := by
  have hsupA := positive_rotated_support hR hA hyA 1 l d 0
  have hsupB := negative_rotated_support hR hB hyB 1 l 0 v
  simp only [work,rotatedPair,Real.sin_zero,Real.cos_zero,phi_zero,
    zero_add,add_zero,mul_zero,mul_one,one_mul,pairNorm_symm 1 l] at hsupA hsupB
  have hAB' : edgeWidth d≤A.a*Real.sin d+A.y*Real.cos d-B.y := by
    simpa [zeroFeasible,zeroProjection] using hAB
  have hBT' : edgeWidth v≤B.a*Real.cos v-B.y*Real.sin v-T.y := by
    simpa [quarterFeasible,quarterProjection] using hBT
  have hweighted := mul_le_mul_of_nonneg_left hAB' hl
  have hwd := width_add_half_phi hd
  have hwv := width_add_half_phi hv
  have hwld := congrArg (fun z : ℝ => l*z) hwd
  dsimp [PositiveAngularEnvelope.phi] at hwd hwv hwld hsupA hsupB
  nlinarith

/-- The original signed three-edge AB0 stress with unequal positive
weights.  This is also the starting identity for the small-wrong-sign
capture; G and T keep their signed coordinates. -/
theorem signed_three_zero {G A B T : SignedPoint} {R a b c x d v : ℝ}
    (hR : 0≤R) (hA : A.Contained (R^2)) (hB : B.Contained (R^2))
    (hyA : 0≤A.y) (hyB : B.y≤0)
    (ha : 0≤a) (hb : 0≤b) (hc : 0≤c)
    (hx : |x|≤frameCap) (hd : |d|≤frameCap) (hv : |v|≤frameCap)
    (hGA : quarterFeasible G A x 0)
    (hAB : zeroFeasible A B d 0) (hBT : quarterFeasible B T v 2) :
    -a*G.y+c*T.y≤
      R*(pairNorm a b x+pairNorm c b (d+v))-
      (a+c)/2-b-a*(1+psi x)-b*(1+psi d)-c*(1+psi v) := by
  have hsupA := positive_rotated_support hR hA hyA a b 0 x
  have hsupB := negative_rotated_support hR hB hyB c b d v
  simp only [work,rotatedPair,Real.sin_zero,Real.cos_zero,phi_zero,
    zero_add,add_zero,mul_zero,mul_one] at hsupA hsupB
  have hGA' : edgeWidth x≤G.y+A.a*Real.cos x+A.y*Real.sin x := by
    simpa [quarterFeasible,quarterProjection] using hGA
  have hAB' : edgeWidth d≤A.y+B.a*Real.sin d-B.y*Real.cos d := by
    simpa [zeroFeasible,zeroProjection] using hAB
  have hBT' : edgeWidth v≤B.a*Real.cos v-B.y*Real.sin v-T.y := by
    simpa [quarterFeasible,quarterProjection] using hBT
  have hwa := mul_le_mul_of_nonneg_left hGA' ha
  have hwb := mul_le_mul_of_nonneg_left hAB' hb
  have hwc := mul_le_mul_of_nonneg_left hBT' hc
  have hwx := width_add_half_phi hx
  have hwd := width_add_half_phi hd
  have hwv := width_add_half_phi hv
  have hwax := congrArg (fun z : ℝ => a*z) hwx
  have hwbd := congrArg (fun z : ℝ => b*z) hwd
  have hwcv := congrArg (fun z : ℝ => c*z) hwv
  dsimp [PositiveAngularEnvelope.phi] at hsupA hsupB hwx hwd hwv hwax hwbd hwcv
  nlinarith

end SquaresInCircles.Eight.MiddlePhysicalStress

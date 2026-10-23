module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDETD2EndpointData

/-!
# The actual intrinsic E endpoints of the negative-DE stress

Uncompiled scalar identities for equations (12)--(15).  The low endpoint
keeps the sorted diagonal D support.  The high endpoint has its full D
norm, including the secant at s=theta.  All A/TD coefficients still depend
on their common total angle.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveTD.Certificate
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

def lowBase (e : Split) (θ s : ℝ) : ℝ :=
  Explicit.baseline .low (Explicit.splitA e θ) (Explicit.splitT e θ) s
def highBase (e : Split) (θ s : ℝ) : ℝ :=
  Explicit.fullBaseline .high (Explicit.splitA e θ) (Explicit.splitT e θ) s

theorem split_sum (e : Split) (θ : ℝ) :
    Explicit.splitA e θ+Explicit.splitT e θ=θ := by cases e <;> simp [Explicit.splitA,Explicit.splitT]

theorem low_D_diagonal {θ s : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) (hs : s∈Icc 0 θ) :
    Explicit.secant s≤Explicit.c .low θ := by
  have hc := (TwoPositive.Split.low_trig ⟨hs.1,hs.2.trans hθ.2⟩).1
  have hr := Explicit.low_ranges hθ
  have hcpos : 0<Real.cos s := by linarith
  apply (div_le_iff₀ hcpos).2
  have hh := mul_le_mul_of_nonneg_left hc
    (show 0≤Explicit.c .low θ by linarith [hr.2.2.2.2.1])
  nlinarith [hr.2.2.2.2.1]

theorem low_baseline_identity (e : Split) {θ s : ℝ}
    (hθ : θ∈Icc (0:ℝ) (1/6)) (hs : s∈Icc 0 θ) :
    lowBase e θ s=lowNonradical e θ-(diagonal-1/2)*(Explicit.secant s-1)+
      Explicit.K*Real.tan s-R*(pairNorm (Explicit.k .low θ) 1 0+
        pairNorm (Explicit.k .low θ) (Explicit.l .low θ) 0+
        pairNorm (Explicit.l .low θ) (Explicit.splitM .low e θ) 0) := by
  have hD := low_D_diagonal hθ hs
  simp only [lowBase,Explicit.baseline,split_sum,fullSupport_pair]
  rw [clippedSupport,if_pos hD]
  dsimp [lowNonradical,diagonalSupport,Explicit.splitM]
  ring

theorem high_baseline_identity (e : Split) (θ s : ℝ) :
    highBase e θ s=highNonradical e θ+Explicit.secant s-1+Explicit.K*Real.tan s-
      R*(pairNorm (Explicit.k .high θ) 1 0+
        pairNorm (Explicit.k .high θ) (Explicit.l .high θ) 0+
        pairNorm (Explicit.l .high θ) (Explicit.splitM .high e θ) 0+
        pairNorm (Explicit.secant s) (Explicit.c .high θ) 0) := by
  simp only [highBase,Explicit.fullBaseline,Explicit.baseline,split_sum,fullSupport_pair]
  rw [pairNorm_symm (Explicit.c .high θ) (Explicit.secant s) 0]
  dsimp [highNonradical,Explicit.splitM]
  ring

theorem low_H_identity (e : Split) {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) (x : ℝ) :
    lowBase e θ 0+V R (Explicit.k .low θ) 1 x=
      lowNonradical e θ+Real.cos x-1-
        R*(pairNorm (Explicit.k .low θ) 1 (-x)+
          pairNorm (Explicit.k .low θ) (Explicit.l .low θ) 0+
          pairNorm (Explicit.l .low θ) (Explicit.splitM .low e θ) 0) := by
  rw [low_baseline_identity e hθ ⟨le_rfl,hθ.1⟩]
  simp only [Explicit.secant,Real.cos_zero,Real.tan_zero,div_one,sub_self,mul_zero,sub_zero,add_zero]
  dsimp [V]
  ring

theorem low_G_identity (e : Split) {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) (x : ℝ) :
    lowBase e θ 0+V R (Explicit.k .low θ) (Explicit.l .low θ) x=
      lowNonradical e θ+Explicit.l .low θ*(Real.cos x-1)-
        R*(pairNorm (Explicit.k .low θ) 1 0+
          pairNorm (Explicit.k .low θ) (Explicit.l .low θ) (-x)+
          pairNorm (Explicit.l .low θ) (Explicit.splitM .low e θ) 0) := by
  rw [low_baseline_identity e hθ ⟨le_rfl,hθ.1⟩]
  simp only [Explicit.secant,Real.cos_zero,Real.tan_zero,div_one,sub_self,mul_zero,sub_zero,add_zero]
  dsimp [V]
  ring

theorem high_H_identity (e : Split) (θ : ℝ) :
    highBase e θ 0+V R (Explicit.k .high θ) 1 θ=
      highNonradical e θ+Real.cos θ-1-
        R*(pairNorm (Explicit.k .high θ) (Explicit.l .high θ) 0+
          pairNorm (Explicit.l .high θ) (Explicit.splitM .high e θ) 0+
          pairNorm (Explicit.k .high θ) 1 (-θ)+pairNorm 1 (Explicit.c .high θ) 0) := by
  rw [high_baseline_identity]
  simp only [Explicit.secant,Real.cos_zero,Real.tan_zero,div_one,mul_zero,add_zero]
  dsimp [V]
  ring

theorem high_G_identity (e : Split) (θ : ℝ) :
    highBase e θ 0+V R (Explicit.k .high θ) (Explicit.l .high θ) θ=
      highNonradical e θ+Explicit.l .high θ*(Real.cos θ-1)-
        R*(pairNorm (Explicit.k .high θ) 1 0+
          pairNorm (Explicit.l .high θ) (Explicit.splitM .high e θ) 0+
          pairNorm (Explicit.k .high θ) (Explicit.l .high θ) (-θ)+
          pairNorm 1 (Explicit.c .high θ) 0) := by
  rw [high_baseline_identity]
  simp only [Explicit.secant,Real.cos_zero,Real.tan_zero,div_one,mul_zero,add_zero]
  dsimp [V]
  ring

theorem high_B_identity (e : Split) (θ : ℝ) :
    highBase e θ 0+V R (min (Explicit.l .high θ) (Explicit.splitM .high e θ))
      (max (Explicit.l .high θ) (Explicit.splitM .high e θ)) θ=
      highNonradical e θ+max (Explicit.l .high θ) (Explicit.splitM .high e θ)*(Real.cos θ-1)-
        R*(pairNorm (Explicit.k .high θ) 1 0+
          pairNorm (Explicit.k .high θ) (Explicit.l .high θ) 0+
          pairNorm (Explicit.l .high θ) (Explicit.splitM .high e θ) (-θ)+
          pairNorm 1 (Explicit.c .high θ) 0) := by
  rw [high_baseline_identity]
  simp only [Explicit.secant,Real.cos_zero,Real.tan_zero,div_one,mul_zero,add_zero,V,
    TwoPositive.Certificate.sorted_pair_norm]
  ring

theorem low_equal_identity (e : Split) {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    Real.cos θ*lowBase e θ θ=
      Real.cos θ*(lowNonradical e θ+(diagonal-1/2))+Explicit.K*Real.sin θ-(diagonal-1/2)-
        R*(Real.cos θ*pairNorm (Explicit.k .low θ) 1 0+
          Real.cos θ*pairNorm (Explicit.k .low θ) (Explicit.l .low θ) 0+
          Real.cos θ*pairNorm (Explicit.l .low θ) (Explicit.splitM .low e θ) 0) := by
  have hc : Real.cos θ≠0 := by linarith [(transport_trig (family_frame_domain .low hθ)).1]
  rw [low_baseline_identity e hθ ⟨hθ.1,le_rfl⟩]
  dsimp [Explicit.secant]
  rw [Real.tan_eq_sin_div_cos]
  field_simp [hc]
  ring

theorem high_equal_identity (e : Split) {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    Real.cos θ*highBase e θ θ=
      Real.cos θ*(highNonradical e θ-1)+1+Explicit.K*Real.sin θ-
        R*(Real.cos θ*pairNorm (Explicit.k .high θ) 1 0+
          Real.cos θ*pairNorm (Explicit.k .high θ) (Explicit.l .high θ) 0+
          Real.cos θ*pairNorm (Explicit.l .high θ) (Explicit.splitM .high e θ) 0+
          Real.cos θ*pairNorm (Explicit.secant θ) (Explicit.c .high θ) 0) := by
  have hc : Real.cos θ≠0 := by linarith [(transport_trig (family_frame_domain .high hθ)).1]
  rw [high_baseline_identity]
  dsimp [Explicit.secant]
  rw [Real.tan_eq_sin_div_cos]
  field_simp [hc]
  ring

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveTD.Certificate

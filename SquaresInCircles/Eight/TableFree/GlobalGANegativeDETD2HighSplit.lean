module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDETD2HighSecant

/-!
# Rejoining the original nonnegative A and positive-TD split

Uncompiled transcription of Section 8.  The coefficient family is fixed
at the original total angle.  Concavity in the actual A/TD split reduces
the pure and equal-angle expressions to the already proved endpoint
norm inequalities; the secant-D correction is independent of this split.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveTD.HighSplit
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open SplitConcavityTools

def zeroScalar (θ a : ℝ) : ℝ := Explicit.fullBaseline .high a (θ-a) 0
def pureScalar (θ : ℝ) (i : Fin 3) (a : ℝ) : ℝ :=
  zeroScalar θ a+Explicit.V .high θ (θ-a) i θ
def equalScalar (θ a : ℝ) : ℝ := Explicit.fullBaseline .high a (θ-a) θ
def correction (θ : ℝ) : ℝ :=
  clippedSupport 1 (Explicit.c .high θ)-fullSupport 1 (Explicit.c .high θ)

theorem zero_identity (θ a : ℝ) :
    zeroScalar θ a=TwoPositive.splitBase (Explicit.k .high θ) (Explicit.l .high θ)
      (Explicit.c .high θ) θ a+correction θ := by
  simp only [zeroScalar,Explicit.fullBaseline,Explicit.baseline,
    show a+(θ-a)=θ by ring,Explicit.secant,Real.cos_zero,Real.tan_zero,
    div_one,sub_self,mul_zero,add_zero,sub_zero,
    TwoPositive.splitBase,PositiveTD.baseline,correction]
  dsimp [Explicit.m,PositiveTD.tilted,Explicit.eta,PositiveTD.eta,
    Explicit.sigma,PositiveTD.sigma]
  ring

theorem equal_identity {θ a : ℝ} (hθ : θ∈Icc 0 frameCap) :
    equalScalar θ a=zeroScalar θ a+secantGain qCap (Explicit.c .high θ) θ := by
  rw [equalScalar,HighSecant.full_gain_identity .high a (θ-a) hθ]
  simp only [zeroScalar,show a+(θ-a)=θ by ring]

theorem coefficient_range {θ a : ℝ}
    (hθ : θ∈Icc (1/6:ℝ) (7/10)) (ha : a∈Icc 0 θ) :
    PositiveTD.tilted (Explicit.c .high θ) (θ-a)∈
      Icc (Explicit.c .high θ/2) ((23/20)*Explicit.l .high θ) := by
  have hz : θ-a∈Icc 0 θ := ⟨by linarith [ha.2],by linarith [ha.1]⟩
  have hr := Explicit.high_ranges hθ
  have hm := Explicit.high_tilted hθ hz
  change Explicit.m .high θ (θ-a)∈Icc _ _
  exact ⟨by linarith [hm.1,hr.1,hr.2.2.2.2.2.1],by nlinarith [hm.2.1,hr.2.2.1]⟩

theorem base_concave {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    ConcaveOn ℝ (Icc 0 θ)
      (TwoPositive.splitBase (Explicit.k .high θ) (Explicit.l .high θ) (Explicit.c .high θ) θ) := by
  have hp := Explicit.high_ranges hθ
  have hl : 0<Explicit.l .high θ := by linarith [hp.2.2.1]
  have hc : 0<Explicit.c .high θ := by linarith [hp.2.2.2.2.1]
  have hr := Explicit.high_ratios hθ
  have hh := TwoPositive.Split.high_increment_concave
    (k:=Explicit.k .high θ) (s:=0) (g:=0) (e:=0)
    hl hr.1.le (show Explicit.c .high θ≤(11/10)*Explicit.l .high θ by nlinarith [hr.2])
    (Certificate.family_frame_domain .high hθ) (by norm_num [frameCap])
    (show 0<Explicit.c .high θ/2 by positivity) le_rfl le_rfl (by simp)
    (coefficient_range hθ)
  simpa only [neg_zero,TwoPositive.Split.increment_zero,add_zero] using hh

theorem zero_concave {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    ConcaveOn ℝ (Icc 0 θ) (zeroScalar θ) := by
  apply TwoPositive.Split.congr_on
    (TwoPositive.Split.add_constant (base_concave hθ) (correction θ))
  intro a _
  exact (zero_identity θ a).symm

theorem pure_concave {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) (i : Fin 3) :
    ConcaveOn ℝ (Icc 0 θ) (pureScalar θ i) := by
  have hp := Explicit.high_ranges hθ
  have hl : 0<Explicit.l .high θ := by linarith [hp.2.2.1]
  have hc : 0<Explicit.c .high θ := by linarith [hp.2.2.2.2.1]
  have hr := Explicit.high_ratios hθ
  fin_cases i
  · simpa only [pureScalar,Explicit.V,Explicit.p,Explicit.q,Matrix.cons_val_zero] using
      TwoPositive.Split.add_constant (zero_concave hθ) (V R (Explicit.k .high θ) 1 θ)
  · simpa only [pureScalar,Explicit.V,Explicit.p,Explicit.q,
      Matrix.cons_val_succ,Matrix.cons_val_zero] using
      TwoPositive.Split.add_constant (zero_concave hθ)
        (V R (Explicit.k .high θ) (Explicit.l .high θ) θ)
  · have hh := TwoPositive.Split.high_increment_concave
      (k:=Explicit.k .high θ) (s:=θ) (g:=0) (e:=Real.cos θ-1)
      hl hr.1.le (show Explicit.c .high θ≤(11/10)*Explicit.l .high θ by nlinarith [hr.2])
      (Certificate.family_frame_domain .high hθ) (Certificate.family_frame_domain .high hθ)
      (show 0<Explicit.c .high θ/2 by positivity) le_rfl
      (sub_nonpos.mpr (Real.cos_le_one θ)) le_rfl (coefficient_range hθ)
    apply TwoPositive.Split.congr_on (TwoPositive.Split.add_constant hh (correction θ))
    intro a _
    rw [pureScalar,zero_identity,TwoPositive.Split.increment_V]
    dsimp [Explicit.V,Explicit.p,Explicit.q,Explicit.m,Explicit.eta,
      PositiveTD.tilted,PositiveTD.eta]
    ring

theorem equal_concave {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    ConcaveOn ℝ (Icc 0 θ) (equalScalar θ) := by
  apply TwoPositive.Split.congr_on (TwoPositive.Split.add_constant (zero_concave hθ)
    (secantGain qCap (Explicit.c .high θ) θ))
  intro a _
  exact (equal_identity (Certificate.family_frame_domain .high hθ)).symm

theorem pure_positive {θ a : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10))
    (ha : a∈Icc 0 θ) (i : Fin 3) : 0<pureScalar θ i a := by
  have hzero : 0<pureScalar θ i 0 := by
    have hh := (Certificate.high_endpoints_positive .atT hθ i).1
    simpa only [pureScalar,zeroScalar,Certificate.highBase,Explicit.splitA,Explicit.splitT,
      sub_zero] using hh
  have htotal : 0<pureScalar θ i θ := by
    have hh := (Certificate.high_endpoints_positive .atA hθ i).1
    simpa only [pureScalar,zeroScalar,Certificate.highBase,Explicit.splitA,Explicit.splitT,
      sub_self] using hh
  exact concave_gt_of_endpoints (pure_concave hθ i) ha hzero htotal

theorem equal_positive {θ a : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10))
    (ha : a∈Icc 0 θ) : 0<equalScalar θ a := by
  have hzero : 0<equalScalar θ 0 := by
    simpa only [equalScalar,Certificate.highBase,Explicit.splitA,Explicit.splitT,sub_zero]
      using Certificate.high_Z_scalar_positive .atT hθ
  have htotal : 0<equalScalar θ θ := by
    simpa only [equalScalar,Certificate.highBase,Explicit.splitA,Explicit.splitT,sub_self]
      using Certificate.high_Z_scalar_positive .atA hθ
  exact concave_gt_of_endpoints (equal_concave hθ) ha hzero htotal

theorem original_pure_at_zero_positive {a z : ℝ}
    (hθ : a+z∈Icc (1/6:ℝ) (7/10)) (ha : 0≤a) (hz : 0≤z) (i : Fin 3) :
    0<Explicit.fullBaseline .high a z 0+Explicit.V .high (a+z) z i (a+z) := by
  have hh := pure_positive hθ (show a∈Icc 0 (a+z) from ⟨ha,by linarith⟩) i
  simpa only [pureScalar,zeroScalar,show a+z-a=z by ring] using hh

theorem original_equal_positive {a z : ℝ}
    (hθ : a+z∈Icc (1/6:ℝ) (7/10)) (ha : 0≤a) (hz : 0≤z) :
    0<Explicit.fullBaseline .high a z (a+z) := by
  have hh := equal_positive hθ (show a∈Icc 0 (a+z) from ⟨ha,by linarith⟩)
  simpa only [equalScalar,show a+z-a=z by ring] using hh

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveTD.HighSplit

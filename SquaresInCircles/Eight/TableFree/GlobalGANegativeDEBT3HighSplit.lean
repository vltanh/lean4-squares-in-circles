module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDEBT3HighSplitCalculus
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDETD2High

/-!
# Every original high-total A/BT split

Uncompiled high split join. Full-circle support is used only as a lower
stress bound; its compensation term has already been paid in the split
curvature. The A endpoint is the previously proved full-D DE/TD endpoint
with zero T angle. The T endpoint is the new complete high-BT3 theorem.
No restriction on the actual original split remains.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveBT.HighSplit
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PairNormCalculus
open SplitConcavityTools

abbrev shiftedD (q c : ℝ) : ℝ := TwoPositive.Coefficient.affineBranch q 0 shift 0 c

lemma D_slope {q c : ℝ} (hq : 1≤q) (hc : c∈Icc (0:ℝ) (6/5)) :
    R*TwoPositive.Coefficient.normD q 0 c<(1521/1000:ℝ) := by
  have hn1 : 0<pairNorm 1 c 0 := by rw [pairNorm_zero]; positivity
  have hnq : 0<pairNorm q c 0 := by rw [pairNorm_zero]; have hq0 : 0<q := by linarith; positivity
  have hs1 := NonnegativeTotals.Analytic.norm_zero_square 1 c
  have hsq := NonnegativeTotals.Analytic.norm_zero_square q c
  have hnorm : pairNorm 1 c 0≤pairNorm q c 0 := by nlinarith
  have hquot := div_le_div_of_nonneg_left
    (mul_nonneg (Real.sqrt_nonneg qCap) hc.1) hn1 hnorm
  have hh := PositiveBT3.Analytic.D_slope hc
  simp only [TwoPositive.Coefficient.normD,Real.sin_zero,mul_zero,add_zero] at hh ⊢
  have he1 : R*(c/pairNorm 1 c 0)=R*c/pairNorm 1 c 0 := by ring
  have heq : R*(c/pairNorm q c 0)=R*c/pairNorm q c 0 := by ring
  rw [he1] at hh
  rw [heq]
  exact hquot.trans_lt hh

lemma shiftedD_concave {q : ℝ} (hq : 1≤q) :
    ConcaveOn ℝ (Icc (4/5:ℝ) (6/5)) (shiftedD q) :=
  TwoPositive.Coefficient.affine_concave (by linarith) (by norm_num) (by norm_num [frameCap])

lemma shiftedD_monotone {q : ℝ} (hq : 1≤q) :
    MonotoneOn (shiftedD q) (Icc (4/5:ℝ) (6/5)) := by
  apply monoOn_of_hasDeriv_nonneg
    (fun c hc => (TwoPositive.Coefficient.affine_derivative
      (w:=shift) (b:=0) (by linarith : 0<q) (by linarith [hc.1] : 0<c)
      (by norm_num [frameCap])).continuousAt.continuousWithinAt)
    (fun c hc => TwoPositive.Coefficient.affine_derivative
      (w:=shift) (b:=0) (by linarith : 0<q) (by linarith [hc.1] : 0<c)
      (by norm_num [frameCap]))
  intro c hc
  have hh := D_slope hq (show c∈Icc (0:ℝ) (6/5) from ⟨by linarith [hc.1],hc.2.le⟩)
  dsimp [TwoPositive.Coefficient.affineD,shift]
  linarith

def fixedPart (θ s : ℝ) (i : Fin 3) : ℝ :=
  k θ+2*l θ+Explicit.sec s+3/2-fullSupport 1 (k θ)-fullSupport (k θ) (l θ)-
    fullSupport (l θ) (m θ)+Explicit.K*Real.tan s+Explicit.V .high θ i (θ-s)

theorem split_identity {θ s a : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10))
    (ha : a∈Icc 0 θ) (i : Fin 3) :
    Explicit.fullBaseline .high a (θ-a) s+Explicit.V .high θ i (θ-s)=
      fixedPart θ s i+(shiftedD (Explicit.sec s) (tilt θ a)+rest θ a) := by
  have hz := (TwoPositive.Split.split_domain (Explicit.frame_domain .high hθ) ha).2
  simp only [Explicit.fullBaseline,show a+(θ-a)=θ by ring]
  rw [edgeWidth_positive_formula hz,fullSupport_pair (Explicit.sec s) (tilt θ a)]
  dsimp [fixedPart,shiftedD,TwoPositive.Coefficient.affineBranch,rest,smooth,tilt,k,l,m,sigma]
  ring

theorem scalar_concave {θ s : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10))
    (hs : s∈Icc 0 frameCap) (i : Fin 3) :
    ConcaveOn ℝ (Icc 0 θ)
      (fun a => Explicit.fullBaseline .high a (θ-a) s+Explicit.V .high θ i (θ-s)) := by
  have hq := (NegativeELargeA.secant_range hs).1
  have hc := (compose (shiftedD_concave hq) (shiftedD_monotone hq)
    (tilt_concave hθ) (tilt_range hθ)).add (rest_concave hθ)
  apply TwoPositive.Split.congr_on
    (OrdinaryMixedShortReserve.constant_add hc (fixedPart θ s i))
  intro a ha
  exact (split_identity hθ ha i).symm

lemma A_identity (θ s : ℝ) (i : Fin 3) :
    Explicit.fullBaseline .high θ 0 s+Explicit.V .high θ i (θ-s)=
      NegativeDEPositiveTD.Explicit.fullBaseline .high θ 0 s+
        NegativeDEPositiveTD.Explicit.V .high θ 0 i (θ-s) := by
  simp only [Explicit.fullBaseline,Explicit.V,Explicit.p,Explicit.q,Explicit.k,Explicit.l,
    Explicit.m,Explicit.c,NegativeDEPositiveTD.Explicit.fullBaseline,
    NegativeDEPositiveTD.Explicit.baseline,NegativeDEPositiveTD.Explicit.V,
    NegativeDEPositiveTD.Explicit.p,NegativeDEPositiveTD.Explicit.q,
    NegativeDEPositiveTD.Explicit.m,NegativeDEPositiveTD.Explicit.secant,
    Explicit.sec,Explicit.K,Real.cos_zero,Real.sin_zero,mul_zero,mul_one,
    add_zero,sub_zero,edgeWidth_zero]
  ring

theorem negative_positive {a z s : ℝ} (hθ : a+z∈Icc (1/6:ℝ) (7/10))
    (ha : 0≤a) (hz : 0≤z) (hs : s∈Icc 0 (a+z)) (i : Fin 3) :
    0<Explicit.fullBaseline .high a z s+Explicit.V .high (a+z) i (a+z-s) := by
  have hf := Explicit.frame_domain .high hθ
  have hsf : s∈Icc 0 frameCap := ⟨hs.1,hs.2.trans hf.2⟩
  have hT := HighT.negative_positive hθ hs i
  have hA : 0<Explicit.fullBaseline .high (a+z) 0 s+
      Explicit.V .high (a+z) i (a+z-s) := by
    rw [A_identity]
    exact NegativeDEPositiveTD.High.negative_positive
      (by simpa only [add_zero] using hθ) (by linarith) (by norm_num)
      (by simpa only [add_zero] using hs) i
  have hh := concave_gt_of_endpoints (scalar_concave hθ hsf i)
    (show a∈Icc 0 (a+z) from ⟨ha,by linarith⟩)
    (by simpa only [sub_zero] using hT) (by simpa only [sub_self] using hA)
  simpa only [show a+z-a=z by ring] using hh

theorem equal_positive {a z : ℝ} (hθ : a+z∈Icc (1/6:ℝ) (7/10))
    (ha : 0≤a) (hz : 0≤z) : 0<Explicit.baseline .high a z (a+z) := by
  have hh := negative_positive hθ ha hz
    (show a+z∈Icc 0 (a+z) from ⟨by linarith,le_rfl⟩) (0:Fin 3)
  simp only [sub_self,Explicit.V,V_zero,add_zero] at hh
  exact hh.trans_le (Explicit.full_lower .high a z (a+z))

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveBT.HighSplit

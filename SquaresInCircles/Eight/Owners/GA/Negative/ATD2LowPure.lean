module

public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2AffectedPositive
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2Concentration
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2LowEqual
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2LowNegativeCurvature

/-!
# Eight squares: every low pure endpoint with the original coefficients

Both signs of the remaining total are included. Every
scalar endpoint is discharged by the literal low-family certificate.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.LowPure
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open SecantCoordinate LowNegativeCurvature

private lemma r71_low_dom {z : ℝ} (hz : z∈Icc 0 (1/5:ℝ)) :
    z∈Icc (Certificate.left .low:ℝ) (Certificate.right .low:ℝ) := by
  norm_num [Certificate.left,Certificate.right,Certificate.split]
  exact hz

def scalar (atG : Bool) (z x : ℝ) : ℝ :=
  pure (baseline atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) 0 z)
    (Explicit.l .low z)
    (SecantBaseline.basicRatio atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) z)
    (Explicit.k .low z) 1 z x

theorem ratio_domain (atG : Bool) {z : ℝ} (hz : z∈Icc 0 (1/5:ℝ)) :
    SecantBaseline.basicRatio atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) z
      ∈Icc 0 (71/50:ℝ) := by
  obtain ⟨hk,hl,hc,hm⟩ := Explicit.family_positive .low (r71_low_dom hz)
  cases atG
  · change Explicit.m .low z/Explicit.l .low z∈Icc 0 (71/50:ℝ)
    exact ⟨div_nonneg hm.le hl.le,(div_le_iff₀ hl).2 (Explicit.low_tilted hz).2.le⟩
  · change Explicit.k .low z/Explicit.l .low z∈Icc 0 (71/50:ℝ)
    exact ⟨div_nonneg hk.le hl.le,(div_le_iff₀ hl).2
      (by linarith [(Explicit.low_ratio hz).2])⟩

theorem scalar_concave (atG : Bool) {z : ℝ} (hz : z∈Icc 0 (1/5:ℝ)) :
    ConcaveOn ℝ (Icc 0 (Real.tan z)) (scalar atG z) := by
  obtain ⟨hklo,hkhi,hllo,hlhi,hclo,hchi⟩ := Explicit.low_ranges hz
  have hzframe : z∈Icc 0 frameCap := ⟨hz.1,by dsimp [frameCap]; linarith [hz.2]⟩
  apply pure_concave (by linarith : 0<Explicit.k .low z) (by norm_num : (0:ℝ)<1)
    hzframe le_rfl hzframe.2
  intro x hx
  have hs := arctan_interval hzframe hx
  have hxhi : x≤203/1000 := by
    have ht := tan_monotone hzframe
      (show (1/5:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hz.2
    linarith [hx.2,tan_low_cut]
  exact (pure_curvature (by linarith : (1:ℝ)≤Explicit.l .low z)
    (ratio_domain atG hz) ⟨hklo.le,hkhi⟩ ⟨hx.1,hxhi⟩
    ⟨by linarith [hs.2],by linarith [hs.1,hz.2]⟩).le.trans (by norm_num)

theorem scalar_zero (atG : Bool) {z : ℝ} (hz : z∈Icc 0 (1/5:ℝ)) :
    0<scalar atG z 0 := by
  have he : scalar atG z 0=PositiveTD.baseline (Explicit.k .low z) (Explicit.l .low z)
      (Explicit.c .low z) z+V R (Explicit.k .low z) 1 z := by
    simp only [scalar,SecantCoordinate.pure,sub_self,mul_zero,Real.arctan_zero,sub_zero,add_zero,
      baseline_zero]
  rw [he]
  exact (Certificate.low_endpoints hz).1

theorem scalar_equal (atG : Bool) {z : ℝ} (hz : z∈Icc 0 (1/5:ℝ)) :
    0<scalar atG z (Real.tan z) := by
  have hzframe : z∈Icc 0 frameCap := ⟨hz.1,by dsimp [frameCap]; linarith [hz.2]⟩
  have hh := pure_at_original (p:=Explicit.k .low z) (q:=1) (k:=Explicit.k .low z)
    (c:=Explicit.c .low z) (z:=z) atG (Explicit.family_positive .low (r71_low_dom hz)).2.1 hzframe
  simpa only [scalar,hh,sub_self,V_zero,add_zero] using LowEqual.original atG hz

theorem H_positive (atG : Bool) {s z : ℝ} (hz : z∈Icc 0 (1/5:ℝ))
    (hs : s∈Icc 0 z) :
    0<baseline atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) s z+
      V R (Explicit.k .low z) 1 (z-s) := by
  have hzframe : z∈Icc 0 frameCap := ⟨hz.1,by dsimp [frameCap]; linarith [hz.2]⟩
  have hsframe : s∈Icc 0 frameCap := ⟨hs.1,hs.2.trans hzframe.2⟩
  have hx : Real.tan s∈Icc 0 (Real.tan z) :=
    ⟨tan_nonnegative hsframe,tan_monotone hsframe hzframe hs.2⟩
  have hm := (scalar_concave atG hz).min_le_of_mem_Icc
    ⟨le_rfl,tan_nonnegative hzframe⟩ ⟨tan_nonnegative hzframe,le_rfl⟩ hx
  have hpos : 0<scalar atG z (Real.tan s) :=
    (lt_min (scalar_zero atG hz) (scalar_equal atG hz)).trans_le hm
  rwa [scalar,pure_at_original atG (Explicit.family_positive .low (r71_low_dom hz)).2.1 hsframe]
    at hpos

theorem negative_positive (atG : Bool) {s z : ℝ} (hz : z∈Icc 0 (1/5:ℝ))
    (hs : s∈Icc 0 (Explicit.angleCut atG)) (hsz : s≤z) (i : Fin 4) :
    0<baseline atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) s z+
      V R (Source.pWeights atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) s i)
        (Source.qWeights atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) s i) (z-s) := by
  have hh := H_positive atG hz ⟨hs.1,hsz⟩
  have hc := LowNegativeComparison.original (t:=z-s) atG hz hs
    ⟨by linarith,by linarith [hz.2,hs.1]⟩ i
  linarith

theorem original (atG : Bool) {s z : ℝ} (hz : z∈Icc 0 (1/5:ℝ))
    (hs : s∈Icc 0 (Explicit.angleCut atG)) (i j : Fin 4) :
    0<baseline atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) s z+
      Concentration.pure R (GlobalGA.Secondary.diagonal-1/2)
        (Source.pWeights atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) s)
        (Source.qWeights atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) s) 3 i j s z := by
  by_cases hsz : s≤z
  · simpa only [Concentration.pure,hsz,↓reduceIte] using negative_positive atG hz hs hsz j
  · have hp := AffectedPositive.all_positive_reduces_to_equal .low atG (r71_low_dom hz) hs
      (le_of_not_ge hsz) i
    have he := LowEqual.original atG hz
    simp only [Concentration.pure,hsz,↓reduceIte]
    linarith

end SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.LowPure

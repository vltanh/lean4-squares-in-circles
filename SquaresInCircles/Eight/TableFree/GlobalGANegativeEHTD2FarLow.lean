module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHTD2FarLowSeparated

/-!
# Complete far-low four-block scalar exclusion

Uncompiled final concentration step of the far-low companion. Every
pure alternative is proved for both surplus signs. Every saturated
ordinary same-block alternative retains its two masses until the charged
comparison is applied. The exceptional D block is treated as separated,
even when both signs lie on that same original DE2 singleton. No owner,
signed-mass budget, or continuous concentration alternative is omitted.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHPositiveTD.FarLow
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

lemma ordinary_same_lower {θ z s : ℝ} (hθ : θ∈Icc (0:ℝ) (1/4))
    (hz : z∈Icc 0 θ) (hs : s∈Icc (1/10:ℝ) (1/4))
    (i : Fin 4) (hi : i≠3) :
    Blocks.pure .far .low θ z s i i≤Blocks.saturated .far .low θ z s i i := by
  have hp := FarLowSlopes.pair_data hθ hz i
  have hP : 0≤frameCap-θ := by norm_num [frameCap]; linarith [hθ.2]
  have hN : 0≤frameCap-s := by norm_num [frameCap]; linarith [hs.2]
  have hNcap : frameCap-s≤3/5 := by norm_num [frameCap]; linarith [hs.1]
  have hPcap : frameCap-θ≤frameCap := by linarith [hθ.1]
  by_cases horder : s≤θ
  · have hPN : frameCap-θ≤frameCap-s := by linarith
    have hh := NegativeEH.SameBlock.negative_charged hp.1 hp.2.2 hP hPN hNcap
    simpa only [Blocks.pure,Blocks.saturated,ChargedHybridConcentration.pure,
      ChargedHybridConcentration.saturated,if_pos horder,if_pos rfl,
      ChargedHybridConcentration.block,PositiveTD.Hybrid.block,if_neg hi,
      Explicit.errorCharge,show frameCap-s-(frameCap-θ)=θ-s by ring] using hh
  · have hNP : frameCap-s≤frameCap-θ := by linarith
    have hh := NegativeEH.SameBlock.positive_charged hp.1 hp.2.2 hN hNP hPcap hNcap
    simpa only [Blocks.pure,Blocks.saturated,ChargedHybridConcentration.pure,
      ChargedHybridConcentration.saturated,if_neg horder,if_pos rfl,
      ChargedHybridConcentration.positive,ChargedHybridConcentration.block,
      PositiveTD.Hybrid.positive,PositiveTD.Hybrid.block,if_neg hi,
      Explicit.errorCharge,show frameCap-θ-(frameCap-s)=s-θ by ring] using hh

lemma saturated_positive {a z s : ℝ} (hθ : a+z∈Icc (0:ℝ) (1/4))
    (ha : 0≤a) (hz : 0≤z) (hs : s∈Icc (1/10:ℝ) (1/4)) (i j : Fin 4) :
    0<Explicit.stressBase .far .low a z s+Blocks.saturated .far .low (a+z) z s i j := by
  by_cases he : i=j
  · subst j
    by_cases hi : i=3
    · subst i
      have hh := FarLowSeparated.original_positive hθ ha hz hs 3 3
      have heq : Blocks.saturated .far .low (a+z) z s 3 3=
          Blocks.block .far .low (a+z) z (frameCap-(a+z)) (frameCap-s) 3 := by
        simp only [Blocks.saturated,ChargedHybridConcentration.saturated,if_pos rfl,Blocks.block]
      rw [heq,Blocks.block_D]
      linarith
    · have hl := ordinary_same_lower hθ ⟨hz,by linarith⟩ hs i hi
      have hh := FarLowPure.pure_positive hθ ha hz hs i i
      linarith
  · have hh := FarLowSeparated.original_positive hθ ha hz hs i j
    simpa only [Blocks.saturated,ChargedHybridConcentration.saturated,if_neg he,
      Blocks.positive,Blocks.negative,add_assoc] using hh

theorem scalar_positive {a z s : ℝ} (P N : Fin 4→ℝ)
    (hθ : a+z∈Icc (0:ℝ) (1/4)) (ha : 0≤a) (hz : 0≤z)
    (hs : s∈Icc (1/10:ℝ) (1/4)) (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hPb : (∑i,P i)≤frameCap-(a+z)) (hNb : (∑i,N i)≤frameCap-s)
    (hbalance : (∑i,N i)-(∑i,P i)=a+z-s) :
    0<Explicit.stressBase .far .low a z s+
      ∑i,Blocks.block .far .low (a+z) z (P i) (N i) i := by
  obtain ⟨i,j,hij⟩ := Blocks.concentrate .far .low P N hθ
    ⟨hz,by linarith⟩ hs hP hN hPb hNb hbalance
  have hpure := FarLowPure.pure_positive hθ ha hz hs i j
  have hsat := saturated_positive hθ ha hz hs i j
  have hmin : -Explicit.stressBase .far .low a z s<
      min (Blocks.pure .far .low (a+z) z s i j) (Blocks.saturated .far .low (a+z) z s i j) :=
    lt_min (by linarith) (by linarith)
  linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHPositiveTD.FarLow

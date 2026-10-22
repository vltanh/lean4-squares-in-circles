module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDEHighShape
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDETD2HighSplit

/-!
# The complete high-total negative-DE / positive-TD2 scalar exclusion

Uncompiled completion of Sections 8--10 of the angle companion. The
actual high coefficient family satisfies the shared third-derivative
domain. Each pure negative function therefore has its minimum at the
two intrinsic E endpoints, whose actual A/TD split bounds were proved
separately. The positive surplus and the common signed mass are then
rejoined, without changing any original angle or coefficient.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveTD.High
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open NegativeAPositiveTD.SecantCoordinate

/-- Concrete coefficient hypotheses, including the original late correlation. -/
theorem shape_domain {θ z : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10))
    (hz : z∈Icc 0 θ) (i : Fin 3) :
    NegativeDEHighShape.Domain false (Explicit.c .high θ)
      (Explicit.p .high θ z i) (Explicit.q .high θ z i) θ := by
  have hc := Explicit.high_ranges hθ
  have hp := Explicit.high_pairs hθ hz i
  refine ⟨Certificate.family_frame_domain .high hθ,?_,hp.1,hp.2.1,
    hp.2.2.1.le,?_,?_,?_⟩
  · constructor
    · linarith [hc.2.2.2.2.1]
    · dsimp [NegativeDEHighShape.Early.C]
      linarith [hc.2.2.2.2.2.1]
  · linarith [hp.2.2.2.1]
  · intro _
    dsimp [NegativeDEHighShape.Late.rate,frameCap]
    linarith [hc.2.2.2.2.2.2.2]
  · intro hlate
    exact Explicit.high_late_q_le_one hθ hz hlate i

theorem negative_endpoint_minimum {a z s : ℝ}
    (hθ : a+z∈Icc (1/6:ℝ) (7/10)) (ha : 0≤a) (hz : 0≤z)
    (hs : s∈Icc 0 (a+z)) (i : Fin 3) :
    min (Explicit.fullBaseline .high a z 0+Explicit.V .high (a+z) z i (a+z))
        (Explicit.fullBaseline .high a z (a+z))≤
      Explicit.fullBaseline .high a z s+Explicit.V .high (a+z) z i (a+z-s) := by
  have hf := Certificate.family_frame_domain .high hθ
  have hzf : z∈Icc 0 (a+z) := ⟨hz,by linarith⟩
  have hsf : s∈Icc 0 frameCap := ⟨hs.1,hs.2.trans hf.2⟩
  have hx : Real.tan s∈Icc 0 (Real.tan (a+z)) :=
    ⟨tan_nonnegative hsf,tan_monotone hsf hf hs.2⟩
  have hh := NegativeDEHighShape.pure_endpoint_minimum
    (B:=Explicit.fullBaseline .high a z 0) false (shape_domain hθ hzf i) hx
    (HighDerivative.high_pure_first_right_negative hθ hzf i).le
  have hleft : pure (Explicit.fullBaseline .high a z 0) 1
      (Explicit.c .high (a+z)) (Explicit.p .high (a+z) z i)
      (Explicit.q .high (a+z) z i) (a+z) 0=
        Explicit.fullBaseline .high a z 0+Explicit.V .high (a+z) z i (a+z) := by
    simp [pure,Explicit.V]
  have hright := HighSecant.pure_at_original (a:=a) (z:=z) hf i
  simp only [sub_self,Explicit.V,V_zero,add_zero] at hright
  rw [hleft,hright,HighSecant.pure_at_original hsf i] at hh
  exact hh

theorem negative_positive {a z s : ℝ}
    (hθ : a+z∈Icc (1/6:ℝ) (7/10)) (ha : 0≤a) (hz : 0≤z)
    (hs : s∈Icc 0 (a+z)) (i : Fin 3) :
    0<Explicit.fullBaseline .high a z s+Explicit.V .high (a+z) z i (a+z-s) := by
  have h0 := HighSplit.original_pure_at_zero_positive hθ ha hz i
  have h1 := HighSplit.original_equal_positive hθ ha hz
  exact (lt_min h0 h1).trans_le (negative_endpoint_minimum hθ ha hz hs i)

theorem pure_positive {a z s : ℝ}
    (hθ : a+z∈Icc (1/6:ℝ) (7/10)) (ha : 0≤a) (hz : 0≤z)
    (hs : s∈Icc 0 frameCap) (i : Fin 3) :
    0<Explicit.fullBaseline .high a z s+HighConcentration.pure (a+z) z s i := by
  by_cases horder : s≤a+z
  · simpa only [HighConcentration.pure,if_pos horder] using
      negative_positive hθ ha hz ⟨hs.1,horder⟩ i
  · have hθs : a+z≤s := (lt_of_not_ge horder).le
    have hcompare := HighSecant.high_equal_le_positive_surplus hθ
      (show z∈Icc 0 (a+z) from ⟨hz,by linarith⟩) ⟨hθs,hs.2⟩ i
    simpa only [HighConcentration.pure,if_neg horder] using
      (HighSplit.original_equal_positive hθ ha hz).trans_le hcompare

/-- Every original high-total allocation has strictly positive scalar
stress; no endpoint-minimum or derivative premise remains. -/
theorem scalar_positive {a z s : ℝ} (P N : Fin 3→ℝ)
    (hθ : a+z∈Icc (1/6:ℝ) (7/10)) (ha : 0≤a) (hz : 0≤z)
    (hs : s∈Icc 0 frameCap) (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hPb : (∑i,P i)≤frameCap-(a+z)) (hNb : (∑i,N i)≤frameCap-s)
    (hbalance : (∑i,N i)-(∑i,P i)=a+z-s) :
    0<Explicit.fullBaseline .high a z s+
      ∑i,mixedBlock R (Explicit.p .high (a+z) z i)
        (Explicit.q .high (a+z) z i) (P i) (N i) := by
  obtain ⟨i,hi⟩ := HighConcentration.sum_to_pure P N hθ
    (show z∈Icc 0 (a+z) from ⟨hz,by linarith⟩) hs hP hN hPb hNb hbalance
  have hp := pure_positive hθ ha hz hs i
  linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveTD.High

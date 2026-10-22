module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDEBT3LowEndpoints
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDEBT3LowPositive
public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveBT3LowSplit

/-!
# The complete low-total scalar with its original three angles

Uncompiled Section 4. The whole negative-DE interval below the total
is concave and retains both original endpoints. At zero DE magnitude
the stress is the already proved ordinary positive-BT3 scalar. At equal
angles the original split is concave and both new sorted-D endpoints
have been proved. Positive surplus is reduced to that same equal-angle
value. The final theorem consumes the complete actual four-block mass
allocation, not a selected scalar alternative as a hypothesis.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveBT.Low
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

abbrev gain := NegativeESecant.gain (diagonal-1/2)

lemma zero_scalar_identity {a z : ℝ} (hθ : a+z∈Icc (0:ℝ) (1/6))
    (ha : 0≤a) (hz : 0≤z) :
    Explicit.baseline .low a z 0+V R (Explicit.k .low (a+z)) 1 (a+z)=
      PositiveBT3.Analytic.lowScalar (a+z) a := by
  have hc := (Explicit.low_c hθ ⟨hz,by linarith⟩).1
  have hm := (Explicit.low_bounds hθ).2.1
  have hc1 : 1≤Explicit.c .low (a+z) z := by linarith
  have hs (k : ℝ) : fullSupport 1 k=fullSupport k 1 := by simp [fullSupport,add_comm]
  simp only [Explicit.baseline,Explicit.sec,NegativeELargeA.secant,
    Real.cos_zero,Real.tan_zero,div_one,sub_self,mul_zero,sub_zero,add_zero]
  rw [PositiveBT3.sortedSupport_diagonal hc1,hs]
  simp only [PositiveBT3.Analytic.lowScalar,PositiveBT3.Analytic.lowBaseline,
    show a+z-a=z by ring,Explicit.k,Explicit.l,Explicit.m,one_mul]
  dsimp [Explicit.c,Explicit.eta,Explicit.sigma,PositiveBT3.tilted,
    PositiveTD.sigma,PositiveTD.eta,fullSupport,diagonalSupport]
  norm_num only [one_pow]
  ring

lemma diagonal_correction {a z s : ℝ} (hθ : a+z∈Icc (0:ℝ) (1/6))
    (ha : 0≤a) (hz : 0≤z) (hs : s∈Icc 0 (a+z)) :
    Explicit.baseline .low a z s=Explicit.baseline .low a z 0+gain s := by
  have hc := (Explicit.source_coefficients .low hθ ⟨hz,by linarith⟩).2.2.2.2.1
  have hsf : s∈Icc 0 frameCap := ⟨hs.1,hs.2.trans (Explicit.frame_domain .low hθ).2⟩
  rw [Explicit.baseline_correction,
    SecantD.PositiveEndpoint.correction_diagonal hc hsf (LowNegative.secant_le_c hθ ⟨hz,by linarith⟩ hs)]

lemma gain_concave : ConcaveOn ℝ (Icc (0:ℝ) (1/6)) gain := by
  apply concave_of_deriv2
    (fun s hs => NegativeESecant.gain_hasDerivAt (diagonal-1/2)
      (show s∈Icc 0 frameCap from ⟨hs.1,by norm_num [frameCap]; linarith [hs.2]⟩))
    (fun s hs => NegativeESecant.gainD_hasDerivAt (diagonal-1/2)
      (show s∈Icc 0 frameCap from ⟨hs.1,by norm_num [frameCap]; linarith [hs.2]⟩))
  intro s hs
  have hsf : s∈Icc 0 frameCap := ⟨hs.1,by norm_num [frameCap]; linarith [hs.2]⟩
  have hsin : Real.sin s≤1/6 := (Real.sin_le hs.1).trans hs.2
  have hcoef : 0≤diagonal-1/2 := by linarith [diagonal_bounds.1]
  have hsquare := mul_nonneg hcoef (sq_nonneg (Real.sin s))
  have hnum : 2*NegativeESecant.K*Real.sin s-(diagonal-1/2)*(1+Real.sin s^2)≤0 := by
    dsimp [NegativeESecant.K]
    nlinarith [diagonal_bounds.1]
  exact div_nonpos_of_nonpos_of_nonneg hnum
    (pow_nonneg (NegativeESecant.cos_pos hsf).le 3)

lemma equal_split_concave {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    ConcaveOn ℝ (Icc 0 θ) (fun a => Explicit.baseline .low a (θ-a) θ) := by
  have hc := TwoPositive.Split.add_constant (PositiveBT3.Analytic.lowScalar_concave hθ)
    (gain θ-V R (Explicit.k .low θ) 1 θ)
  apply TwoPositive.Split.congr_on hc
  intro a ha
  have ht : a+(θ-a)∈Icc (0:ℝ) (1/6) := by simpa only [add_sub_cancel] using hθ
  have hz : 0≤θ-a := sub_nonneg.mpr ha.2
  have hzero := zero_scalar_identity ht ha.1 hz
  have hcor := diagonal_correction ht ha.1 hz
    (show θ∈Icc 0 (a+(θ-a)) by simpa only [add_sub_cancel] using ⟨hθ.1,le_rfl⟩)
  simp only [add_sub_cancel] at hzero hcor
  linarith

theorem equal_positive {a z : ℝ} (hθ : a+z∈Icc (0:ℝ) (1/6))
    (ha : 0≤a) (hz : 0≤z) : 0<Explicit.baseline .low a z (a+z) := by
  have hc := equal_split_concave hθ
  have h0 := LowEndpoints.equal_positive .atT hθ
  have h1 := LowEndpoints.equal_positive .atA hθ
  have hh := concave_gt_of_endpoints hc
    (show a∈Icc 0 (a+z) from ⟨ha,by linarith⟩)
    (by simpa only [Explicit.splitA,Explicit.splitT,sub_zero] using h0)
    (by simpa only [Explicit.splitA,Explicit.splitT,sub_self] using h1)
  simpa only [show a+z-a=z by ring] using hh

theorem negative_positive {a z s : ℝ} (hθ : a+z∈Icc (0:ℝ) (1/6))
    (ha : 0≤a) (hz : 0≤z) (hs : s∈Icc 0 (a+z)) :
    0<Explicit.baseline .low a z s+V R (Explicit.k .low (a+z)) 1 (a+z-s) := by
  have hp := Explicit.family_pairs .low hθ 0
  have hg := gain_concave.subset (Icc_subset_Icc le_rfl hθ.2) (convex_Icc 0 (a+z))
  have hv := concave_affine_argument
    (V_concave (Real.sqrt_nonneg qCap) radius_sq.le hp.1 hp.2.1 hp.2.2)
    (a:=-1) (b:=a+z) (l:=0) (u:=a+z)
    (fun s hs => ⟨by linarith [hs.2],by norm_num [frameCap]; linarith [hs.1,hθ.2]⟩)
  have hc := TwoPositive.Split.add_constant (hg.add hv) (Explicit.baseline .low a z 0)
  have h0 : 0<gain 0+V R (Explicit.k .low (a+z)) 1 (a+z-0)+Explicit.baseline .low a z 0 := by
    have hh := PositiveBT3.Analytic.low_scalar_positive hθ
      (show a∈Icc 0 (a+z) from ⟨ha,by linarith⟩)
    rw [←zero_scalar_identity hθ ha hz] at hh
    simpa only [gain,NegativeESecant.gain_zero,zero_add,sub_zero,add_comm] using hh
  have h1 : 0<gain (a+z)+V R (Explicit.k .low (a+z)) 1 (a+z-(a+z))+
      Explicit.baseline .low a z 0 := by
    have hh := equal_positive hθ ha hz
    rw [diagonal_correction hθ ha hz ⟨hθ.1,le_rfl⟩] at hh
    simpa only [sub_self,V_zero,add_zero,add_comm] using hh
  have hh := concave_gt_of_endpoints hc hs
    (by simpa only [neg_one_mul,neg_add_eq_sub] using h0)
    (by simpa only [neg_one_mul,neg_add_eq_sub] using h1)
  rw [diagonal_correction hθ ha hz hs]
  simpa only [neg_one_mul,neg_add_eq_sub,add_assoc,add_comm,add_left_comm] using hh

/-- Complete closed low-total scalar domain, including both surplus signs. -/
theorem scalar_positive {a z s : ℝ} (P N : Fin 4→ℝ)
    (hθ : a+z∈Icc (0:ℝ) (1/6)) (ha : 0≤a) (hz : 0≤z)
    (hs : s∈Icc 0 frameCap) (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hPb : (∑i,P i)≤frameCap-(a+z)) (hNb : (∑i,N i)≤frameCap-s)
    (hbalance : (∑i,N i)-(∑i,P i)=a+z-s) :
    0<Explicit.baseline .low a z s+
      ∑i,Blocks.block .low (a+z) z s (P i) (N i) i := by
  have hzd : z∈Icc 0 (a+z) := ⟨hz,by linarith⟩
  by_cases hst : s≤a+z
  · have hb := LowNegative.sum_to_H P N hθ hzd ⟨hs.1,hst⟩ hP hN hPb hNb hbalance
    have hp := negative_positive hθ ha hz ⟨hs.1,hst⟩
    linarith
  · have hsf : s∈Icc (a+z) frameCap := ⟨(lt_of_not_ge hst).le,hs.2⟩
    obtain ⟨i,j,hij⟩ := LowPositive.sum_to_pure P N hθ hzd hsf hP hN hPb hNb hbalance
    have hp := equal_positive hθ ha hz
    have hc := PositivePure.pure_intrinsic_lower .low hθ ha hz hsf i j
    linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveBT.Low

module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDEBT3Polynomial
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDEHighShape

/-!
# The actual high-BT3 T endpoint satisfies the complete shape domain

Uncompiled Section 7.1 and the coefficient join of Section 7.3. The
polynomial majorant is evaluated in x=theta-1/6, and its derivative
controls the entire high interval. The late affine correlation follows
from concavity of the exact polynomial difference and its two original
endpoints. This supplies the hypotheses of the already drafted shared
third-derivative theorem with its BT3 flag, rather than redoing that
argument or assuming a sampled coefficient bound.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveBT.HighShape
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open WholeIntervalPolynomial

lemma polynomial_hasDerivAt (p : ℚ[X]) (x : ℝ) :
    HasDerivAt (fun x : ℝ => aeval x p) (aeval x p.derivative) x := by
  convert (p.map (algebraMap ℚ ℝ)).hasDerivAt x using 1 <;>
    simp [Polynomial.aeval_def,Polynomial.derivative_map]

lemma native_domain {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    θ-(Certificate.L:ℝ)∈Icc (0:ℝ) (8/15) := by
  norm_num [Certificate.L]
  exact ⟨by linarith [hθ.1],by linarith [hθ.2]⟩

lemma native_total (θ : ℝ) : θ-(Certificate.L:ℝ)+(Certificate.L:ℝ)=θ := by ring

lemma coefficient_majorant {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    Explicit.c .high θ θ≤aeval (θ-(Certificate.L:ℝ)) Certificate.highC := by
  have ht := PositiveTD.Certificate.taylor_bounds (Explicit.frame_domain .high hθ)
  have he := Explicit.high_eta hθ
  have hm := (Explicit.high_bounds hθ).m_lower
  have hs := mul_le_mul_of_nonneg_left ht.2.2.1
    (show 0≤Explicit.eta .high θ by linarith [he.1])
  have hh := mul_le_mul_of_nonneg_left (add_le_add ht.2.2.2.2.2 hs)
    (show 0≤Explicit.m .high θ by linarith)
  simpa only [Certificate.highC,map_mul,map_add,aeval_comp,
    Certificate.theta_eval,Certificate.highM_eval,Certificate.highEta_eval,native_total,
    Explicit.c] using hh

lemma majorant_derivative_negative {x : ℝ} (hx : x∈Icc (0:ℝ) (8/15)) :
    aeval x Certificate.highC.derivative<0 := by
  have hc := Certificate.high_auxiliary_certificate.2.2.1
  have hh := positive_on_interval
    (by norm_num [Certificate.span,Certificate.h,Certificate.L] : (0:ℚ)<Certificate.span)
    hc.1 hc.2 hx
  simp only [map_neg] at hh
  norm_num at hh
  linarith

lemma majorant_antitone :
    AntitoneOn (fun x : ℝ => aeval x Certificate.highC) (Icc (0:ℝ) (8/15)) := by
  apply antiOn_of_hasDeriv_nonpos
    (fun x _ => (polynomial_hasDerivAt Certificate.highC x).continuousAt.continuousWithinAt)
    (fun x _ => polynomial_hasDerivAt Certificate.highC x)
  intro x hx
  exact (majorant_derivative_negative (Ioo_subset_Icc_self hx)).le

theorem coefficient_upper {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    Explicit.c .high θ θ<(1057/1000:ℝ) := by
  have hx := native_domain hθ
  have hm := majorant_antitone (by norm_num : (0:ℝ)∈Icc 0 (8/15)) hx hx.1
  have h0 : aeval (0:ℝ) Certificate.highC<(1057/1000:ℝ) := by
    rw [NegativeDEPositiveTD.Certificate.eval_rat]
    exact_mod_cast Certificate.high_auxiliary_certificate.2.2.2
  exact (coefficient_majorant hθ).trans_lt (hm.trans_lt h0)

lemma late_difference_concave :
    ConcaveOn ℝ (Icc (Certificate.lateLeft:ℝ) (Certificate.span:ℝ))
      (fun x : ℝ => aeval x Certificate.lateDifference) := by
  apply concave_of_deriv2
    (fun x _ => polynomial_hasDerivAt Certificate.lateDifference x)
    (fun x _ => polynomial_hasDerivAt Certificate.lateDifference.derivative x)
  intro x hx
  have hc := Certificate.late_coefficient_certificate.1
  have hh := positive_on_interval
    (by norm_num [Certificate.lateLeft,Certificate.span,Certificate.h,Certificate.L] :
      Certificate.lateLeft<Certificate.span) hc.1 hc.2 hx
  simp only [map_neg] at hh
  norm_num at hh
  linarith

theorem late_coefficient_upper {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10))
    (hlate : (11/20:ℝ)≤θ) : Explicit.c .high θ θ≤2153/2000-(61/200)*θ := by
  have hx : θ-(Certificate.L:ℝ)∈Icc (Certificate.lateLeft:ℝ) (Certificate.span:ℝ) := by
    norm_num [Certificate.lateLeft,Certificate.span,Certificate.h,Certificate.L]
    exact ⟨by linarith,by linarith [hθ.2]⟩
  have h0 : 0<aeval (Certificate.lateLeft:ℝ) Certificate.lateDifference := by
    rw [NegativeDEPositiveTD.Certificate.eval_rat]
    have hh : (9/50000:ℝ)<(Certificate.lateDifference.eval Certificate.lateLeft:ℝ) := by
      exact_mod_cast Certificate.late_coefficient_certificate.2.1
    linarith
  have h1 : 0<aeval (Certificate.span:ℝ) Certificate.lateDifference := by
    rw [NegativeDEPositiveTD.Certificate.eval_rat]
    have hh : (3/62500:ℝ)<(Certificate.lateDifference.eval Certificate.span:ℝ) := by
      exact_mod_cast Certificate.late_coefficient_certificate.2.2
    linarith
  have hd := concave_gt_of_endpoints late_difference_concave hx h0 h1
  have hc := coefficient_majorant hθ
  simp only [Certificate.lateDifference,Certificate.lateLine,map_sub,map_mul,
    aeval_C,Certificate.theta_eval,native_total] at hd
  norm_num at hd
  linarith

lemma late_larger {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10))
    (hlate : (11/20:ℝ)≤θ) (i : Fin 3) : Explicit.q .high θ i≤1 := by
  have hh := NegativeDEPositiveTD.Explicit.high_late_q_le_one hθ
    (show (0:ℝ)∈Icc 0 θ from ⟨le_rfl,by linarith [hθ.1]⟩) hlate i
  simpa [Explicit.q,Explicit.l,Explicit.m,NegativeDEPositiveTD.Explicit.q,
    NegativeDEPositiveTD.Explicit.m] using hh

/-- The shared shape theorem uses the BT3 correlation, not the TD2 one. -/
theorem shape_domain {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) (i : Fin 3) :
    NegativeDEHighShape.Domain true (Explicit.c .high θ θ)
      (Explicit.p .high θ i) (Explicit.q .high θ i) θ := by
  have hp := Explicit.high_pairs hθ i
  have hq := Explicit.high_q_bounds hθ i
  have hm := (Explicit.high_bounds hθ).m_lower
  have hc := (Explicit.high_c hθ ⟨by linarith [hθ.1],le_rfl⟩).1
  refine ⟨Explicit.frame_domain .high hθ,?_,hp.1,hp.2.1,hp.2.2.le,hq.1,?_,?_⟩
  · exact ⟨by linarith,by simpa [NegativeDEHighShape.Early.C] using (coefficient_upper hθ).le⟩
  · intro hlate
    have hh := late_coefficient_upper hθ hlate
    dsimp [NegativeDEHighShape.Late.rate,frameCap]
    linarith
  · exact fun hlate => late_larger hθ hlate i

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveBT.HighShape

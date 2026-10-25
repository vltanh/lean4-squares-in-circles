module

public import SquaresInCircles.Eight.Owners.FiniteActiveRadicalTransfer
public import SquaresInCircles.Eight.Owners.GA.Negative.EHBT3EndpointNorms
public import SquaresInCircles.Eight.Owners.GA.Negative.EHBT3Polynomial

/-!
# Eight squares: all thirty-four actual EH1/BT3 endpoint inequalities

The existing finite
polynomial certificates are applied on their original closed intervals;
all mass, norm, support, sign and angle inputs are derived internally.
The conclusion is the actual trigonometric/circle scalar, not a
polynomial surrogate. Continuous concentration and the original-source
stress must still supply the full-domain argument using these endpoints.
-/

@[expose] public section
noncomputable section
open Set Polynomial
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeEHBT3.Endpoints
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open Certificate EndpointInputs EndpointSupport EndpointNorms

lemma radius_upper : R≤(Certificate.Rbar:ℝ) := by
  have hh : R^2=qCap := radius_sq
  have hr := Real.sqrt_nonneg qCap
  norm_num [qCap,Certificate.Rbar] at hh ⊢
  nlinarith

lemma numerator_identity (r : Row) (ep : Split) (x : ℝ) :
    aeval x (numerator r ep)=
      2*aeval x (A r ep)*(∏i,aeval x (mass r ep i))-(Certificate.Rbar:ℝ)*
        ∑i,if active r i then (aeval x (P r ep i)+(aeval x (mass r ep i))^2)*
          ∏j∈Finset.univ.erase i,aeval x (mass r ep j) else 0 := by
  simp only [numerator,map_sub,map_mul,map_prod,map_sum,aeval_C,eq_ratCast]
  congr 2
  refine Finset.sum_congr rfl (fun i _ => ?_)
  split_ifs <;> simp [map_prod]

/-- Every row and both split endpoints, with no analytic positivity premise. -/
theorem value_positive (r : Row) (ep : Split) {x : ℝ}
    (hx : x∈Icc 0 (GlobalGA.NegativeEHBT3.Certificate.width r:ℝ)) : 0<value r ep x := by
  have hnum := numerator_positive r ep hx
  rw [numerator_identity] at hnum
  have hh := FiniteActiveRadicalTransfer.positive (active r)
    (fun i => aeval x (mass r ep i)) (normAt r ep x)
    (fun i => aeval x (P r ep i))
    (fun i => mass_positive r ep i hx)
    (norm_nonnegative r ep x)
    (fun i => norm_square_bound r ep hx i)
    (fun i hi => by simp [normAt,hi]) radius_upper
    (by norm_num [Certificate.Rbar] : (0:ℝ)≤(Certificate.Rbar:ℝ))
    (nonradical_lower r ep hx) hnum
  rw [scalar_identity r ep hx]
  exact hh

lemma native_coordinate (r : Row) {t : ℝ}
    (ht : t∈Icc (left r:ℝ) (right r:ℝ)) :
    t-(left r:ℝ)∈Icc 0 (GlobalGA.NegativeEHBT3.Certificate.width r:ℝ) := by
  dsimp [GlobalGA.NegativeEHBT3.Certificate.width]
  push_cast
  exact ⟨by linarith [ht.1],by linarith [ht.2]⟩

/-- Public endpoint form in the original total angle rather than x=theta-b. -/
theorem original_endpoint_positive (r : Row) (ep : Split) {t : ℝ}
    (ht : t∈Icc (left r:ℝ) (right r:ℝ)) :
    0<value r ep (t-(left r:ℝ)) := value_positive r ep (native_coordinate r ht)

/-- The two small-low equal-angle endpoints. -/
theorem small_low_equal (ep : Split) {t : ℝ} (ht : t∈Icc (0:ℝ) (1/10)) :
    0<baseline .smallLow t (aAt ep t) (zAt ep t)+gain t := by
  have ht' : t∈Icc (left .lowEqual:ℝ) (right .lowEqual:ℝ) := by
    norm_num [left,right]; exact ht
  simpa [value,increment,charge,far,Certificate.family,Certificate.equal,
    Certificate.gainArgument,thetaAt,Certificate.left] using
    original_endpoint_positive .lowEqual ep ht'

/-- The two small-low shifted-negative endpoints retain their actual H norm. -/
theorem small_low_negative (ep : Split) {t : ℝ} (ht : t∈Icc (1/10:ℝ) (1/6)) :
    0<baseline .smallLow t (aAt ep t) (zAt ep t)+gain (1/10)+
      V R (Explicit.k .smallLow t) 1 (t-1/10) := by
  have ht' : t∈Icc (left .lowNegative:ℝ) (right .lowNegative:ℝ) := by
    norm_num [left,right]; exact ht
  have hx := native_coordinate .lowNegative ht'
  have hk := (coefficient_bounds .lowNegative hx).2.2.2.1
  have hkn : Explicit.k .smallLow t≤1 := by
    simpa [Kactual,thetaAt,Certificate.family] using hk
  simpa [value,increment,charge,far,Certificate.family,Certificate.equal,
    Certificate.positive,Certificate.gainArgument,thetaAt,Certificate.left,
    argument,pAt,qAt,pairA,pairB,Certificate.index,Kactual,Lactual,Mactual,
    min_eq_left hkn,max_eq_right hkn,v] using original_endpoint_positive .lowNegative ep ht'

/-- The two far-low equal-angle endpoints include the original EH charge. -/
theorem far_low_equal (ep : Split) {t : ℝ} (ht : t∈Icc (1/10:ℝ) (1/4)) :
    0<baseline .farLow t (aAt ep t) (zAt ep t)+charge .farLow t := by
  have ht' : t∈Icc (left .farEqual:ℝ) (right .farEqual:ℝ) := by
    norm_num [left,right]; exact ht
  simpa [value,increment,Certificate.family,Certificate.equal,
    Certificate.gainArgument,thetaAt,Certificate.left] using
    original_endpoint_positive .farEqual ep ht'

end SquaresInCircles.Eight.GlobalGA.NegativeEHBT3.Endpoints

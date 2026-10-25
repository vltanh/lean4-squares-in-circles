module

public import SquaresInCircles.Eight.TableFree.EndpointBudget

/-!
# Unclipped signed charges for the two outer zero edges

Uncompiled source draft.  The required affine charge is proved directly
from each retained weak transverse owner.  A negative error uses the
opposite endpoint's actual tangent bound.  A wrong intermediate sign uses
the selected owner's original sign implication and the intermediate's
actual circle.  Neither signed tangent is replaced in the conclusion.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
namespace ZeroSignedCharge
open EndpointRotationPenalty EndpointBudgetScalars EndpointECharge

def kappa : ℝ := 49/50

theorem positive_scalar {x : ℝ} (hx : x∈Icc 0 frameCap) :
    0≤x-kappa*(183/200)*Real.sin x-(kappa/2)*(1-Real.cos x) := by
  have hs := sin_upper_five hx.1
  have hc := Real.one_sub_sq_div_two_le_cos (x := x)
  have h2 : x^2≤(7/10 : ℝ)^2 := pow_le_pow_left₀ hx.1 hx.2 2
  have h4 : x^4≤(49/100 : ℝ)*x^2 := by
    nlinarith [mul_le_mul_of_nonneg_right h2 (sq_nonneg x)]
  have hp : 0≤1-kappa*(183/200)-(kappa/4)*x+
      (kappa*(183/200)/6)*x^2-(kappa*(183/200)/120)*x^4 := by
    dsimp [kappa]
    nlinarith [sq_nonneg (x-7/10),hx.2]
  have hp' := mul_nonneg hx.1 hp
  dsimp [kappa] at *
  nlinarith

/-- Multiplication by the positive cosine removes every reciprocal from
the negative-error comparison.  One polynomial bounds the full interval. -/
theorem negative_scalar {x : ℝ} (hx : x∈Icc 0 frameCap) :
    x*Real.cos x≤kappa*K*Real.sin x-(2*kappa/5)*(1-Real.cos x) := by
  have hx7 : x≤7/10 := hx.2
  have hs := sin_lower_seven hx.1
  have hc := cos_lower_six hx.1
  have hcu := cos_upper_four hx.1
  have h2 : x^2≤(1/2 : ℝ) := by
    linarith [pow_le_pow_left₀ hx.1 hx7 2]
  have h3 : x^3≤(1/2 : ℝ) := by
    linarith [pow_le_pow_left₀ hx.1 hx7 3]
  have h4 : x^4≤(1/2 : ℝ)*x^2 := by
    linarith [mul_le_mul_of_nonneg_right h2 (sq_nonneg x)]
  have h5 : x^5≤(1/2 : ℝ)*x^2 := by
    linarith [mul_le_mul_of_nonneg_right h3 (sq_nonneg x)]
  have h6 : x^6≤(1/2 : ℝ)*x^2 := by
    have hx4 : x^4≤(1/2 : ℝ) := by
      linarith [pow_le_pow_left₀ hx.1 hx7 4]
    linarith [mul_le_mul_of_nonneg_right hx4 (sq_nonneg x)]
  have hp : 0≤(1503/40000 : ℝ)-(49/250)*x+(78497/240000)*x^2+
      (49/3000)*x^3-(158497/4800000)*x^4-(49/90000)*x^5-
      (41503/201600000)*x^6 := by
    linarith [sq_nonneg (x-1/3),pow_nonneg hx.1 3,hx.1]
  have hp' := mul_nonneg hx.1 hp
  have hxc := mul_le_mul_of_nonneg_left hcu hx.1
  dsimp [kappa,K]
  linarith

/-- Actual wrong-sign circle support.  The degree-seven lower sine and
degree-five half-angle upper sine leave a strict rational endpoint reserve. -/
theorem chord_scalar {x : ℝ} (hx : x∈Icc 0 frameCap) :
    kappa*(2*R*Real.sin (x/2)-Real.sin x)≤x := by
  have hx7 : x≤7/10 := hx.2
  have hRu : R≤1979/1000 :=
    le_of_pow_le_pow_left₀ two_ne_zero (by norm_num) (by rw [R_sq]; norm_num [qCap])
  have hhalf : x/2∈Icc 0 (frameCap/2) := by
    simp only [frameCap]
    constructor <;> linarith [hx.1]
  have hsh := (MiddleAngularPenalty.half_trig hhalf).2.1
  have hs := sin_lower_seven hx.1
  have hsu := sin_upper_five hhalf.1
  have hm := mul_le_mul hRu hsu hsh (by norm_num : (0:ℝ)≤1979/1000)
  have h3 : x^3≤(49/100 : ℝ)*x := by
    linarith [mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx.1 hx7 2) hx.1]
  have h7 : x^7≤(117649/1000000 : ℝ)*x := by
    linarith [mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx.1 hx7 6) hx.1]
  dsimp [kappa]
  linarith [pow_nonneg hx.1 5,hx.1]

theorem positive_projection {a b B x : ℝ}
    (ha : a≤283/200) (hb : 0≤b) (hx : x∈Icc 0 frameCap)
    (hf : edgeWidth x≤a*Real.sin x+b*Real.cos x+B) :
    0≤x+kappa*(b+B-1) := by
  have hs0 := (transport_trig hx).2.2.1
  have hc1 := Real.cos_le_one x
  have hpa := mul_nonneg (show 0≤283/200-a by linarith) hs0
  have hpb := mul_nonneg hb (show 0≤1-Real.cos x by linarith)
  rw [edgeWidth_positive_formula hx] at hf
  have hD : -(183/200)*Real.sin x-(1-Real.cos x)/2≤b+B-1 := by
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hD (by norm_num [kappa] : 0≤kappa)
  linarith [positive_scalar hx]

theorem negative_projection {a b B x : ℝ}
    (ha : 447/800≤a) (hB : B≤9/10) (hx : x∈Icc 0 frameCap)
    (hf : edgeWidth (-x)≤ -a*Real.sin x+b*Real.cos x+B) :
    0≤-x+kappa*(b+B-1) := by
  have hs0 := (transport_trig hx).2.2.1
  have hcpos : 0<Real.cos x := by linarith [(transport_trig hx).1]
  have hc1 := Real.cos_le_one x
  have hpa := mul_nonneg (show 0≤a+1/2-K by dsimp [K]; linarith) hs0
  have hpB := mul_nonneg (show 0≤9/10-B by linarith)
    (show 0≤1-Real.cos x by linarith)
  rw [edgeWidth_negative_formula hx] at hf
  have hD : K*Real.sin x-(2/5)*(1-Real.cos x)≤(b+B-1)*Real.cos x := by
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hD (by norm_num [kappa] : 0≤kappa)
  have hprod : 0≤(-x+kappa*(b+B-1))*Real.cos x := by
    nlinarith [negative_scalar hx]
  by_contra! hneg
  exact (not_lt_of_ge hprod) (mul_neg_of_neg_of_pos hneg hcpos)

/-- The two original transverse witnesses have the same scalar charge.
Only source coordinate bounds enter; the scalar signs do not create a
replacement physical point. -/
theorem nonnegative_zero {a A b B d : ℝ}
    (ha : a∈Icc (447/800 : ℝ) (283/200))
    (hA : A∈Icc (447/800 : ℝ) (283/200))
    (hb : b∈Icc 0 (9/10 : ℝ)) (hB : B∈Icc 0 (9/10 : ℝ))
    (hd : |d|≤frameCap)
    (hf : edgeWidth d≤b+A*Real.sin d+B*Real.cos d ∨
      edgeWidth d≤a*Real.sin d+b*Real.cos d+B) :
    0≤d+kappa*(b+B-1) := by
  by_cases hd0 : 0≤d
  · have hd' : d∈Icc 0 frameCap := ⟨hd0,(le_abs_self d).trans hd⟩
    rcases hf with hf | hf
    · have h := positive_projection hA.2 hB.1 hd'
        (show edgeWidth d≤A*Real.sin d+B*Real.cos d+b by linarith)
      linarith
    · exact positive_projection ha.2 hb.1 hd' hf
  · have hd' : -d∈Icc 0 frameCap := ⟨by linarith,(neg_le_abs d).trans hd⟩
    rcases hf with hf | hf
    · have hf' : edgeWidth (-(-d))≤ -A*Real.sin (-d)+B*Real.cos (-d)+b := by
        simpa only [neg_neg,Real.sin_neg,Real.cos_neg,neg_mul_neg] using
          (show edgeWidth d≤A*Real.sin d+B*Real.cos d+b by linarith)
      have h := negative_projection hA.1 hb.2 hd' hf'
      linarith
    · have hf' : edgeWidth (-(-d))≤ -a*Real.sin (-d)+b*Real.cos (-d)+B := by
        simpa only [neg_neg,Real.sin_neg,Real.cos_neg,neg_mul_neg] using hf
      simpa only [neg_neg] using negative_projection ha.1 hB.2 hd' hf'

/-- The selected canceling owner carries the original sign implication.
The conclusion retains the signed G tangent, including when it is wrong. -/
theorem signed_right {q d : ℝ} {H G : SignedPoint}
    (hHs : H.Sorted) (hGs : G.Sorted)
    (hHc : H.AvoidsCore) (hGc : G.AvoidsCore)
    (hHcont : H.Contained q) (hGcont : G.Contained q)
    (hq : q≤qCap) (hyH : 0≤H.y) (hd : |d|≤frameCap)
    (hHG : zeroFeasible H G d 0 ∨ (zeroFeasible H G d 2 ∧ G.y≤0)) :
    1-EndpointRotationPenalty.charge*d≤H.y-G.y := by
  have hH := SignedPoint.coordinate_bounds hHs hHc hHcont hq
  have hG := SignedPoint.coordinate_bounds hGs hGc hGcont hq
  by_cases hyG : G.y≤0
  · have hf : edgeWidth d≤H.y+G.a*Real.sin d+(-G.y)*Real.cos d ∨
        edgeWidth d≤H.a*Real.sin d+H.y*Real.cos d+(-G.y) := by
      rcases hHG with hf | ⟨hf,_⟩
      · left
        simpa [zeroFeasible,zeroProjection,sub_eq_add_neg,neg_mul] using hf
      · right
        simpa [zeroFeasible,zeroProjection,sub_eq_add_neg] using hf
    have hz := nonnegative_zero ⟨hH.1.le,hH.2.1.le⟩ ⟨hG.1.le,hG.2.1.le⟩
      ⟨hyH,(le_abs_self H.y).trans hH.2.2.le⟩
      ⟨by linarith,(neg_le_abs G.y).trans hG.2.2.le⟩ hd hf
    dsimp [kappa,EndpointRotationPenalty.charge] at *
    linarith
  · have hyG0 : 0<G.y := lt_of_not_ge hyG
    have hf : zeroFeasible H G d 0 := by
      rcases hHG with hf | ⟨_,hbad⟩
      · exact hf
      · exact (hyG hbad).elim
    have hfp : edgeWidth d≤H.y+G.a*Real.sin d-G.y*Real.cos d := by
      simpa [zeroFeasible,zeroProjection] using hf
    have hd0 : 0≤d := by
      by_contra! hdneg
      have hn : -d∈Icc 0 frameCap := ⟨by linarith,(neg_le_abs d).trans hd⟩
      have hs : Real.sin d≤0 := by
        simpa only [Real.sin_neg,neg_nonneg] using (transport_trig hn).2.2.1
      have hc : 0<Real.cos d := by
        have h := (transport_trig hn).1
        simp only [Real.cos_neg] at h
        linarith
      have hp := mul_nonpos_of_nonneg_of_nonpos hGs.1.le hs
      have hn' := mul_nonneg hyG0.le hc.le
      linarith [edgeWidth_ge_one d,(le_abs_self H.y).trans_lt hH.2.2]
    have hd' : d∈Icc 0 frameCap := ⟨hd0,(le_abs_self d).trans hd⟩
    have hcircle : (G.a+1/2)^2+(G.y+1/2)^2≤qCap := by
      simpa [SignedPoint.circle,abs_of_pos hyG0] using hGcont.trans hq
    have hsupport := circle_chord_support hcircle hd'
    have hscalar := chord_scalar hd'
    rw [edgeWidth_positive_formula hd'] at hfp
    have hlocal : 1-H.y+G.y≤2*R*Real.sin (d/2)-Real.sin d := by
      linarith
    have hm := mul_le_mul_of_nonneg_left hlocal (by norm_num [kappa] : 0≤kappa)
    dsimp [kappa,EndpointRotationPenalty.charge] at *
    linarith

end ZeroSignedCharge

namespace SignedCycle
open Candidate EndpointRotationPenalty

/-- Both actual outer zero edges retain the signed intermediate sum. -/
theorem signed_outer_charges {q : ℝ} {C : SignedCycle}
    (hq : q≤qCap) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (w : C.Witnesses) (hz : C.ZeroSignImplications w) :
    1-EndpointRotationPenalty.charge*(C.theta G-C.theta H)≤(C.point H).y-(C.point G).y ∧
    1-EndpointRotationPenalty.charge*(C.theta D-C.theta T)≤(C.point T).y-(C.point D).y := by
  have hownerH : w.owner H=0 ∨ w.owner H=2 := by
    simpa [normalOwners,H] using w.allowed H
  have hownerT : w.owner T=0 ∨ w.owner T=2 := by
    simpa [normalOwners,T] using w.allowed T
  have hHG : zeroFeasible (C.point H) (C.point G) (C.theta G-C.theta H) 0 ∨
      (zeroFeasible (C.point H) (C.point G) (C.theta G-C.theta H) 2 ∧
        (C.point G).y≤0) := by
    have hw := w.feasible H
    rcases hownerH with ho | ho
    · left
      rw [ho] at hw
      simpa [Feasible,slack,edge,delta,next,word,H,G,zeroFeasible] using hw
    · refine Or.inr ⟨?_,(hz.HG_canceling ho).le⟩
      rw [ho] at hw
      simpa [Feasible,slack,edge,delta,next,word,H,G,zeroFeasible] using hw
  have hTD : zeroFeasible (C.point D).reflect (C.point T).reflect
        (C.theta D-C.theta T) 0 ∨
      (zeroFeasible (C.point D).reflect (C.point T).reflect
        (C.theta D-C.theta T) 2 ∧ (C.point T).reflect.y≤0) := by
    have hw := w.feasible T
    rcases hownerT with ho | ho
    · have hf : zeroFeasible (C.point T) (C.point D) (C.theta D-C.theta T) 0 := by
        rw [ho] at hw
        simpa [Feasible,slack,edge,delta,next,word,T,D,zeroFeasible] using hw
      refine Or.inr ⟨?_,?_⟩
      · simpa [reflectedOwner] using (zeroFeasible_reflect _ _ _ 0).2 hf
      · simpa [SignedPoint.reflect] using neg_nonpos.mpr (hz.TD_canceling ho).le
    · have hf : zeroFeasible (C.point T) (C.point D) (C.theta D-C.theta T) 2 := by
        rw [ho] at hw
        simpa [Feasible,slack,edge,delta,next,word,T,D,zeroFeasible] using hw
      left
      simpa [reflectedOwner] using (zeroFeasible_reflect _ _ _ 2).2 hf
  constructor
  · exact ZeroSignedCharge.signed_right (hC.sorted H) (hC.sorted G)
      (hC.core H) (hC.core G) (hC.contained H) (hC.contained G) hq
      hn.H_nonneg (hC.spread G H) hHG
  · have hh := ZeroSignedCharge.signed_right
      ((SignedPoint.reflect_sorted _).2 (hC.sorted D))
      ((SignedPoint.reflect_sorted _).2 (hC.sorted T))
      ((SignedPoint.reflect_avoidsCore _).2 (hC.core D))
      ((SignedPoint.reflect_avoidsCore _).2 (hC.core T))
      ((SignedPoint.reflect_contained _ _).2 (hC.contained D))
      ((SignedPoint.reflect_contained _ _).2 (hC.contained T)) hq
      (show 0≤(C.point D).reflect.y by simpa [SignedPoint.reflect] using neg_nonneg.mpr hn.D_nonpos)
      (hC.spread D T) hTD
    simpa [SignedPoint.reflect,sub_eq_add_neg,add_comm] using hh

end SignedCycle
end SquaresInCircles.Eight.TableFree

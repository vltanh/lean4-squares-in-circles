module

public import SquaresInCircles.Eight.TableFree.GlobalGAJointNegativeAETD2CommonData

/-!
# The whole-domain common-gain coefficient certificates

Uncompiled transcription of (16)--(17) and (23)--(25). The two odd
terms in the second certificate are retained together, just as in the
hand proof. All remaining powers receive a single exact rational tail
bound; no angular samples or assumed reserves occur.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.JointNegativeAETD2.CommonGain.Certificate
open Polynomial PowerTailBounds DirectedPowerBounds

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem P_identity :
    centeredP=C (centeredP.coeff 0)+C (centeredP.coeff 1)*X+
      C (centeredP.coeff 2)*X^2+tail centeredP 3 11 := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem P_coefficients :
    (4097/50000:ℚ)<centeredP.coeff 0 ∧ |centeredP.coeff 1|<(2001/4000:ℚ) ∧
      (133/50:ℚ)<centeredP.coeff 2-PowerTailBounds.norm centeredP 3 11 (2/5) := by decide

theorem P_positive {y : ℝ} (hy : y∈Icc (0:ℝ) (129/200)) :
    (73/1250:ℝ)<aeval y P := by
  let u := y-2/5
  have hu : |u|≤(2/5:ℝ) := by
    apply abs_le.mpr
    dsimp [u]
    exact ⟨by linarith [hy.1],by linarith [hy.2]⟩
  have hh := PowerTailBounds.quadratic_lower P_identity (by norm_num) hu
  have hc :
      (4097/50000:ℝ)<(centeredP.coeff 0:ℝ) ∧ |(centeredP.coeff 1:ℝ)|<(2001/4000:ℝ) ∧
      (133/50:ℝ)<(centeredP.coeff 2:ℝ)-(PowerTailBounds.norm centeredP 3 11 (2/5):ℝ) := by
    exact_mod_cast P_coefficients
  have hl : -(2001/4000:ℝ)*|u|≤(centeredP.coeff 1:ℝ)*u := by
    have ht := mul_le_mul_of_nonneg_right hc.2.1.le (abs_nonneg u)
    rw [←abs_mul] at ht
    exact (abs_le.mp ht).1
  have hq := mul_le_mul_of_nonneg_right hc.2.2.le (sq_nonneg u)
  have hm := ChebyshevLeadingBounds.quadratic_min (a:=(4097/50000:ℝ))
    (b:=-(2001/4000:ℝ)) (x:=|u|) (show (0:ℝ)<133/50 by norm_num)
  have hid : aeval u centeredP=aeval y P := by simp [centeredP,u]
  rw [hid] at hh
  rw [sq_abs] at hm
  norm_num at hm
  nlinarith

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem J_identity :
    centeredJ=C (centeredJ.coeff 0)+C (centeredJ.coeff 1)*X+
      C (centeredJ.coeff 2)*X^2+C (centeredJ.coeff 3)*X^3+
      C (centeredJ.coeff 4)*X^4+C (centeredJ.coeff 5)*X^5+tail centeredJ 6 145 := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem J_coefficients :
    (1589/250000:ℚ)<centeredJ.coeff 0 ∧ |centeredJ.coeff 1|<(361/200000:ℚ) ∧
    (23599/100000:ℚ)<centeredJ.coeff 2 ∧
    (19703/100000:ℚ)<centeredJ.coeff 3 ∧ centeredJ.coeff 3<(2463/12500:ℚ) ∧
    (-85627/100000:ℚ)<centeredJ.coeff 4 ∧
    (-144289/100000:ℚ)<centeredJ.coeff 5 ∧ centeredJ.coeff 5<0 ∧
    jTailNorm<(3033/125000:ℚ) := by decide

theorem J_tail_lower {u : ℝ} (hu : |u|≤(7/20:ℝ)) :
    -(jTailNorm:ℝ)*u^2≤aeval u (tail centeredJ 6 145) := by
  have hterm (i : Fin 145) :
      -|(centeredJ.coeff (i.val+6):ℝ)|*(7/20:ℝ)^(i.val+4)*u^2≤
        (centeredJ.coeff (i.val+6):ℝ)*u^(i.val+6) := by
    have hp : |u^(i.val+4)|≤(7/20:ℝ)^(i.val+4) := by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg u) hu _
    have hm := mul_le_mul_of_nonneg_left hp (abs_nonneg (centeredJ.coeff (i.val+6):ℝ))
    rw [←abs_mul] at hm
    have hlo := mul_le_mul_of_nonneg_right (abs_le.mp hm).1 (sq_nonneg u)
    have he : (centeredJ.coeff (i.val+6):ℝ)*u^(i.val+6)=
        ((centeredJ.coeff (i.val+6):ℝ)*u^(i.val+4))*u^2 := by
      rw [show i.val+6=(i.val+4)+2 by omega,pow_add]
      ring
    rw [he]
    linarith
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hterm i)
  simp only [tail,map_sum,map_mul,map_pow,aeval_C,aeval_X]
  have he : (jTailNorm:ℝ)=∑i:Fin 145,|(centeredJ.coeff (i.val+6):ℝ)|*(7/20:ℝ)^(i.val+4) := by
    simp [jTailNorm]
  rw [he]
  simpa only [neg_mul,Finset.sum_neg_distrib,Finset.sum_mul] using hh

theorem J_positive {x : ℝ} (hx : x∈Icc 0 frameCap) :
    (3167/500000:ℝ)<aeval x J := by
  let u := x-7/20
  have hu : |u|≤(7/20:ℝ) := by
    apply abs_le.mpr
    dsimp [u]
    exact ⟨by linarith [hx.1],by norm_num [frameCap] at hx; linarith [hx.2]⟩
  have hu2 : u^2≤(7/20:ℝ)^2 := by nlinarith [(abs_le.mp hu).1,(abs_le.mp hu).2]
  have hc :
      (1589/250000:ℝ)<(centeredJ.coeff 0:ℝ) ∧ |(centeredJ.coeff 1:ℝ)|<(361/200000:ℝ) ∧
      (23599/100000:ℝ)<(centeredJ.coeff 2:ℝ) ∧
      (19703/100000:ℝ)<(centeredJ.coeff 3:ℝ) ∧ (centeredJ.coeff 3:ℝ)<(2463/12500:ℝ) ∧
      (-85627/100000:ℝ)<(centeredJ.coeff 4:ℝ) ∧
      (-144289/100000:ℝ)<(centeredJ.coeff 5:ℝ) ∧ (centeredJ.coeff 5:ℝ)<0 ∧
      (jTailNorm:ℝ)<(3033/125000:ℝ) := by exact_mod_cast J_coefficients
  have hbracket : 0≤(centeredJ.coeff 3:ℝ)+(centeredJ.coeff 5:ℝ)*u^2 ∧
      (centeredJ.coeff 3:ℝ)+(centeredJ.coeff 5:ℝ)*u^2≤2463/12500 := by
    have hl := mul_le_mul_of_nonneg_right hc.2.2.2.2.2.2.1.le (sq_nonneg u)
    have hh := mul_nonpos_of_nonpos_of_nonneg hc.2.2.2.2.2.2.2.1.le (sq_nonneg u)
    exact ⟨by nlinarith [hc.2.2.2.1],by linarith [hc.2.2.2.2.1]⟩
  have hodd : -(2463/12500:ℝ)*(7/20)≤
      ((centeredJ.coeff 3:ℝ)+(centeredJ.coeff 5:ℝ)*u^2)*u := by
    have hl := mul_le_mul_of_nonneg_left (abs_le.mp hu).1 hbracket.1
    have hh := mul_le_mul_of_nonpos_right hbracket.2 (show -(7/20:ℝ)≤0 by norm_num)
    linarith
  have heven : -(85627/100000:ℝ)*(7/20)^2≤(centeredJ.coeff 4:ℝ)*u^2 := by
    have hl := mul_le_mul_of_nonneg_right hc.2.2.2.2.2.1.le (sq_nonneg u)
    nlinarith
  have hquadratic : (3786/100000:ℝ)≤(centeredJ.coeff 2:ℝ)+
      (centeredJ.coeff 3:ℝ)*u+(centeredJ.coeff 4:ℝ)*u^2+
      (centeredJ.coeff 5:ℝ)*u^3-(jTailNorm:ℝ) := by
    nlinarith [hc.2.2.1,hc.2.2.2.2.2.2.2.2]
  have hq := mul_le_mul_of_nonneg_right hquadratic (sq_nonneg u)
  have hl : -(361/200000:ℝ)*|u|≤(centeredJ.coeff 1:ℝ)*u := by
    have ht := mul_le_mul_of_nonneg_right hc.2.1.le (abs_nonneg u)
    rw [←abs_mul] at ht
    exact (abs_le.mp ht).1
  have ht := J_tail_lower hu
  have hi := congrArg (fun p : ℚ[X] => aeval u p) J_identity
  simp only [map_add,map_mul,map_pow,aeval_C,aeval_X] at hi
  have hm := ChebyshevLeadingBounds.quadratic_min (a:=(1589/250000:ℝ))
    (b:=-(361/200000:ℝ)) (x:=|u|) (show (0:ℝ)<3786/100000 by norm_num)
  rw [sq_abs] at hm
  norm_num at hm
  have hid : aeval u centeredJ=aeval x J := by simp [centeredJ,u]
  rw [hid] at hi
  nlinarith

end SquaresInCircles.Eight.TableFree.GlobalGA.JointNegativeAETD2.CommonGain.Certificate

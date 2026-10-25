module

public import SquaresInCircles.Eight.TableFree.ShortOuterOneOppositeFiveAxialPolynomialData

/-!
# The whole axial polynomial is positive

Uncompiled transcription of equations (35)--(43) of
`HAND_SHORT_WORD_OPPOSITE_EDGE_FIVE_WITHOUT_TABLES.md`.
One bound for the entire high-degree tail leaves the displayed
degree-eight polynomial. Its quotient by h-X is bounded by the
displayed cubic, whose exact Taylor identity and one completed square
prove positivity on the whole interval.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterOne.OppositeFive.AxialPolynomial
open Polynomial

lemma tail_lower (r : Bool) {x : ℝ} (hx : x∈Icc 0 (h:ℝ)) :
    -2*x^9≤aeval x (PowerTailBounds.tail (polynomial r) 9 18) := by
  have hterm (j : Fin 18) :
      -|((polynomial r).coeff (j.val+9):ℝ)| *(h:ℝ)^j.val*x^9≤
        ((polynomial r).coeff (j.val+9):ℝ)*x^(j.val+9) := by
    have hp : |x^j.val|≤(h:ℝ)^j.val := by
      rw [abs_pow,abs_of_nonneg hx.1]
      exact pow_le_pow_left₀ hx.1 hx.2 _
    have hm := mul_le_mul_of_nonneg_left hp (abs_nonneg ((polynomial r).coeff (j.val+9):ℝ))
    rw [←abs_mul] at hm
    have hlo := mul_le_mul_of_nonneg_right (abs_le.mp hm).1 (pow_nonneg hx.1 9)
    have he : ((polynomial r).coeff (j.val+9):ℝ)*x^(j.val+9)=
        (((polynomial r).coeff (j.val+9):ℝ)*x^j.val)*x^9 := by rw [pow_add]; ring
    rw [he]
    linarith
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => hterm j)
  have hcast : (tailReserve r:ℝ)=
      ∑j : Fin 18,|((polynomial r).coeff (j.val+9):ℝ)| *(h:ℝ)^j.val := by simp [tailReserve]
  have hsum : -(tailReserve r:ℝ)*x^9≤aeval x (PowerTailBounds.tail (polynomial r) 9 18) := by
    simp only [PowerTailBounds.tail,map_sum,map_mul,map_pow,aeval_C,aeval_X,eq_ratCast]
    rw [hcast]
    simpa only [neg_mul,Finset.sum_neg_distrib,Finset.sum_mul] using hs
  have hres : (tailReserve r:ℝ)≤2 := by exact_mod_cast (tail_reserve r).1.trans (tail_reserve r).2
  have hm := mul_le_mul_of_nonneg_right hres (pow_nonneg hx.1 9)
  linarith

lemma difference_positive (r : Bool) {x : ℝ} (hx : 0≤x) : 0<aeval x (lowDifference r) := by
  have he := congrArg (fun z : ℚ[X] => aeval x z) (difference_expansion r)
  simp only [map_add,map_sum,map_mul,map_pow,aeval_C,aeval_X,eq_ratCast] at he
  have hs : 0≤∑j : Fin 8,((lowDifference r).coeff (j.val+1):ℝ)*x^(j.val+1) := by
    apply Finset.sum_nonneg
    intro j hj
    have hc : (0:ℝ)≤((lowDifference r).coeff (j.val+1):ℝ) := by
      exact_mod_cast (difference_coefficients r).2 j
    exact mul_nonneg hc (pow_nonneg hx _)
  have hzero : (0:ℝ)<((lowDifference r).coeff 0:ℝ) := by
    exact_mod_cast (difference_coefficients r).1
  linarith

lemma polynomial_above_low (r : Bool) {x : ℝ} (hx : x∈Icc 0 (h:ℝ)) :
    aeval x (low r)<aeval x (polynomial r) := by
  have he := congrArg (fun z : ℚ[X] => aeval x z) (low_expansion r)
  simp only [map_add,map_mul,map_pow,aeval_C,aeval_X,eq_ratCast] at he
  have ht := tail_lower r hx
  have hd := difference_positive r hx.1
  have hp := mul_nonneg (show 0≤(h:ℝ)-x by linarith [hx.2]) (pow_nonneg hx.1 8)
  push_cast at he
  nlinarith only [he,ht,hd,hp]

lemma cubic_taylor (r : Bool) (x : ℝ) :
    aeval x (cubic r)=aeval (reference r:ℝ) (cubic r)+
      aeval (reference r:ℝ) (cubic r).derivative*(x-reference r)+
        (x-reference r)^2*((cubic2 r:ℝ)+(cubic3 r:ℝ)*(x+2*reference r)) := by
  cases r <;> norm_num [cubic,reference,cubic0,cubic1,cubic2,cubic3] <;> ring

lemma cubic_positive (r : Bool) {x : ℝ} (hx : x∈Icc 0 (h:ℝ)) : 0<aeval x (cubic r) := by
  let m : ℝ := reference r
  let v : ℝ := aeval m (cubic r)
  let d : ℝ := aeval m (cubic r).derivative
  let κ : ℝ := curvature r
  have hκ : 0<κ := by cases r <;> norm_num [κ,curvature]
  have hδ : 0<(slopeUpper r:ℝ) := by cases r <;> norm_num [slopeUpper]
  have hv : (valueLower r:ℝ)<v := by
    cases r <;> norm_num [v,m,cubic,reference,valueLower,cubic0,cubic1,cubic2,cubic3]
  have hd : |d|<(slopeUpper r:ℝ) := by
    cases r <;> norm_num [d,m,cubic,reference,slopeUpper,cubic0,cubic1,cubic2,cubic3]
  have hcurv : κ≤(cubic2 r:ℝ)+(cubic3 r:ℝ)*(x+2*m) := by
    have ha : (cubic3 r:ℝ)<0 := by cases r <;> norm_num [cubic3]
    have hmono := mul_le_mul_of_nonpos_left (show x+2*m≤(h:ℝ)+2*m by linarith [hx.2]) ha.le
    have hfixed : κ<(cubic2 r:ℝ)+(cubic3 r:ℝ)*((h:ℝ)+2*m) := by
      dsimp [κ,m]
      exact_mod_cast (cubic_reference r).2.2.1
    linarith
  have hreserve : 0<(valueLower r:ℝ)-(slopeUpper r:ℝ)^2/(4*κ) := by
    dsimp [κ]
    exact_mod_cast (cubic_reference r).2.2.2
  have hdisc0 : (slopeUpper r:ℝ)^2<4*κ*(valueLower r:ℝ) := by
    have hh := (div_lt_iff₀ (show 0<4*κ by positivity)).mp
      (show (slopeUpper r:ℝ)^2/(4*κ)<(valueLower r:ℝ) by linarith)
    nlinarith only [hh]
  have hdsq : d^2<(slopeUpper r:ℝ)^2 := by
    have ha := abs_lt.1 hd
    nlinarith
  have hvκ := mul_lt_mul_of_pos_left hv (show 0<4*κ by positivity)
  have hdisc : d^2<4*κ*v := by linarith
  have hQ : 0<v+d*(x-m)+κ*(x-m)^2 := by
    have hsq := sq_nonneg (2*κ*(x-m)+d)
    have he : 4*κ*(v+d*(x-m)+κ*(x-m)^2)=4*κ*v-d^2+(2*κ*(x-m)+d)^2 := by ring
    have hp : 0<(4*κ)*(v+d*(x-m)+κ*(x-m)^2) := by nlinarith only [he,hsq,hdisc]
    exact (mul_pos_iff_of_pos_left (by positivity : 0<4*κ)).mp hp
  have hlast := mul_le_mul_of_nonneg_left hcurv (sq_nonneg (x-m))
  have ht := cubic_taylor r x
  change aeval x (cubic r)=v+d*(x-m)+(x-m)^2*((cubic2 r:ℝ)+(cubic3 r:ℝ)*(x+2*m)) at ht
  nlinarith only [ht,hQ,hlast]

lemma quotient_above_cubic (r : Bool) {x : ℝ} (hx : x∈Icc 0 (h:ℝ)) :
    aeval x (cubic r)<aeval x (quotient r) := by
  have hc : (cubic0 r:ℝ)<((quotient r).coeff 0:ℝ) ∧
      (cubic1 r:ℝ)≤((quotient r).coeff 1:ℝ) ∧
      (cubic2 r:ℝ)≤((quotient r).coeff 2:ℝ) ∧
      (cubic3 r:ℝ)≤((quotient r).coeff 3:ℝ)+((quotient r).coeff 5:ℝ)*(h:ℝ)^2+
        ((quotient r).coeff 7:ℝ)*(h:ℝ)^4 ∧
      0≤((quotient r).coeff 4:ℝ) ∧ ((quotient r).coeff 5:ℝ)≤0 ∧
      0≤((quotient r).coeff 6:ℝ) ∧ ((quotient r).coeff 7:ℝ)≤0 := by
    exact_mod_cast quotient_coefficients r
  have hx2 := pow_le_pow_left₀ hx.1 hx.2 2
  have hx4 := pow_le_pow_left₀ hx.1 hx.2 4
  have hp5 : x^5≤(h:ℝ)^2*x^3 := by
    have hh := mul_le_mul_of_nonneg_right hx2 (pow_nonneg hx.1 3)
    nlinarith only [hh]
  have hp7 : x^7≤(h:ℝ)^4*x^3 := by
    have hh := mul_le_mul_of_nonneg_right hx4 (pow_nonneg hx.1 3)
    nlinarith only [hh]
  have h5 := mul_le_mul_of_nonpos_left hp5 hc.2.2.2.2.2.1
  have h7 := mul_le_mul_of_nonpos_left hp7 hc.2.2.2.2.2.2.2
  have h4 := mul_nonneg hc.2.2.2.2.1 (pow_nonneg hx.1 4)
  have h6 := mul_nonneg hc.2.2.2.2.2.2.1 (pow_nonneg hx.1 6)
  have h1 := mul_le_mul_of_nonneg_right hc.2.1 hx.1
  have h2 := mul_le_mul_of_nonneg_right hc.2.2.1 (sq_nonneg x)
  have h3 := mul_le_mul_of_nonneg_right hc.2.2.2.1 (pow_nonneg hx.1 3)
  have he := congrArg (fun z : ℚ[X] => aeval x z) (quotient_expansion r)
  simp only [map_add,map_mul,map_pow,aeval_C,aeval_X,eq_ratCast] at he
  simp only [cubic,map_add,map_mul,map_pow,aeval_C,aeval_X,eq_ratCast]
  nlinarith only [he,hc.1,h1,h2,h3,h4,h5,h6,h7]

lemma low_positive (r : Bool) {x : ℝ} (hx : x∈Icc 0 (h:ℝ)) : 0<aeval x (low r) := by
  have hq : 0<aeval x (quotient r) := (cubic_positive r hx).trans (quotient_above_cubic r hx)
  have hprod := mul_nonneg (show 0≤(h:ℝ)-x by linarith [hx.2]) hq.le
  have he := congrArg (fun z : ℚ[X] => aeval x z) (quotient_identity r)
  simp only [map_add,map_sub,map_mul,map_pow,aeval_C,aeval_X,eq_ratCast] at he
  have hr : (0:ℝ)<(endpoint r:ℝ) := by
    have hrat : (0:ℚ)<endpoint r := by
      have hh := endpoint_reserve r
      cases r <;> norm_num at hh <;> linarith
    exact_mod_cast hrat
  nlinarith [pow_nonneg hx.1 8]

theorem positive (r : Bool) {x : ℝ} (hx : x∈Icc 0 (h:ℝ)) : 0<aeval x (polynomial r) :=
  (low_positive r hx).trans (polynomial_above_low r hx)

end SquaresInCircles.Eight.TableFree.ShortOuterOne.OppositeFive.AxialPolynomial

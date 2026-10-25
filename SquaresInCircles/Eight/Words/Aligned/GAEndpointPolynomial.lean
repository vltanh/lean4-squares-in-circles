module

public import Mathlib.Tactic
public import SquaresInCircles.Eight.Arithmetic.PolynomialExpressions
public import SquaresInCircles.Eight.Owners.PowerTailBounds

/-!
# Eight squares: the continuous stress polynomial at the wrong aligned GA/DE endpoint

The coefficients are rational edge weights (`aP`, `betaP`, `deltaP`, `epsilonP`) and circle
masses (`massAP`, …, `massEP`), polynomials in the sine `s`. Clearing their positive
denominators gives one polynomial `P = X * L` (`P_factor`) on the sine interval `[0, 11/50]`.
The negative tail of `L` is bounded by its coefficient norm (`negative_tail_cubic`,
`tail_reserve`) and the remaining cubic is positive by one completed square
(`cubic_positive`), so `P` is positive (`P_positive`).
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.AlignedGAEndpointPolynomial
open Polynomial PowerTailBounds PolynomialExpressions

def aP : ℚ[X] := C (24/41)+C (3/5)*X+C (1/10)*X^2+C (1/5)*X^3
def betaP : ℚ[X] := 1+C (33/100)*X-C (27/200)*X^2+C (9/25)*X^3
def deltaP : ℚ[X] := C (36/31)-C (49/100)*X-C (1/20)*X^2+C (9/100)*X^3
def epsilonP : ℚ[X] := C (36/31)-C (159/200)*X+C (83/200)*X^2-C (87/400)*X^3
def massAP : ℚ[X] := C (12/41)+C (19/250)*X+C (41/1000)*X^2
def massBP : ℚ[X] := C (12/41)+C (1/50)*X-C (67/500)*X^2+C (19/500)*X^3
def massDP : ℚ[X] := C (12/31)-C (1/25)*X-C (7/1000)*X^2+C (41/500)*X^3
def massHP : ℚ[X] := C (12/31)-C (19/125)*X+C (101/1000)*X^2-C (53/1000)*X^3
def massEP : ℚ[X] := X*(C (38/125)-C (47/250)*X+C (11/100)*X^2-C (11/250)*X^3)
def denominator : ℚ[X] := C 4*massAP*massBP*massDP*massHP*massEP

def constantNumerator : ℚ[X] :=
  denominator*(C 3+C 2*aP+C 2*betaP+C 2*deltaP+epsilonP+epsilonP*X-
      C (9789/2500)*(massAP+massBP+massDP+massHP+massEP))-
    massBP*massDP*massHP*massEP*(1+aP^2)-
    massAP*massDP*massHP*massEP*(betaP^2+aP^2-C 2*aP*betaP*X)-
    massAP*massBP*massHP*massEP*(deltaP^2+betaP^2)-
    massAP*massBP*massDP*massEP*(epsilonP^2+1)-
    massAP*massBP*massDP*massHP*(deltaP^2+epsilonP^2)

def cosineNumerator : ℚ[X] :=
  denominator*betaP+C 2*deltaP*epsilonP*massAP*massBP*massDP*massHP
def cosineLower : ℚ[X] := 1-C (1/2)*X^2-C (13/100)*X^4
def P : ℚ[X] := constantNumerator+cosineNumerator*cosineLower
def L : ℚ[X] := ∑j : Fin 22,C (P.coeff (j.val+1))*X^j.val

def negativeTailNorm (p : ℚ[X]) (start count : ℕ) (r : ℚ) : ℚ :=
  ∑j : Fin count,max 0 (-(p.coeff (j.val+start)))*r^(j.val+start-3)

/-! The kernel computes the integer coefficients of `P` (`PolyExpr`) and checks the coefficient
facts below on them. -/

/-- Unfold `P` into an expression. -/
local macro "reify" : tactic => `(tactic| simp only [P,constantNumerator,cosineNumerator,
  denominator,aP,betaP,deltaP,epsilonP,massAP,massBP,massDP,massHP,massEP,cosineLower,
  reify_C,reify_X,reify_one,reify_add,reify_sub,reify_mul,reify_pow])

/-- The negative tail of `L` against the budget: `L` has the coefficients of `P` shifted by one. -/
private def tailOK (e : PolyExpr) : Bool :=
  decide (tailSumZ (fun x => max 0 (-x)) 14 9 5 (11/50:ℚ).num.natAbs (11/50:ℚ).den e.z.l*
      (1/40000-(2163/1000000)*(11/50)^3:ℚ).den<
    (1/40000-(2163/1000000)*(11/50)^3:ℚ).num*((e.z.s*(11/50:ℚ).den^(14-1+5) : ℕ) : ℤ))

private def certOK (e : PolyExpr) : Bool :=
  coeffZero 0 e && (cmSeries 22 e && (coeffGt 1 (5947/100000000) e &&
    (coeffGt 2 (-(10203/10000000)) e && (coeffGt 3 (5211/1000000) e &&
    (coeffGt 4 (-(2193/500000)) e && (coeffGe 5 0 e && (coeffGe 6 0 e &&
    (coeffGt 7 (-(2163/1000000)) e && (coeffGe 8 0 e && tailOK e)))))))))

private theorem cert : ∃ e : PolyExpr, P=e.poly ∧ certOK e=true := by
  refine ⟨_,by reify; rfl,?_⟩
  decide +kernel

private theorem L_coeff (k : ℕ) (hk : k<22) : L.coeff k=P.coeff (k+1) := by
  simp only [L,finsetSum_coeff,coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single ⟨k,hk⟩]
  · simp
  · intro j _ hj
    rw [ite_eq_right_iff]
    intro h
    exact absurd (Fin.ext h.symm) hj
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem negative_tail_cubic {p : ℚ[X]} {start count : ℕ} {r : ℚ} {s : ℝ}
    (hstart : 3≤ start) (_hr : 0≤r) (hs : s∈Icc 0 (r:ℝ)) :
    -(negativeTailNorm p start count r:ℝ)*s^3≤aeval s (tail p start count) := by
  have hterm (j : Fin count) :
      -(max 0 (-(p.coeff (j.val+start))):ℝ)*(r:ℝ)^(j.val+start-3)*s^3≤
        (p.coeff (j.val+start):ℝ)*s^(j.val+start) := by
    have hco : -(max 0 (-(p.coeff (j.val+start))):ℝ)≤(p.coeff (j.val+start):ℝ) := by
      have hh : -(max 0 (-(p.coeff (j.val+start))))≤p.coeff (j.val+start) := by
        linarith [le_max_right 0 (-(p.coeff (j.val+start)))]
      exact_mod_cast hh
    have hn0 : (0:ℝ)≤(max 0 (-(p.coeff (j.val+start))):ℝ) := by
      exact_mod_cast (le_max_left 0 (-(p.coeff (j.val+start))))
    have hp := pow_le_pow_left₀ hs.1 hs.2 (j.val+start-3)
    have hm := mul_le_mul_of_nonneg_left hp hn0
    have hm' := mul_le_mul_of_nonneg_right hm (pow_nonneg hs.1 3)
    have hc := mul_le_mul_of_nonneg_right hco (pow_nonneg hs.1 (j.val+start))
    have hid : s^(j.val+start-3)*s^3=s^(j.val+start) := by
      rw [←pow_add]
      congr 1
      omega
    nlinarith [hid]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hterm j)
  simp only [tail,map_sum,map_mul,map_pow,aeval_C,aeval_X,eq_ratCast]
  have hn : (negativeTailNorm p start count r:ℝ)=
      ∑j : Fin count,(max 0 (-(p.coeff (j.val+start))):ℝ)*(r:ℝ)^(j.val+start-3) := by
    simp [negativeTailNorm]
  rw [hn]
  simpa only [neg_mul,Finset.sum_neg_distrib,Finset.sum_mul] using hsum

theorem P_factor : P=X*L := by
  obtain ⟨e,he,h⟩ := cert
  simp only [certOK,Bool.and_eq_true] at h
  have hdeg : P.natDegree<23 := by
    rw [he]
    have := natDegree_of_check h.2.1
    omega
  have h0 : P.coeff 0=0 := by rw [he]; exact coeff_zero_of_check h.1
  conv_lhs => rw [as_sum_range_C_mul_X_pow' P hdeg]
  rw [Finset.sum_range_succ',h0,map_zero,zero_mul,add_zero,← Fin.sum_univ_eq_sum_range,L,
    Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

theorem L_expansion :
    L=C (L.coeff 0)+C (L.coeff 1)*X+C (L.coeff 2)*X^2+C (L.coeff 3)*X^3+
      C (L.coeff 4)*X^4+C (L.coeff 5)*X^5+C (L.coeff 6)*X^6+
      C (L.coeff 7)*X^7+tail L 8 14 := by
  have hdeg : L.natDegree<22 := by
    have h : L.natDegree≤21 := by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro N hN
      simp only [L,finsetSum_coeff,coeff_C_mul_X_pow]
      refine Finset.sum_eq_zero (fun j _ => ?_)
      have := j.2
      rw [ite_eq_right_iff]
      intro h
      omega
    omega
  conv_lhs => rw [as_sum_range_C_mul_X_pow' L hdeg]
  rw [show (22:ℕ)=8+14 from rfl,Finset.sum_range_add,tail,
    Fin.sum_univ_eq_sum_range (fun j => C (L.coeff (j+8))*X^(j+8)) 14]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,pow_zero,pow_one,mul_one,zero_add]

theorem leading_reserves :
    (5947/100000000 : ℚ)<L.coeff 0 ∧
      -(10203/10000000 : ℚ)<L.coeff 1 ∧
      (5211/1000000 : ℚ)<L.coeff 2 ∧
      -(2193/500000 : ℚ)<L.coeff 3 ∧
      0≤L.coeff 4 ∧ 0≤L.coeff 5 ∧
      -(2163/1000000 : ℚ)<L.coeff 6 ∧ 0≤L.coeff 7 := by
  obtain ⟨e,he,h⟩ := cert
  simp only [certOK,Bool.and_eq_true] at h
  rw [L_coeff 0 (by norm_num),L_coeff 1 (by norm_num),L_coeff 2 (by norm_num),
    L_coeff 3 (by norm_num),L_coeff 4 (by norm_num),L_coeff 5 (by norm_num),
    L_coeff 6 (by norm_num),L_coeff 7 (by norm_num),he]
  exact ⟨coeff_gt_of_check h.2.2.1,coeff_gt_of_check h.2.2.2.1,coeff_gt_of_check h.2.2.2.2.1,
    coeff_gt_of_check h.2.2.2.2.2.1,coeff_ge_of_check h.2.2.2.2.2.2.1,
    coeff_ge_of_check h.2.2.2.2.2.2.2.1,coeff_gt_of_check h.2.2.2.2.2.2.2.2.1,
    coeff_ge_of_check h.2.2.2.2.2.2.2.2.2.1⟩

theorem tail_reserve :
    (2163/1000000 : ℚ)*(11/50)^3+negativeTailNorm L 8 14 (11/50)<1/40000 := by
  obtain ⟨e,he,h⟩ := cert
  simp only [certOK,Bool.and_eq_true] at h
  have hn : negativeTailNorm L 8 14 (11/50)=
      ∑ j : Fin 14,max 0 (-(e.poly.coeff (j.val+9)))*(11/50:ℚ)^(j.val+5) := by
    unfold negativeTailNorm
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [L_coeff _ (by omega),he,show j.val+8+1=j.val+9 by omega,show j.val+8-3=j.val+5 by omega]
  rw [hn,tailSum_eq (fun y => max 0 (-y)) (fun x => max 0 (-x)) negPart_div_pos e.rep
    e.scale_ne_zero 14 9 5 (by norm_num)]
  have ht := div_lt_of_int (Nat.mul_ne_zero e.scale_ne_zero (pow_ne_zero _ (11/50:ℚ).den_nz))
    (of_decide_eq_true h.2.2.2.2.2.2.2.2.2.2)
  linarith

def cubic (s : ℝ) : ℝ :=
  5947/100000000-(10203/10000000)*s+(5211/1000000)*s^2-(4411/1000000)*s^3

theorem cubic_lower {s : ℝ} (hs : s∈Icc 0 (11/50 : ℝ)) : cubic s≤aeval s L := by
  have hs' : s∈Icc 0 ((11/50:ℚ):ℝ) := by
    push_cast
    exact hs
  have ht := negative_tail_cubic (p := L) (start := 8) (count := 14)
    (by norm_num) (by norm_num : (0:ℚ)≤11/50) hs'
  have hc0 : (5947/100000000 : ℝ)≤(L.coeff 0:ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr leading_reserves.1.le
    push_cast at h
    exact h
  have hc1 : -(10203/10000000 : ℝ)≤(L.coeff 1:ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr leading_reserves.2.1.le
    push_cast at h
    exact h
  have hc2 : (5211/1000000 : ℝ)≤(L.coeff 2:ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr leading_reserves.2.2.1.le
    push_cast at h
    exact h
  have hc3 : -(2193/500000 : ℝ)≤(L.coeff 3:ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr leading_reserves.2.2.2.1.le
    push_cast at h
    exact h
  have hc4 : (0:ℝ)≤(L.coeff 4:ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr leading_reserves.2.2.2.2.1
    push_cast at h
    exact h
  have hc5 : (0:ℝ)≤(L.coeff 5:ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr leading_reserves.2.2.2.2.2.1
    push_cast at h
    exact h
  have hc6 : -(2163/1000000 : ℝ)≤(L.coeff 6:ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr leading_reserves.2.2.2.2.2.2.1.le
    push_cast at h
    exact h
  have hc7 : (0:ℝ)≤(L.coeff 7:ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr leading_reserves.2.2.2.2.2.2.2
    push_cast at h
    exact h
  have ht' : (2163/1000000 : ℝ)*(11/50)^3+(negativeTailNorm L 8 14 (11/50):ℝ)≤1/40000 := by
    have h := (Rat.cast_le (K := ℝ)).mpr tail_reserve.le
    push_cast at h
    exact h
  have h1 := mul_le_mul_of_nonneg_right hc1 hs.1
  have h2 := mul_le_mul_of_nonneg_right hc2 (pow_nonneg hs.1 2)
  have h3 := mul_le_mul_of_nonneg_right hc3 (pow_nonneg hs.1 3)
  have h4 := mul_nonneg hc4 (pow_nonneg hs.1 4)
  have h5 := mul_nonneg hc5 (pow_nonneg hs.1 5)
  have h6 := mul_le_mul_of_nonneg_right hc6 (pow_nonneg hs.1 6)
  have h6power := mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ hs.1 hs.2 3) (pow_nonneg hs.1 3)
  have h7 := mul_nonneg hc7 (pow_nonneg hs.1 7)
  have htail := mul_le_mul_of_nonneg_right ht' (pow_nonneg hs.1 3)
  have hid := congrArg (fun p : ℚ[X] => aeval s p) L_expansion
  simp only [map_add,map_mul,map_pow,aeval_C,aeval_X,eq_ratCast] at hid
  have h66 : s^3*s^3=s^6 := by ring
  dsimp [cubic]
  linarith

theorem cubic_positive {s : ℝ} (hs : s∈Icc 0 (11/50 : ℝ)) : 0<cubic s := by
  have hcoef : 0≤99529/50000000-(4411/1000000)*s := by linarith [hs.2]
  have hrem := mul_nonneg (sq_nonneg (s-11/100)) hcoef
  have hid : cubic s=
      4419059/1000000000000-(339993/10000000000)*(s-11/100)+
        (9/4000)*(s-11/100)^2+
        (s-11/100)^2*(99529/50000000-(4411/1000000)*s) := by
    dsimp [cubic]
    ring
  nlinarith [sq_nonneg (s-11/100-37777/5000000)]

theorem P_positive {s : ℝ} (hs : s∈Ioc 0 (11/50 : ℝ)) : 0<aeval s P := by
  have hl := (cubic_positive ⟨hs.1.le,hs.2⟩).trans_le (cubic_lower ⟨hs.1.le,hs.2⟩)
  rw [P_factor,map_mul,aeval_X]
  exact mul_pos hs.1 hl

theorem cosine_lower {s c : ℝ} (hs : s∈Icc 0 (11/50 : ℝ))
    (hc : 0≤c) (hunit : c^2+s^2=1) :
    (1-s^2/2-(13/100)*s^4)≤c := by
  have h2 := pow_le_pow_left₀ hs.1 hs.2 2
  have h4 := pow_le_pow_left₀ hs.1 hs.2 4
  have hpositive : 0≤1-s^2/2-(13/100)*s^4 := by nlinarith
  have hcoef : -(1/100 : ℝ)+(13/100)*s^2+(169/10000)*s^4≤0 := by nlinarith
  have hprod := mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hs.1 4) hcoef
  have hid : (1-s^2/2-(13/100)*s^4)^2-(1-s^2)=
      s^4*(-1/100+(13/100)*s^2+(169/10000)*s^4) := by ring
  nlinarith

end SquaresInCircles.Eight.AlignedGAEndpointPolynomial

module

public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2PositiveSlopes

/-!
# Eight squares: the positive D singleton in the negative-EH concentration

The coefficient interval contains both the fixed far-low H coefficient and the small-low H family.
The comparison `H_le_D` is non-strict at zero angle. It changes only a scalar minorant; the DE2
angle stays as it is.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeEH.PositiveD
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PairNormCalculus
open NegativeAPositiveTD.PositiveSlope

def reserve (k : ℝ) : ℝ := qCap*k^2-(k+2/5)^2*(1+k^2)
def reserveFirst (k : ℝ) : ℝ := -4*k^3-(12/5)*k^2+2*(qCap-29/25)*k-4/5
def reserveSecond (k : ℝ) : ℝ := -12*k^2-(24/5)*k+2*(qCap-29/25)

theorem reserve_derivative (k : ℝ) : HasDerivAt reserve (reserveFirst k) k := by
  have h2 : HasDerivAt (fun x : ℝ => x^2) (2*k) k := by simpa using hasDerivAt_pow 2 k
  have ha : HasDerivAt (fun x : ℝ => (x+2/5)^2) (2*(k+2/5)) k :=
    (((hasDerivAt_id' k).add_const (2/5)).fun_pow 2).congr_deriv (by norm_num)
  have h : HasDerivAt reserve
      (qCap*(2*k)-(2*(k+2/5)*(1+k^2)+(k+2/5)^2*(2*k))) k :=
    (h2.const_mul qCap).fun_sub (ha.fun_mul (h2.const_add 1))
  exact h.congr_deriv (by dsimp only [reserveFirst]; ring)

theorem reserveFirst_derivative (k : ℝ) : HasDerivAt reserveFirst (reserveSecond k) k := by
  have h2 : HasDerivAt (fun x : ℝ => x^2) (2*k) k := by simpa using hasDerivAt_pow 2 k
  have h3 : HasDerivAt (fun x : ℝ => x^3) (3*k^2) k := by simpa using hasDerivAt_pow 3 k
  have h : HasDerivAt reserveFirst
      (-4*(3*k^2)-(12/5)*(2*k)+2*(qCap-29/25)*1) k :=
    (((h3.const_mul (-4)).fun_sub (h2.const_mul (12/5))).fun_add
      ((hasDerivAt_id' k).const_mul (2*(qCap-29/25)))).sub_const (4/5)
  exact h.congr_deriv (by dsimp only [reserveSecond]; ring)

theorem reserve_positive {k : ℝ} (hk : k∈Icc (3/5:ℝ) (4/5)) : 0<reserve k := by
  have hc : ConcaveOn ℝ (Icc (3/5:ℝ) (4/5)) reserve := by
    apply concave_of_deriv2 (fun k _ => reserve_derivative k)
      (fun k _ => reserveFirst_derivative k)
    intro k hk
    have hk2 : (3/5:ℝ)^2≤k^2 := by nlinarith [hk.1]
    dsimp [reserveSecond,qCap]
    nlinarith [hk.1]
  exact concave_gt_of_endpoints hc hk
    (by norm_num [reserve,qCap]) (by norm_num [reserve,qCap])

theorem H_zero_slope {k : ℝ} (hk : k∈Icc (3/5:ℝ) (4/5)) : Ud k 1 0< -(2/5:ℝ) := by
  have hk0 : 0<k := by linarith [hk.1]
  have hn := pairNorm_pos (t:=0) hk0 (by norm_num : (0:ℝ)<1) (by norm_num [frameCap])
  have hn2 := pairNorm_sq (t:=0) hk0 (by norm_num : (0:ℝ)<1) (by norm_num [frameCap])
  simp only [pairEnergy,pairProduct,Real.sin_zero,mul_zero,add_zero,one_pow] at hn2
  have hpoly := reserve_positive hk
  have hR2 : R^2=qCap := Real.sq_sqrt (by norm_num [qCap])
  have hcross : (k+2/5)*pairNorm k 1 0<R*k := by
    have hR : 0<R := by linarith [Secondary.radius_bounds.1]
    dsimp [reserve] at hpoly
    have hsquare : ((k+2/5)*pairNorm k 1 0)^2<(R*k)^2 := by
      rw [mul_pow,mul_pow,hn2,hR2]
      nlinarith only [hpoly]
    nlinarith [mul_pos hR hk0]
  have hdiv := (lt_div_iff₀ hn).2 hcross
  rw [mul_div_assoc] at hdiv
  simp only [Ud,mixedPDerivative,normD1,pairProduct,sub_zero,Real.sin_zero,Real.cos_zero,
    mul_one,sub_self]
  linarith

theorem H_linear_upper {k t : ℝ} (hk : k∈Icc (3/5:ℝ) (4/5))
    (ht : t∈Icc 0 frameCap) : U R k 1 t≤-(2/5)*t := by
  have hk0 : 0<k := by linarith [hk.1]
  have hd (x : ℝ) (hx : x∈Icc 0 frameCap) :
      HasDerivAt (fun x => U R k 1 x+(2/5)*x) (Ud k 1 x+2/5) x := by
    have h3 : HasDerivAt (fun x : ℝ => (2/5)*x) (2/5) x := by
      simpa using (hasDerivAt_id x).const_mul (2/5:ℝ)
    exact (U_hasDerivAt hk0 (by norm_num) hx).fun_add h3
  have hm : AntitoneOn (fun x => U R k 1 x+(2/5)*x) (Icc 0 frameCap) := by
    apply antiOn_of_hasDeriv_nonpos
      (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
      (fun x hx => hd x (Ioo_subset_Icc_self hx))
    intro x hx
    have hh := Ud_antitone (q:=1) hk0 (by linarith [hk.2]) (by linarith [hk.1])
      (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) (Ioo_subset_Icc_self hx) hx.1.le
    linarith [H_zero_slope hk]
  have hh := hm (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) ht ht.1
  simp only [U_zero,mul_zero,add_zero] at hh
  linarith

theorem H_le_D {k t ε : ℝ} (hk : k∈Icc (3/5:ℝ) (4/5))
    (ht : t∈Icc 0 frameCap) :
    U R k 1 t-ε*t≤ -(GlobalGA.Secondary.diagonal-1/2+ε)*t := by
  have hh := H_linear_upper hk ht
  have hc := mul_le_mul_of_nonneg_right
    (show GlobalGA.Secondary.diagonal-1/2≤2/5 by linarith [diagonal_bounds.2]) ht.1
  nlinarith

end SquaresInCircles.Eight.GlobalGA.NegativeEH.PositiveD

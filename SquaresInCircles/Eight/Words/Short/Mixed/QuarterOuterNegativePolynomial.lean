module

public import SquaresInCircles.Eight.Words.Short.Mixed.QuarterOuterNegativeData

/-!
# Eight squares: the one polynomial curvature reserve for every core endpoint

The expansion is a single polynomial identity. Its odd
powers are bounded by absolute values and its remaining quadratic is
completed to a square on the whole height interval.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortWord.MixedQuarter.OuterNegative.Curvature
open CommonQuarter Arithmetic

def K0 : ℝ := 112479/100000
def E (u : ℝ) : ℝ := Q0*(K0-(u-1)^2)-u*(u-1)*(Q0-u^2)
def E1 (u : ℝ) : ℝ := 4*u^3-3*u^2-4*Q0*u+3*Q0
def E2 (u : ℝ) : ℝ := 12*u^2-6*u-4*Q0
def E3 (u : ℝ) : ℝ := 24*u-6
def A (u : ℝ) : ℝ := (13/20)/(767/1000)+(253/1000)*(u-1)
def P (u : ℝ) : ℝ := E u^2-A u^2*(Q0-u^2)^3

theorem E_hasDerivAt (u : ℝ) : HasDerivAt E (E1 u) u := by
  have h := (((hasDerivAt_const u K0).sub (((hasDerivAt_id' u).sub_const 1).pow 2)).const_mul
    Q0).sub (((hasDerivAt_id' u).mul ((hasDerivAt_id' u).sub_const 1)).mul
      ((hasDerivAt_const u Q0).sub ((hasDerivAt_id' u).pow 2)))
  exact h.congr_deriv (by simp only [E1]; norm_num; ring)
theorem E1_hasDerivAt (u : ℝ) : HasDerivAt E1 (E2 u) u := by
  have h := (((((hasDerivAt_id' u).pow 3).const_mul 4).sub
    (((hasDerivAt_id' u).pow 2).const_mul 3)).sub
      ((hasDerivAt_id' u).const_mul (4*Q0))).add_const (3*Q0)
  exact h.congr_deriv (by simp only [E2]; norm_num; ring)
theorem E2_hasDerivAt (u : ℝ) : HasDerivAt E2 (E3 u) u := by
  have h := ((((hasDerivAt_id' u).pow 2).const_mul 12).sub
    ((hasDerivAt_id' u).const_mul 6)).sub_const (4*Q0)
  exact h.congr_deriv (by simp only [E3]; norm_num; ring)
theorem E1_negative {u : ℝ} (hu : HeightRange u) : E1 u< -(389/100:ℝ) := by
  have hc : ConcaveOn ℝ (Icc (33/25) (17/10)) (fun u => -E1 u) :=
    concave_of_deriv2 (fun u _ => (E1_hasDerivAt u).neg)
      (fun u _ => (E2_hasDerivAt u).neg)
      (fun u hu => by dsimp [E3]; linarith [hu.1])
  have h := concave_gt_of_endpoints hc hu
    (show (389/100:ℝ)< -E1 (33/25) by norm_num [E1,Q0])
    (show (389/100:ℝ)< -E1 (17/10) by norm_num [E1,Q0])
  linarith
theorem E_antitone : AntitoneOn E (Icc (33/25) (17/10)) :=
  antiOn_of_hasDeriv_nonpos
    (fun u _ => (E_hasDerivAt u).continuousAt.continuousWithinAt)
    (fun u _ => E_hasDerivAt u)
    (fun u hu => by linarith [E1_negative (Ioo_subset_Icc_self hu)])
theorem E_positive {u : ℝ} (hu : HeightRange u) : (253/200:ℝ)<E u := by
  have h := E_antitone hu (show (17/10:ℝ)∈Icc (33/25) (17/10) by norm_num) hu.2
  have he : (253/200:ℝ)<E (17/10) := by norm_num [E,K0,Q0]
  linarith
theorem A_positive {u : ℝ} (hu : HeightRange u) : 0<A u := by
  dsimp [A]
  linarith [hu.1]

def e0 : ℝ := 27/16+Q0*(K0-1)
def e1 : ℝ := 27/4-3*Q0
def e2 : ℝ := 9-2*Q0
def a0 : ℝ := (13/20)/(767/1000)+253/2000
def a1 : ℝ := 253/1000
def z0 : ℝ := Q0-9/4
def c0 : ℝ := z0^3
def c1 : ℝ := -9*z0^2
def c2 : ℝ := 27*z0-3*z0^2
def c3 : ℝ := 18*z0-27
def c4 : ℝ := 3*z0-27
def c5 : ℝ := -9
def c6 : ℝ := -1
def p0 : ℝ := e0^2-a0^2*c0
def p1 : ℝ := 2*e0*e1-(a0^2*c1+2*a0*a1*c0)
def p2 : ℝ := e1^2+2*e0*e2-(a0^2*c2+2*a0*a1*c1+a1^2*c0)
def p3 : ℝ := 10*e0+2*e1*e2-(a0^2*c3+2*a0*a1*c2+a1^2*c1)
def p4 : ℝ := 2*e0+10*e1+e2^2-(a0^2*c4+2*a0*a1*c3+a1^2*c2)
def p5 : ℝ := 2*e1+10*e2-(a0^2*c5+2*a0*a1*c4+a1^2*c3)
def p6 : ℝ := 2*e2+25-(a0^2*c6+2*a0*a1*c5+a1^2*c4)
def p7 : ℝ := 10-(2*a0*a1*c6+a1^2*c5)
def p8 : ℝ := 1-a1^2*c6

theorem expansion (t : ℝ) :
    P (3/2+t)=p0+p1*t+p2*t^2+p3*t^3+p4*t^4+p5*t^5+p6*t^6+p7*t^7+p8*t^8 := by
  dsimp [P,E,A,p0,p1,p2,p3,p4,p5,p6,p7,p8,e0,e1,e2,a0,a1,z0,c0,c1,c2,c3,c4,c5,c6]
  ring

theorem coefficients :
    (3523/10000:ℝ)<p0 ∧ |p1|≤3401/10000 ∧ 72993/10000<p2 ∧
      |p3|≤921/100 ∧ -(27193/1000:ℝ)<p4 ∧ |p5|≤4177/200 ∧
        0≤p6 ∧ |p7|≤11069/1000 ∧ 0≤p8 := by
  norm_num [p0,p1,p2,p3,p4,p5,p6,p7,p8,e0,e1,e2,a0,a1,z0,c0,c1,c2,c3,c4,c5,c6,Q0,K0]

theorem signed_power_lower {c B t : ℝ} (hc : |c|≤B) (n : ℕ) : -B*|t|^n≤c*t^n := by
  have hp := mul_le_mul_of_nonneg_right hc (pow_nonneg (abs_nonneg t) n)
  have hneg := neg_abs_le (c*t^n)
  rw [abs_mul,abs_pow] at hneg
  linarith

theorem absolute_lower (t : ℝ) :
    (3523/10000:ℝ)-(3401/10000)*|t|+
      t^2*((72993/10000)-(921/100)*|t|-(27193/1000)*t^2-
        (4177/200)*|t|^3-(11069/1000)*|t|^5)<P (3/2+t) := by
  have hc := coefficients
  have h1 := signed_power_lower (t:=t) hc.2.1 1
  have h2 := mul_le_mul_of_nonneg_right hc.2.2.1.le (sq_nonneg t)
  have h3 := signed_power_lower (t:=t) hc.2.2.2.1 3
  have h4 := mul_le_mul_of_nonneg_right hc.2.2.2.2.1.le (by positivity : 0≤t^4)
  have h5 := signed_power_lower (t:=t) hc.2.2.2.2.2.1 5
  have h6 := mul_nonneg hc.2.2.2.2.2.2.1 (by positivity : 0≤t^6)
  have h7 := signed_power_lower (t:=t) hc.2.2.2.2.2.2.2.1 7
  have h8 := mul_nonneg hc.2.2.2.2.2.2.2.2 (by positivity : 0≤t^8)
  have ha2 : |t|^2=t^2 := sq_abs t
  have ha3 : |t|^3=t^2*|t| := by rw [pow_succ,ha2]
  have ha5 : |t|^5=t^2*|t|^3 := by rw [show 5=2+3 by rfl,pow_add,ha2]
  have ha7 : |t|^7=t^2*|t|^5 := by rw [show 7=2+5 by rfl,pow_add,ha2]
  rw [expansion]
  simp only [pow_one,ha3,ha5,ha7] at h1 h3 h5 h7 ⊢
  linarith [hc.1]

theorem brace_lower {t : ℝ} (ht : |t|≤1/5) :
    (419/100:ℝ)<(72993/10000)-(921/100)*|t|-(27193/1000)*t^2-
      (4177/200)*|t|^3-(11069/1000)*|t|^5 := by
  have ht2 := pow_le_pow_left₀ (abs_nonneg t) ht 2
  have ht3 := pow_le_pow_left₀ (abs_nonneg t) ht 3
  have ht5 := pow_le_pow_left₀ (abs_nonneg t) ht 5
  rw [sq_abs] at ht2
  norm_num at ht2 ht3 ht5
  linarith

theorem P_positive {u : ℝ} (hu : HeightRange u) : (69/200:ℝ)<P u := by
  let t := u-3/2
  have ht : |t|≤1/5 := abs_le.mpr ⟨by dsimp [t]; linarith [hu.1],by dsimp [t]; linarith [hu.2]⟩
  have hpoly := absolute_lower t
  have hbrace := mul_le_mul_of_nonneg_left (brace_lower ht).le (sq_nonneg t)
  have hsq := sq_nonneg ((419/50)*|t|-3401/10000)
  have ha2 : |t|^2=t^2 := sq_abs t
  have he : 3/2+t=u := by dsimp [t]; ring
  rw [he] at hpoly
  nlinarith

theorem radical_reserve {u : ℝ} (hu : HeightRange u) : A u*(v u)^3<E u := by
  have hv := height_v_bounds hu
  have he := source_v_square (height_source_domain hu)
  simp only [sub_add_cancel] at he
  have hE := E_positive hu
  have hA := A_positive hu
  have hP := P_positive hu
  have hp : 0≤A u*(v u)^3 := mul_nonneg hA.le (pow_nonneg (by linarith [hv.1]) 3)
  have hid : (A u*(v u)^3)^2=A u^2*(Q0-u^2)^3 := by
    calc
      _ = A u^2*((v u)^2)^3 := by ring
      _ = _ := by rw [he]
  dsimp [P] at hP
  nlinarith

/-- Equation (5), retaining the actual endpoint radius K. -/
theorem endpoint_second_lower {p q K u d2 : ℝ}
    (hq : (767/1000:ℝ)<q) (hp : p<(253/1000)*q) (hK : K0<K)
    (hu : HeightRange u)
    (hid : d2*(v u)^3=q*(Q0*(K-(u-1)^2)-u*(u-1)*(Q0-u^2))-p*(u-1)*(v u)^3) :
    (13/20:ℝ)<d2 := by
  have hv := height_v_bounds hu
  have hv3 : 0<(v u)^3 := pow_pos (by linarith [hv.1]) 3
  have hu1 : 0<u-1 := by linarith [hu.1]
  have hrad := mul_lt_mul_of_pos_left (radical_reserve hu) (show 0<q by linarith)
  have hp' := mul_lt_mul_of_pos_right hp (mul_pos hu1 hv3)
  have hk := mul_pos (mul_pos (show 0<q by linarith) (show 0<Q0 by norm_num [Q0]))
    (sub_pos.mpr hK)
  have hq' := mul_lt_mul_of_pos_right hq (show 0<(13/20:ℝ)/(767/1000) by norm_num)
  have hqv := mul_lt_mul_of_pos_right hq' hv3
  dsimp [A,E] at hrad
  have hprod : (13/20)*(v u)^3<d2*(v u)^3 := by nlinarith
  exact (mul_lt_mul_iff_of_pos_right hv3).mp hprod

end SquaresInCircles.Eight.ShortWord.MixedQuarter.OuterNegative.Curvature

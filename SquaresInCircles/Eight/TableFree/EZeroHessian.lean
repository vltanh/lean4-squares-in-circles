module

public import SquaresInCircles.Eight.TableFree.EZeroNested

/-!
# A uniform negative Hessian for the actual E-zero scalar

Uncompiled draft.  Both variables range over the single full square
[0,.11]^2.  The off-diagonal entry is positive and both row sums are less
than -.2, giving a negative quadratic-form bound for every direction.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.EZeroHessian
open EZeroFunctions EZeroNested

def F (e d : ℝ) : ℝ := h d+X e*Real.cos (e+d)-Y e*Real.sin (e+d)
def Fe (e d : ℝ) : ℝ :=
  (Xd e-Y e)*Real.cos (e+d)+(k e-X e)*Real.sin (e+d)
def Fd (e d : ℝ) : ℝ :=
  hd d-X e*Real.sin (e+d)-Y e*Real.cos (e+d)
def Fee (e d : ℝ) : ℝ :=
  (Xdd e+2*k e-X e)*Real.cos (e+d)+(Y e-l e-2*Xd e)*Real.sin (e+d)
def Fed (e d : ℝ) : ℝ :=
  (k e-X e)*Real.cos (e+d)+(Y e-Xd e)*Real.sin (e+d)
def Fdd (e d : ℝ) : ℝ := hdd d-X e*Real.cos (e+d)+Y e*Real.sin (e+d)
def T (e : ℝ) : ℝ := qCap/(r e)^3+qCap*Y e/(r e*(A e)^2*w e)
def J (e : ℝ) : ℝ := Xdd e+3*k e-2*X e
def K (e : ℝ) : ℝ := 2*Y e-l e-3*Xd e

theorem trig {e d : ℝ} (he : e∈Icc 0 (11/100 : ℝ)) (hd : d∈Icc 0 (11/100 : ℝ)) :
    (97/100 : ℝ)<Real.cos (e+d) ∧ Real.cos (e+d)≤1 ∧
      0≤Real.sin (e+d) ∧ Real.sin (e+d)≤11/50 := by
  have ha : e+d∈Icc 0 (11/50 : ℝ) := ⟨by linarith [he.1,hd.1],by linarith [he.2,hd.2]⟩
  have hc := Real.one_sub_sq_div_two_le_cos (x := e+d)
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi ha.1 (by linarith [ha.2,Real.pi_gt_three])
  have hsq := pow_le_pow_left₀ ha.1 ha.2 2
  exact ⟨by nlinarith,Real.cos_le_one _,hs,(Real.sin_le ha.1).trans ha.2⟩

theorem kr_bounds {e : ℝ} (he : e∈Icc 0 (11/100 : ℝ)) :
    (131/180 : ℝ)<k e/r e ∧ k e/r e<183/170 := by
  have hb := bounds he
  have hp := r_pos he
  exact ⟨(lt_div_iff₀ hp).2 (by linarith [hb.k_bounds.1,hb.r_bounds.2]),
    (div_lt_iff₀ hp).2 (by linarith [hb.k_bounds.2,hb.r_bounds.1])⟩

theorem T_lower {e : ℝ} (he : e∈Icc 0 (11/100 : ℝ)) : (127/100 : ℝ)<T e := by
  have hb := bounds he
  have hr := r_pos he
  have hw := w_pos he
  have hA : 0<A e := by linarith [hb.A_bounds.1]
  have hY : 0<Y e := by linarith [hb.Y_bounds.1]
  have hcube := pow_lt_pow_left₀ hb.r_bounds.2 hr.le (by decide : (3:ℕ)≠0)
  have hden : 0<r e*(A e)^2*w e := by positivity
  have hdenU : r e*(A e)^2*w e<(9/5 : ℝ)*3 := by
    have h1 := mul_lt_mul_of_pos_left (cubic_bound he) hr
    have h2 := mul_lt_mul_of_pos_right hb.r_bounds.2 (show (0:ℝ)<3 by norm_num)
    nlinarith
  have h1 : qCap/(9/5 : ℝ)^3<qCap/(r e)^3 :=
    div_lt_div_of_pos_left (by norm_num [qCap]) (pow_pos hr 3) hcube
  have h2 : qCap*(83/100 : ℝ)/((9/5)*3)<qCap*Y e/(r e*(A e)^2*w e) := by
    calc
      qCap*(83/100 : ℝ)/((9/5)*3)<qCap*Y e/((9/5)*3) :=
        div_lt_div_of_pos_right
          (mul_lt_mul_of_pos_left hb.Y_bounds.1 (by norm_num [qCap])) (by norm_num)
      _ < qCap*Y e/(r e*(A e)^2*w e) :=
        div_lt_div_of_pos_left (mul_pos (by norm_num [qCap]) hY) hden hdenU
  have hn : (127/100 : ℝ)<qCap/(9/5)^3+qCap*(83/100)/((9/5)*3) := by
    norm_num [qCap]
  dsimp [T]
  linarith

theorem J_identity {e : ℝ} (he : e∈Icc 0 (11/100 : ℝ)) :
    J e= -T e*(k e)^2+(Y e/r e)*(A e/w e)*hdd e-2*X e+3*k e := by
  have hA : A e≠0 := ne_of_gt (by linarith [(A_bounds he).1])
  dsimp [J,T,Xdd,l,k]
  field_simp [(r_pos he).ne',(w_pos he).ne',hA]
  ring

theorem J_upper {e : ℝ} (he : e∈Icc 0 (11/100 : ℝ)) :
    J e< -(2037503/9000000 : ℝ) := by
  have hb := bounds he
  have hr := r_pos he
  have hy : (83/180 : ℝ)<Y e/r e :=
    (lt_div_iff₀ hr).2 (by linarith [hb.Y_bounds.1,hb.r_bounds.2])
  have hpY : 0<Y e/r e := by linarith
  have hpA : 0<A e/w e := by linarith [hb.ratio_bounds.1]
  have hpH : (23/25 : ℝ)< -hdd e := by linarith [small_hdd he]
  have hp : (83/180 : ℝ)*(34/25)*(23/25)<
      (Y e/r e)*(A e/w e)*(-hdd e) := by
    calc
      (83/180 : ℝ)*(34/25)*(23/25) < (Y e/r e)*(34/25)*(23/25) := by
        nlinarith
      _ < (Y e/r e)*(A e/w e)*(23/25) := by
        have hm := mul_lt_mul_of_pos_left hb.ratio_bounds.1 hpY
        nlinarith
      _ < (Y e/r e)*(A e/w e)*(-hdd e) :=
        mul_lt_mul_of_pos_left hpH (mul_pos hpY hpA)
  have hk0 : 0<k e := by linarith [hb.k_bounds.1]
  have hT := mul_lt_mul_of_pos_right (T_lower he) (sq_pos_of_pos hk0)
  have hquad : -(127/100 : ℝ)*(k e)^2+3*k e≤
      -(127/100)*(131/100)^2+3*(131/100) := by
    nlinarith [sq_nonneg (k e-131/100),hb.k_bounds.1]
  rw [J_identity he]
  nlinarith [hb.X_bounds.1]

theorem K_negative {e : ℝ} (he : e∈Icc 0 (11/100 : ℝ)) : K e<0 := by
  have hb := bounds he
  have hx : 0<Xd e := div_pos
    (mul_pos (by linarith [hb.Y_bounds.1]) (by linarith [hb.k_bounds.1])) (r_pos he)
  dsimp [K]
  linarith [hb.Y_bounds.2,hb.l_lower]

theorem mixed_positive {e d : ℝ}
    (he : e∈Icc 0 (11/100 : ℝ)) (hd : d∈Icc 0 (11/100 : ℝ)) : 0<Fed e d := by
  have hb := bounds he
  obtain ⟨hc,hc1,hs,hs1⟩ := trig he hd
  have hkr := kr_bounds he
  have hY : 0≤Y e := by linarith [hb.Y_bounds.1]
  have hYs : 0≤Y e*Real.sin (e+d) := mul_nonneg hY hs
  have hYs1 : Y e*Real.sin (e+d)≤(101/100 : ℝ)*(11/50) :=
    mul_le_mul hb.Y_bounds.2.le hs1 hs (by norm_num)
  have hleft : (51/100 : ℝ)*(97/100)<(k e-X e)*Real.cos (e+d) := by
    have h1 := mul_lt_mul_of_pos_right
      (show (51/100 : ℝ)<k e-X e by linarith [hb.k_bounds.1,hb.X_bounds.2])
      (show 0<Real.cos (e+d) by linarith)
    nlinarith
  have hright0 := mul_le_mul_of_nonneg_right
    (show -(13/170 : ℝ)≤1-k e/r e by linarith [hkr.2]) hYs
  have hright1 := mul_le_mul_of_nonpos_left hYs1 (show -(13/170 : ℝ)≤0 by norm_num)
  have heq : Fed e d=(k e-X e)*Real.cos (e+d)+(1-k e/r e)*(Y e*Real.sin (e+d)) := by
    dsimp [Fed,Xd]
    ring
  rw [heq]
  nlinarith

theorem second_row {e d : ℝ}
    (he : e∈Icc 0 (11/100 : ℝ)) (hd : d∈Icc 0 (11/100 : ℝ)) :
    Fdd e d+Fed e d< -(1/5 : ℝ) := by
  have hb := bounds he
  obtain ⟨hc,hc1,hs,hs1⟩ := trig he hd
  have hkr := kr_bounds he
  have hcoeff : k e-2*X e<(43/100 : ℝ) := by linarith [hb.k_bounds.2,hb.X_bounds.1]
  have hfirst : (k e-2*X e)*Real.cos (e+d)≤43/100 := by
    by_cases hp : 0≤k e-2*X e
    · have hh := mul_le_mul_of_nonneg_left hc1 hp
      nlinarith
    · have hh := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hp) (by linarith : 0≤Real.cos (e+d))
      linarith
  have hY : 0≤Y e := by linarith [hb.Y_bounds.1]
  have hYs : 0≤Y e*Real.sin (e+d) := mul_nonneg hY hs
  have hYs1 : Y e*Real.sin (e+d)≤(101/100 : ℝ)*(11/50) :=
    mul_le_mul hb.Y_bounds.2.le hs1 hs (by norm_num)
  have hlast := mul_le_mul_of_nonneg_right
    (show 2-k e/r e≤2-131/180 by linarith [hkr.1]) hYs
  have hlast' := mul_le_mul_of_nonneg_left hYs1 (show (0:ℝ)≤2-131/180 by norm_num)
  have heq : Fdd e d+Fed e d=hdd d+(k e-2*X e)*Real.cos (e+d)+
      (2-k e/r e)*(Y e*Real.sin (e+d)) := by
    dsimp [Fdd,Fed,Xd]
    ring
  rw [heq]
  linarith [small_hdd hd]

theorem first_row {e d : ℝ}
    (he : e∈Icc 0 (11/100 : ℝ)) (hd : d∈Icc 0 (11/100 : ℝ)) :
    Fee e d+Fed e d< -(1/5 : ℝ) := by
  obtain ⟨hc,hc1,hs,hs1⟩ := trig he hd
  have hJ := J_upper he
  have hK := K_negative he
  have hterm0 := mul_nonpos_of_nonpos_of_nonneg hK.le hs
  have hterm1 := mul_lt_mul_of_pos_right hJ (show 0<Real.cos (e+d) by linarith)
  have heq : Fee e d+Fed e d=J e*Real.cos (e+d)+K e*Real.sin (e+d) := by
    dsimp [Fee,Fed,J,K]
    ring
  rw [heq]
  nlinarith

theorem quadratic_form {e d : ℝ}
    (he : e∈Icc 0 (11/100 : ℝ)) (hd : d∈Icc 0 (11/100 : ℝ)) (a b : ℝ) :
    Fee e d*a^2+2*Fed e d*a*b+Fdd e d*b^2≤ -(1/5 : ℝ)*(a^2+b^2) := by
  have h1 := mul_le_mul_of_nonneg_right (first_row he hd).le (sq_nonneg a)
  have h2 := mul_le_mul_of_nonneg_right (second_row he hd).le (sq_nonneg b)
  have h3 := mul_nonneg (mixed_positive he hd).le (sq_nonneg (a-b))
  nlinarith

theorem F_e_hasDerivAt {e d : ℝ} (he : e∈Icc 0 (11/100 : ℝ)) :
    HasDerivAt (fun z => F z d) (Fe e d) e := by
  have hc := (Real.hasDerivAt_cos (e+d)).comp e ((hasDerivAt_id e).add_const d)
  have hs := (Real.hasDerivAt_sin (e+d)).comp e ((hasDerivAt_id e).add_const d)
  have hh := ((hasDerivAt_const e (h d)).add ((X_hasDerivAt he).mul hc)).sub
    ((Y_hasDerivAt he).mul hs)
  convert hh using 1
  · rfl
  · dsimp [Fe]
    ring

theorem F_d_hasDerivAt {e d : ℝ} (hd : d∈Icc 0 (11/100 : ℝ)) :
    HasDerivAt (F e) (Fd e d) d := by
  have hc := (Real.hasDerivAt_cos (e+d)).comp d ((hasDerivAt_id d).const_add e)
  have hs := (Real.hasDerivAt_sin (e+d)).comp d ((hasDerivAt_id d).const_add e)
  have hh := ((h_hasDerivAt ⟨hd.1,by linarith [hd.2]⟩).add (hc.const_mul (X e))).sub
    (hs.const_mul (Y e))
  convert hh using 1
  · rfl
  · dsimp [Fd]
    ring

end SquaresInCircles.Eight.TableFree.EZeroHessian

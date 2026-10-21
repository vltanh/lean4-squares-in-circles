module

public import SquaresInCircles.Eight.TableFree.EZeroFunctions

/-!
# The two successive shared-circle eliminations in the E-zero bound

Uncompiled draft.  Every function below is the displayed radical obtained
from H--G--A--B.  The positive derivative quantities k and l are derived
from those functions, with uniform bounds on the single full interval.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.EZeroNested
open EZeroFunctions

def A (t : ℝ) : ℝ := 5/2-h t
def w (t : ℝ) : ℝ := Real.sqrt (qCap-(A t)^2)
def Y (t : ℝ) : ℝ := 2-w t
def r (t : ℝ) : ℝ := Real.sqrt (qCap-(Y t)^2)
def X (t : ℝ) : ℝ := r t-1
def k (t : ℝ) : ℝ := A t*hd t/w t
def l (t : ℝ) : ℝ := -A t*hdd t/w t+qCap*(hd t)^2/(w t)^3
def Xd (t : ℝ) : ℝ := Y t*k t/r t
def Xdd (t : ℝ) : ℝ := -qCap*(k t)^2/(r t)^3-Y t*l t/r t

structure Bounds (t : ℝ) : Prop where
  A_bounds : A t∈Ioo (799/500 : ℝ) (171/100)
  w_bounds : w t∈Ioo (199/200 : ℝ) (117/100)
  Y_bounds : Y t∈Ioo (83/100 : ℝ) (101/100)
  r_bounds : r t∈Ioo (17/10 : ℝ) (9/5)
  X_bounds : X t∈Ioo (7/10 : ℝ) (4/5)
  ratio_bounds : A t/w t∈Ioo (34/25 : ℝ) (43/25)
  k_bounds : k t∈Ioo (131/100 : ℝ) (183/100)
  l_lower : (7/2 : ℝ)<l t

theorem A_bounds {t : ℝ} (ht : t∈Icc 0 (11/100 : ℝ)) :
    A t∈Ioo (799/500 : ℝ) (171/100) := by
  have hh := small_h ht
  dsimp [A]
  exact ⟨by linarith,by linarith⟩

theorem w_pos {t : ℝ} (ht : t∈Icc 0 (11/100 : ℝ)) : 0<w t := by
  have hA := A_bounds ht
  have hA2 := pow_le_pow_left₀ (show 0≤A t by linarith [hA.1]) hA.2.le 2
  apply Real.sqrt_pos.mpr
  dsimp [qCap]
  nlinarith

theorem w_sq {t : ℝ} (ht : t∈Icc 0 (11/100 : ℝ)) :
    (w t)^2=qCap-(A t)^2 := by
  have hA := A_bounds ht
  apply Real.sq_sqrt
  have hA2 := pow_le_pow_left₀ (show 0≤A t by linarith [hA.1]) hA.2.le 2
  dsimp [qCap]
  nlinarith

theorem w_bounds {t : ℝ} (ht : t∈Icc 0 (11/100 : ℝ)) :
    w t∈Ioo (199/200 : ℝ) (117/100) := by
  have hA := A_bounds ht
  have hw := w_sq ht
  have hp := w_pos ht
  have hAl := pow_le_pow_left₀ (show (0:ℝ)≤799/500 by norm_num) hA.1.le 2
  have hAu := pow_le_pow_left₀ (show 0≤A t by linarith [hA.1]) hA.2.le 2
  dsimp [qCap] at hw
  exact ⟨by nlinarith,by nlinarith⟩

theorem Y_bounds {t : ℝ} (ht : t∈Icc 0 (11/100 : ℝ)) :
    Y t∈Ioo (83/100 : ℝ) (101/100) := by
  have hw := w_bounds ht
  dsimp [Y]
  exact ⟨by linarith,by linarith⟩

theorem r_pos {t : ℝ} (ht : t∈Icc 0 (11/100 : ℝ)) : 0<r t := by
  have hY := Y_bounds ht
  have hY2 := pow_le_pow_left₀ (show 0≤Y t by linarith [hY.1]) hY.2.le 2
  apply Real.sqrt_pos.mpr
  dsimp [qCap]
  nlinarith

theorem r_sq {t : ℝ} (ht : t∈Icc 0 (11/100 : ℝ)) :
    (r t)^2=qCap-(Y t)^2 := by
  have hY := Y_bounds ht
  have hY2 := pow_le_pow_left₀ (show 0≤Y t by linarith [hY.1]) hY.2.le 2
  apply Real.sq_sqrt
  dsimp [qCap]
  nlinarith

theorem r_bounds {t : ℝ} (ht : t∈Icc 0 (11/100 : ℝ)) :
    r t∈Ioo (17/10 : ℝ) (9/5) := by
  have hY := Y_bounds ht
  have hr := r_sq ht
  have hp := r_pos ht
  have hYl := pow_le_pow_left₀ (show (0:ℝ)≤83/100 by norm_num) hY.1.le 2
  have hYu := pow_le_pow_left₀ (show 0≤Y t by linarith [hY.1]) hY.2.le 2
  dsimp [qCap] at hr
  exact ⟨by nlinarith,by nlinarith⟩

theorem ratio_bounds {t : ℝ} (ht : t∈Icc 0 (11/100 : ℝ)) :
    A t/w t∈Ioo (34/25 : ℝ) (43/25) := by
  have hA := A_bounds ht
  have hw := w_bounds ht
  have hp := w_pos ht
  exact ⟨(lt_div_iff₀ hp).2 (by linarith),
    (div_lt_iff₀ hp).2 (by linarith)⟩

theorem k_bounds {t : ℝ} (ht : t∈Icc 0 (11/100 : ℝ)) :
    k t∈Ioo (131/100 : ℝ) (183/100) := by
  have hA := A_bounds ht
  have hw := w_bounds ht
  have hp := w_pos ht
  have hh := small_hd ht
  have hmulL := mul_lt_mul_of_pos_right hA.1 (show (0:ℝ)<24/25 by norm_num)
  have hmulL' := mul_lt_mul_of_pos_left hh.1 (show 0<A t by linarith [hA.1])
  have hmulU := mul_lt_mul_of_pos_left hh.2 (show 0<A t by linarith [hA.1])
  have hmulU' := mul_lt_mul_of_pos_right hA.2 (show (0:ℝ)<1063/1000 by norm_num)
  dsimp [k]
  exact ⟨(lt_div_iff₀ hp).2 (by linarith),
    (div_lt_iff₀ hp).2 (by linarith)⟩

theorem l_lower {t : ℝ} (ht : t∈Icc 0 (11/100 : ℝ)) : (7/2 : ℝ)<l t := by
  have hratio := ratio_bounds ht
  have hh := small_hd ht
  have hhh := small_hdd ht
  have hw := w_bounds ht
  have hwp := w_pos ht
  have h1 : (34/25 : ℝ)*(23/25)< -A t*hdd t/w t := by
    have ha := mul_lt_mul_of_pos_right hratio.1 (show (0:ℝ)<23/25 by norm_num)
    have hb := mul_lt_mul_of_pos_left (show (23/25 : ℝ)< -hdd t by linarith)
      (show 0<A t/w t by linarith [hratio.1])
    have he : (A t/w t)*(-hdd t)= -A t*hdd t/w t := by ring
    rw [he] at hb
    linarith
  have hsq : (24/25 : ℝ)^2<(hd t)^2 := by
    nlinarith [sq_nonneg (hd t-24/25)]
  have hcube : (w t)^3<(117/100 : ℝ)^3 :=
    pow_lt_pow_left₀ hwp.le hw.2 (by decide : (3:ℕ)≠0)
  have h2 : qCap*(24/25 : ℝ)^2/(117/100)^3<qCap*(hd t)^2/(w t)^3 := by
    calc
      qCap*(24/25 : ℝ)^2/(117/100)^3 < qCap*(hd t)^2/(117/100)^3 :=
        div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hsq (by norm_num [qCap])) (by norm_num)
      _ < qCap*(hd t)^2/(w t)^3 :=
        div_lt_div_of_pos_left (by positivity) (pow_pos hwp 3) hcube
  have hnum : (7/2 : ℝ)<(34/25)*(23/25)+qCap*(24/25)^2/(117/100)^3 := by
    norm_num [qCap]
  dsimp [l]
  linarith

theorem bounds {t : ℝ} (ht : t∈Icc 0 (11/100 : ℝ)) : Bounds t where
  A_bounds := A_bounds ht
  w_bounds := w_bounds ht
  Y_bounds := Y_bounds ht
  r_bounds := r_bounds ht
  X_bounds := by
    have hr := r_bounds ht
    dsimp [X]
    exact ⟨by linarith,by linarith⟩
  ratio_bounds := ratio_bounds ht
  k_bounds := k_bounds ht
  l_lower := l_lower ht

theorem A_hasDerivAt {t : ℝ} (ht : t∈Icc 0 (11/100 : ℝ)) :
    HasDerivAt A (-hd t) t :=
  (h_hasDerivAt ⟨ht.1,by linarith [ht.2]⟩).const_sub (5/2)

theorem w_hasDerivAt {t : ℝ} (ht : t∈Icc 0 (11/100 : ℝ)) :
    HasDerivAt w (k t) t := by
  have hr : qCap-(A t)^2≠0 := by nlinarith [w_sq ht,w_pos ht]
  have hh := (((A_hasDerivAt ht).pow 2).const_sub qCap).sqrt hr
  convert hh using 1
  · rfl
  · dsimp [k,w]
    field_simp [(w_pos ht).ne']
    ring

theorem Y_hasDerivAt {t : ℝ} (ht : t∈Icc 0 (11/100 : ℝ)) :
    HasDerivAt Y (-k t) t := (w_hasDerivAt ht).const_sub 2

theorem k_hasDerivAt {t : ℝ} (ht : t∈Icc 0 (11/100 : ℝ)) :
    HasDerivAt k (-l t) t := by
  have hh := ((A_hasDerivAt ht).mul
    (hd_hasDerivAt ⟨ht.1,by linarith [ht.2]⟩)).div
      (w_hasDerivAt ht) (w_pos ht).ne'
  convert hh using 1
  · rfl
  · dsimp [l,k]
    have hq : qCap=(w t)^2+(A t)^2 := by linarith [w_sq ht]
    rw [hq]
    field_simp [(w_pos ht).ne']
    ring

theorem r_hasDerivAt {t : ℝ} (ht : t∈Icc 0 (11/100 : ℝ)) :
    HasDerivAt r (Xd t) t := by
  have hr : qCap-(Y t)^2≠0 := by nlinarith [r_sq ht,r_pos ht]
  have hh := (((Y_hasDerivAt ht).pow 2).const_sub qCap).sqrt hr
  convert hh using 1
  · rfl
  · dsimp [Xd,r]
    field_simp [(r_pos ht).ne']
    ring

theorem X_hasDerivAt {t : ℝ} (ht : t∈Icc 0 (11/100 : ℝ)) :
    HasDerivAt X (Xd t) t := (r_hasDerivAt ht).sub_const 1

theorem Xd_hasDerivAt {t : ℝ} (ht : t∈Icc 0 (11/100 : ℝ)) :
    HasDerivAt Xd (Xdd t) t := by
  have hh := ((Y_hasDerivAt ht).mul (k_hasDerivAt ht)).div
    (r_hasDerivAt ht) (r_pos ht).ne'
  convert hh using 1
  · rfl
  · dsimp [Xd,Xdd]
    have hq : qCap=(r t)^2+(Y t)^2 := by linarith [r_sq ht]
    rw [hq]
    field_simp [(r_pos ht).ne']
    ring

/-- The unrestricted elementary cubic maximum, expressed as a square. -/
theorem cubic_bound {t : ℝ} (ht : t∈Icc 0 (11/100 : ℝ)) : (A t)^2*w t<3 := by
  have hw := w_pos ht
  have hA := A_bounds ht
  have hsq := w_sq ht
  have hfac : 0≤(qCap-3*(w t)^2)^2*(4*qCap-3*(w t)^2) := by
    apply mul_nonneg (sq_nonneg _)
    nlinarith [sq_nonneg (A t)]
  have he : 4*qCap^3-27*((A t)^2*w t)^2=
      (qCap-3*(w t)^2)^2*(4*qCap-3*(w t)^2) := by
    rw [show (A t)^2=qCap-(w t)^2 by linarith]
    ring
  have hn : 4*qCap^3<(243:ℝ) := by norm_num [qCap]
  have hp : 0≤(A t)^2*w t := mul_nonneg (sq_nonneg _) hw.le
  nlinarith

end SquaresInCircles.Eight.TableFree.EZeroNested

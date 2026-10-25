module

public import Mathlib.Algebra.Order.Star.Real
public import SquaresInCircles.Eight.Owners.CircleGeometry
public import SquaresInCircles.Eight.Owners.TrigonometricReserves

/-!
# Eight squares: A uniform negative Hessian for the actual E-zero scalar

Both variables range over the single full square
[0,.11]^2.  The off-diagonal entry is positive and both row sums are less
than -.2, giving a negative quadratic-form bound for every direction.
-/

section
/-!
## The shared E-zero endpoint functions on their complete domains

The two outer anchors are bounded using the same original E coordinate.
All derivative estimates below concern the displayed radical functions.
The strict second-derivative bound is proved by one polynomial positive-
square comparison on the whole interval; it needs no subdivision.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.EZeroFunctions

def v : ℝ := Real.sqrt (qCap-1/4)-1
def energy : ℝ := 1/4+v^2
def u (t : ℝ) : ℝ := 1+Real.cos t/2-v*Real.sin t
def j (t : ℝ) : ℝ := Real.sin t/2+v*Real.cos t
def rho (t : ℝ) : ℝ := Real.sqrt (qCap-(u t)^2)
def h (t : ℝ) : ℝ := rho t-1/2
def hd (t : ℝ) : ℝ := u t*j t/rho t
def numerator (x r : ℝ) : ℝ := -x^4+x^3+2*qCap*x^2-3*qCap*x+qCap*(1-r)
def hdd (t : ℝ) : ℝ :=
  ((u t*(u t-1)-(j t)^2)*(qCap-(u t)^2)-(u t)^2*(j t)^2)/(rho t)^3
def capped (t : ℝ) : ℝ := min (diagonalCoordinate qCap) (h t)

theorem v_bounds : (914575/1000000 : ℝ)<v ∧ v<914576/1000000 := by
  have hs := Real.sq_sqrt (show 0≤qCap-1/4 by norm_num [qCap])
  have hn := Real.sqrt_nonneg (qCap-1/4)
  dsimp [v,qCap] at *
  constructor <;> nlinarith

theorem energy_bounds : (679/625 : ℝ)<energy ∧ energy<21729/20000 := by
  have hv := v_bounds
  have hl := sq_nonneg (v-914575/1000000)
  have hu := mul_nonneg (show 0≤914576/1000000-v by linarith)
    (show 0≤914576/1000000+v by linarith)
  dsimp [energy]
  constructor <;> nlinarith

theorem uj_identity (t : ℝ) : (u t-1)^2+(j t)^2=energy := by
  dsimp [u,j,energy]
  linear_combination (v^2+1/4)*(Real.sin_sq_add_cos_sq t)

theorem u_hasDerivAt (t : ℝ) : HasDerivAt u (-j t) t := by
  have hh := (((Real.hasDerivAt_cos t).div_const 2).const_add 1).sub
    ((Real.hasDerivAt_sin t).const_mul v)
  convert hh using 1
  · rfl
  · dsimp [j]
    ring

theorem j_hasDerivAt (t : ℝ) : HasDerivAt j (u t-1) t := by
  convert ((Real.hasDerivAt_sin t).div_const 2).add
    ((Real.hasDerivAt_cos t).const_mul v) using 1
  · rfl
  · dsimp [u]
    ring

theorem uj_bounds {t : ℝ} (ht : t∈Icc 0 (7/10 : ℝ)) :
    0<u t ∧ u t≤3/2 ∧ 0<j t := by
  obtain ⟨hc,hc1,hs,hs1,_⟩ := transport_trig ht
  have hv := v_bounds
  have hvc := mul_pos (show 0<v by linarith) (show 0<Real.cos t by linarith)
  have hvs0 := mul_nonneg (show 0≤v by linarith) hs
  have hvs : v*Real.sin t≤(914576/1000000 : ℝ)*(6443/10000) :=
    mul_le_mul hv.2.le hs1.le hs (by norm_num)
  dsimp [u,j]
  exact ⟨by linarith,by linarith,by linarith⟩

theorem u_antitone : AntitoneOn u (Icc 0 (7/10 : ℝ)) := by
  apply antiOn_of_hasDeriv_nonpos
  · exact fun t _ => (u_hasDerivAt t).continuousAt.continuousWithinAt
  · exact fun t _ => u_hasDerivAt t
  · intro t ht
    exact neg_nonpos.mpr (uj_bounds (Ioo_subset_Icc_self ht)).2.2.le

theorem rho_pos {t : ℝ} (ht : t∈Icc 0 (7/10 : ℝ)) : 0<rho t := by
  have hu := uj_bounds ht
  apply Real.sqrt_pos.mpr
  dsimp [qCap]
  nlinarith [pow_le_pow_left₀ hu.1.le hu.2.1 2]

theorem rho_sq {t : ℝ} (ht : t∈Icc 0 (7/10 : ℝ)) :
    (rho t)^2=qCap-(u t)^2 := by
  apply Real.sq_sqrt
  have hu := uj_bounds ht
  dsimp [qCap]
  nlinarith [pow_le_pow_left₀ hu.1.le hu.2.1 2]

theorem rho_hasDerivAt {t : ℝ} (ht : t∈Icc 0 (7/10 : ℝ)) :
    HasDerivAt rho (hd t) t := by
  have hr : qCap-(u t)^2≠0 := by
    have hh := rho_sq ht
    have hp := rho_pos ht
    nlinarith
  have hh := (((u_hasDerivAt t).pow 2).const_sub qCap).sqrt hr
  convert hh using 1
  · rfl
  · dsimp [hd,rho]
    field_simp [(rho_pos ht).ne']

theorem h_hasDerivAt {t : ℝ} (ht : t∈Icc 0 (7/10 : ℝ)) :
    HasDerivAt h (hd t) t := (rho_hasDerivAt ht).sub_const (1/2)

theorem hd_pos {t : ℝ} (ht : t∈Icc 0 (7/10 : ℝ)) : 0<hd t :=
  div_pos (mul_pos (uj_bounds ht).1 (uj_bounds ht).2.2) (rho_pos ht)

theorem h_monotone : MonotoneOn h (Icc 0 (7/10 : ℝ)) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun t ht => (h_hasDerivAt ht).continuousAt.continuousWithinAt
  · exact fun t ht => h_hasDerivAt (Ioo_subset_Icc_self ht)
  · exact fun t ht => (hd_pos (Ioo_subset_Icc_self ht)).le

theorem hd_hasDerivAt {t : ℝ} (ht : t∈Icc 0 (7/10 : ℝ)) :
    HasDerivAt hd (hdd t) t := by
  have hh := ((u_hasDerivAt t).mul (j_hasDerivAt t)).div
    (rho_hasDerivAt ht) (rho_pos ht).ne'
  convert hh using 1
  · rfl
  · dsimp [hd,hdd]
    rw [← rho_sq ht]
    field_simp [(rho_pos ht).ne']
    ring

theorem hdd_formula (t : ℝ) : hdd t=numerator (u t) energy/(rho t)^3 := by
  have hj : (j t)^2=energy-(u t-1)^2 := by linarith [uj_identity t]
  unfold hdd
  rw [hj]
  congr 1
  dsimp [numerator]
  ring

theorem small_u {t : ℝ} (ht : t∈Icc 0 (11/100 : ℝ)) :
    (2793/2000 : ℝ)<u t ∧ u t≤3/2 := by
  have ht' : t∈Icc 0 (7/10 : ℝ) := ⟨ht.1,by linarith [ht.2]⟩
  have hm := u_antitone ht' (show (11/100 : ℝ)∈Icc 0 (7/10) by norm_num) ht.2
  have hb := trig_bracket (l := (11/100 : ℝ)) (u := (11/100 : ℝ))
    (by norm_num) (by linarith [Real.pi_gt_three]) (by constructor <;> rfl)
  have hs0 := (transport_trig (show (11/100 : ℝ)∈Icc 0 (7/10) by norm_num)).2.2.1
  have hv := v_bounds
  have hprod := mul_le_mul (show v≤4573/5000 by linarith) hb.2.1 hs0 (by norm_num)
  have he : (2793/2000 : ℝ)<
      1+(1-(11/100 : ℝ)^2/2+(11/100 : ℝ)^4/24-(11/100 : ℝ)^6/720)/2-
        (4573/5000)*((11/100 : ℝ)-(11/100 : ℝ)^3/6+(11/100 : ℝ)^5/120) := by
    norm_num
  refine ⟨?_,(uj_bounds ht').2.1⟩
  have hu : u (11/100)=1+Real.cos (11/100)/2-v*Real.sin (11/100) := rfl
  linarith [hb.2.2.1]

theorem small_h {t : ℝ} (ht : t∈Icc 0 (11/100 : ℝ)) :
    (79/100 : ℝ)<h t ∧ h t<451/500 := by
  have ht' : t∈Icc 0 (7/10 : ℝ) := ⟨ht.1,by linarith [ht.2]⟩
  have hu := small_u ht
  have hr := rho_sq ht'
  have hp := rho_pos ht'
  have hu2 := pow_le_pow_left₀ (show 0≤u t by linarith [hu.1]) hu.2 2
  have hl2 := pow_le_pow_left₀ (show (0:ℝ)≤2793/2000 by norm_num) hu.1.le 2
  dsimp [h,qCap] at *
  constructor <;> nlinarith

/-- Elementary whole-interval power bound used in the three comparisons. -/
theorem power_linear {x r : ℝ} (hx : 0≤x) (hxr : x≤r) (n : ℕ) :
    x^(n+1)≤r^n*x := by
  have hp := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx hxr n) hx
  simpa [pow_succ] using hp

theorem curvature_square {x : ℝ} (hx : x∈Icc (139/100 : ℝ) (3/2)) :
    numerator x (679/625)<0 ∧
      (23/25 : ℝ)^2*(qCap-x^2)^3<(numerator x (679/625))^2 := by
  let z := x-139/100
  have hz : z∈Icc 0 (11/100 : ℝ) := ⟨by dsimp [z]; linarith [hx.1],by dsimp [z]; linarith [hx.2]⟩
  have hz2 := power_linear hz.1 hz.2 1
  have hz4 := power_linear hz.1 hz.2 3
  have hz5 := power_linear hz.1 hz.2 4
  have hN : numerator x (679/625)=
      -258308973/100000000+(15868/3125)*z+(2043/5000)*z^2-(114/25)*z^3-z^4 := by
    dsimp [numerator,qCap,z]
    ring
  have hP : (numerator x (679/625))^2-(23/25 : ℝ)^2*(qCap-x^2)^3=
      673609609660729/10000000000000000+(962071234629/625000000000)*z-
      (1315365385859/250000000000)*z^2+(11180768369/625000000)*z^3-
      (263885877/10000000)*z^4-(106609/15625)*z^5+
      (52057/2500)*z^6+(228/25)*z^7+z^8 := by
    dsimp [numerator,qCap,z]
    ring
  refine ⟨?_,?_⟩
  · rw [hN]
    nlinarith [pow_nonneg hz.1 3,pow_nonneg hz.1 4]
  · have hp : 0<(numerator x (679/625))^2-(23/25 : ℝ)^2*(qCap-x^2)^3 := by
      rw [hP]
      nlinarith [pow_nonneg hz.1 3,pow_nonneg hz.1 6,
        pow_nonneg hz.1 7,pow_nonneg hz.1 8]
    linarith

theorem first_lower_square {x : ℝ} (hx : x∈Icc (2793/2000 : ℝ) (3/2)) :
    (24/25 : ℝ)^2*(qCap-x^2)<x^2*((679/625)-(x-1)^2) := by
  let z := x-2793/2000
  have hz : z∈Icc 0 (11/100 : ℝ) := ⟨by dsimp [z]; linarith [hx.1],by dsimp [z]; linarith [hx.2]⟩
  have hp2 := power_linear hz.1 hz.2 1
  have hp3 := power_linear hz.1 hz.2 2
  have hp4 := power_linear hz.1 hz.2 3
  have he : x^2*((679/625)-(x-1)^2)-(24/25 : ℝ)^2*(qCap-x^2)=
      12991715199/16000000000000+(7245463743/2000000000)*z-
        (4628547/2000000)*z^2-(1793/500)*z^3-z^4 := by
    dsimp [qCap,z]
    ring
  have hp : 0<x^2*((679/625)-(x-1)^2)-(24/25 : ℝ)^2*(qCap-x^2) := by
    rw [he]
    nlinarith
  linarith

theorem first_upper_square {x : ℝ} (hx : x∈Icc (139/100 : ℝ) (3/2)) :
    x^2*((21729/20000)-(x-1)^2)<(1063/1000 : ℝ)^2*(qCap-x^2) := by
  let z := 3/2-x
  have hz : z∈Icc 0 (11/100 : ℝ) := ⟨by dsimp [z]; linarith [hx.2],by dsimp [z]; linarith [hx.1]⟩
  have hp3 : z^3≤(11/100)^2*z := power_linear hz.1 hz.2 2
  have he : (1063/1000 : ℝ)^2*(qCap-x^2)-x^2*((21729/20000)-(x-1)^2)=
      79833/1250000000+(3649257/1000000)*z+
        (3283581/1000000)*z^2-4*z^3+z^4 := by
    dsimp [qCap,z]
    ring
  have hp : 0<(1063/1000 : ℝ)^2*(qCap-x^2)-x^2*((21729/20000)-(x-1)^2) := by
    rw [he]
    nlinarith [pow_nonneg hz.1 4,sq_nonneg z,hz.1]
  linarith

theorem small_hd {t : ℝ} (ht : t∈Icc 0 (11/100 : ℝ)) :
    (24/25 : ℝ)<hd t ∧ hd t<1063/1000 := by
  have ht' : t∈Icc 0 (7/10 : ℝ) := ⟨ht.1,by linarith [ht.2]⟩
  have hu := small_u ht
  have hp := uj_bounds ht'
  have hr := rho_sq ht'
  have hrp := rho_pos ht'
  have hj := uj_identity t
  have he := energy_bounds
  have hL := first_lower_square ⟨hu.1.le,hu.2⟩
  have hU := first_upper_square ⟨by linarith [hu.1],hu.2⟩
  have heL := mul_le_mul_of_nonneg_left he.1.le (sq_nonneg (u t))
  have heU := mul_le_mul_of_nonneg_left he.2.le (sq_nonneg (u t))
  have hprod : 0<u t*j t := mul_pos hp.1 hp.2.2
  have hprod_sq : (u t*j t)^2=(u t)^2*(energy-(u t-1)^2) := by
    rw [mul_pow,show (j t)^2=energy-(u t-1)^2 by linarith]
  have hprodL : (24/25 : ℝ)*rho t<u t*j t := by
    by_contra! hcon
    have h1 := mul_le_mul_of_nonneg_left hcon hprod.le
    have h2 := mul_le_mul_of_nonneg_left hcon hrp.le
    generalize qCap = Q at hr hL
    linarith
  have hprodU : u t*j t<(1063/1000 : ℝ)*rho t := by
    by_contra! hcon
    have h1 := mul_le_mul_of_nonneg_left hcon hprod.le
    have h2 := mul_le_mul_of_nonneg_left hcon hrp.le
    generalize qCap = Q at hr hU
    linarith
  dsimp [hd]
  exact ⟨(lt_div_iff₀ hrp).2 hprodL,(div_lt_iff₀ hrp).2 hprodU⟩

theorem small_hdd {t : ℝ} (ht : t∈Icc 0 (11/100 : ℝ)) : hdd t< -(23/25 : ℝ) := by
  have ht' : t∈Icc 0 (7/10 : ℝ) := ⟨ht.1,by linarith [ht.2]⟩
  have hu := small_u ht
  have hr := rho_sq ht'
  have hrp := rho_pos ht'
  have hsq := curvature_square ⟨by linarith [hu.1],hu.2⟩
  have hN : numerator (u t) energy≤numerator (u t) (679/625) := by
    have he := energy_bounds.1
    dsimp [numerator,qCap]
    linarith
  have hr3 : 0<(rho t)^3 := pow_pos hrp 3
  have hpow : (qCap-(u t)^2)^3=((rho t)^3)^2 := by rw [← hr]; ring
  rw [hpow] at hsq
  have hc : (23/25 : ℝ)*(rho t)^3< -numerator (u t) (679/625) := by
    nlinarith [sq_nonneg (numerator (u t) (679/625)+(23/25)*(rho t)^3)]
  rw [hdd_formula]
  apply (div_lt_iff₀ hr3).2
  linarith

end SquaresInCircles.Eight.EZeroFunctions
end
end
end

section
/-!
## The two successive shared-circle eliminations in the E-zero bound

Every function below is the displayed radical obtained
from H--G--A--B.  The positive derivative quantities k and l are derived
from those functions, with uniform bounds on the single full interval.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.EZeroNested
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
  exact ⟨by linarith [hw.2],by linarith [hw.1]⟩

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
  exact ⟨(lt_div_iff₀ hp).2 (by linarith [hA.1,hw.2]),
    (div_lt_iff₀ hp).2 (by linarith [hA.2,hw.1])⟩

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
  exact ⟨(lt_div_iff₀ hp).2 (by linarith [hw.2]),
    (div_lt_iff₀ hp).2 (by linarith [hw.1])⟩

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
    nlinarith [sq_nonneg (hd t-24/25),hh.1]
  have hcube : (w t)^3<(117/100 : ℝ)^3 :=
    pow_lt_pow_left₀ hw.2 hwp.le (by decide : (3:ℕ)≠0)
  have h2 : qCap*(24/25 : ℝ)^2/(117/100)^3<qCap*(hd t)^2/(w t)^3 := by
    calc
      qCap*(24/25 : ℝ)^2/(117/100)^3 < qCap*(hd t)^2/(117/100)^3 :=
        div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hsq (by norm_num [qCap])) (by norm_num)
      _ < qCap*(hd t)^2/(w t)^3 :=
        div_lt_div_of_pos_left
          (mul_pos (by norm_num [qCap]) (sq_pos_of_pos (by linarith [hh.1])))
          (pow_pos hwp 3) hcube
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
    exact ⟨by linarith [hr.1],by linarith [hr.2]⟩
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

end SquaresInCircles.Eight.EZeroNested
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.EZeroHessian
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

end SquaresInCircles.Eight.EZeroHessian
end
end
end

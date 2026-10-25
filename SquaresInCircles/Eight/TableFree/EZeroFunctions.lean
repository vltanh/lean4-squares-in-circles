module

public import SquaresInCircles.Eight.TableFree.HighOrderTaylor
public import SquaresInCircles.Eight.TableFree.HardSplitCap

/-!
# The shared E-zero endpoint functions on their complete domains

Uncompiled draft, following the coupled aligned E-zero exclusion.
The two outer anchors are bounded using the same original E coordinate.
All derivative estimates below concern the displayed radical functions.
The strict second-derivative bound is proved by one polynomial positive-
square comparison on the whole interval; it needs no subdivision.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.EZeroFunctions

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

end SquaresInCircles.Eight.TableFree.EZeroFunctions

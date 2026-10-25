module

public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.TotallySplit
public import SquaresInCircles.Eight.Owners.GA.Joint.NegativeAETD2CommonBounds
public import SquaresInCircles.Eight.Owners.GA.Joint.NegativeAETD2CommonTaylor

/-!
# Eight squares: the symmetric second-derivative envelope and uncharged allocation

The secant angles range continuously over their complete total
interval. The bound keeps the reserve depending on the unused angle.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.JointNegativeAETD2.CommonGain
open Candidate Secondary

theorem B_positive (k : ℝ) {y : ℝ} (hy : y∈Icc (0:ℝ) (129/200)) : 0<shapeB k y := by
  have hy2 : y^2≤(129/200:ℝ)^2 := by nlinarith [hy.1,hy.2]
  have he : shapeB k y=1+y^2+k^2*(1-y^2)*(1+2*y^2) := by dsimp [shapeB]; ring
  rw [he]
  have hp := mul_nonneg (mul_nonneg (sq_nonneg k) (by linarith : 0≤1-y^2))
    (show 0≤1+2*y^2 by positivity)
  linarith [sq_nonneg y]

theorem high_factor {x : ℝ} (hx : x∈Icc 0 frameCap) :
    D (751/1000) x=Real.sqrt (1564001/1000000)*
      inverseRoot ((564001/1564001)*Real.sin x^2) := by
  have hy := sine_domain hx
  have hv : (564001/1564001)*Real.sin x^2<1 := by nlinarith [hy.1,hy.2]
  have hS : 0<Real.sqrt (1564001/1000000:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hS2 := Real.sq_sqrt (show (0:ℝ)≤1564001/1000000 by norm_num)
  have hv2 := inverseRoot_square hv
  have hp := mul_pos hS (inverseRoot_positive hv)
  have he : (Real.sqrt (1564001/1000000:ℝ)*inverseRoot ((564001/1564001)*Real.sin x^2))^2=
      (D (751/1000) x)^2 := by rw [mul_pow,hS2,hv2,D_shape]; dsimp [shapeA]; ring
  nlinarith [D_positive (751/1000) x]

theorem high_radius_ratio : (6323/6250:ℝ)<R/(Real.sqrt (1564001/1000000:ℝ))^3 := by
  have hs : 0<Real.sqrt (1564001/1000000:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hs2 := Real.sq_sqrt (show (0:ℝ)≤1564001/1000000 by norm_num)
  have hs6 : (Real.sqrt (1564001/1000000:ℝ)^3)^2=(1564001/1000000:ℝ)^3 := by
    rw [←pow_mul,show 3*2=2*3 by norm_num,pow_mul,hs2]
  have hr : R^2=9789/2500 := Secondary.radius_sq
  have hsq : ((6323/6250)*Real.sqrt (1564001/1000000:ℝ)^3)^2<R^2 := by
    rw [mul_pow,hs6,hr]
    norm_num
  have hbound := lt_of_pow_lt_pow_left₀ 2 (Real.sqrt_nonneg _) hsq
  exact (lt_div_iff₀ (pow_pos hs 3)).2 hbound

theorem high_inverse_lower {x : ℝ} (hx : x∈Icc 0 frameCap) :
    (6323/6250)*L2 ((564001/1564001)*Real.sin x^2)<R/(D (751/1000) x)^3 := by
  let v := (564001/1564001)*Real.sin x^2
  have hy := sine_domain hx
  have hv : 0≤v := by dsimp [v]; positivity
  have hv1 : v<1 := by dsimp [v]; nlinarith [hy.1,hy.2]
  have hL := inverse_three_lower hv hv1
  have hroot := inverseRoot_positive hv1
  have hfirst := mul_le_mul_of_nonneg_left hL (show (0:ℝ)≤6323/6250 by norm_num)
  have hsecond := mul_lt_mul_of_pos_right high_radius_ratio
    (show 0<1/(inverseRoot v)^3 by positivity)
  have hh := hfirst.trans_lt hsecond
  rw [high_factor hx,mul_pow]
  calc (6323/6250)*L2 ((564001/1564001)*Real.sin x^2)
      <R/(Real.sqrt (1564001/1000000:ℝ))^3*(1/(inverseRoot v)^3) := hh
    _=R/((Real.sqrt (1564001/1000000:ℝ))^3*(inverseRoot ((564001/1564001)*Real.sin x^2))^3) := by
      rw [div_mul_div_comm,mul_one]

theorem second_envelope {x : ℝ} (hx : x∈Icc 0 frameCap) : F2 (751/1000) x<E2 x := by
  have hj := actual_J_positive hx
  rw [jNative_formula] at hj
  have hB := B_positive (751/1000) (sine_domain hx)
  have hr := mul_lt_mul_of_pos_right (high_inverse_lower hx) hB
  have hc : 0<Real.cos x := by linarith [(transport_trig hx).1]
  dsimp [F2]
  apply (div_lt_iff₀ (pow_pos hc 3)).2
  have he : R*shapeB (751/1000) (Real.sin x)/(D (751/1000) x)^3=
      (R/(D (751/1000) x)^3)*shapeB (751/1000) (Real.sin x) := by ring
  rw [he]
  nlinarith

theorem symmetric_envelope (x : ℝ) :
    E2 x+E2 (frameCap-x)= -1/125-(1/5)*(x-7/20)^2 := by
  dsimp [E2,frameCap]
  ring

theorem second_sum {k r s : ℝ} (hk : k∈Icc (13/20:ℝ) (751/1000))
    (hr : 0≤r) (hs : 0≤ s) (ht : r+s≤frameCap) :
    F2 k r+F2 k s< -1/125-(11/10)*(frameCap-r-s) := by
  have hr' : r∈Icc 0 frameCap := ⟨hr,by linarith⟩
  have hs' : s∈Icc 0 frameCap := ⟨hs,by linarith⟩
  have hc' : frameCap-r∈Icc 0 frameCap := ⟨by linarith [hr'.2],by linarith⟩
  have hmr := (parameter_monotonicity hr').2.1 hk ⟨by norm_num,le_rfl⟩ hk.2
  have hms := (parameter_monotonicity hs').2.1 hk ⟨by norm_num,le_rfl⟩ hk.2
  have hg := derivative_reserve
    (f:=F2 (751/1000)) (df:=F3 (751/1000))
    (l:=0) (u:=frameCap) (k:=(11/10:ℝ))
    (fun x hx => (F2_derivative (k:=(751/1000:ℝ)) hx).continuousAt.continuousWithinAt)
    (fun x hx => F2_derivative (Ioo_subset_Icc_self hx))
    (fun x hx => (third_lower (show (751/1000:ℝ)∈Icc (13/20:ℝ) (751/1000) by norm_num)
      (Ioo_subset_Icc_self hx)).le)
    hs' hc' (by linarith)
  have hleft := second_envelope hr'
  have hright := second_envelope hc'
  have he := symmetric_envelope r
  nlinarith [sq_nonneg (r-7/20)]

theorem second_negative_short {k x : ℝ} (hk : k∈Icc (13/20:ℝ) (751/1000))
    (hx : x∈Icc (0:ℝ) (3/20)) : F2 k x<0 := by
  have hx' : x∈Icc 0 frameCap := ⟨hx.1,by norm_num [frameCap]; linarith [hx.2]⟩
  have hm := (parameter_monotonicity hx').2.1 hk ⟨by norm_num,le_rfl⟩ hk.2
  have he := second_envelope hx'
  have hu : x-7/20≤0 := by linarith [hx.2]
  have hc : (x-7/20)^3≤0 := by
    have hh := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (x-7/20)) hu
    simpa only [pow_succ] using hh
  have hE : E2 x<0 := by dsimp [E2]; nlinarith [sq_nonneg (x-7/20)]
  linarith

theorem growth {k x y : ℝ} (hk : (13/20:ℝ)≤k)
    (hx : x∈Icc 0 frameCap) (hy : y∈Icc 0 frameCap) (hxy : x≤y) :
    (9/10)*(y-x)≤F k y-F k x := by
  exact derivative_reserve (f:=F k) (df:=F1 k)
    (fun t ht => (F_derivative (k:=k) ht).continuousAt.continuousWithinAt)
    (fun t ht => F_derivative (Ioo_subset_Icc_self ht))
    (fun t ht => (first_lower hk (Ioo_subset_Icc_self ht)).le) hx hy hxy

theorem merge_concave {k S : ℝ} (hk : k∈Icc (13/20:ℝ) (751/1000))
    (hS : S∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc 0 S) (fun r => F k r+F k (S-r)) := by
  have hd (r : ℝ) (hr : r∈Icc 0 S) :
      HasDerivAt (fun r => F k r+F k (S-r)) (F1 k r-F1 k (S-r)) r := by
    have hleft := F_derivative (k:=k) ⟨hr.1,hr.2.trans hS.2⟩
    have hright := (F_derivative (k:=k) (x:=S-r) ⟨by linarith [hr.2],by linarith [hS.2,hr.1]⟩).comp r
      ((hasDerivAt_id' r).const_sub S)
    exact (hleft.fun_add hright).congr_deriv (by ring)
  have hdd (r : ℝ) (hr : r∈Icc 0 S) :
      HasDerivAt (fun r => F1 k r-F1 k (S-r)) (F2 k r+F2 k (S-r)) r := by
    have hleft := F1_derivative (k:=k) ⟨hr.1,hr.2.trans hS.2⟩
    have hright := (F1_derivative (k:=k) (x:=S-r) ⟨by linarith [hr.2],by linarith [hS.2,hr.1]⟩).comp r
      ((hasDerivAt_id' r).const_sub S)
    exact (hleft.fun_sub hright).congr_deriv (by ring)
  apply concave_of_deriv2 hd hdd
  intro r hr
  have hh := second_sum hk hr.1 (show 0≤S-r by linarith [hr.2]) (by linarith [hS.2])
  have hS2 := hS.2
  simp only [frameCap] at hh hS2
  linarith

theorem merge {k r s : ℝ} (hk : k∈Icc (13/20:ℝ) (751/1000))
    (hr : 0≤r) (hs : 0≤ s) (ht : r+s≤frameCap) :
    F k (r+s)≤F k r+F k s := by
  have hc := merge_concave hk ⟨add_nonneg hr hs,ht⟩
  have hh := hc.min_le_of_mem_Icc ⟨le_rfl,add_nonneg hr hs⟩
    ⟨add_nonneg hr hs,le_rfl⟩ (show r∈Icc 0 (r+s) by exact ⟨hr,by linarith⟩)
  simpa only [F_zero,zero_add,sub_zero,sub_self,add_zero,add_sub_cancel_left,min_self] using hh

end SquaresInCircles.Eight.GlobalGA.JointNegativeAETD2.CommonGain

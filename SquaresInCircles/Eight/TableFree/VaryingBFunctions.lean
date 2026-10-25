module

public import SquaresInCircles.Eight.TableFree.OrdinaryCurvatureBounds
public import SquaresInCircles.Eight.TableFree.PositiveStressCoefficients

/-!
# Differential identities for the varying larger coefficient

Uncompiled source draft. The displayed functions are the derivatives of
the original negative ordinary force increment. Their denominator powers
come from a single positive quadratic, and every identity is algebraic
after the square of its positive root is substituted.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.VaryingBFunctions
open OrdinaryCurvatureBounds PositiveStressCoefficients

def root (r u : ℝ) : ℝ := Real.sqrt (1+r^2-2*r*u)
def gain (r u : ℝ) : ℝ := 1/shape r-(1-r*u)/root r u
def integrand (r u : ℝ) : ℝ := r^2*(r-u)/(root r u)^3
def integrandD (r u : ℝ) : ℝ := r^2*(2*r^2-1-r*u)/(root r u)^5
def integrandDD (r u : ℝ) : ℝ := 3*r^3*(3*r^2-2-r*u)/(root r u)^7
def D (R r t : ℝ) : ℝ := Real.cos t-1+R*gain r (Real.sin t)
def Dt (R r t : ℝ) : ℝ := -Real.sin t+R*Real.cos t*integrand r (Real.sin t)
def Dtt (R r t : ℝ) : ℝ := -Real.cos t+
  R*(-Real.sin t*integrand r (Real.sin t)+(Real.cos t)^2*integrandD r (Real.sin t))
def Dr (R r t : ℝ) : ℝ :=
  R*r*((Real.cos t)^2/(root r (Real.sin t))^3-1/(shape r)^3)

theorem radicand_pos (r : ℝ) {u : ℝ} (hu : u∈Icc 0 frameCap) :
    0<1+r^2-2*r*u := by
  have hu2 := pow_le_pow_left₀ hu.1 hu.2 2
  dsimp [frameCap] at hu2
  nlinarith [sq_nonneg (r-u)]

theorem root_pos (r : ℝ) {u : ℝ} (hu : u∈Icc 0 frameCap) : 0<root r u :=
  Real.sqrt_pos.mpr (radicand_pos r hu)

theorem root_sq (r : ℝ) {u : ℝ} (hu : u∈Icc 0 frameCap) :
    (root r u)^2=1+r^2-2*r*u := Real.sq_sqrt (radicand_pos r hu).le

theorem root_power_reduce (r : ℝ) {u : ℝ} (hu : u∈Icc 0 frameCap) (n : ℕ) :
    (root r u)^(n+2)=(root r u)^n*(1+r^2-2*r*u) := by
  rw [pow_add,root_sq r hu]

@[simp] theorem root_zero (r : ℝ) : root r 0=shape r := by simp [root,shape]
@[simp] theorem gain_zero (r : ℝ) : gain r 0=0 := by simp [gain]
@[simp] theorem D_zero (R r : ℝ) : D R r 0=0 := by simp [D]

theorem sin_mem {t : ℝ} (ht : t∈Icc 0 frameCap) :
    Real.sin t∈Icc 0 frameCap := by
  have hs := transport_trig ht
  exact ⟨hs.2.2.1,by dsimp [frameCap]; linarith [hs.2.2.2.1]⟩

theorem root_hasDerivAt_u (r : ℝ) {u : ℝ} (hu : u∈Icc 0 frameCap) :
    HasDerivAt (root r) (-r/root r u) u := by
  have hraw := ((hasDerivAt_const u (1+r^2)).sub
    ((hasDerivAt_id u).const_mul (2*r))).sqrt (radicand_pos r hu).ne'
  convert hraw using 1
  · rfl
  · dsimp [root]
    ring

theorem root_hasDerivAt_r {r u : ℝ} (hu : u∈Icc 0 frameCap) :
    HasDerivAt (fun x => root x u) ((r-u)/root r u) r := by
  have hin : HasDerivAt (fun x => 1+x^2-2*x*u) (2*r-2*u) r := by
    have h := (((hasDerivAt_id r).fun_pow 2).const_add 1).fun_sub
      ((hasDerivAt_id r).const_mul 2 |>.mul_const u)
    convert h using 1 <;> simp
  have hraw := hin.sqrt (radicand_pos r hu).ne'
  have hn := (root_pos r hu).ne'
  convert hraw using 1
  · rfl
  · change (r-u)/root r u=(2*r-2*u)/(2*root r u)
    field_simp

theorem gain_hasDerivAt_u (r : ℝ) {u : ℝ} (hu : u∈Icc 0 frameCap) :
    HasDerivAt (gain r) (integrand r u) u := by
  have hn := (root_pos r hu).ne'
  have h2 := root_sq r hu
  have hnum := ((hasDerivAt_id u).const_mul r).const_sub 1
  have hraw := (hasDerivAt_const u (1/shape r)).fun_sub
    (hnum.fun_div (root_hasDerivAt_u r hu) hn)
  convert hraw using 1
  · rfl
  · dsimp only [integrand,id_eq]
    field_simp
    linear_combination (-r)*h2

theorem gain_hasDerivAt_r {r u : ℝ} (hu : u∈Icc 0 frameCap) :
    HasDerivAt (fun x => gain x u)
      (r*((1-u^2)/(root r u)^3-1/(shape r)^3)) r := by
  have hn := (root_pos r hu).ne'
  have hs := (shape_pos r).ne'
  have h2 := root_sq r hu
  have hnum := ((hasDerivAt_id r).mul_const u).const_sub 1
  have hraw := ((hasDerivAt_const r (1:ℝ)).fun_div (shape_hasDerivAt r) hs).fun_sub
    (hnum.fun_div (root_hasDerivAt_r hu) hn)
  convert hraw using 1
  · rfl
  · dsimp only [id_eq]
    field_simp
    linear_combination (-u*(shape r)^3)*h2

theorem integrand_hasDerivAt (r : ℝ) {u : ℝ} (hu : u∈Icc 0 frameCap) :
    HasDerivAt (integrand r) (integrandD r u) u := by
  have hn := (root_pos r hu).ne'
  have h2 := root_sq r hu
  have hnum := ((hasDerivAt_id u).const_sub r).const_mul (r^2)
  have hraw := hnum.fun_div ((root_hasDerivAt_u r hu).fun_pow 3) (pow_ne_zero 3 hn)
  convert hraw using 1
  · rfl
  · simp only [Nat.cast_ofNat,show (3:ℕ)-1=2 from rfl,id_eq]
    dsimp only [integrand,integrandD]
    field_simp
    linear_combination r^2*h2

theorem integrandD_hasDerivAt (r : ℝ) {u : ℝ} (hu : u∈Icc 0 frameCap) :
    HasDerivAt (integrandD r) (integrandDD r u) u := by
  have hn := (root_pos r hu).ne'
  have h2 := root_sq r hu
  have hnum := (((hasDerivAt_id u).const_mul r).const_sub (2*r^2-1)).const_mul (r^2)
  have hraw := hnum.fun_div ((root_hasDerivAt_u r hu).fun_pow 5) (pow_ne_zero 5 hn)
  convert hraw using 1
  · rfl
  · simp only [Nat.cast_ofNat,show (5:ℕ)-1=4 from rfl,id_eq]
    dsimp only [integrandD,integrandDD]
    field_simp
    linear_combination r^3*h2

theorem D_hasDerivAt_t {R r t : ℝ} (ht : t∈Icc 0 frameCap) :
    HasDerivAt (D R r) (Dt R r t) t := by
  have hraw := ((Real.hasDerivAt_cos t).sub_const 1).add
    (((gain_hasDerivAt_u r (sin_mem ht)).comp t (Real.hasDerivAt_sin t)).const_mul R)
  convert hraw using 1
  · rfl
  · dsimp [Dt]
    ring

theorem Dt_hasDerivAt {R r t : ℝ} (ht : t∈Icc 0 frameCap) :
    HasDerivAt (Dt R r) (Dtt R r t) t := by
  have hraw := (Real.hasDerivAt_sin t).neg.add
    (((Real.hasDerivAt_cos t).const_mul R).mul
      ((integrand_hasDerivAt r (sin_mem ht)).comp t (Real.hasDerivAt_sin t)))
  convert hraw using 1
  · rfl
  · dsimp [Dtt]
    ring

theorem D_hasDerivAt_r {R r t : ℝ} (ht : t∈Icc 0 frameCap) :
    HasDerivAt (fun x => D R x t) (Dr R r t) r := by
  have hraw := (hasDerivAt_const r (Real.cos t-1)).add
    ((gain_hasDerivAt_r (sin_mem ht)).const_mul R)
  convert hraw using 1
  · rfl
  · have hc : 1-(Real.sin t)^2=(Real.cos t)^2 := by
      nlinarith [Real.sin_sq_add_cos_sq t]
    dsimp [Dr]
    rw [hc]
    ring

/-- A polynomial inequality on the whole sine interval. -/
theorem cubic_sine_bound {u : ℝ} (hu : u∈Icc 0 (129/200)) :
    (1-(4/5)*u)^3≤(1-u^2)^2 := by
  have hu2 := pow_le_pow_left₀ hu.1 hu.2 2
  have hfactor : 0≤(98/25 : ℝ)-(64/125)*(u+129/200)-
      (u^2+(129/200)*u+(129/200)^2) := by nlinarith [hu.2]
  have hproduct := mul_nonneg (sub_nonneg.mpr hu.2) hfactor
  have he : (12/5 : ℝ)-(98/25)*u+(64/125)*u^2+u^3=
      14117637/40000000+(129/200-u)*
        ((98/25 : ℝ)-(64/125)*(u+129/200)-
          (u^2+(129/200)*u+(129/200)^2)) := by ring
  have hpoly : 0≤(12/5 : ℝ)-(98/25)*u+(64/125)*u^2+u^3 := by
    rw [he]
    linarith
  have h := mul_nonneg hu.1 hpoly
  nlinarith

/-- The larger-coefficient derivative increases with the smaller/larger
ratio throughout `[1/2,1]`, at every admissible angle. -/
theorem Dr_nonneg {R r t : ℝ} (hR : 0≤R) (hr : r∈Icc (1/2) 1)
    (ht : t∈Icc 0 frameCap) : 0≤Dr R r t := by
  let u : ℝ := Real.sin t
  have hu : u∈Icc 0 (129/200) := ⟨(transport_trig ht).2.2.1,
    by dsimp [u]; linarith [(transport_trig ht).2.2.2.1]⟩
  have hu' : u∈Icc 0 frameCap := sin_mem ht
  have hroot := root_pos r hu'
  have hroot2 := root_sq r hu'
  have hshape := shape_pos r
  have hshape2 := shape_sq r
  have hratio : (4/5)*(1+r^2)≤2*r := by
    have h := mul_nonneg (show 0≤r-1/2 by linarith [hr.1])
      (show 0≤2-r by linarith [hr.2])
    nlinarith
  have hbase : (root r u)^2≤(1+r^2)*(1-(4/5)*u) := by
    nlinarith [mul_le_mul_of_nonneg_right hratio hu.1]
  have hcube := pow_le_pow_left₀ (sq_nonneg (root r u)) hbase 3
  have hpoly := mul_le_mul_of_nonneg_left (cubic_sine_bound hu)
    (show 0≤(1+r^2)^3 by positivity)
  have hsquare : ((root r u)^3)^2≤((1-u^2)*(shape r)^3)^2 := by
    have heN : ((root r u)^3)^2=((root r u)^2)^3 := by ring
    have heS : ((1-u^2)*(shape r)^3)^2=(1-u^2)^2*((shape r)^2)^3 := by ring
    rw [heN,heS,hshape2]
    nlinarith only [hcube,hpoly]
  have hu2 := pow_le_pow_left₀ hu.1 hu.2 2
  have hright : 0≤(1-u^2)*(shape r)^3 := by
    exact mul_nonneg (by nlinarith) (pow_nonneg hshape.le 3)
  have hle : (root r u)^3≤(1-u^2)*(shape r)^3 := by
    nlinarith [pow_nonneg hroot.le 3]
  have hfrac : 1/(shape r)^3≤(1-u^2)/(root r u)^3 := by
    exact (div_le_div_iff₀ (pow_pos hshape 3) (pow_pos hroot 3)).2 (by simpa using hle)
  have hc : (Real.cos t)^2=1-u^2 := by dsimp [u]; nlinarith [Real.sin_sq_add_cos_sq t]
  dsimp [Dr]
  rw [hc]
  exact mul_nonneg (mul_nonneg hR (by linarith [hr.1])) (sub_nonneg.mpr hfrac)

theorem D_monotone_ratio {R t : ℝ} (hR : 0≤R) (ht : t∈Icc 0 frameCap) :
    MonotoneOn (fun r => D R r t) (Icc (1/2) 1) := by
  apply monoOn_of_hasDeriv_nonneg
  · intro r _
    exact (D_hasDerivAt_r (R := R) (r := r) ht).continuousAt.continuousWithinAt
  · intro r _
    exact D_hasDerivAt_r ht
  · intro r hr
    exact Dr_nonneg hR (Ioo_subset_Icc_self hr) ht

theorem integrandD_antitone {r : ℝ} (hr : r∈Icc (117/200) (1527/2000)) :
    AntitoneOn (integrandD r) (Icc 0 frameCap) := by
  have hr0 : 0≤r := by linarith [hr.1]
  have hr2 : r^2≤(1527/2000 : ℝ)^2 := pow_le_pow_left₀ hr0 hr.2 2
  apply antiOn_of_hasDeriv_nonpos
  · intro u hu
    exact (integrandD_hasDerivAt r hu).continuousAt.continuousWithinAt
  · intro u hu
    exact integrandD_hasDerivAt r (Ioo_subset_Icc_self hu)
  · intro u hu
    have hnum : 3*r^2-2-r*u≤0 := by nlinarith [mul_nonneg hr0 hu.1.le]
    dsimp [integrandDD]
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (by positivity) hnum)
      (pow_nonneg (root_pos r (Ioo_subset_Icc_self hu)).le 7)

theorem integrandD_zero_upper {r : ℝ} (hr : r∈Icc (117/200) (1527/2000)) :
    integrandD r 0<(1/10 : ℝ) := by
  have hr0 : 0≤r := by linarith [hr.1]
  have hr2 : r^2≤(73/125 : ℝ) := by
    have h := pow_le_pow_left₀ hr0 hr.2 2
    norm_num at h ⊢
    linarith
  have hproduct := mul_nonpos_of_nonpos_of_nonneg
    (show r^2-73/125≤0 by linarith) (show 0≤2*r^2+21/125 by positivity)
  have hnum : r^2*(2*r^2-1)<(1/10 : ℝ) := by nlinarith
  have hshape1 : 1≤ shape r := by nlinarith [shape_sq r,shape_pos r,sq_nonneg r]
  have hpow : 1≤(shape r)^5 := by simpa using pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1) hshape1 5
  simp only [integrandD,mul_zero,sub_zero,root_zero]
  apply (div_lt_iff₀ (pow_pos (shape_pos r) 5)).2
  nlinarith

theorem integrandD_upper {r u : ℝ} (hr : r∈Icc (117/200) (1527/2000))
    (hu : u∈Icc 0 frameCap) : integrandD r u<(1/10 : ℝ) :=
  (integrandD_antitone hr
    (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hu hu.1).trans_lt
      (integrandD_zero_upper hr)

theorem ratio_integrand_nonneg {d t : ℝ} (hd : d∈Icc 0 frameCap)
    (ht : t∈Icc 0 d) : 0≤ integrand (ratio d) (Real.sin t) := by
  have ht' : t∈Icc 0 frameCap := ⟨ht.1,ht.2.trans hd.2⟩
  have hd7 : d≤7/10 := hd.2
  have hdiff : 0≤ratio d-Real.sin t := by
    have hs := Real.sin_le ht.1
    dsimp [ratio]
    linarith [hd.1,ht.2]
  dsimp [integrand]
  exact div_nonneg (mul_nonneg (sq_nonneg _) hdiff)
    (pow_nonneg (root_pos (ratio d) (sin_mem ht')).le 3)

theorem Dtt_negative {R d t : ℝ} (hR : 0≤R) (hR2 : R≤2)
    (hd : d∈Icc 0 frameCap) (ht : t∈Icc 0 d) :
    Dtt R (ratio d) t<0 := by
  have ht' : t∈Icc 0 frameCap := ⟨ht.1,ht.2.trans hd.2⟩
  have hd7 : d≤7/10 := hd.2
  have hr : ratio d∈Icc (117/200) (1527/2000) := by
    constructor <;> dsimp [ratio] <;> linarith [hd.1]
  have hI := ratio_integrand_nonneg hd ht
  have hId := (integrandD_upper hr (sin_mem ht')).le
  have hsin := (transport_trig ht').2.2.1
  have hc := (transport_trig ht').1
  have hc2 : (Real.cos t)^2≤1 := by nlinarith [Real.sin_sq_add_cos_sq t,sq_nonneg (Real.sin t)]
  have hmul := mul_le_mul_of_nonneg_left hId (sq_nonneg (Real.cos t))
  have hneg := mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hsin) hI
  have hbracket : -Real.sin t*integrand (ratio d) (Real.sin t)+
      (Real.cos t)^2*integrandD (ratio d) (Real.sin t)≤1/10 := by nlinarith
  have hRmul := mul_le_mul_of_nonneg_left hbracket hR
  dsimp [Dtt]
  nlinarith

/-- The correlated ratio makes the derivative concave over the entire
actual angle interval, including its zero endpoint. -/
theorem D_concave {R d : ℝ} (hR : 0≤R) (hR2 : R≤2)
    (hd : d∈Icc 0 frameCap) : ConcaveOn ℝ (Icc 0 d) (D R (ratio d)) := by
  apply concave_of_deriv2
  · intro t ht
    exact D_hasDerivAt_t ⟨ht.1,ht.2.trans hd.2⟩
  · intro t ht
    exact Dt_hasDerivAt ⟨ht.1,ht.2.trans hd.2⟩
  · intro t ht
    exact (Dtt_negative hR hR2 hd ht).le

end SquaresInCircles.Eight.TableFree.VaryingBFunctions

module

public import SquaresInCircles.Eight.TableFree.ContactArcMinimum
public import SquaresInCircles.Eight.TableFree.TrigonometricReserves

/-!
# The two actual-circle contact branches of a positive primary pair

Uncompiled draft. All estimates hold at the actual squared radius q in
[qLow,qTrial]; qCap is used only as an upper estimate. The contact curves are
explicit rotations of points on that q-circle. The two second-derivative
bounds are uniform on the entire frame interval, not on a numerical cover.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
namespace PairedPrimary

/-- The positive branch has y≥0; the negative branch has y≤0. -/
def zPlus (P u : ℝ) : ℝ := Real.sin u-P
def zMinus (P u : ℝ) : ℝ := Real.sin u+Real.cos u-P

def rootPlus (q P u : ℝ) : ℝ := Real.sqrt (q-(zPlus P u)^2)
def rootMinus (q P u : ℝ) : ℝ := Real.sqrt (q-(zMinus P u)^2)

def plusCurve (q P u : ℝ) : SignedPoint :=
  ⟨rootPlus q P u*Real.cos u+zPlus P u*Real.sin u-1/2,
    rootPlus q P u*Real.sin u-zPlus P u*Real.cos u-1/2⟩

def minusCurve (q P u : ℝ) : SignedPoint :=
  ⟨rootMinus q P u*Real.cos u+zMinus P u*Real.sin u-1/2,
    1/2+rootMinus q P u*Real.sin u-zMinus P u*Real.cos u⟩

def plusDemand (q P t u : ℝ) : ℝ :=
  1/2-P*Real.cos t+(Real.sin t+Real.cos t)*Real.cos u+
    Real.sin t*Real.sin u-Real.sin t*rootPlus q P u

def minusDemand (q P t u : ℝ) : ℝ :=
  1/2-P*Real.cos t+(Real.sin t+Real.cos t)*Real.cos u-
    Real.sin t*rootMinus q P u

def plusDerivative (q P t u : ℝ) : ℝ :=
  -(Real.sin t+Real.cos t)*Real.sin u+Real.sin t*Real.cos u+
    Real.sin t*zPlus P u*Real.cos u/rootPlus q P u

def minusDerivative (q P t u : ℝ) : ℝ :=
  -(Real.sin t+Real.cos t)*Real.sin u+
    Real.sin t*zMinus P u*(Real.cos u-Real.sin u)/rootMinus q P u

def plusSecond (q P t u : ℝ) : ℝ :=
  -(Real.sin t+Real.cos t)*Real.cos u-Real.sin t*Real.sin u+
    Real.sin t*(q*(Real.cos u)^2/(rootPlus q P u)^3-
      zPlus P u*Real.sin u/rootPlus q P u)

def minusSecond (q P t u : ℝ) : ℝ :=
  -(Real.sin t+Real.cos t)*Real.cos u+
    Real.sin t*(q*(Real.cos u-Real.sin u)^2/(rootMinus q P u)^3-
      zMinus P u*(Real.sin u+Real.cos u)/rootMinus q P u)

/-- Differential identities for a circle root along an arbitrary C² scalar
coordinate. The radius is constant along the derivative. -/
theorem circle_root_derivatives {q x : ℝ} {z dz ddz : ℝ → ℝ}
    (hz : HasDerivAt z (dz x) x) (hdz : HasDerivAt dz (ddz x) x)
    (hroot : 0<q-(z x)^2) :
    HasDerivAt (fun y => Real.sqrt (q-(z y)^2))
      (-(z x)*dz x/Real.sqrt (q-(z x)^2)) x ∧
    HasDerivAt (fun y => -(z y)*dz y/Real.sqrt (q-(z y)^2))
      (-q*(dz x)^2/(Real.sqrt (q-(z x)^2))^3-
        z x*ddz x/Real.sqrt (q-(z x)^2)) x := by
  let m := Real.sqrt (q-(z x)^2)
  have hm : 0<m := Real.sqrt_pos.mpr hroot
  have hm2 : m^2=q-(z x)^2 := Real.sq_sqrt hroot.le
  have hrad := (hasDerivAt_const x q).sub (hz.pow 2)
  have hfirst : HasDerivAt (fun y => Real.sqrt (q-(z y)^2))
      (-z x*dz x/m) x := by
    convert hrad.sqrt hroot.ne' using 1
    field_simp [hm.ne']
    ring
  refine ⟨hfirst,?_⟩
  convert ((hz.neg.mul hdz).div hfirst hm.ne') using 1
  field_simp [hm.ne']
  nlinarith [hm2]

theorem branch_bounds {q P u : ℝ}
    (hqL : qLow≤q) (hqU : q≤qCap)
    (hP : 3/8≤P ∧ P≤183/200) (hu : u∈Icc 0 (7/10 : ℝ)) :
    |zPlus P u|≤183/200 ∧ 0<zMinus P u ∧ zMinus P u<59/56 ∧
      7/4<rootPlus q P u ∧ 5/3<rootMinus q P u := by
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hu
  have hunit := Real.sin_sq_add_cos_sq u
  have hsum : 1≤Real.sin u+Real.cos u := by
    have h := one_le_abs_cos_add_abs_sin u
    simpa [abs_of_nonneg hs0,abs_of_pos hc,add_comm] using h
  have hsumUpper : Real.sin u+Real.cos u<10/7 := by
    nlinarith [sq_nonneg (Real.cos u-Real.sin u)]
  have hp : |zPlus P u|≤183/200 := by
    apply abs_le.mpr
    dsimp [zPlus]
    constructor <;> linarith [hP.1,hP.2]
  have hmlo : 0<zMinus P u := by dsimp [zMinus]; linarith [hP.2]
  have hmhi : zMinus P u<59/56 := by dsimp [zMinus]; linarith [hP.1]
  have hp2 := pow_le_pow_left₀ (abs_nonneg (zPlus P u)) hp 2
  rw [sq_abs] at hp2
  have hm2 : (zMinus P u)^2<(59/56 : ℝ)^2 :=
    pow_lt_pow_left₀ hmlo.le hmhi (by norm_num)
  have hrp : (7/4 : ℝ)^2<q-(zPlus P u)^2 := by
    dsimp [qLow] at hqL
    nlinarith
  have hrm : (5/3 : ℝ)^2<q-(zMinus P u)^2 := by
    dsimp [qLow] at hqL
    nlinarith
  have hprad : 0≤q-(zPlus P u)^2 := by nlinarith
  have hmrad : 0≤q-(zMinus P u)^2 := by nlinarith
  have hpsq := Real.sq_sqrt hprad
  have hmsq := Real.sq_sqrt hmrad
  have hpnon := Real.sqrt_nonneg (q-(zPlus P u)^2)
  have hmnon := Real.sqrt_nonneg (q-(zMinus P u)^2)
  refine ⟨hp,hmlo,hmhi,?_,?_⟩ <;>
    dsimp [rootPlus,rootMinus] <;> nlinarith

theorem plus_derivatives {q P t u : ℝ} (hr : 0<q-(zPlus P u)^2) :
    HasDerivAt (plusDemand q P t) (plusDerivative q P t u) u ∧
      HasDerivAt (plusDerivative q P t) (plusSecond q P t u) u := by
  have hz : HasDerivAt (zPlus P) (Real.cos u) u := by
    simpa [zPlus] using (Real.hasDerivAt_sin u).sub_const P
  have hm := circle_root_derivatives hz (Real.hasDerivAt_cos u) hr
  have hroot : 0<rootPlus q P u := Real.sqrt_pos.mpr hr
  constructor
  · convert ((((hasDerivAt_const u (1/2-P*Real.cos t)).add
        ((Real.hasDerivAt_cos u).const_mul (Real.sin t+Real.cos t))).add
        ((Real.hasDerivAt_sin u).const_mul (Real.sin t))).sub
        (hm.1.const_mul (Real.sin t))) using 1 <;>
      dsimp [plusDemand,plusDerivative,rootPlus] <;> ring
  · have hR : HasDerivAt (fun x => zPlus P x*Real.cos x/rootPlus q P x)
        (q*(Real.cos u)^2/(rootPlus q P u)^3-
          zPlus P u*Real.sin u/rootPlus q P u) u := by
      convert hm.2.neg using 1 <;> dsimp [rootPlus] <;> ring
    convert (((Real.hasDerivAt_sin u).const_mul (-(Real.sin t+Real.cos t))).add
      ((Real.hasDerivAt_cos u).const_mul (Real.sin t))).add
      (hR.const_mul (Real.sin t)) using 1 <;>
      dsimp [plusDerivative,plusSecond] <;> ring

theorem minus_derivatives {q P t u : ℝ} (hr : 0<q-(zMinus P u)^2) :
    HasDerivAt (minusDemand q P t) (minusDerivative q P t u) u ∧
      HasDerivAt (minusDerivative q P t) (minusSecond q P t u) u := by
  have hz : HasDerivAt (zMinus P) (Real.cos u-Real.sin u) u := by
    convert ((Real.hasDerivAt_sin u).add (Real.hasDerivAt_cos u)).sub_const P using 1 <;>
      dsimp [zMinus] <;> ring
  have hdz : HasDerivAt (fun x => Real.cos x-Real.sin x)
      (-(Real.sin u+Real.cos u)) u := by
    convert (Real.hasDerivAt_cos u).sub (Real.hasDerivAt_sin u) using 1 <;> ring
  have hm := circle_root_derivatives hz hdz hr
  constructor
  · convert (((hasDerivAt_const u (1/2-P*Real.cos t)).add
      ((Real.hasDerivAt_cos u).const_mul (Real.sin t+Real.cos t))).sub
      (hm.1.const_mul (Real.sin t))) using 1 <;>
      dsimp [minusDemand,minusDerivative,rootMinus] <;> ring
  · have hR : HasDerivAt
        (fun x => zMinus P x*(Real.cos x-Real.sin x)/rootMinus q P x)
        (q*(Real.cos u-Real.sin u)^2/(rootMinus q P u)^3-
          zMinus P u*(Real.sin u+Real.cos u)/rootMinus q P u) u := by
      convert hm.2.neg using 1 <;> dsimp [rootMinus] <;> ring
    convert ((Real.hasDerivAt_sin u).const_mul (-(Real.sin t+Real.cos t))).add
      (hR.const_mul (Real.sin t)) using 1 <;>
      dsimp [minusDerivative,minusSecond] <;> ring

theorem plus_second_negative {q P t u : ℝ}
    (hqL : qLow≤q) (hqU : q≤qCap)
    (hP : 3/8≤P ∧ P≤183/200)
    (ht : t∈Icc 0 (7/10 : ℝ)) (hu : u∈Icc 0 (7/10 : ℝ)) :
    plusSecond q P t u≤-(1/25) := by
  obtain ⟨hp,hm0,hm,hroot,hrm⟩ := branch_bounds hqL hqU hP hu
  obtain ⟨hc,hs0,hs⟩ := transport_trig_coarse hu
  obtain ⟨hC,hS0,hS⟩ := transport_trig_coarse ht
  have hunit := Real.sin_sq_add_cos_sq u
  have hsum : 1≤Real.sin t+Real.cos t := by
    have h := one_le_abs_cos_add_abs_sin t
    simpa [abs_of_nonneg hS0,abs_of_pos hC,add_comm] using h
  have hroot0 : 0<rootPlus q P u := by linarith
  have hpow : (7/4 : ℝ)^3≤(rootPlus q P u)^3 :=
    pow_le_pow_left₀ (by norm_num) hroot.le 3
  have hcos2 : (Real.cos u)^2≤1 := by nlinarith [sq_nonneg (Real.sin u)]
  have hq0 : 0≤q := by dsimp [qLow] at hqL; linarith
  have hnum := mul_le_mul_of_nonneg_left hcos2 hq0
  have hfirst : q*(Real.cos u)^2/(rootPlus q P u)^3≤256/343 := by
    apply (div_le_iff₀ (pow_pos hroot0 3)).2
    dsimp [qCap] at hqU
    nlinarith
  have hzlo := (abs_le.mp hp).1
  have hzs := mul_nonneg (show 0≤zPlus P u+183/200 by linarith) hs0
  have hsecond : -(zPlus P u*Real.sin u)/rootPlus q P u≤
      (183/200)*(13/20)*(4/7) := by
    apply (div_le_iff₀ hroot0).2
    nlinarith
  have hrest : q*(Real.cos u)^2/(rootPlus q P u)^3-
      zPlus P u*Real.sin u/rootPlus q P u≤
      256/343+(183/200)*(13/20)*(4/7) := by linarith
  have hmult := mul_le_mul_of_nonneg_left hrest hS0
  have hmult2 := mul_le_mul_of_nonneg_right hS.le
    (by norm_num : (0:ℝ)≤256/343+(183/200)*(13/20)*(4/7))
  have hbase := mul_nonneg (sub_nonneg.mpr hsum) hc.le
  have hss := mul_nonneg hS0 hs0
  unfold plusSecond
  nlinarith

theorem minus_second_negative {q P t u : ℝ}
    (hqL : qLow≤q) (hqU : q≤qCap)
    (hP : 3/8≤P ∧ P≤183/200)
    (ht : t∈Icc 0 (7/10 : ℝ)) (hu : u∈Icc 0 (7/10 : ℝ)) :
    minusSecond q P t u≤-(1/10) := by
  obtain ⟨hp,hz0,hz,hpr,hr⟩ := branch_bounds hqL hqU hP hu
  obtain ⟨hc,hs0,hs⟩ := transport_trig_coarse hu
  obtain ⟨hC,hS0,hS⟩ := transport_trig_coarse ht
  have hsum : 1≤Real.sin t+Real.cos t := by
    have h := one_le_abs_cos_add_abs_sin t
    simpa [abs_of_nonneg hS0,abs_of_pos hC,add_comm] using h
  have hr0 : 0<rootMinus q P u := by linarith
  have hpow : (5/3 : ℝ)^3≤(rootMinus q P u)^3 :=
    pow_le_pow_left₀ (by norm_num) hr.le 3
  have hdiff : (Real.cos u-Real.sin u)^2≤1 := by
    nlinarith [Real.sin_sq_add_cos_sq u,mul_nonneg hc.le hs0]
  have hq0 : 0≤q := by dsimp [qLow] at hqL; linarith
  have hnum := mul_le_mul_of_nonneg_left hdiff hq0
  have hfirst : q*(Real.cos u-Real.sin u)^2/(rootMinus q P u)^3≤108/125 := by
    apply (div_le_iff₀ (pow_pos hr0 3)).2
    dsimp [qCap] at hqU
    nlinarith
  have hsecond : 0≤zMinus P u*(Real.sin u+Real.cos u)/rootMinus q P u :=
    div_nonneg (mul_nonneg hz0.le (by linarith)) hr0.le
  have hmult := mul_le_mul_of_nonneg_left hfirst hS0
  have hmult2 := mul_nonneg hS0 hsecond
  have hbase := mul_nonneg (sub_nonneg.mpr hsum) hc.le
  unfold minusSecond
  nlinarith

/-- Exact circle identities precede every use of the word `outer`. -/
theorem plusCurve_circle {q P u : ℝ} (hr : 0≤q-(zPlus P u)^2)
    (hy : 0≤(plusCurve q P u).y) : (plusCurve q P u).circle=q := by
  have hm := Real.sq_sqrt hr
  have hid := circle_rotation_identity (rootPlus q P u) (-zPlus P u) u
  simp only [SignedPoint.circle,abs_of_nonneg hy]
  dsimp [plusCurve,rootPlus] at *
  nlinarith

theorem minusCurve_circle {q P u : ℝ} (hr : 0≤q-(zMinus P u)^2)
    (hy : (minusCurve q P u).y≤0) : (minusCurve q P u).circle=q := by
  have hm := Real.sq_sqrt hr
  have hid := circle_rotation_identity (rootMinus q P u) (-zMinus P u) u
  simp only [SignedPoint.circle,abs_of_nonpos hy]
  dsimp [minusCurve,rootMinus] at *
  nlinarith

theorem plusCurve_contact (q P u : ℝ) :
    P+1/2+(plusCurve q P u).a*Real.sin u-(plusCurve q P u).y*Real.cos u=
      (1+Real.cos u+Real.sin u)/2 := by
  dsimp [plusCurve,zPlus]
  nlinarith [Real.sin_sq_add_cos_sq u]

theorem minusCurve_contact (q P u : ℝ) :
    P+1/2+(minusCurve q P u).a*Real.sin u-(minusCurve q P u).y*Real.cos u=
      (1+Real.cos u+Real.sin u)/2 := by
  dsimp [minusCurve,zMinus]
  nlinarith [Real.sin_sq_add_cos_sq u]

theorem plusCurve_demand (q P t u : ℝ) :
    (1+Real.cos (t-u)+Real.sin (t-u))/2-
      (plusCurve q P u).a*Real.sin (t-u)-(plusCurve q P u).y*Real.cos (t-u)=
      plusDemand q P t u := by
  dsimp [plusCurve,plusDemand,zPlus]
  simp only [Real.sin_sub,Real.cos_sub]
  nlinarith [Real.sin_sq_add_cos_sq u]

theorem minusCurve_demand (q P t u : ℝ) :
    (1+Real.cos (t-u)+Real.sin (t-u))/2-
      (minusCurve q P u).a*Real.sin (t-u)-(minusCurve q P u).y*Real.cos (t-u)=
      minusDemand q P t u := by
  dsimp [minusCurve,minusDemand,zMinus]
  simp only [Real.sin_sub,Real.cos_sub]
  nlinarith [Real.sin_sq_add_cos_sq u]

/-- Positive square roots recover the original contact state, rather than
merely exhibiting a different state with equal scalar support. -/
theorem plusCurve_recovery {q P u : ℝ} {p : SignedPoint}
    (hs : p.Sorted) (ho : p.Outer q) (hy : 0≤p.y)
    (hu : u∈Icc 0 (7/10 : ℝ))
    (hc : P+1/2+p.a*Real.sin u-p.y*Real.cos u=(1+Real.cos u+Real.sin u)/2) :
    plusCurve q P u=p := by
  obtain ⟨hcos,hsin0,hsin⟩ := transport_trig_coarse hu
  let X := p.a+1/2
  let Y := p.y+1/2
  have hX : 0<X := by dsimp [X]; linarith [hs.1]
  have hY : 0<Y := by dsimp [Y]; linarith
  have hz : X*Real.sin u-Y*Real.cos u=zPlus P u := by
    dsimp [X,Y,zPlus]
    linarith
  have hn : 0<X*Real.cos u+Y*Real.sin u := by positivity
  have hnorm : X^2+Y^2=q := by
    simpa [SignedPoint.Outer,SignedPoint.circle,abs_of_nonneg hy,X,Y] using ho
  have hsq : (X*Real.cos u+Y*Real.sin u)^2=q-(zPlus P u)^2 := by
    have hrot := circle_rotation_identity X Y u
    nlinarith [Real.sin_sq_add_cos_sq u]
  have hroot : rootPlus q P u=X*Real.cos u+Y*Real.sin u := by
    rw [rootPlus,← hsq,Real.sqrt_sq_eq_abs,abs_of_pos hn]
  cases p
  apply SignedPoint.ext <;> dsimp [plusCurve] <;> rw [hroot,← hz] <;>
    dsimp [X,Y] at * <;> nlinarith [Real.sin_sq_add_cos_sq u]

theorem minusCurve_recovery {q P u : ℝ} {p : SignedPoint}
    (hs : p.Sorted) (ho : p.Outer q) (hy : p.y≤0)
    (hu : u∈Icc 0 (7/10 : ℝ))
    (hc : P+1/2+p.a*Real.sin u-p.y*Real.cos u=(1+Real.cos u+Real.sin u)/2) :
    minusCurve q P u=p := by
  obtain ⟨hcos,hcos1,hsin0,hsin,hsc⟩ := transport_trig hu
  let X := p.a+1/2
  let Z := -p.y+1/2
  have hX : 0<X := by dsimp [X]; linarith [hs.1]
  have hZ : 0<Z := by dsimp [Z]; linarith
  have hZX : Z≤X := by
    have h := hs.2
    rw [abs_of_nonpos hy] at h
    dsimp [X,Z]
    linarith
  have hz : X*Real.sin u+Z*Real.cos u=zMinus P u := by
    dsimp [X,Z,zMinus]
    linarith
  have hn : 0<X*Real.cos u-Z*Real.sin u := by
    have h := mul_le_mul_of_nonneg_right hZX hsin0
    have hp := mul_pos hX (sub_pos.mpr hsc)
    nlinarith
  have hnorm : X^2+Z^2=q := by
    simpa [SignedPoint.Outer,SignedPoint.circle,abs_of_nonpos hy,X,Z] using ho
  have hsq : (X*Real.cos u-Z*Real.sin u)^2=q-(zMinus P u)^2 := by
    have hrot := circle_rotation_identity X Z u
    nlinarith [Real.sin_sq_add_cos_sq u]
  have hroot : rootMinus q P u=X*Real.cos u-Z*Real.sin u := by
    rw [rootMinus,← hsq,Real.sqrt_sq_eq_abs,abs_of_pos hn]
  cases p
  apply SignedPoint.ext <;> dsimp [minusCurve] <;> rw [hroot,← hz] <;>
    dsimp [X,Z] at * <;> nlinarith [Real.sin_sq_add_cos_sq u]

end PairedPrimary
end SquaresInCircles.Eight.TableFree
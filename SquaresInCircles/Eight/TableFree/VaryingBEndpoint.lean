module

public import SquaresInCircles.Eight.TableFree.VaryingBFunctions
public import SquaresInCircles.Eight.TableFree.VaryingBCertificate

/-!
# The actual varying-B derivative at its intrinsic endpoint

Uncompiled source draft. This file transfers the proved degree-70
polynomial inequality to the original trigonometric derivative. Both
positive square comparisons are displayed, with every Taylor direction
and every denominator sign retained.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.VaryingBEndpoint
open PositiveStressCoefficients OrdinaryCurvatureBounds VaryingBFunctions

theorem S11_nonneg {d : ℝ} (hd : d∈Icc 0 frameCap) :
    0≤HighOrderTaylor.S11 d := by
  have h2 := pow_le_pow_left₀ hd.1 hd.2 2
  have h6 := pow_le_pow_left₀ hd.1 hd.2 6
  have h10 := pow_le_pow_left₀ hd.1 hd.2 10
  have hfactor : 0≤1-d^2/6+d^4/120-d^6/5040+d^8/362880-d^10/39916800 := by
    dsimp [frameCap] at h2 h6 h10
    nlinarith [pow_nonneg hd.1 4,pow_nonneg hd.1 8]
  have he : HighOrderTaylor.S11 d=
      d*(1-d^2/6+d^4/120-d^6/5040+d^8/362880-d^10/39916800) := by
    dsimp [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7]
    ring
  rw [he]
  exact mul_nonneg hd.1 hfactor

theorem C12_le_one {d : ℝ} (hd : d∈Icc 0 frameCap) :
    HighOrderTaylor.C12 d≤1 := by
  have h2 := pow_le_pow_left₀ hd.1 hd.2 2
  have h6 := pow_le_pow_left₀ hd.1 hd.2 6
  have h10 := pow_le_pow_left₀ hd.1 hd.2 10
  have hfactor : 0≤1/2-d^2/24+d^4/720-d^6/40320+d^8/3628800-d^10/479001600 := by
    dsimp [frameCap] at h2 h6 h10
    nlinarith [pow_nonneg hd.1 4,pow_nonneg hd.1 8]
  have he : 1-HighOrderTaylor.C12 d=
      d^2*(1/2-d^2/24+d^4/720-d^6/40320+d^8/3628800-d^10/479001600) := by
    dsimp [HighOrderTaylor.C12,Arithmetic.cos10,Arithmetic.cos8]
    ring
  have h := mul_nonneg (sq_nonneg d) hfactor
  rw [← he] at h
  linarith

/-- The degree-70 certificate is a proof about the actual derivative,
not an additional condition on the geometric input. -/
theorem D_endpoint_pos {d : ℝ} (hd : d∈Ioc 0 frameCap) :
    0<D (Real.sqrt qCap) (ratio d) d := by
  have hd' : d∈Icc 0 frameCap := Ioc_subset_Icc_self hd
  let r : ℝ := ratio d
  let u : ℝ := Real.sin d
  let v : ℝ := 1-Real.cos d
  let A : ℝ := 1+r^2
  let B : ℝ := A-2*r*u
  let slo : ℝ := HighOrderTaylor.S11 d
  let sup : ℝ := Arithmetic.sin9 d
  let clo : ℝ := Arithmetic.cos10 d
  let cup : ℝ := HighOrderTaylor.C12 d
  let bm : ℝ := A-2*r*sup
  let bp : ℝ := A-2*r*slo
  let H : ℝ := qCap*r^2*slo*(2*r-A*sup)+(1-cup)^2*A*bm
  let R : ℝ := Real.sqrt qCap
  have hR : 0<R := Real.sqrt_pos.mpr (by norm_num [qCap])
  have hR2 : R^2=qCap := Real.sq_sqrt (by norm_num [qCap])
  have hRlo : 1<R := by dsimp [qCap] at hR2; nlinarith
  have hr : r∈Icc (117/200) (1527/2000) := by
    constructor <;> dsimp [r,ratio] <;> linarith [hd'.1,hd'.2]
  have hr0 : 0<r := by linarith [hr.1]
  have hr2 : r^2≤(1527/2000 : ℝ)^2 := pow_le_pow_left₀ hr0.le hr.2 2
  have hu : u∈Icc 0 frameCap := sin_mem hd'
  have hu0 : 0≤u := hu.1
  have hv0 : 0≤v := by dsimp [v]; linarith [Real.cos_le_one d]
  have hvsmall : v<147/625 := by dsimp [v]; linarith [(transport_trig hd').1]
  have hA : 0<A := by dsimp [A]; positivity
  have hB : 0<B := radicand_pos r hu
  have hS : 0<shape r := shape_pos r
  have hS2 : (shape r)^2=A := shape_sq r
  have hSupper : shape r≤2 := by dsimp [A] at hS2; nlinarith
  have hN : 0<root r u := root_pos r hu
  have hN2 : (root r u)^2=B := root_sq r hu
  have hslo0 : 0≤slo := S11_nonneg hd'
  have hslou : slo≤u := HighOrderTaylor.S11_le_sin hd'.1
  have husup : u≤sup := Arithmetic.sin_le_sin9 hd'.1
  have hclo : clo≤Real.cos d := Arithmetic.cos10_le_cos hd'.1
  have hcup : Real.cos d≤cup := HighOrderTaylor.cos_le_C12 hd'.1
  have hcup1 : cup≤1 := C12_le_one hd'
  have hvlo : 0≤1-cup := by linarith
  have hvhi : 0≤1-clo := by linarith [Real.cos_le_one d]
  have hvlv : 1-cup≤v := by dsimp [v]; linarith
  have hvvu : v≤1-clo := by dsimp [v]; linarith
  have hsign := VaryingBCertificate.sign_bounds hd'
  have hrsup : (19/200 : ℝ)<r-sup := by
    simpa only [map_sub,VaryingBCertificate.r_eval,VaryingBCertificate.S9_eval] using hsign.1
  have hfactor : (2511/5000 : ℝ)<2*r-A*sup := by
    simpa [VaryingBCertificate.A,A,r,sup] using hsign.2
  have hbm : 0<bm := by dsimp [bm,A]; nlinarith
  have hbmB : bm≤B := by
    dsimp [bm,B]
    nlinarith [mul_le_mul_of_nonneg_left husup hr0.le]
  have hBbp : B≤bp := by
    dsimp [B,bp]
    nlinarith [mul_le_mul_of_nonneg_left hslou hr0.le]
  have hbp : 0<bp := hB.trans_le hBbp
  have htruefactor : 2*r-A*sup≤2*r-A*u := by
    nlinarith [mul_le_mul_of_nonneg_left husup hA.le]
  have hH0 : 0≤H := by
    dsimp [H]
    exact add_nonneg
      (mul_nonneg (by positivity) (by linarith))
      (by positivity)
  have hpoly : 0<H^2-4*qCap*(1-clo)^2*A*bp^2 := by
    have h := VaryingBCertificate.numerator_positive hd
    simpa [VaryingBCertificate.numerator,VaryingBCertificate.H,
      VaryingBCertificate.A,VaryingBCertificate.Bminus,VaryingBCertificate.Bplus,
      H,A,bm,bp,r,slo,sup,clo,cup,qCap] using h
  have hcrossUpper0 : 0≤2*R*(1-clo)*shape r*bp := by positivity
  have hcrossUpperSq : (2*R*(1-clo)*shape r*bp)^2=
      4*qCap*(1-clo)^2*A*bp^2 := by
    calc
      (2*R*(1-clo)*shape r*bp)^2=4*R^2*(1-clo)^2*(shape r)^2*bp^2 := by ring
      _=4*qCap*(1-clo)^2*A*bp^2 := by rw [hR2,hS2]
  have hHcross : 2*R*(1-clo)*shape r*bp<H := by nlinarith
  have hvcross : v*B≤(1-clo)*bp :=
    mul_le_mul hvvu hBbp hB.le hvhi
  have hcross : 2*R*v*shape r*B≤2*R*(1-clo)*shape r*bp := by
    nlinarith only [mul_le_mul_of_nonneg_left hvcross
      (show 0≤2*R*shape r by positivity)]
  have hfirst : slo*(2*r-A*sup)≤u*(2*r-A*u) :=
    mul_le_mul hslou htruefactor (by linarith) hu0
  have hfirst' := mul_le_mul_of_nonneg_left hfirst (show 0≤qCap*r^2 by positivity)
  have hvSq : (1-cup)^2≤v^2 := pow_le_pow_left₀ hvlo hvlv 2
  have hsecond := mul_le_mul hvSq hbmB hbm.le (sq_nonneg v)
  have hsecond' := mul_le_mul_of_nonneg_left hsecond hA.le
  have hHactual : H≤qCap*r^2*u*(2*r-A*u)+v^2*A*B := by
    dsimp [H]
    nlinarith only [hfirst',hsecond']
  have hpositiveSquare :
      0<qCap*r^2*u*(2*r-A*u)+v^2*A*B-2*R*v*shape r*B := by
    linarith
  have hleft : 0<R-v*shape r := by
    have hprod := mul_le_mul_of_nonneg_left hSupper hv0
    nlinarith
  have hright : 0<1-r*u := by
    have hmul := mul_le_mul hr.2 hu.2 hu0 (by norm_num : (0:ℝ)≤1527/2000)
    dsimp [frameCap] at hmul
    nlinarith
  have hleftprod : 0<(R-v*shape r)*root r u := mul_pos hleft hN
  have hrightprod : 0<R*(1-r*u)*shape r := by positivity
  have hid : ((R-v*shape r)*root r u)^2-(R*(1-r*u)*shape r)^2=
      qCap*r^2*u*(2*r-A*u)+v^2*A*B-2*R*v*shape r*B := by
    calc
      ((R-v*shape r)*root r u)^2-(R*(1-r*u)*shape r)^2=
        (R^2-2*R*v*shape r+v^2*(shape r)^2)*(root r u)^2-
          R^2*(1-r*u)^2*(shape r)^2 := by ring
      _=(qCap-2*R*v*shape r+v^2*A)*B-qCap*(1-r*u)^2*A := by rw [hR2,hS2,hN2]
      _=qCap*r^2*u*(2*r-A*u)+v^2*A*B-2*R*v*shape r*B := by
        dsimp [B,A]
        ring
  have hcompare : R*(1-r*u)*shape r<(R-v*shape r)*root r u := by
    rw [← hid] at hpositiveSquare
    nlinarith
  have hclear : D R r d*(shape r*root r u)=
      (R-v*shape r)*root r u-R*(1-r*u)*shape r := by
    dsimp [D,gain,v,u]
    field_simp [hS.ne',hN.ne']
    ring
  have hpositive : 0<D R r d*(shape r*root r u) := by rw [hclear]; linarith
  change 0<D R r d
  by_contra! hbad
  have hnon := mul_nonpos_of_nonpos_of_nonneg hbad (mul_pos hS hN).le
  linarith

end SquaresInCircles.Eight.TableFree.VaryingBEndpoint

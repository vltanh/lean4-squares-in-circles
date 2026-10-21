module

public import SquaresInCircles.Eight.TableFree.CrossedUpperRateInverse

/-!
# Inverse-HG rates on the lower active tangent interval

Uncompiled source draft.  The exact Y derivative is negative on the
whole interval [48/49,1.04], uniformly at the actual q.  Consequently
only two intrinsic transverse endpoints need bounds.  Both endpoint
bounds hold for the complete q interval directly; no q monotonicity or
angular table is assumed.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.CrossedLowerRate
open CrossedClampRates
open CrossedUpperRate (inverseE inverseDPart inverseRateD radius_hasDerivAt)

def shortTangent : ℝ := 20011/500000

structure InverseDomain (q Y t : ℝ) : Prop where
  floor : qLow≤q
  ceiling : q≤qCap
  Y_mem : Y∈Icc (48/49 : ℝ) (26/25)
  t_mem : t∈Icc 0 shortTangent

theorem inverse_radicals {q Y t : ℝ} (C : InverseDomain q Y t) :
    0<q-Y^2 ∧ radius q Y∈Ioo (42/25 : ℝ) (43/25) ∧
      transverse q Y∈Ioo (17/25 : ℝ) (18/25) ∧
      0<q-(transverse q Y)^2 ∧ adjacent q Y∈Ioo (46/25 : ℝ) (93/50) ∧
      (radius q Y)^2+Y^2=q ∧ (adjacent q Y)^2+(transverse q Y)^2=q := by
  have hqL := C.floor
  have hq := C.ceiling
  dsimp [qLow,qCap] at hqL hq
  have hY0 : 0≤Y := by linarith [C.Y_mem.1]
  have hY2 := pow_le_pow_left₀ hY0 C.Y_mem.2 2
  have hYlo2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤48/49) C.Y_mem.1 2
  have hr : 0<q-Y^2 := by nlinarith
  have hR0 : 0≤radius q Y := Real.sqrt_nonneg _
  have hR2 : (radius q Y)^2=q-Y^2 := Real.sq_sqrt hr.le
  have hR : radius q Y∈Ioo (42/25 : ℝ) (43/25) := by constructor <;> nlinarith
  have hD : transverse q Y∈Ioo (17/25 : ℝ) (18/25) := by
    dsimp [transverse]
    constructor <;> linarith [hR.1,hR.2]
  have hD2 := pow_le_pow_left₀ (show 0≤transverse q Y by linarith [hD.1]) hD.2.le 2
  have hx : 0<q-(transverse q Y)^2 := by nlinarith
  have hX0 : 0≤adjacent q Y := Real.sqrt_nonneg _
  have hX2 : (adjacent q Y)^2=q-(transverse q Y)^2 := Real.sq_sqrt hx.le
  have hX : adjacent q Y∈Ioo (46/25 : ℝ) (93/50) := by
    constructor <;> nlinarith [hD.1,sq_nonneg (transverse q Y-17/25)]
  exact ⟨hr,hR,hD,hx,hX,by nlinarith,by nlinarith⟩

theorem inverse_denominator {q Y t : ℝ} (C : InverseDomain q Y t) :
    181/100<adjacent q Y-transverse q Y*t := by
  obtain ⟨_,_,hD,_,hX,_,_⟩ := inverse_radicals C
  have ht : t≤41/1000 := by have hh := C.t_mem.2; dsimp [shortTangent] at hh; linarith
  have hm := mul_le_mul hD.2.le ht C.t_mem.1 (by norm_num : (0:ℝ)≤18/25)
  linarith [hX.1]

theorem inverse_E_lower {q Y t : ℝ} (C : InverseDomain q Y t) :
    21/25<inverseE q Y t := by
  obtain ⟨_,_,hD,_,hX,_,_⟩ := inverse_radicals C
  have hd := inverse_denominator C
  have hf : 0≤t*(adjacent q Y-transverse q Y)/(adjacent q Y-transverse q Y*t) :=
    div_nonneg (mul_nonneg C.t_mem.1 (by linarith [hX.1,hD.2])) (by linarith)
  dsimp [inverseE]
  linarith [hX.1]

theorem inverse_D_part_upper {q Y t : ℝ} (C : InverseDomain q Y t) :
    inverseDPart q Y t<1/2 := by
  obtain ⟨_,_,hD,_,hX,_,_⟩ := inverse_radicals C
  have hX0 : 0<adjacent q Y := by linarith [hX.1]
  have hd := inverse_denominator C
  have hd0 : 0<adjacent q Y-transverse q Y*t := by linarith
  have hfirst : transverse q Y/adjacent q Y<2/5 := by
    apply (div_lt_iff₀ hX0).2
    nlinarith [hD.2,hX.1]
  have hq0 : 0≤q := by have hh := C.floor; dsimp [qLow] at hh; linarith
  have ht : t≤41/1000 := by have hh := C.t_mem.2; dsimp [shortTangent] at hh; linarith
  have hnum1 := mul_le_mul C.ceiling ht C.t_mem.1 (by norm_num [qCap] : (0:ℝ)≤qCap)
  have hnum2 := mul_le_mul_of_nonneg_left (show 1-t≤1 by linarith [C.t_mem.1])
    (mul_nonneg hq0 C.t_mem.1)
  have hnum : q*t*(1-t)≤qCap*(41/1000) := by nlinarith
  have hd2 := pow_lt_pow_left₀ (by norm_num : (0:ℝ)≤181/100) hd (by decide : (2:ℕ)≠0)
  have hden := (mul_lt_mul_of_pos_left hd2 (by norm_num : (0:ℝ)<46/25)).trans
    (mul_lt_mul_of_pos_right hX.1 (sq_pos_of_pos hd0))
  have hsecond : q*t*(1-t)/(adjacent q Y*(adjacent q Y-transverse q Y*t)^2)<1/10 := by
    apply (div_lt_iff₀ (mul_pos hX0 (sq_pos_of_pos hd0))).2
    dsimp [qCap] at hnum
    nlinarith
  dsimp [inverseDPart]
  linarith

theorem inverse_radial_factor {q Y t : ℝ} (C : InverseDomain q Y t) :
    2<q/(radius q Y*Y^2) := by
  obtain ⟨_,hR,_,_,_,_,_⟩ := inverse_radicals C
  have hY0 : 0<Y := by linarith [C.Y_mem.1]
  have hR0 : 0<radius q Y := by linarith [hR.1]
  have hY2 := pow_le_pow_left₀ hY0.le C.Y_mem.2 2
  have hprod := mul_le_mul hR.2.le hY2 (sq_nonneg Y) (by norm_num : (0:ℝ)≤43/25)
  apply (lt_div_iff₀ (mul_pos hR0 (sq_pos_of_pos hY0))).2
  have hqL := C.floor
  dsimp [qLow] at hqL
  nlinarith

theorem inverse_rate_derivative_negative {q Y t : ℝ} (C : InverseDomain q Y t) :
    inverseRateD q Y t< -1 := by
  have hE := inverse_E_lower C
  have hR := inverse_radial_factor C
  have hD := inverse_D_part_upper C
  have hm1 := mul_lt_mul_of_pos_right hR (by norm_num : (0:ℝ)<21/25)
  have hm2 := mul_lt_mul_of_pos_left hE (by linarith : 0<q/(radius q Y*Y^2))
  have hid : -q*inverseE q Y t/(radius q Y*Y^2)=
      -((q/(radius q Y*Y^2))*inverseE q Y t) := by ring
  dsimp [inverseRateD]
  rw [hid]
  nlinarith

theorem adjacent_hasDerivAt {q Y t : ℝ} (C : InverseDomain q Y t) :
    HasDerivAt (adjacent q) (transverse q Y*Y/(radius q Y*adjacent q Y)) Y := by
  obtain ⟨hr,hR,_,hx,hX,_,_⟩ := inverse_radicals C
  have hR0 : radius q Y≠0 := (by linarith [hR.1] : 0<radius q Y).ne'
  have hX0 : adjacent q Y≠0 := (by linarith [hX.1] : 0<adjacent q Y).ne'
  have hd : HasDerivAt (transverse q) (-Y/radius q Y) Y := (radius_hasDerivAt hr).sub_const 1
  have hh := ((hd.pow 2).const_sub q).sqrt hx.ne'
  convert hh using 1
  · rfl
  · dsimp [adjacent]
    field_simp [hR0,show Real.sqrt (q-(transverse q Y)^2)≠0 from hX0]
    ring

private theorem inverse_E_derivative_algebra {q R X D Y t : ℝ}
    (hR : R≠0) (hX : X≠0) (hden : X-D*t≠0) (hcircle : X^2+D^2=q) :
    D*Y/(R*X)+t*((D*Y/(R*X)+Y/R)*(X-D*t)-
        (X-D)*(D*Y/(R*X)+t*Y/R))/(X-D*t)^2=
      (Y/R)*(D/X+q*t*(1-t)/(X*(X-D*t)^2)) := by
  have hid : Y*t*((D+X)*(X-D*t)-(X-D)*(D+t*X)-q*(1-t))=0 := by
    linear_combination Y*t*(1-t)*hcircle
  field_simp [hR,hX,hden]
  nlinarith

theorem inverseE_hasDerivAt {q Y t : ℝ} (C : InverseDomain q Y t) :
    HasDerivAt (fun y => inverseE q y t) ((Y/radius q Y)*inverseDPart q Y t) Y := by
  obtain ⟨hr,hR,_,_,hX,_,hcircle⟩ := inverse_radicals C
  have hR0 : radius q Y≠0 := (by linarith [hR.1] : 0<radius q Y).ne'
  have hX0 : adjacent q Y≠0 := (by linarith [hX.1] : 0<adjacent q Y).ne'
  have hd0 : adjacent q Y-transverse q Y*t≠0 :=
    (by linarith [inverse_denominator C] : 0<adjacent q Y-transverse q Y*t).ne'
  have hd : HasDerivAt (transverse q) (-Y/radius q Y) Y := (radius_hasDerivAt hr).sub_const 1
  have hx := adjacent_hasDerivAt C
  have hh := (hx.sub_const 1).add (((hx.sub hd).div (hx.sub (hd.mul_const t)) hd0).const_mul t)
  convert hh using 1
  · funext y
    dsimp [inverseE]
    ring
  · dsimp [inverseDPart]
    have ha := inverse_E_derivative_algebra (q := q) (R := radius q Y) (X := adjacent q Y)
      (D := transverse q Y) (Y := Y) (t := t) hR0 hX0 hd0 hcircle
    convert ha.symm using 1 <;> ring

theorem inverseRate_hasDerivAt {q Y t : ℝ} (C : InverseDomain q Y t) :
    HasDerivAt (fun y => inverseRate q y t) (inverseRateD q Y t) Y := by
  obtain ⟨hr,hR,_,_,_,hcircle,_⟩ := inverse_radicals C
  have hR0 : radius q Y≠0 := (by linarith [hR.1] : 0<radius q Y).ne'
  have hY0 : Y≠0 := (by linarith [C.Y_mem.1] : 0<Y).ne'
  have hh := ((radius_hasDerivAt hr).div (hasDerivAt_id Y) hY0).mul (inverseE_hasDerivAt C)
  convert hh using 1
  · rfl
  · dsimp [inverseRateD]
    field_simp [hR0,hY0]
    nlinarith [congrArg (fun x : ℝ => inverseE q Y t*x) hcircle]

theorem inverse_antitone {q t : ℝ} (hqL : qLow≤q) (hq : q≤qCap)
    (ht : t∈Icc 0 shortTangent) :
    AntitoneOn (fun Y => inverseRate q Y t) (Icc (48/49:ℝ) (26/25)) := by
  apply antiOn_of_hasDeriv_nonpos
  · intro y hy
    exact (inverseRate_hasDerivAt ⟨hqL,hq,hy,ht⟩).continuousAt.continuousWithinAt
  · intro y hy
    exact inverseRate_hasDerivAt ⟨hqL,hq,Ioo_subset_Icc_self hy,ht⟩
  · intro y hy
    exact (inverse_rate_derivative_negative ⟨hqL,hq,Ioo_subset_Icc_self hy,ht⟩).le.trans (by norm_num)

theorem inverse_upper_box {q Y t Rmax Xmin Xmax Dmin Dmax : ℝ}
    (C : InverseDomain q Y t)
    (hR : radius q Y<Rmax) (hXlo : Xmin<adjacent q Y) (hXhi : adjacent q Y<Xmax)
    (hDlo : Dmin<transverse q Y) (hDhi : transverse q Y<Dmax)
    (hDmax : 0≤Dmax) (hden : 0<Xmin-Dmax*shortTangent) :
    inverseRate q Y t<(Rmax/Y)*(Xmax-1+
      shortTangent*(Xmax-Dmin)/(Xmin-Dmax*shortTangent)) := by
  obtain ⟨_,hRi,hDi,_,hXi,_,_⟩ := inverse_radicals C
  have hY0 : 0<Y := by linarith [C.Y_mem.1]
  have hRmax : 0<Rmax := by linarith [hRi.1]
  let d := Xmin-Dmax*shortTangent
  let N := shortTangent*(Xmax-Dmin)
  have ht0 : 0<shortTangent := by norm_num [shortTangent]
  have hN0 : 0<N := by
    dsimp [N]
    apply mul_pos ht0
    linarith [hXi.1,hDi.2]
  have hDt := mul_le_mul hDhi.le C.t_mem.2 C.t_mem.1 hDmax
  have hd : d<adjacent q Y-transverse q Y*t := by dsimp [d]; linarith
  have hd0 : 0<adjacent q Y-transverse q Y*t := lt_trans hden hd
  have hdiff : 0≤adjacent q Y-transverse q Y := by linarith [hXi.1,hDi.2]
  have hn1 := mul_le_mul_of_nonneg_right C.t_mem.2 hdiff
  have hn2 := mul_lt_mul_of_pos_left
    (show adjacent q Y-transverse q Y<Xmax-Dmin by linarith) ht0
  have hnum : t*(adjacent q Y-transverse q Y)<N := by dsimp [N]; linarith
  have hf : t*(adjacent q Y-transverse q Y)/(adjacent q Y-transverse q Y*t)<N/d := by
    apply (div_lt_iff₀ hd0).2
    have hm := mul_lt_mul_of_pos_left hd (div_pos hN0 hden)
    have he : (N/d)*d=N := by field_simp [hden.ne']
    rw [he] at hm
    linarith
  have hE : inverseE q Y t<Xmax-1+N/d := by dsimp [inverseE]; linarith
  have hE0 : 0<inverseE q Y t := by linarith [inverse_E_lower C]
  have hratio := div_lt_div_of_pos_right hR hY0
  have hm := (mul_lt_mul_of_pos_right hratio hE0).trans
    (mul_lt_mul_of_pos_left hE (div_pos hRmax hY0))
  exact hm

theorem inverse_at_one_upper {q t : ℝ} (hqL : qLow≤q) (hq : q≤qCap)
    (ht : t∈Icc 0 shortTangent) : inverseRate q 1 t<1491/1000 := by
  let C : InverseDomain q 1 t := ⟨hqL,hq,by norm_num,ht⟩
  obtain ⟨_,hR,_,_,hX,hR2,hX2⟩ := inverse_radicals C
  have hqL' := hqL
  have hq' := hq
  dsimp [qLow,qCap] at hqL' hq'
  have hRs : radius q 1∈Ioo (8537/5000 : ℝ) (10672/6250) := by
    constructor <;> nlinarith [hR.1]
  have hDs : transverse q 1∈Ioo (3537/5000 : ℝ) (4422/6250) := by
    dsimp [transverse]
    constructor <;> linarith [hRs.1,hRs.2]
  have hXrel : (adjacent q 1)^2=2*radius q 1 := by
    dsimp [transverse] at hX2
    nlinarith
  have hXs : adjacent q 1∈Ioo (18479/10000 : ℝ) (184799/100000) := by
    constructor <;> nlinarith [hX.1,hRs.1,hRs.2]
  have hb := inverse_upper_box C hRs.2 hXs.1 hXs.2 hDs.1 hDs.2
    (by norm_num : (0:ℝ)≤4422/6250)
    (by norm_num [shortTangent] : 0<(18479/10000:ℝ)-(4422/6250)*shortTangent)
  have hk : ((10672/6250:ℝ)/1)*(184799/100000-1+
      shortTangent*(184799/100000-3537/5000)/(18479/10000-(4422/6250)*shortTangent))<1491/1000 := by
    norm_num [shortTangent]
  exact hb.trans hk

theorem inverse_at_floor_upper {q t : ℝ} (hqL : qLow≤q) (hq : q≤qCap)
    (ht : t∈Icc 0 shortTangent) : inverseRate q (48/49) t<153/100 := by
  let C : InverseDomain q (48/49) t := ⟨hqL,hq,by norm_num,ht⟩
  obtain ⟨_,hR,hD,_,hX,hR2,hX2⟩ := inverse_radicals C
  have hqL' := hqL
  have hq' := hq
  dsimp [qLow,qCap] at hqL' hq'
  have hRs : 1719/1000<radius q (48/49) := by nlinarith [hR.1]
  have hDs : 719/1000<transverse q (48/49) := by dsimp [transverse]; linarith
  have hXs : adjacent q (48/49)<461/250 := by
    dsimp [transverse] at hX2
    nlinarith [hR.2,hX.1]
  have hb := inverse_upper_box C hR.2 hX.1 hXs hDs hD.2
    (by norm_num : (0:ℝ)≤18/25)
    (by norm_num [shortTangent] : 0<(46/25:ℝ)-(18/25)*shortTangent)
  have hk : ((43/25:ℝ)/(48/49))*(461/250-1+
      shortTangent*(461/250-719/1000)/(46/25-(18/25)*shortTangent))<153/100 := by
    norm_num [shortTangent]
  exact hb.trans hk

theorem tangent_short {r : ℝ} (hr : r∈Icc (0:ℝ) (1/25)) :
    Real.tan r∈Icc 0 shortTangent := by
  have hi : r∈Icc 0 frameCap := ⟨hr.1,by dsimp [frameCap]; linarith [hr.2]⟩
  have he : (1/25:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have ht := transport_trig hi
  have hc0 : 0<Real.cos r := by linarith [ht.1]
  have hs := CorrelatedSameBlock.sin_mono hi he hr.2
  have hc := CorrelatedSameBlock.cos_anti hi he hr.2
  have hsU := sin_upper_five (show (0:ℝ)≤1/25 by norm_num)
  have hcL := cos_lower_six (show (0:ℝ)≤1/25 by norm_num)
  constructor
  · rw [Real.tan_eq_sin_div_cos]
    exact div_nonneg ht.2.2.1 hc0.le
  · rw [Real.tan_eq_sin_div_cos]
    apply (div_le_iff₀ hc0).2
    dsimp [shortTangent]
    nlinarith

theorem angular_inverse_medium {q Y r : ℝ} (hqL : qLow≤q) (hq : q≤qCap)
    (hY : Y∈Icc (1:ℝ) (26/25)) (hr : r∈Icc (0:ℝ) (1/25)) :
    angularInverseRate q Y r<1491/1000 := by
  have ht := tangent_short hr
  have hm := inverse_antitone hqL hq ht
    (show (1:ℝ)∈Icc (48/49) (26/25) by norm_num)
    (show Y∈Icc (48/49:ℝ) (26/25) from ⟨by linarith [hY.1],hY.2⟩) hY.1
  exact hm.trans_lt (inverse_at_one_upper hqL hq ht)

theorem angular_inverse_small {q Y r : ℝ} (hqL : qLow≤q) (hq : q≤qCap)
    (hY : Y∈Icc (48/49:ℝ) 1) (hr : r∈Icc (0:ℝ) (1/25)) :
    angularInverseRate q Y r<153/100 := by
  have ht := tangent_short hr
  have hm := inverse_antitone hqL hq ht
    (show (48/49:ℝ)∈Icc (48/49) (26/25) by norm_num)
    (show Y∈Icc (48/49:ℝ) (26/25) from ⟨hY.1,by linarith [hY.2]⟩) hY.1
  exact hm.trans_lt (inverse_at_floor_upper hqL hq ht)

end SquaresInCircles.Eight.TableFree.CrossedLowerRate

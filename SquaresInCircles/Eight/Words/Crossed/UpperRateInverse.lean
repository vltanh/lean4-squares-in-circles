module

public import SquaresInCircles.Eight.Words.Crossed.UpperRateEndpoint

/-!
# Eight squares: the inverse-HG rate decreases on the full upper tangent interval

Every radical uses the actual q.  The exact
Y derivative is bounded above by -.9 on the entire feasible transverse
interval, uniformly in tan r <= .0401.  One rational endpoint bounds the
initial inverse rate by 1.43.  No scalar subdivision is used.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CrossedUpperRate
open CrossedClampRates EndpointRotationPenalty

def inverseE (q Y t : ℝ) : ℝ := adjacent q Y-1+
  t*(adjacent q Y-transverse q Y)/(adjacent q Y-transverse q Y*t)
def inverseDPart (q Y t : ℝ) : ℝ := transverse q Y/adjacent q Y+
  q*t*(1-t)/(adjacent q Y*(adjacent q Y-transverse q Y*t)^2)
def inverseRateD (q Y t : ℝ) : ℝ :=
  -q*inverseE q Y t/(CrossedClampRates.radius q Y*Y^2)+inverseDPart q Y t

structure InverseDomain (q Y t : ℝ) : Prop where
  floor : qLow≤q
  ceiling : q≤qCap
  Y_mem : Y∈Icc (26/25 : ℝ) (Real.sqrt (q-9/4))
  t_mem : t∈Icc (0 : ℝ) (401/10000)

theorem inverse_radicals {q Y t : ℝ} (C : InverseDomain q Y t) :
    Y<1291/1000 ∧ 0<q-Y^2 ∧ CrossedClampRates.radius q Y∈Ico (3/2 : ℝ) (427/250) ∧
      transverse q Y∈Ico (1/2 : ℝ) (177/250) ∧
      0<q-(transverse q Y)^2 ∧ adjacent q Y∈Ioo (1847/1000 : ℝ) (383/200) ∧
      (CrossedClampRates.radius q Y)^2+Y^2=q ∧ (adjacent q Y)^2+(transverse q Y)^2=q := by
  have hqL := C.floor
  have hq := C.ceiling
  dsimp [qLow,qCap] at hqL hq
  have hY0 : 0≤Y := by linarith [C.Y_mem.1]
  have htop : 0≤q-9/4 := by linarith
  have htop2 := Real.sq_sqrt htop
  have hY2 := pow_le_pow_left₀ hY0 C.Y_mem.2 2
  have hfloor2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤26/25) C.Y_mem.1 2
  have hYmax : Y<1291/1000 := by nlinarith
  have hr : 0<q-Y^2 := by nlinarith
  have hR0 : 0≤CrossedClampRates.radius q Y := Real.sqrt_nonneg _
  have hR2 : (CrossedClampRates.radius q Y)^2=q-Y^2 := Real.sq_sqrt hr.le
  have hR : CrossedClampRates.radius q Y∈Ico (3/2 : ℝ) (427/250) := by constructor <;> nlinarith
  have hD : transverse q Y∈Ico (1/2 : ℝ) (177/250) := by
    dsimp [transverse]
    constructor <;> linarith [hR.1,hR.2]
  have hD2 := pow_le_pow_left₀ (show 0≤transverse q Y by linarith [hD.1]) hD.2.le 2
  have hx : 0<q-(transverse q Y)^2 := by nlinarith
  have hX0 : 0≤adjacent q Y := Real.sqrt_nonneg _
  have hX2 : (adjacent q Y)^2=q-(transverse q Y)^2 := Real.sq_sqrt hx.le
  have hX : adjacent q Y∈Ioo (1847/1000 : ℝ) (383/200) := by
    constructor <;> nlinarith [hD.1,sq_nonneg (transverse q Y-1/2)]
  exact ⟨hYmax,hr,hR,hD,hx,hX,by nlinarith,by nlinarith⟩

theorem inverse_denominator {q Y t : ℝ} (C : InverseDomain q Y t) :
    (1847/1000-(177/250)*(401/10000) : ℝ)<
      adjacent q Y-transverse q Y*t := by
  obtain ⟨_,_,_,hD,_,hX,_,_⟩ := inverse_radicals C
  have hDt := mul_le_mul hD.2.le C.t_mem.2 C.t_mem.1
    (by norm_num : (0:ℝ)≤177/250)
  linarith [hX.1]

theorem inverse_E_lower {q Y t : ℝ} (C : InverseDomain q Y t) :
    847/1000< inverseE q Y t := by
  obtain ⟨_,_,_,hD,_,hX,_,_⟩ := inverse_radicals C
  have hd := inverse_denominator C
  have hfrac : 0≤t*(adjacent q Y-transverse q Y)/
      (adjacent q Y-transverse q Y*t) := by
    apply div_nonneg
    · exact mul_nonneg C.t_mem.1 (by linarith [hX.1,hD.2])
    · linarith
  dsimp [inverseE]
  linarith [hX.1]

theorem inverse_D_part_upper {q Y t : ℝ} (C : InverseDomain q Y t) :
    inverseDPart q Y t<5/12 := by
  obtain ⟨_,_,_,hD,_,hX,_,_⟩ := inverse_radicals C
  have hX0 : 0<adjacent q Y := by linarith [hX.1]
  have hden := inverse_denominator C
  let d : ℝ := 1847/1000-(177/250)*(401/10000)
  have hd0 : 0<d := by norm_num [d]
  have hden0 : 0<adjacent q Y-transverse q Y*t := lt_trans hd0 hden
  have hk : transverse q Y/adjacent q Y<48/125 := by
    apply (div_lt_iff₀ hX0).2
    nlinarith [hD.2,hX.1]
  have hq0 : 0≤q := by have hh := C.floor; dsimp [qLow] at hh; linarith
  have hqt : q*t≤qCap*(401/10000) :=
    mul_le_mul C.ceiling C.t_mem.2 C.t_mem.1 (by norm_num [qCap])
  have hnum : q*t*(1-t)≤qCap*(401/10000) := by
    have hh := mul_le_mul_of_nonneg_left (show 1-t≤1 by linarith [C.t_mem.1])
      (mul_nonneg hq0 C.t_mem.1)
    nlinarith
  have hd2 := pow_lt_pow_left₀ hden hd0.le (by decide : (2:ℕ)≠0)
  have hbigden := (mul_lt_mul_of_pos_left hd2
      (by norm_num : (0:ℝ)<1847/1000)).trans
    (mul_lt_mul_of_pos_right hX.1 (sq_pos_of_pos hden0))
  let M : ℝ := qCap*(401/10000)/((1847/1000)*d^2)
  have hM : 0<M := by norm_num [M,d,qCap]
  have hsecond : q*t*(1-t)/(adjacent q Y*(adjacent q Y-transverse q Y*t)^2)<M := by
    apply (div_lt_iff₀ (mul_pos hX0 (sq_pos_of_pos hden0))).2
    have hm := mul_lt_mul_of_pos_left hbigden hM
    have hcancel : M*((1847/1000)*d^2)=qCap*(401/10000) := by
      dsimp [M]
      field_simp [hd0.ne']
    rw [hcancel] at hm
    exact hnum.trans_lt hm
  have hscalar : 48/125+M<5/12 := by norm_num [M,d,qCap]
  dsimp [inverseDPart]
  linarith

/-- The sharp monotone factor is a cubic with a factor R-3/2.
The actual-q term has the same favorable sign as qCap-q. -/
theorem inverse_radial_factor {q Y t : ℝ} (C : InverseDomain q Y t) :
    3263/2082≤q/(CrossedClampRates.radius q Y*Y^2) := by
  obtain ⟨_,_,hR,_,_,_,hcircle,_⟩ := inverse_radicals C
  have hY0 : 0<Y := by linarith [C.Y_mem.1]
  have hR0 : 0<CrossedClampRates.radius q Y := by linarith [hR.1]
  have hden : 0<CrossedClampRates.radius q Y*Y^2 := mul_pos hR0 (sq_pos_of_pos hY0)
  apply (le_div_iff₀ hden).2
  have hc : 0≤(CrossedClampRates.radius q Y)^2+(3/2)*CrossedClampRates.radius q Y+9/4-qCap := by
    dsimp [qCap]
    nlinarith [hR.1]
  have hfactor := mul_nonneg (show 0≤CrossedClampRates.radius q Y-3/2 by linarith [hR.1]) hc
  have hqterm := mul_nonneg (sub_nonneg.mpr C.ceiling)
    (show 0≤(3263/2082)*CrossedClampRates.radius q Y-1 by linarith [hR.1])
  have hid : q-(3263/2082)*CrossedClampRates.radius q Y*Y^2=
      (3263/2082)*(CrossedClampRates.radius q Y-3/2)*
        ((CrossedClampRates.radius q Y)^2+(3/2)*CrossedClampRates.radius q Y+9/4-qCap)+
      (qCap-q)*((3263/2082)*CrossedClampRates.radius q Y-1) := by
    dsimp [qCap]
    linear_combination -((3263/2082)*CrossedClampRates.radius q Y)*hcircle
  nlinarith

theorem inverse_rate_derivative_upper {q Y t : ℝ} (C : InverseDomain q Y t) :
    inverseRateD q Y t< -(9/10 : ℝ) := by
  have hE := inverse_E_lower C
  have hR := inverse_radial_factor C
  have hD := inverse_D_part_upper C
  have hR0 : 0<q/(CrossedClampRates.radius q Y*Y^2) := by linarith
  have hproduct := (mul_le_mul_of_nonneg_right hR
      (by norm_num : (0:ℝ)≤847/1000)).trans_lt
    (mul_lt_mul_of_pos_left hE hR0)
  have hid : -q*inverseE q Y t/(CrossedClampRates.radius q Y*Y^2)=
      -((q/(CrossedClampRates.radius q Y*Y^2))*inverseE q Y t) := by ring
  dsimp [inverseRateD]
  rw [hid]
  nlinarith

theorem adjacent_hasDerivAt {q Y t : ℝ} (C : InverseDomain q Y t) :
    HasDerivAt (adjacent q)
      (transverse q Y*Y/(CrossedClampRates.radius q Y*adjacent q Y)) Y := by
  obtain ⟨_,hr,hR,_,hx,hX,_,_⟩ := inverse_radicals C
  have hR0 : CrossedClampRates.radius q Y≠0 := (by linarith [hR.1] : 0<CrossedClampRates.radius q Y).ne'
  have hX0 : adjacent q Y≠0 := (by linarith [hX.1] : 0<adjacent q Y).ne'
  have hd : HasDerivAt (transverse q) (-Y/CrossedClampRates.radius q Y) Y :=
    (radius_hasDerivAt hr).sub_const 1
  have hh := ((hd.pow 2).const_sub q).sqrt hx.ne'
  convert hh using 1
  · rfl
  · dsimp [adjacent]
    field_simp [hR0,show Real.sqrt (q-(transverse q Y)^2)≠0 from hX0]

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
    HasDerivAt (fun y => inverseE q y t)
      ((Y/CrossedClampRates.radius q Y)*inverseDPart q Y t) Y := by
  obtain ⟨_,hr,hR,_,_,hX,_,hcircle⟩ := inverse_radicals C
  have hR0 : CrossedClampRates.radius q Y≠0 := (by linarith [hR.1] : 0<CrossedClampRates.radius q Y).ne'
  have hX0 : adjacent q Y≠0 := (by linarith [hX.1] : 0<adjacent q Y).ne'
  have hd0 : adjacent q Y-transverse q Y*t≠0 :=
    (by linarith [inverse_denominator C] : 0<adjacent q Y-transverse q Y*t).ne'
  have hd : HasDerivAt (transverse q) (-Y/CrossedClampRates.radius q Y) Y :=
    (radius_hasDerivAt hr).sub_const 1
  have hx := adjacent_hasDerivAt C
  have hh := (hx.sub_const 1).add (((hx.sub hd).div (hx.sub (hd.mul_const t)) hd0).const_mul t)
  convert hh using 1
  · funext y
    dsimp [inverseE]
    ring
  · dsimp [inverseDPart]
    have ha := inverse_E_derivative_algebra (q := q) (R := CrossedClampRates.radius q Y) (X := adjacent q Y)
      (D := transverse q Y) (Y := Y) (t := t) hR0 hX0 hd0 hcircle
    convert ha.symm using 1 <;> ring

theorem inverseRate_hasDerivAt {q Y t : ℝ} (C : InverseDomain q Y t) :
    HasDerivAt (fun y => inverseRate q y t) (inverseRateD q Y t) Y := by
  obtain ⟨_,hr,hR,_,_,_,hcircle,_⟩ := inverse_radicals C
  have hR0 : CrossedClampRates.radius q Y≠0 := (by linarith [hR.1] : 0<CrossedClampRates.radius q Y).ne'
  have hY0 : Y≠0 := (by linarith [C.Y_mem.1] : 0<Y).ne'
  have hh := ((radius_hasDerivAt hr).div (hasDerivAt_id Y) hY0).mul (inverseE_hasDerivAt C)
  convert hh using 1
  · rfl
  · dsimp [inverseRateD]
    field_simp [hR0,hY0]
    nlinarith [congrArg (fun x : ℝ => inverseE q Y t*x) hcircle]

theorem base_inverse_domain {q t : ℝ} (hqL : qLow≤q) (hq : q≤qCap)
    (ht : t∈Icc (0 : ℝ) (401/10000)) : InverseDomain q (26/25) t := by
  refine ⟨hqL,hq,⟨le_rfl,?_⟩,ht⟩
  have hqL' := hqL
  dsimp [qLow] at hqL'
  have hr : 0≤q-9/4 := by linarith
  have hR0 := Real.sqrt_nonneg (q-9/4)
  have hR2 := Real.sq_sqrt hr
  nlinarith

theorem base_inverse_upper {q t : ℝ} (hqL : qLow≤q) (hq : q≤qCap)
    (ht : t∈Icc (0 : ℝ) (401/10000)) : inverseRate q (26/25) t<143/100 := by
  let C := base_inverse_domain hqL hq ht
  obtain ⟨_,_,hR,hD,_,hX,hR2,hX2⟩ := inverse_radicals C
  have hqL' := hqL
  have hq' := hq
  dsimp [qLow,qCap] at hqL' hq'
  have hRsharp : CrossedClampRates.radius q (26/25)∈Ioo (16833/10000 : ℝ) (3367/2000) := by
    constructor <;> nlinarith [hR.1]
  have hDsharp : 6833/10000<transverse q (26/25) := by
    dsimp [transverse]
    linarith [hRsharp.1]
  have hXsharp : adjacent q (26/25)<18571/10000 := by
    nlinarith [hX.1]
  let d : ℝ := 1847/1000-(177/250)*(401/10000)
  let N : ℝ := (401/10000)*(18571/10000-6833/10000)
  let M : ℝ := 18571/10000-1+N/d
  have hd0 : 0<d := by norm_num [d]
  have hden := inverse_denominator C
  have hden0 : 0<adjacent q (26/25)-transverse q (26/25)*t := lt_trans hd0 hden
  have hdiff : 0≤adjacent q (26/25)-transverse q (26/25) := by linarith [hX.1,hD.2]
  have hn1 := mul_le_mul_of_nonneg_right ht.2 hdiff
  have hn2 := mul_lt_mul_of_pos_left
    (show adjacent q (26/25)-transverse q (26/25)<18571/10000-6833/10000 by linarith)
    (by norm_num : (0:ℝ)<401/10000)
  have hnum : t*(adjacent q (26/25)-transverse q (26/25))<N := by dsimp [N]; linarith
  have hf : t*(adjacent q (26/25)-transverse q (26/25))/
      (adjacent q (26/25)-transverse q (26/25)*t)<N/d := by
    apply (div_lt_iff₀ hden0).2
    have hm := mul_lt_mul_of_pos_left hden (show 0<N/d by norm_num [N,d])
    have hid : (N/d)*d=N := by field_simp [hd0.ne']
    rw [hid] at hm
    linarith
  have hE : inverseE q (26/25) t<M := by dsimp [inverseE,M]; linarith
  have hE0 : 0< inverseE q (26/25) t := by linarith [inverse_E_lower C]
  have hM0 : 0<M := by norm_num [M,N,d]
  have hratio : CrossedClampRates.radius q (26/25)/(26/25)<(3367/2000)/(26/25) := by
    exact div_lt_div_of_pos_right hRsharp.2 (by norm_num)
  have hprod := (mul_lt_mul_of_pos_right hratio hE0).trans
    (mul_lt_mul_of_pos_left hE (by norm_num : (0:ℝ)<(3367/2000)/(26/25)))
  have hconst : ((3367/2000)/(26/25))*M<143/100 := by norm_num [M,N,d]
  change (CrossedClampRates.radius q (26/25)/(26/25))*inverseE q (26/25) t<143/100
  exact hprod.trans hconst

theorem tangent_short {r : ℝ} (hr : r∈Icc (0 : ℝ) (1/25)) :
    Real.tan r∈Icc (0 : ℝ) (401/10000) := by
  have hi : r∈Icc 0 frameCap := ⟨hr.1,by dsimp [frameCap]; linarith [hr.2]⟩
  have he : (1/25 : ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have ht := transport_trig hi
  have hcos : 0<Real.cos r := by linarith [ht.1]
  have hs := CorrelatedSameBlock.sin_mono hi he hr.2
  have hc := CorrelatedSameBlock.cos_anti hi he hr.2
  have hsU := sin_upper_five (show (0:ℝ)≤1/25 by norm_num)
  have hcL := cos_lower_six (show (0:ℝ)≤1/25 by norm_num)
  constructor
  · rw [Real.tan_eq_sin_div_cos]
    exact div_nonneg ht.2.2.1 hcos.le
  · rw [Real.tan_eq_sin_div_cos,div_le_iff₀ hcos]
    norm_num at hsU hcL
    linarith

end SquaresInCircles.Eight.CrossedUpperRate

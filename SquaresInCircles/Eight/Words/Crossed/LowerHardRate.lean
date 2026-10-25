module

public import Mathlib.Algebra.Ring.IsFormallyReal
public import SquaresInCircles.Eight.Words.Crossed.ClampBudget
public import SquaresInCircles.Eight.Words.Crossed.UpperRateEndpoint

/-!
# Eight squares: opposite hard-cap rates on the lower active tangent interval

In the actual q interval the hard rate is
antitone in both B and u on their complete lower-tangent domains.  Its
two endpoint estimates use cubic lower sine, quadratic lower cosine,
and quintic upper sine.  Their rational reserves exceed the inverse-HG
endpoint bounds, without varying or normalizing the original H/T data.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CrossedLowerRate
open CrossedClampRates EndpointRotationPenalty
open CrossedClampBudget (U V U_hasDerivAt)
open CrossedUpperRate (radius_hasDerivAt)

structure HardDomain (q B : ℝ) : Prop where
  floor : qLow≤q
  ceiling : q≤qCap
  B_mem : B∈Icc (24/25:ℝ) charge

def physicalRate (q B u : ℝ) : ℝ :=
  CrossedClampRates.radius q B*U q B u/(U q B u+Real.sin u)
def physicalRateB (q B u : ℝ) : ℝ :=
  (-B*U q B u*(U q B u+Real.sin u)+
      (CrossedClampRates.radius q B)^2*Real.sin u*Real.cos u-CrossedClampRates.radius q B*B*(Real.sin u)^2)/
    (CrossedClampRates.radius q B*(U q B u+Real.sin u)^2)

theorem hard_radicals {q B : ℝ} (C : HardDomain q B) :
    0<q-B^2 ∧ CrossedClampRates.radius q B∈Ioo (169/100:ℝ) (1731/1000) ∧
      (CrossedClampRates.radius q B)^2+B^2=q := by
  have hqL := C.floor
  have hq := C.ceiling
  have hB := C.B_mem
  dsimp [qLow,qCap] at hqL hq
  dsimp [charge] at hB
  have hB0 : 0≤B := by linarith [hB.1]
  have hB2 := pow_le_pow_left₀ hB0 hB.2 2
  have hr : 0<q-B^2 := by nlinarith
  have hZ0 : 0≤CrossedClampRates.radius q B := Real.sqrt_nonneg _
  have hZ2 : (CrossedClampRates.radius q B)^2=q-B^2 := Real.sq_sqrt hr.le
  have hZ : CrossedClampRates.radius q B∈Ioo (169/100:ℝ) (1731/1000) := by
    constructor <;> nlinarith [hB.1,sq_nonneg (B-24/25)]
  exact ⟨hr,hZ,by nlinarith⟩

theorem hard_rotated_bounds {q B u : ℝ} (C : HardDomain q B)
    (hu : u∈Icc (0:ℝ) (79/500)) :
    0<Real.cos u ∧ 0≤Real.sin u ∧
      47/50<U q B u ∧ 0<U q B u+Real.sin u := by
  obtain ⟨_,hZ,_⟩ := hard_radicals C
  have hi : u∈Icc 0 frameCap := ⟨hu.1,by dsimp [frameCap]; linarith [hu.2]⟩
  have ht := transport_trig hi
  have hu2 := pow_le_pow_left₀ hu.1 hu.2 2
  have hcL : 1-(79/500:ℝ)^2/2≤Real.cos u := by
    linarith [Real.one_sub_sq_div_two_le_cos (x := u)]
  have hc0 : 0<Real.cos u := by linarith
  have hP : 0≤CrossedClampRates.radius q B-1 := by linarith [hZ.1]
  have hm1 := mul_nonneg hP ht.2.2.1
  have hm2 := mul_le_mul C.B_mem.1 hcL
    (by norm_num : (0:ℝ)≤1-(79/500:ℝ)^2/2)
    (by linarith [C.B_mem.1] : 0≤B)
  have hU : 47/50<U q B u := by dsimp [U]; linarith
  exact ⟨hc0,ht.2.2.1,hU,by linarith⟩

theorem physicalRate_eq_angular {q B u : ℝ} (C : HardDomain q B)
    (hu : u∈Icc (0:ℝ) (79/500)) : physicalRate q B u=angularHardRate q B u := by
  obtain ⟨hc,_,_,hS⟩ := hard_rotated_bounds C hu
  have hden : B*Real.cos u+CrossedClampRates.radius q B*Real.sin u≠0 := by
    have he : B*Real.cos u+CrossedClampRates.radius q B*Real.sin u=U q B u+Real.sin u := by dsimp [U]; ring
    rw [he]
    exact hS.ne'
  have h1 : B+(CrossedClampRates.radius q B-1)*(Real.sin u/Real.cos u)=U q B u/Real.cos u := by
    dsimp [U]; field_simp; ring
  have h2 : B+CrossedClampRates.radius q B*(Real.sin u/Real.cos u)=(U q B u+Real.sin u)/Real.cos u := by
    dsimp [U]; field_simp; ring
  dsimp [physicalRate,angularHardRate,hardRate]
  rw [Real.tan_eq_sin_div_cos,h1,h2]
  field_simp

theorem physicalRate_u_hasDerivAt {q B u : ℝ} (C : HardDomain q B)
    (hu : u∈Icc (0:ℝ) (79/500)) :
    HasDerivAt (physicalRate q B)
      (-CrossedClampRates.radius q B*B/(U q B u+Real.sin u)^2) u := by
  have hS := (hard_rotated_bounds C hu).2.2.2
  have hd := ((U_hasDerivAt q B u).const_mul (CrossedClampRates.radius q B)).div
    ((U_hasDerivAt q B u).add (Real.hasDerivAt_sin u)) hS.ne'
  have hid : V q B u*Real.sin u-U q B u*Real.cos u= -B := by
    dsimp [U,V]
    linear_combination -B*(Real.sin_sq_add_cos_sq u)
  convert hd using 1
  · funext x; simp only [physicalRate,Pi.div_apply,Pi.add_apply]
  · show _=(CrossedClampRates.radius q B*V q B u*(U q B u+Real.sin u)-CrossedClampRates.radius q B*U q B u*(V q B u+Real.cos u))/
      (U q B u+Real.sin u)^2
    rw [div_left_inj' (pow_ne_zero 2 hS.ne')]
    linear_combination (-CrossedClampRates.radius q B)*hid

theorem physicalRate_B_hasDerivAt {q B u : ℝ} (C : HardDomain q B)
    (hu : u∈Icc (0:ℝ) (79/500)) :
    HasDerivAt (fun b => physicalRate q b u) (physicalRateB q B u) B := by
  obtain ⟨hr,hZ,_⟩ := hard_radicals C
  have hZ0 : CrossedClampRates.radius q B≠0 := (by linarith [hZ.1] : 0<CrossedClampRates.radius q B).ne'
  have hS := (hard_rotated_bounds C hu).2.2.2
  have hz := radius_hasDerivAt hr
  have hU : HasDerivAt (fun b => U q b u)
      (-B/CrossedClampRates.radius q B*Real.sin u+Real.cos u) B := by
    have h := ((hz.sub_const 1).mul_const (Real.sin u)).add
      ((hasDerivAt_id' B).mul_const (Real.cos u))
    rw [one_mul] at h
    exact h
  have hd := (hz.mul hU).div (hU.add_const (Real.sin u)) hS.ne'
  convert hd using 1
  · rfl
  · dsimp [physicalRateB]
    field_simp [hZ0,hS.ne']
    ring

theorem physicalRate_B_negative {q B u : ℝ} (C : HardDomain q B)
    (hu : u∈Icc (0:ℝ) (79/500)) : physicalRateB q B u<0 := by
  obtain ⟨_,hZ,hcircle⟩ := hard_radicals C
  obtain ⟨hc,hs,hU,hS⟩ := hard_rotated_bounds C hu
  have hB0 : 0<B := by linarith [C.B_mem.1]
  have hZ0 : 0<CrossedClampRates.radius q B := by linarith [hZ.1]
  have hSlo : 47/50<U q B u+Real.sin u := by linarith
  have hUS := mul_le_mul hU.le hSlo.le
    (by norm_num : (0:ℝ)≤47/50) (by linarith : 0≤U q B u)
  have hBUS := mul_le_mul C.B_mem.1 hUS (by norm_num) hB0.le
  have hsin := Real.sin_le hu.1
  have hsc1 := mul_le_mul_of_nonneg_left (Real.cos_le_one u) hs
  have hsc : Real.sin u*Real.cos u≤79/500 := by linarith [hu.2]
  have hZ2 : (CrossedClampRates.radius q B)^2≤qCap := by linarith [C.ceiling,sq_nonneg B]
  have hterm := mul_le_mul hZ2 hsc (mul_nonneg hs hc.le)
    (by norm_num [qCap] : (0:ℝ)≤qCap)
  have hlast := mul_nonneg (mul_nonneg hZ0.le hB0.le) (sq_nonneg (Real.sin u))
  have hnum : -B*U q B u*(U q B u+Real.sin u)+
      (CrossedClampRates.radius q B)^2*Real.sin u*Real.cos u-CrossedClampRates.radius q B*B*(Real.sin u)^2<0 := by
    dsimp [qCap] at hterm
    linarith
  dsimp [physicalRateB]
  exact div_neg_of_neg_of_pos hnum (mul_pos hZ0 (sq_pos_of_pos hS))

theorem physicalRate_antitone_B {q u : ℝ} (hqL : qLow≤q) (hq : q≤qCap)
    (hu : u∈Icc (0:ℝ) (79/500)) :
    AntitoneOn (fun B => physicalRate q B u) (Icc (24/25:ℝ) charge) := by
  apply antiOn_of_hasDeriv_nonpos
  · intro B hB
    exact (physicalRate_B_hasDerivAt ⟨hqL,hq,hB⟩ hu).continuousAt.continuousWithinAt
  · intro B hB
    exact physicalRate_B_hasDerivAt ⟨hqL,hq,Ioo_subset_Icc_self hB⟩ hu
  · intro B hB
    exact (physicalRate_B_negative ⟨hqL,hq,Ioo_subset_Icc_self hB⟩ hu).le

theorem physicalRate_antitone_u {q B : ℝ} (C : HardDomain q B) :
    AntitoneOn (physicalRate q B) (Icc (0:ℝ) (79/500)) := by
  apply antiOn_of_hasDeriv_nonpos
  · intro u hu
    exact (physicalRate_u_hasDerivAt C hu).continuousAt.continuousWithinAt
  · intro u hu
    exact physicalRate_u_hasDerivAt C (Ioo_subset_Icc_self hu)
  · intro u hu
    obtain ⟨_,hZ,_⟩ := hard_radicals C
    apply div_nonpos_of_nonpos_of_nonneg
    · have hh := mul_nonneg (by linarith [hZ.1] : 0≤CrossedClampRates.radius q B)
        (by linarith [C.B_mem.1] : 0≤B)
      nlinarith
    · exact sq_nonneg _

def endpointUlower (Z B u : ℝ) : ℝ :=
  (Z-1)*(u-u^3/6)+B*(1-u^2/2)
def endpointSinUpper (u : ℝ) : ℝ := u-u^3/6+u^5/120
def endpointLower (Z B u : ℝ) : ℝ :=
  Z*endpointUlower Z B u/(endpointUlower Z B u+endpointSinUpper u)

theorem physical_endpoint_lower {q B u Z : ℝ} (C : HardDomain q B)
    (hu : u∈Icc (0:ℝ) (79/500)) (hZ : 1<Z) (hZq : Z<CrossedClampRates.radius q B)
    (hU : 0<endpointUlower Z B u) : endpointLower Z B u<physicalRate q B u := by
  obtain ⟨_,hs,hUa,hS⟩ := hard_rotated_bounds C hu
  have hB0 : 0≤B := by linarith [C.B_mem.1]
  have hsL := Real.sin_ge_sub_cube hu.1
  have hcL := Real.one_sub_sq_div_two_le_cos (x := u)
  have hsU : Real.sin u≤endpointSinUpper u := sin_upper_five hu.1
  have hsl : 0≤u-u^3/6 := by
    have hu2 := pow_le_pow_left₀ hu.1 hu.2 2
    have hh := mul_nonneg hu.1 (show 0≤1-u^2/6 by linarith)
    linarith
  have hpart1 := mul_le_mul (show Z-1≤CrossedClampRates.radius q B-1 by linarith) hsL hsl
    (by linarith : 0≤CrossedClampRates.radius q B-1)
  have hpart2 := mul_le_mul_of_nonneg_left hcL hB0
  have hUl : endpointUlower Z B u≤U q B u := by dsimp [endpointUlower,U]; linarith
  have hsUp0 : 0≤endpointSinUpper u := hs.trans hsU
  have hden0 : 0<endpointUlower Z B u+endpointSinUpper u := add_pos_of_pos_of_nonneg hU hsUp0
  have hcross := mul_le_mul hUl hsU hs (by linarith : 0≤U q B u)
  have hstrict := mul_pos (sub_pos.mpr hZq)
    (mul_pos (by linarith : 0<U q B u) hden0)
  have hweak := mul_nonneg (by linarith : 0≤Z)
    (show 0≤U q B u*endpointSinUpper u-endpointUlower Z B u*Real.sin u by linarith)
  dsimp [endpointLower,physicalRate]
  apply (div_lt_div_iff₀ hden0 hS).2
  linarith

theorem hard_at_one_lower {q : ℝ} (hqL : qLow≤q) (hq : q≤qCap) :
    1493/1000<physicalRate q 1 (79/500) := by
  let C : HardDomain q 1 := ⟨hqL,hq,by norm_num [charge]⟩
  obtain ⟨_,hZ,hcircle⟩ := hard_radicals C
  have hqL' := hqL
  dsimp [qLow] at hqL'
  have hZsharp : 8537/5000<CrossedClampRates.radius q 1 := by nlinarith [hZ.1]
  have hh := physical_endpoint_lower C (show (79/500:ℝ)∈Icc 0 (79/500) by norm_num)
    (by norm_num : (1:ℝ)<8537/5000) hZsharp
    (by norm_num [endpointUlower] : 0<endpointUlower (8537/5000) 1 (79/500))
  have hn : 1493/1000<endpointLower (8537/5000) 1 (79/500) := by
    norm_num [endpointLower,endpointUlower,endpointSinUpper]
  exact hn.trans hh

theorem hard_at_charge_lower {q : ℝ} (hqL : qLow≤q) (hq : q≤qCap) :
    8/5<physicalRate q charge (3/50) := by
  let C : HardDomain q charge := ⟨hqL,hq,by norm_num [charge]⟩
  obtain ⟨_,hZ,hcircle⟩ := hard_radicals C
  have hqL' := hqL
  dsimp [qLow] at hqL'
  have hZsharp : 339/200<CrossedClampRates.radius q charge := by
    simp only [charge] at hcircle hZ ⊢
    nlinarith [hZ.1]
  have hh := physical_endpoint_lower C (show (3/50:ℝ)∈Icc 0 (79/500) by norm_num)
    (by norm_num : (1:ℝ)<339/200) hZsharp
    (by norm_num [endpointUlower,charge] : 0<endpointUlower (339/200) charge (3/50))
  have hn : 8/5<endpointLower (339/200) charge (3/50) := by
    norm_num [endpointLower,endpointUlower,endpointSinUpper,charge]
  exact hn.trans hh

theorem angular_hard_medium {q B u : ℝ} (hqL : qLow≤q) (hq : q≤qCap)
    (hB : B∈Icc (24/25:ℝ) 1) (hu : u∈Icc (0:ℝ) (79/500)) :
    1493/1000<angularHardRate q B u := by
  have hBc : B∈Icc (24/25:ℝ) charge := ⟨hB.1,by dsimp [charge]; linarith [hB.2]⟩
  have h1c : (1:ℝ)∈Icc (24/25) charge := by norm_num [charge]
  have hmB := physicalRate_antitone_B hqL hq hu hBc h1c hB.2
  have hmu := physicalRate_antitone_u (show HardDomain q 1 from ⟨hqL,hq,h1c⟩)
    hu (show (79/500:ℝ)∈Icc 0 (79/500) by norm_num) hu.2
  have hh := hard_at_one_lower hqL hq
  rw [←physicalRate_eq_angular (show HardDomain q B from ⟨hqL,hq,hBc⟩) hu]
  linarith

theorem angular_hard_small {q B u : ℝ} (hqL : qLow≤q) (hq : q≤qCap)
    (hB : B∈Icc (1:ℝ) charge) (hu : u∈Icc (0:ℝ) (3/50)) :
    8/5<angularHardRate q B u := by
  have hBc : B∈Icc (24/25:ℝ) charge := ⟨by linarith [hB.1],hB.2⟩
  have hpc : charge∈Icc (24/25:ℝ) charge := by norm_num [charge]
  have hui : u∈Icc (0:ℝ) (79/500) := ⟨hu.1,by linarith [hu.2]⟩
  have hmB := physicalRate_antitone_B hqL hq hui hBc hpc hB.2
  have hmu := physicalRate_antitone_u (show HardDomain q charge from ⟨hqL,hq,hpc⟩)
    hui (show (3/50:ℝ)∈Icc 0 (79/500) by norm_num) hu.2
  have hh := hard_at_charge_lower hqL hq
  rw [←physicalRate_eq_angular (show HardDomain q B from ⟨hqL,hq,hBc⟩) hui]
  linarith

end SquaresInCircles.Eight.CrossedLowerRate

module

public import SquaresInCircles.Eight.TableFree.CrossedClampRates

/-!
# Exact opposite hard endpoint for the upper crossed clamp rate

Uncompiled source draft.  The zero-tangent hard endpoint is represented
by its algebraic sine and cosine.  Its contact, unit-circle identity,
derivatives, and comparison with every actual hard angle are proved
directly.  No inverse-angle function or selected optimizer is assumed.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.CrossedUpperRate
open CrossedClampRates EndpointRotationPenalty

def endpointL (q B : ℝ) : ℝ := q+1-2*CrossedClampRates.radius q B
def endpointU (q B : ℝ) : ℝ := Real.sqrt (q+3/4-2*CrossedClampRates.radius q B)
def endpointSin (q B : ℝ) : ℝ :=
  ((CrossedClampRates.radius q B-1)*endpointU q B-B/2)/endpointL q B
def endpointCos (q B : ℝ) : ℝ :=
  ((CrossedClampRates.radius q B-1)/2+B*endpointU q B)/endpointL q B
def endpointSum (q B : ℝ) : ℝ := endpointU q B+endpointSin q B
def endpointRate (q B : ℝ) : ℝ := CrossedClampRates.radius q B*endpointU q B/endpointSum q B
def endpointRateD (q B : ℝ) : ℝ :=
  (endpointCos q B-B*endpointU q B/CrossedClampRates.radius q B)/endpointSum q B+
    B*endpointSin q B/(endpointU q B*(endpointSum q B)^2)

structure EndpointDomain (q B : ℝ) : Prop where
  floor : qLow≤q
  ceiling : q≤qCap
  B_mem : B∈Icc (709/1000 : ℝ) (24/25)

theorem endpoint_radicals {q B : ℝ} (C : EndpointDomain q B) :
    0<q-B^2 ∧ CrossedClampRates.radius q B∈Ioo (173/100 : ℝ) (231/125) ∧
      0<q+3/4-2*CrossedClampRates.radius q B ∧ endpointU q B∈Ioo (49/50 : ℝ) (11/10) ∧
      0<endpointL q B ∧ (CrossedClampRates.radius q B)^2+B^2=q ∧
      (endpointU q B)^2=endpointL q B-1/4 ∧
      endpointL q B=(CrossedClampRates.radius q B-1)^2+B^2 := by
  have hB0 : 0≤B := by linarith [C.B_mem.1]
  have hB2 := pow_le_pow_left₀ hB0 C.B_mem.2 2
  have hBl := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤709/1000) C.B_mem.1 2
  have hqL := C.floor
  have hq := C.ceiling
  dsimp [qLow,qCap] at hqL hq
  have hr : 0<q-B^2 := by nlinarith
  have hZ0 : 0≤CrossedClampRates.radius q B := Real.sqrt_nonneg _
  have hZ2 : (CrossedClampRates.radius q B)^2=q-B^2 := Real.sq_sqrt hr.le
  have hZ : CrossedClampRates.radius q B∈Ioo (173/100 : ℝ) (231/125) := by
    constructor <;> nlinarith
  have hu : 0<q+3/4-2*CrossedClampRates.radius q B := by linarith [hZ.2]
  have hU0 : 0≤endpointU q B := Real.sqrt_nonneg _
  have hU2 : (endpointU q B)^2=q+3/4-2*CrossedClampRates.radius q B := Real.sq_sqrt hu.le
  have hU : endpointU q B∈Ioo (49/50 : ℝ) (11/10) := by
    constructor <;> nlinarith [hZ.1,hZ.2]
  refine ⟨hr,hZ,hu,hU,?_,by nlinarith,?_,?_⟩
  · dsimp [endpointL]
    linarith
  · dsimp [endpointL]
    linarith
  · dsimp [endpointL]
    nlinarith

theorem endpoint_identities {q B : ℝ} (C : EndpointDomain q B) :
    (CrossedClampRates.radius q B-1)*endpointCos q B-B*endpointSin q B=1/2 ∧
      (CrossedClampRates.radius q B-1)*endpointSin q B+B*endpointCos q B=endpointU q B ∧
      (endpointSin q B)^2+(endpointCos q B)^2=1 ∧
      B=endpointU q B*endpointCos q B-endpointSin q B/2 := by
  obtain ⟨_,_,_,_,hL,hZ,hU,hcircle⟩ := endpoint_radicals C
  have hc : (CrossedClampRates.radius q B-1)*endpointCos q B-B*endpointSin q B=1/2 := by
    dsimp [endpointCos,endpointSin]
    field_simp [hL.ne']
    nlinarith
  have hs : (CrossedClampRates.radius q B-1)*endpointSin q B+B*endpointCos q B=endpointU q B := by
    dsimp [endpointCos,endpointSin]
    field_simp [hL.ne']
    nlinarith [congrArg (fun x : ℝ => endpointU q B*x) hcircle]
  have hnorm : (endpointSin q B)^2+(endpointCos q B)^2=1 := by
    have hid : ((CrossedClampRates.radius q B-1)*endpointCos q B-B*endpointSin q B)^2+
        ((CrossedClampRates.radius q B-1)*endpointSin q B+B*endpointCos q B)^2=
        endpointL q B*((endpointSin q B)^2+(endpointCos q B)^2) := by
      rw [hcircle]
      ring
    rw [hc,hs] at hid
    apply mul_left_cancel₀ hL.ne'
    nlinarith
  have hinv : B=endpointU q B*endpointCos q B-endpointSin q B/2 := by
    have hid : ((CrossedClampRates.radius q B-1)*endpointSin q B+B*endpointCos q B)*endpointCos q B-
        ((CrossedClampRates.radius q B-1)*endpointCos q B-B*endpointSin q B)*endpointSin q B=
        B*((endpointSin q B)^2+(endpointCos q B)^2) := by ring
    rw [hc,hs,hnorm] at hid
    linarith
  exact ⟨hc,hs,hnorm,hinv⟩

theorem endpoint_trig {q B : ℝ} (C : EndpointDomain q B) :
    endpointSin q B∈Ioo (0 : ℝ) (2/5) ∧
      endpointCos q B∈Ioc (0 : ℝ) 1 := by
  obtain ⟨_,hZ,_,hU,hL,_,hU2,hcircle⟩ := endpoint_radicals C
  obtain ⟨hcontact,_,hnorm,_⟩ := endpoint_identities C
  have hB : 0<B := by linarith [C.B_mem.1]
  have hP : 0<CrossedClampRates.radius q B-1 := by linarith [hZ.1]
  have hU0 : 0<endpointU q B := by linarith [hU.1]
  have hnum : 0<(CrossedClampRates.radius q B-1)*endpointU q B-B/2 := by
    have hpU := mul_pos hP hU0
    have hid : ((CrossedClampRates.radius q B-1)*endpointU q B)^2-(B/2)^2=
        endpointL q B*((CrossedClampRates.radius q B-1)^2-1/4) := by
      linear_combination (CrossedClampRates.radius q B-1)^2*hU2+(1/4)*hcircle
    have hpp : 0<(CrossedClampRates.radius q B-1)^2-1/4 := by
      have h := pow_lt_pow_left₀ (show (1/2:ℝ)<CrossedClampRates.radius q B-1 by linarith [hZ.1]) (by norm_num)
        two_ne_zero
      linarith
    have hsq : (B/2)^2<((CrossedClampRates.radius q B-1)*endpointU q B)^2 := by linarith [mul_pos hL hpp]
    have h := lt_of_pow_lt_pow_left₀ 2 hpU.le hsq
    linarith
  have hs0 : 0<endpointSin q B := div_pos hnum hL
  have hc0 : 0<endpointCos q B := by
    apply div_pos _ hL
    exact add_pos (by linarith) (mul_pos hB hU0)
  have hc1 : endpointCos q B≤1 := by
    have h2 : (endpointCos q B)^2≤1^2 := by linarith [sq_nonneg (endpointSin q B)]
    exact le_of_pow_le_pow_left₀ two_ne_zero zero_le_one h2
  have hs4 : endpointSin q B<2/5 := by
    by_contra! hs
    have hc917 : endpointCos q B<917/1000 := by
      by_contra! h
      have h1 := pow_le_pow_left₀ (by norm_num) h 2
      have h2 := pow_le_pow_left₀ (by norm_num) hs 2
      linarith
    have hpc := (mul_lt_mul_of_pos_right
      (show CrossedClampRates.radius q B-1<106/125 by linarith [hZ.2]) hc0).trans
      (mul_lt_mul_of_pos_left hc917 (by norm_num : (0:ℝ)<106/125))
    have hbs := mul_le_mul C.B_mem.1 hs (by norm_num : (0:ℝ)≤2/5)
      (by linarith [C.B_mem.1])
    linarith
  exact ⟨⟨hs0,hs4⟩,⟨hc0,hc1⟩⟩

theorem radius_hasDerivAt {q B : ℝ} (hr : 0<q-B^2) :
    HasDerivAt (CrossedClampRates.radius q) (-B/CrossedClampRates.radius q B) B := by
  have hd := (((hasDerivAt_id B).pow 2).const_sub q).sqrt hr.ne'
  have hR : CrossedClampRates.radius q B≠0 := (Real.sqrt_pos.2 hr).ne'
  convert hd using 1
  · rfl
  · dsimp [CrossedClampRates.radius]
    field_simp [show Real.sqrt (q-B^2)≠0 from hR]

theorem endpointU_hasDerivAt {q B : ℝ} (C : EndpointDomain q B) :
    HasDerivAt (endpointU q) (B/(CrossedClampRates.radius q B*endpointU q B)) B := by
  obtain ⟨hr,hZ,hu,hU,_,_,_,_⟩ := endpoint_radicals C
  have hZ0 : CrossedClampRates.radius q B≠0 := (by linarith [hZ.1] : 0<CrossedClampRates.radius q B).ne'
  have hU0 : endpointU q B≠0 := (by linarith [hU.1] : 0<endpointU q B).ne'
  have hd := ((radius_hasDerivAt hr).const_mul 2).const_sub (q+3/4)
  convert hd.sqrt hu.ne' using 1
  · rfl
  · dsimp [endpointU]
    field_simp [hZ0,show Real.sqrt (q+3/4-2*CrossedClampRates.radius q B)≠0 from hU0]

private theorem sin_derivative_algebra {Z U B L : ℝ}
    (hZ : Z≠0) (hU : U≠0) (hL : L≠0)
    (hcircle : L=(Z-1)^2+B^2) (hU2 : U^2=L-1/4) :
    (((-B/Z)*U+(Z-1)*(B/(Z*U))-1/2)*L-
        ((Z-1)*U-B/2)*(2*B/Z))/L^2=
      -(((Z-1)/2+B*U)/L)*(U+((Z-1)*U-B/2)/L)/(Z*U) := by
  have hid : ((-B*U^2+(Z-1)*B-Z*U/2)*L-2*B*U*((Z-1)*U-B/2))+
      ((Z-1)/2+B*U)*(U*L+(Z-1)*U-B/2)=0 := by
    linear_combination -(B*(Z-1))*hU2-(U/2)*hcircle
  field_simp [hZ,hU,hL]
  nlinarith

theorem endpointSin_hasDerivAt {q B : ℝ} (C : EndpointDomain q B) :
    HasDerivAt (endpointSin q)
      (-endpointCos q B*endpointSum q B/(CrossedClampRates.radius q B*endpointU q B)) B := by
  obtain ⟨hr,hZ,_,hU,hL,_,hU2,hcircle⟩ := endpoint_radicals C
  have hZ0 : CrossedClampRates.radius q B≠0 := (by linarith [hZ.1] : 0<CrossedClampRates.radius q B).ne'
  have hU0 : endpointU q B≠0 := (by linarith [hU.1] : 0<endpointU q B).ne'
  have hz := radius_hasDerivAt hr
  have hu := endpointU_hasDerivAt C
  have hl : HasDerivAt (endpointL q) (2*B/CrossedClampRates.radius q B) B := by
    have h := (hz.const_mul 2).const_sub (q+1)
    convert h using 1
    · funext x; simp only [endpointL]
    · ring
  have hn := ((hz.sub_const 1).mul hu).sub ((hasDerivAt_id B).div_const 2)
  convert hn.div hl hL.ne' using 1
  · rfl
  · dsimp [endpointCos,endpointSum,endpointSin]
    exact (sin_derivative_algebra hZ0 hU0 hL.ne' hcircle hU2).symm

theorem endpointSum_hasDerivAt {q B : ℝ} (C : EndpointDomain q B) :
    HasDerivAt (endpointSum q)
      (-endpointSin q B*(1/2+endpointCos q B)/(CrossedClampRates.radius q B*endpointU q B)) B := by
  obtain ⟨_,hZ,_,hU,_,_,_,_⟩ := endpoint_radicals C
  have hZ0 : CrossedClampRates.radius q B≠0 := (by linarith [hZ.1] : 0<CrossedClampRates.radius q B).ne'
  have hU0 : endpointU q B≠0 := (by linarith [hU.1] : 0<endpointU q B).ne'
  have hinv := (endpoint_identities C).2.2.2
  convert (endpointU_hasDerivAt C).add (endpointSin_hasDerivAt C) using 1
  · rfl
  · dsimp [endpointSum]
    field_simp [hZ0,hU0]
    nlinarith

theorem endpointRate_hasDerivAt {q B : ℝ} (C : EndpointDomain q B) :
    HasDerivAt (endpointRate q) (endpointRateD q B) B := by
  obtain ⟨hr,hZ,_,hU,_,_,_,_⟩ := endpoint_radicals C
  obtain ⟨hs,hc⟩ := endpoint_trig C
  have hZ0 : CrossedClampRates.radius q B≠0 := (by linarith [hZ.1] : 0<CrossedClampRates.radius q B).ne'
  have hU0 : endpointU q B≠0 := (by linarith [hU.1] : 0<endpointU q B).ne'
  have hS : 0<endpointSum q B := by dsimp [endpointSum]; linarith [hs.1,hU.1]
  have hd := ((radius_hasDerivAt hr).mul (endpointU_hasDerivAt C)).div
    ((endpointU_hasDerivAt C).add (endpointSin_hasDerivAt C)) hS.ne'
  convert hd using 1
  · rfl
  · dsimp [endpointRateD,endpointSum]
    field_simp [hZ0,hU0,hS.ne']
    ring

theorem base_endpoint_bounds {q : ℝ} (hqL : qLow≤q) (hq : q≤qCap) :
    13/10<endpointSum q (24/25) ∧ 1439/1000<endpointRate q (24/25) := by
  let C : EndpointDomain q (24/25) := ⟨hqL,hq,by norm_num⟩
  obtain ⟨_,hZ,_,hU,hL,hZ2,hU2,_⟩ := endpoint_radicals C
  have hqL' := hqL
  have hq' := hq
  dsimp [qLow,qCap] at hqL' hq'
  have hZsharp : CrossedClampRates.radius q (24/25)∈Ioo (173/100 : ℝ) (2163/1250) := by
    constructor
    · exact hZ.1
    · nlinarith [hZ.1]
  have hLsharp : endpointL q (24/25)∈Ioo (7273/5000 : ℝ) (3639/2500) := by
    dsimp [endpointL]
    constructor <;> linarith [hZsharp.1,hZsharp.2]
  have hUsharp : endpointU q (24/25)∈Ioo (439/400 : ℝ) (549/500) := by
    constructor <;> nlinarith [hU.1,hLsharp.1,hLsharp.2]
  have hnumL := (mul_lt_mul_of_pos_left hUsharp.1
      (by norm_num : (0:ℝ)<73/100)).trans
    (mul_lt_mul_of_pos_right
      (show (73/100 : ℝ)<CrossedClampRates.radius q (24/25)-1 by linarith [hZsharp.1])
      (by linarith [hUsharp.1] : 0<endpointU q (24/25)))
  have hnumU := (mul_lt_mul_of_pos_right
      (show CrossedClampRates.radius q (24/25)-1<913/1250 by linarith [hZsharp.2])
      (by linarith [hUsharp.1] : 0<endpointU q (24/25))).trans
    (mul_lt_mul_of_pos_left hUsharp.2 (by norm_num : (0:ℝ)<913/1250))
  have hsL : 21/100<endpointSin q (24/25) := by
    rw [endpointSin,lt_div_iff₀ hL]
    nlinarith [hLsharp.2]
  have hsU : endpointSin q (24/25)<1107/5000 := by
    rw [endpointSin,div_lt_iff₀ hL]
    nlinarith [hLsharp.1]
  have hsum : 13/10<endpointSum q (24/25) := by
    dsimp [endpointSum]
    linarith [hUsharp.1]
  have hprod := (mul_lt_mul_of_pos_left hUsharp.1
      (by norm_num : (0:ℝ)<173/100)).trans
    (mul_lt_mul_of_pos_right hZsharp.1
      (by linarith [hUsharp.1] : 0<endpointU q (24/25)))
  refine ⟨hsum,?_⟩
  rw [endpointRate,lt_div_iff₀ (show 0<endpointSum q (24/25) by linarith)]
  dsimp [endpointSum]
  nlinarith [hUsharp.2]

theorem endpoint_sum_lower {q B : ℝ} (C : EndpointDomain q B) :
    13/10<endpointSum q B := by
  have hanti : AntitoneOn (endpointSum q) (Icc (709/1000 : ℝ) (24/25)) := by
    apply antiOn_of_hasDeriv_nonpos
    · intro b hb
      exact (endpointSum_hasDerivAt ⟨C.floor,C.ceiling,hb⟩).continuousAt.continuousWithinAt
    · intro b hb
      exact endpointSum_hasDerivAt ⟨C.floor,C.ceiling,Ioo_subset_Icc_self hb⟩
    · intro b hb
      let D : EndpointDomain q b := ⟨C.floor,C.ceiling,Ioo_subset_Icc_self hb⟩
      have hd := endpoint_radicals D
      have ht := endpoint_trig D
      apply div_nonpos_of_nonpos_of_nonneg
      · have h := mul_nonneg ht.1.1.le (show 0≤1/2+endpointCos q b by linarith [ht.2.1])
        linarith
      · exact mul_nonneg (by linarith [hd.2.1.1]) (by linarith [hd.2.2.2.1.1])
  have hm := hanti C.B_mem (show (24/25 : ℝ)∈Icc (709/1000) (24/25) by norm_num) C.B_mem.2
  exact (base_endpoint_bounds C.floor C.ceiling).1.trans_le hm

theorem endpoint_rate_derivative_upper {q B : ℝ} (C : EndpointDomain q B) :
    endpointRateD q B<3/4 := by
  obtain ⟨_,hZ,_,hU,_,_,_,_⟩ := endpoint_radicals C
  obtain ⟨hs,hc⟩ := endpoint_trig C
  have hS := endpoint_sum_lower C
  have hZ0 : 0<CrossedClampRates.radius q B := by linarith [hZ.1]
  have hU0 : 0<endpointU q B := by linarith [hU.1]
  have hS0 : 0<endpointSum q B := by linarith
  have hBU := (mul_lt_mul_of_pos_left hU.1
      (by norm_num : (0:ℝ)<709/1000)).trans_le
    (mul_le_mul_of_nonneg_right C.B_mem.1 hU0.le)
  have hratio : (709/1000)*(49/50)/(37/20)<B*endpointU q B/CrossedClampRates.radius q B := by
    apply (lt_div_iff₀ hZ0).2
    nlinarith [hZ.2]
  let K1 : ℝ := (1-(709/1000)*(49/50)/(37/20))/(13/10)
  let K2 : ℝ := ((24/25)*(2/5))/((49/50)*(13/10)^2)
  have hK1 : 0<K1 := by norm_num [K1]
  have hfirst : (endpointCos q B-B*endpointU q B/CrossedClampRates.radius q B)/endpointSum q B<K1 := by
    apply (div_lt_iff₀ hS0).2
    have hm := mul_lt_mul_of_pos_left hS hK1
    dsimp [K1] at hm
    linarith [hc.2]
  have hBs := (mul_le_mul_of_nonneg_right C.B_mem.2 hs.1.le).trans_lt
    (mul_lt_mul_of_pos_left hs.2 (by norm_num : (0:ℝ)<24/25))
  have hS2 := pow_lt_pow_left₀ hS (by norm_num : (0:ℝ)≤13/10) (by decide : (2:ℕ)≠0)
  have hden := (mul_lt_mul_of_pos_left hS2
      (by norm_num : (0:ℝ)<49/50)).trans
    (mul_lt_mul_of_pos_right hU.1 (sq_pos_of_pos hS0))
  have hsecond : B*endpointSin q B/(endpointU q B*(endpointSum q B)^2)<K2 := by
    apply (div_lt_iff₀ (mul_pos hU0 (sq_pos_of_pos hS0))).2
    have hm := mul_lt_mul_of_pos_left hden (show 0<K2 by norm_num [K2])
    dsimp only [K2] at hm ⊢
    linarith
  dsimp [endpointRateD]
  have hsum : K1+K2<3/4 := by norm_num [K1,K2]
  linarith

/-- Every actual normal hard contact is at least as strong as the exact
zero-tangent endpoint rate.  The comparison is algebraic in the two
rotated components; no inverse angle is introduced. -/
theorem hard_rate_lower {q B u : ℝ} (C : EndpointDomain q B)
    (hu : u∈Icc 0 frameCap)
    (hcontact : (CrossedClampRates.radius q B-1)*Real.cos u-B*Real.sin u≥1/2) :
    endpointRate q B≤angularHardRate q B u := by
  obtain ⟨_,hZ,_,hU,hL,_,hU2,hcircle⟩ := endpoint_radicals C
  obtain ⟨hs,hc⟩ := endpoint_trig C
  obtain ⟨hroot,hrot,hnorm,_⟩ := endpoint_identities C
  have ht := transport_trig hu
  have hcos : 0<Real.cos u := by linarith [ht.1]
  have hB : 0<B := by linarith [C.B_mem.1]
  have hP : 0<CrossedClampRates.radius q B-1 := by linarith [hZ.1]
  let V := (CrossedClampRates.radius q B-1)*Real.cos u-B*Real.sin u
  let U := (CrossedClampRates.radius q B-1)*Real.sin u+B*Real.cos u
  have hU0 : 0<U := by
    dsimp [U]
    exact add_pos_of_nonneg_of_pos (mul_nonneg hP.le ht.2.2.1) (mul_pos hB hcos)
  have hrotation : V^2+U^2=endpointL q B := by
    dsimp [V,U]
    rw [hcircle]
    linear_combination (((CrossedClampRates.radius q B-1)^2+B^2)*(Real.sin_sq_add_cos_sq u))
  have hUle : U≤endpointU q B := by
    have hV : 1/2≤V := hcontact
    have hV2 := pow_le_pow_left₀ (by norm_num) hV 2
    have h2 : U^2≤(endpointU q B)^2 := by linarith
    exact le_of_pow_le_pow_left₀ two_ne_zero (by linarith [hU.1]) h2
  have hinv : endpointL q B*Real.sin u=(CrossedClampRates.radius q B-1)*U-B*V := by
    rw [hcircle]
    dsimp [U,V]
    ring
  have hend : endpointL q B*endpointSin q B=
      (CrossedClampRates.radius q B-1)*endpointU q B-B/2 := by
    dsimp [endpointSin]
    field_simp [hL.ne']
  have hsin : Real.sin u≤endpointSin q B := by
    have hleft := mul_le_mul_of_nonneg_left hUle hP.le
    have hright := mul_le_mul_of_nonneg_left hcontact hB.le
    refine le_of_mul_le_mul_left ?_ hL
    linarith
  have hcosle : endpointCos q B≤Real.cos u := by
    have hsin2 := pow_le_pow_left₀ ht.2.2.1 hsin 2
    have h2 : (endpointCos q B)^2≤(Real.cos u)^2 := by linarith [Real.sin_sq_add_cos_sq u]
    exact le_of_pow_le_pow_left₀ two_ne_zero hcos.le h2
  have hcross := mul_le_mul hsin hcosle hc.1.le hs.1.le
  have hden : 0<B*Real.cos u+CrossedClampRates.radius q B*Real.sin u := by
    exact add_pos_of_pos_of_nonneg (mul_pos hB hcos)
      (mul_nonneg (by linarith [hZ.1]) ht.2.2.1)
  have hsum : 0<endpointSum q B := by dsimp [endpointSum]; linarith [hs.1,hU.1]
  have hrate : angularHardRate q B u=
      CrossedClampRates.radius q B*((CrossedClampRates.radius q B-1)*Real.sin u+B*Real.cos u)/
        (B*Real.cos u+CrossedClampRates.radius q B*Real.sin u) := by
    dsimp [angularHardRate,hardRate]
    rw [Real.tan_eq_sin_div_cos]
    field_simp [hcos.ne',hden.ne']
    ring
  rw [hrate,endpointRate]
  apply (div_le_div_iff₀ hsum hden).2
  have hid : CrossedClampRates.radius q B*((CrossedClampRates.radius q B-1)*Real.sin u+B*Real.cos u)*endpointSum q B-
      CrossedClampRates.radius q B*endpointU q B*(B*Real.cos u+CrossedClampRates.radius q B*Real.sin u)=
      CrossedClampRates.radius q B*B*(endpointSin q B*Real.cos u-endpointCos q B*Real.sin u) := by
    dsimp [endpointSum]
    rw [←hrot]
    ring
  have hm := mul_nonneg (mul_nonneg (by linarith [hZ.1] : 0≤CrossedClampRates.radius q B) hB.le)
    (show 0≤endpointSin q B*Real.cos u-endpointCos q B*Real.sin u by linarith)
  linarith

end SquaresInCircles.Eight.TableFree.CrossedUpperRate

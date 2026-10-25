module

public import Mathlib.Algebra.Ring.IsFormallyReal
public import SquaresInCircles.Eight.Owners.Endpoint.Budget
public import SquaresInCircles.Eight.Words.Crossed.ClampBudget
public import SquaresInCircles.Eight.Words.Crossed.SmallWrongScalar
public import SquaresInCircles.Eight.Words.Second.Outer.LabelBounds

/-!
# Eight squares: the crossed wrong-sign endpoint bound

The zero-tangent contact divides the two intrinsic cap alternatives. In the positive cap,
monotonicity of the zero demand gives the lower bound (`positive_cap_reserve`). In the wrong cap,
the two HG-angle endpoints give the same bound after the loss `27/6400`
(`wrong_cap_reserve`).
-/

section
/-!
## Exact opposite hard endpoint for the upper crossed clamp rate

The zero-tangent hard endpoint is represented
by its algebraic sine and cosine.  Its contact, unit-circle identity,
derivatives, and comparison with every actual hard angle are proved
directly.  No inverse-angle function or selected optimizer is assumed.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CrossedUpperRate
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

end SquaresInCircles.Eight.CrossedUpperRate
end
end
end

section
/-!
## Opposite hard-cap rates on the lower active tangent interval

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
end
end
end

section
/-!
## The two intrinsic crossed wrong-sign endpoints

For each wrong-sign circle cap, the charged
HG demand has its minimum at the two actual ends of the HG-angle
interval.  The far endpoint has curvature at least 2/3 in the intrinsic
GA angle.  At the zero-tangent contact its slope is at least -.075.
These bounds give the exact loss 27/6400 by one completed square.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CrossedWrongEndpointCalculus
open PositiveSmallScalar CrossedSmallWrongScalar EndpointRotationPenalty

def zeroDemand (q h : ℝ) : ℝ :=
  1/2+Real.cos h/2-(Real.sqrt (q-1/4)-1)*Real.sin h

def chargedDemand (q P Y z h : ℝ) : ℝ :=
  1/2+(1-V P Y z)*Real.cos h-(SmallWrongScalar.W q P Y z-1)*Real.sin h+
    charge*(h-z)

def K (q P Y z : ℝ) : ℝ := chargedDemand q P Y z frameCap

def K1 (q P Y z : ℝ) : ℝ :=
  U P Y z*(Real.cos frameCap+
    (1-V P Y z)/SmallWrongScalar.W q P Y z*Real.sin frameCap)-charge

def K2 (q P Y z : ℝ) : ℝ :=
  V P Y z*(Real.cos frameCap+
    (1-V P Y z)/SmallWrongScalar.W q P Y z*Real.sin frameCap)+
      q*(U P Y z)^2/(SmallWrongScalar.W q P Y z)^3*Real.sin frameCap

theorem fixed_trig : (478/625 : ℝ)≤Real.cos frameCap ∧
    (3221/5000 : ℝ)≤Real.sin frameCap := by
  have hc := cos_lower_six (show (0:ℝ)≤7/10 by norm_num)
  have hs := sin_lower_seven (show (0:ℝ)≤7/10 by norm_num)
  dsimp [frameCap]
  constructor <;> norm_num at * <;> linarith

theorem zeroDemand_antitone {q : ℝ} (hq : qLow≤q) :
    AntitoneOn (zeroDemand q) (Icc (0:ℝ) (11/10)) := by
  have hr : 0≤q-1/4 := by dsimp [qLow] at hq; linarith
  have hw := Real.sq_sqrt hr
  have hs := Real.sqrt_nonneg (q-1/4)
  have hk : 0≤Real.sqrt (q-1/4)-1 := by dsimp [qLow] at hq; nlinarith
  apply antiOn_of_hasDeriv_nonpos (d := fun h =>
    -Real.sin h/2-(Real.sqrt (q-1/4)-1)*Real.cos h)
  · unfold zeroDemand
    fun_prop
  · intro h hh
    have hd : HasDerivAt (fun x => 1/2+Real.cos x/2-(Real.sqrt (q-1/4)-1)*Real.sin x)
        (-Real.sin h/2-(Real.sqrt (q-1/4)-1)*Real.cos h) h := by
      have h' := (((Real.hasDerivAt_cos h).div_const 2).const_add (1/2)).fun_sub
        ((Real.hasDerivAt_sin h).const_mul (Real.sqrt (q-1/4)-1))
      convert h' using 1
    exact hd
  · intro h hh
    have hsin := CrossedZeroReserve.sin_nonneg (Ioo_subset_Icc_self hh)
    have hsq := pow_le_pow_left₀ hh.1.le hh.2.le 2
    have hcos : 0≤Real.cos h := by linarith [Real.one_sub_sq_div_two_le_cos (x := h)]
    have hm := mul_nonneg hk hcos
    linarith

theorem zeroDemand_reserve {q h : ℝ} (hqL : qLow≤q) (hq : q≤qCap)
    (hh : h∈Icc (39/200 : ℝ) (11/10)) :
    1+7/1000<zeroDemand q h+charge*h := by
  have hr : 0≤q-1/4 := by dsimp [qLow] at hqL; linarith
  have hw := Real.sq_sqrt hr
  have hs := Real.sqrt_nonneg (q-1/4)
  have hk : Real.sqrt (q-1/4)-1≤183/200 := by dsimp [qCap] at hq; nlinarith
  have hf := CrossedZeroReserve.strict hk hh
  dsimp [zeroDemand]
  linarith

theorem K_hasDerivAt {q P Y z : ℝ} (hr : 0<q-(1-V P Y z)^2) :
    HasDerivAt (K q P Y) (K1 q P Y z) z := by
  have hv := (hasDerivAt_const z (1:ℝ)).sub (V_hasDerivAt P Y z)
  have hw := SmallWrongScalar.W_hasDerivAt hr
  have hd := (((hv.mul_const (Real.cos frameCap)).const_add (1/2)).sub
    ((hw.sub_const 1).mul_const (Real.sin frameCap))).add
      (((hasDerivAt_id z).const_sub frameCap).const_mul charge)
  convert hd using 1
  · rfl
  · dsimp [K1]
    ring

theorem ratio_hasDerivAt {q P Y z : ℝ} (hr : 0<q-(1-V P Y z)^2) :
    HasDerivAt (fun z => (1-V P Y z)/SmallWrongScalar.W q P Y z)
      (q*U P Y z/(SmallWrongScalar.W q P Y z)^3) z := by
  have hw : SmallWrongScalar.W q P Y z≠0 := (Real.sqrt_pos.2 hr).ne'
  have hw2 : (SmallWrongScalar.W q P Y z)^2=q-(1-V P Y z)^2 := Real.sq_sqrt hr.le
  have hd := ((hasDerivAt_const z (1:ℝ)).sub (V_hasDerivAt P Y z)).div
    (SmallWrongScalar.W_hasDerivAt hr) hw
  convert hd using 1
  simp only [Pi.sub_apply]
  obtain ⟨w,hwdef⟩ : ∃ w,w=SmallWrongScalar.W q P Y z := ⟨_,rfl⟩
  rw [←hwdef] at hw hw2 ⊢
  rw [show q=w^2+(1-V P Y z)^2 by linarith]
  field_simp
  ring

theorem K1_hasDerivAt {q P Y z : ℝ} (hr : 0<q-(1-V P Y z)^2) :
    HasDerivAt (K1 q P Y) (K2 q P Y z) z := by
  have hd := ((U_hasDerivAt P Y z).mul
    (((ratio_hasDerivAt hr).mul_const (Real.sin frameCap)).const_add
      (Real.cos frameCap))).sub_const charge
  convert hd using 1
  · rfl
  · dsimp [K2]
    ring

theorem root_uniform_bounds {q P Y z : ℝ} (S : CrossedSmallWrongScalar.CapData q P Y)
    (hz : z∈Icc 0 frameCap) (hv : V P Y z∈Icc (2/5 : ℝ) (1/2)) :
    0<SmallWrongScalar.W q P Y z ∧ SmallWrongScalar.W q P Y z<383/200 ∧
      1267/1250<U P Y z := by
  have hb := CrossedSmallWrongScalar.root_bounds S hz hv
  have hw0 : 0<SmallWrongScalar.W q P Y z := Real.sqrt_pos.2 hb.1
  have hw2 : (SmallWrongScalar.W q P Y z)^2=q-(1-V P Y z)^2 :=
    Real.sq_sqrt hb.1.le
  have hC2 := pow_le_pow_left₀ (show (0:ℝ)≤1/2 by norm_num)
    (show 1/2≤1-V P Y z by linarith [hv.2]) 2
  have hw : SmallWrongScalar.W q P Y z<383/200 := by
    have hq := S.ceiling
    dsimp [qCap] at hq
    nlinarith
  have hu : 1267/1250<U P Y z := by linarith [hb.2.2.1,hv.2]
  exact ⟨hw0,hw,hu⟩

theorem K1_contact_lower {q P Y z : ℝ} (S : CrossedSmallWrongScalar.CapData q P Y)
    (hz : z∈Icc 0 frameCap) (hv : V P Y z=1/2) :
    -(3/40 : ℝ)≤K1 q P Y z := by
  obtain ⟨hw0,hw,hu⟩ := root_uniform_bounds S hz (by rw [hv]; norm_num)
  have hc := fixed_trig.1
  have hs := fixed_trig.2
  have hs0 : 0≤Real.sin frameCap := by linarith
  have hr : (1/2 : ℝ)/(383/200)≤(1/2)/SmallWrongScalar.W q P Y z :=
    (div_le_div_iff₀ (by norm_num) hw0).2 (by linarith)
  have hm := mul_le_mul hr hs (by norm_num : (0:ℝ)≤3221/5000)
    (div_nonneg (by norm_num) hw0.le)
  have hi : 478/625+((1/2)/(383/200))*(3221/5000)≤
      Real.cos frameCap+((1/2)/SmallWrongScalar.W q P Y z)*Real.sin frameCap := by
    linarith
  have hp := mul_le_mul hu.le hi (by norm_num :
      (0:ℝ)≤478/625+((1/2)/(383/200))*(3221/5000)) (by linarith : 0≤U P Y z)
  dsimp [K1,charge]
  rw [hv]
  norm_num at hp ⊢
  linarith

theorem K2_lower {q P Y z : ℝ} (S : CrossedSmallWrongScalar.CapData q P Y)
    (hz : z∈Icc 0 frameCap) (hv : V P Y z∈Icc (2/5 : ℝ) (1/2)) :
    2/3≤K2 q P Y z := by
  obtain ⟨hw0,hw,hu⟩ := root_uniform_bounds S hz hv
  have hc := fixed_trig.1
  have hs := fixed_trig.2
  have hs0 : 0≤Real.sin frameCap := by linarith
  have hu0 : 0≤U P Y z := by linarith
  have hu2 := pow_le_pow_left₀ (show (0:ℝ)≤1267/1250 by norm_num) hu.le 2
  have hw3 := pow_le_pow_left₀ hw0.le hw.le 3
  have hq0 : 0≤q := by have hh := S.floor; dsimp [qLow] at hh; linarith
  have hn1 := mul_le_mul S.floor hu2 (by norm_num [qLow] : (0:ℝ)≤(1267/1250)^2) hq0
  have hn := mul_le_mul hn1 hs (by norm_num : (0:ℝ)≤3221/5000)
    (mul_nonneg hq0 (sq_nonneg (U P Y z)))
  let n0 : ℝ := qLow*(1267/1250)^2*(3221/5000)
  have hn0 : 0≤n0 := by norm_num [n0,qLow]
  have hcross1 := mul_le_mul_of_nonneg_left hw3 hn0
  have hcross2 := mul_le_mul_of_nonneg_right hn
    (show (0:ℝ)≤(383/200)^3 by norm_num)
  have hquot : n0/(383/200)^3≤
      (q*(U P Y z)^2*Real.sin frameCap)/(SmallWrongScalar.W q P Y z)^3 := by
    apply (div_le_div_iff₀ (by norm_num) (pow_pos hw0 3)).2
    exact hcross1.trans hcross2
  have hfirst := mul_le_mul hv.1 hc (by norm_num : (0:ℝ)≤478/625)
    (by linarith [hv.1] : 0≤V P Y z)
  have hextra : 0≤V P Y z*((1-V P Y z)/SmallWrongScalar.W q P Y z*
      Real.sin frameCap) := by
    exact mul_nonneg (by linarith [hv.1])
      (mul_nonneg (div_nonneg (by linarith [hv.2]) hw0.le) hs0)
  dsimp [K2]
  have hid : q*(U P Y z)^2/(SmallWrongScalar.W q P Y z)^3*Real.sin frameCap=
      (q*(U P Y z)^2*Real.sin frameCap)/(SmallWrongScalar.W q P Y z)^3 := by ring
  rw [hid]
  norm_num [n0,qLow] at hquot
  nlinarith

theorem K_contact_loss {q P Y Z z : ℝ} (S : CrossedSmallWrongScalar.CapData q P Y)
    (hZ : Z∈Icc 0 frameCap) (hz : z∈Icc 0 frameCap) (hZz : Z≤z)
    (hcontact : V P Y Z=1/2) (hv : V P Y z∈Icc (2/5 : ℝ) (1/2)) :
    K q P Y Z-27/6400≤K q P Y z := by
  have hdom {t : ℝ} (ht : t∈Icc Z z) :
      t∈Icc 0 frameCap ∧ V P Y t∈Icc (2/5 : ℝ) (1/2) := by
    have hi : t∈Icc 0 frameCap := ⟨hZ.1.trans ht.1,ht.2.trans hz.2⟩
    have hlo := CrossedSmallWrongScalar.V_antitone S hi hz ht.2
    have hhi := CrossedSmallWrongScalar.V_antitone S hZ hi ht.1
    exact ⟨hi,⟨hv.1.trans hlo,by linarith⟩⟩
  have htan := curvature_tangent (κ := (2/3 : ℝ))
    (show z∈Icc Z z from ⟨hZz,le_rfl⟩) (show Z∈Icc Z z from ⟨le_rfl,hZz⟩)
    (fun t ht => K_hasDerivAt (CrossedSmallWrongScalar.root_bounds S
      (hdom ht).1 (hdom ht).2).1)
    (fun t ht => K1_hasDerivAt (CrossedSmallWrongScalar.root_bounds S
      (hdom ht).1 (hdom ht).2).1)
    (fun t ht => K2_lower S (hdom ht).1 (hdom ht).2)
  have hslope := K1_contact_lower S hZ hcontact
  have hm := mul_le_mul_of_nonneg_right hslope (sub_nonneg.mpr hZz)
  nlinarith [sq_nonneg (z-Z-9/80)]

/-- The right HG-angle endpoint has negative first derivative uniformly
over the intrinsic wrong-sign cap. -/
theorem fixed_right_negative {q C w : ℝ} (hq : qLow≤q)
    (hC : C∈Icc (1/2 : ℝ) (3/5)) (hw : 0<w) (hw2 : w^2=q-C^2) :
    -C*Real.sin frameCap-(w-1)*Real.cos frameCap+charge<0 := by
  let x := C-1/2
  have hx : x∈Icc (0:ℝ) (1/10) := by dsimp [x]; constructor <;> linarith [hC.1,hC.2]
  have hx2 : x^2≤x/10 := by
    nlinarith [mul_nonneg hx.1 (show 0≤1/10-x by linarith [hx.2])]
  have hline : 3829/2000-(3/10)*x<w := by
    have hid : q-C^2-(3829/2000-(3/10)*x)^2=
        q-19577/5000+359/4000000+(1487/10000)*x-(109/100)*x^2 := by
      dsimp [x]
      ring
    have hline0 : 0<3829/2000-(3/10)*x := by linarith [hx.2]
    have hq' := hq
    dsimp [qLow] at hq'
    nlinarith
  have hw1 : 0≤w-1 := by linarith [hx.2]
  have hcs := mul_le_mul_of_nonneg_left fixed_trig.2 (by linarith [hC.1] : 0≤C)
  have hwc := mul_le_mul_of_nonneg_left fixed_trig.1 hw1
  have hlin := mul_le_mul_of_nonneg_right hline.le (show (0:ℝ)≤478/625 by norm_num)
  dsimp [x,charge] at *
  nlinarith

theorem chargedDemand_endpoint_lower {q P Y z h L : ℝ}
    (S : CrossedSmallWrongScalar.CapData q P Y)
    (hz : z∈Icc 0 frameCap) (hv : V P Y z∈Icc (2/5 : ℝ) (1/2))
    (hh : h∈Icc z frameCap)
    (hleft : L≤SmallWrongScalar.demand q P Y 0 z) (hright : L≤K q P Y z) :
    L≤chargedDemand q P Y z h := by
  let C := 1-V P Y z
  let w := SmallWrongScalar.W q P Y z
  let f := fun s : ℝ => C*Real.cos s-(w-1)*Real.sin s+charge*s
  let d := fun s : ℝ => -C*Real.sin s-(w-1)*Real.cos s+charge
  let dd := fun s : ℝ => -C*Real.cos s+(w-1)*Real.sin s
  let ddd := fun s : ℝ => C*Real.sin s+(w-1)*Real.cos s
  have hb := CrossedSmallWrongScalar.root_bounds S hz hv
  have hC : C∈Icc (1/2 : ℝ) (3/5) := by dsimp [C]; constructor <;> linarith [hv.1,hv.2]
  have hw0 : 0<w := Real.sqrt_pos.2 hb.1
  have hw2 : w^2=q-C^2 := Real.sq_sqrt hb.1.le
  have hw1 : 0≤w-1 := by dsimp [w]; linarith [hb.2.1,hv.1]
  have hf (s : ℝ) : HasDerivAt f (d s) s := by
    have h := (((Real.hasDerivAt_cos s).const_mul C).fun_sub
      ((Real.hasDerivAt_sin s).const_mul (w-1))).fun_add
        ((hasDerivAt_id' s).const_mul charge)
    convert h using 1
    simp only [d]; ring
  have hd (s : ℝ) : HasDerivAt d (dd s) s := by
    have h := (((Real.hasDerivAt_sin s).const_mul (-C)).fun_sub
      ((Real.hasDerivAt_cos s).const_mul (w-1))).add_const charge
    convert h using 1
    simp only [dd]; ring
  have hdd (s : ℝ) : HasDerivAt dd (ddd s) s := by
    have h := ((Real.hasDerivAt_cos s).const_mul (-C)).fun_add
      ((Real.hasDerivAt_sin s).const_mul (w-1))
    convert h using 1
    simp only [ddd]; ring
  have hm := SecondWord.MinimumCalculus.endpoint_minimum hh
    (fun s _ => hf s) (fun s _ => hd s) (fun s _ => hdd s)
    (by
      intro s hs
      have ht := transport_trig (show s∈Icc 0 frameCap from ⟨hz.1.trans hs.1,hs.2⟩)
      exact add_nonneg (mul_nonneg (by linarith [hC.1]) ht.2.2.1)
        (mul_nonneg hw1 (by linarith [ht.1])))
    (fixed_right_negative S.floor hC hw0 hw2)
  have hl : L-1/2+charge*z≤f z := by
    dsimp [SmallWrongScalar.demand,f,C,w] at hleft ⊢
    simp only [zero_add] at hleft
    linarith
  have hr : L-1/2+charge*z≤f frameCap := by
    dsimp [K,chargedDemand,f,C,w] at hright ⊢
    linarith
  have hmin := le_min hl hr
  dsimp [chargedDemand,f,C,w] at *
  linarith

end SquaresInCircles.Eight.CrossedWrongEndpointCalculus
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CrossedWrongEndpointBound
open PositiveSmallScalar CrossedSmallWrongScalar CrossedWrongEndpointCalculus
open EndpointRotationPenalty

theorem contact_mem {Z : ℝ} (hZ : Z∈Ioo (39/200 : ℝ) (2/5)) :
    Z∈Icc 0 frameCap := by
  dsimp [frameCap]
  constructor <;> linarith [hZ.1,hZ.2]

theorem positive_cap_reserve {q P Y Z z r : ℝ}
    (S : CrossedSmallWrongScalar.CapData q P Y)
    (hZ : Z∈Ioo (39/200 : ℝ) (2/5)) (hcontact : V P Y Z=1/2)
    (hz : z∈Icc 0 frameCap) (hcap : 1/2≤V P Y z)
    (hr : 0≤r) (hh : r+z≤frameCap) :
    1+7/1000-27/6400≤zeroDemand q (r+z)+charge*r+charge*Z := by
  have hZi := contact_mem hZ
  have hzZ : z≤Z := by
    by_contra! hbad
    have hs := CrossedSmallWrongScalar.V_strictAnti S hZi hz hbad
    rw [hcontact] at hs
    linarith
  have hrmax : r≤7/10 := by dsimp [frameCap] at hh; linarith [hz.1]
  have hlarge : r+Z∈Icc (39/200 : ℝ) (11/10) := by
    constructor <;> linarith [hZ.1,hZ.2]
  have hsmall : r+z∈Icc (0:ℝ) (11/10) := by
    dsimp [frameCap] at hh
    exact ⟨add_nonneg hr hz.1,by linarith⟩
  have hm := zeroDemand_antitone S.floor hsmall
    (show r+Z∈Icc (0:ℝ) (11/10) from ⟨by linarith [hlarge.1],hlarge.2⟩)
    (by linarith : r+z≤r+Z)
  have hf := zeroDemand_reserve S.floor S.ceiling hlarge
  linarith

theorem wrong_cap_reserve {q P Y Z z h : ℝ}
    (S : CrossedSmallWrongScalar.CapData q P Y)
    (hZ : Z∈Ioo (39/200 : ℝ) (2/5)) (hcontact : V P Y Z=1/2)
    (hz : z∈Icc 0 frameCap) (hcap : V P Y z∈Icc (2/5 : ℝ) (1/2))
    (hh : h∈Icc z frameCap) :
    1+7/1000-27/6400≤chargedDemand q P Y z h+charge*Z := by
  have hZi := contact_mem hZ
  have hZz : Z≤z := by
    by_contra! hbad
    have hs := CrossedSmallWrongScalar.V_strictAnti S hz hZi hbad
    rw [hcontact] at hs
    linarith [hcap.2]
  have hmono := CrossedSmallWrongScalar.demand_monotone S (Θ := 0) (l := Z) (r := z)
    le_rfl (by
      intro t ht
      have hi : t∈Icc 0 frameCap := ⟨hZi.1.trans ht.1,ht.2.trans hz.2⟩
      have hlo := CrossedSmallWrongScalar.V_antitone S hi hz ht.2
      have hhi := CrossedSmallWrongScalar.V_antitone S hZi hi ht.1
      simpa only [zero_add] using
        (show 0≤t ∧ t∈Icc 0 frameCap ∧ V P Y t∈Icc (2/5 : ℝ) (1/2) from
          ⟨hi.1,hi,⟨hcap.1.trans hlo,by linarith⟩⟩))
  have hordered := hmono (show Z∈Icc Z z from ⟨le_rfl,hZz⟩)
    (show z∈Icc Z z from ⟨hZz,le_rfl⟩) hZz
  have hzero : SmallWrongScalar.demand q P Y 0 Z=zeroDemand q Z := by
    norm_num [SmallWrongScalar.demand,SmallWrongScalar.W,zeroDemand,hcontact]
    ring
  have hzeroReserve := zeroDemand_reserve S.floor S.ceiling
    (show Z∈Icc (39/200 : ℝ) (11/10) from ⟨hZ.1.le,by linarith [hZ.2]⟩)
  have hleft : 1+7/1000-27/6400-charge*Z≤SmallWrongScalar.demand q P Y 0 z := by
    rw [hzero] at hordered
    linarith
  have hKloss := K_contact_loss S hZi hz hZz hcontact hcap
  have hKzero : K q P Y Z+charge*Z=zeroDemand q frameCap+charge*frameCap := by
    norm_num [K,chargedDemand,SmallWrongScalar.W,zeroDemand,hcontact]
    ring
  have hfarReserve := zeroDemand_reserve S.floor S.ceiling
    (show frameCap∈Icc (39/200 : ℝ) (11/10) by norm_num [frameCap])
  have hright : 1+7/1000-27/6400-charge*Z≤K q P Y z := by
    simp only [frameCap] at hKzero hfarReserve
    linarith
  have hfinal := chargedDemand_endpoint_lower S hz hcap hh hleft hright
  linarith

end SquaresInCircles.Eight.CrossedWrongEndpointBound
end
end
end

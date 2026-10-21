module

public import SquaresInCircles.Eight.TableFree.PositiveScalarTransfer

/-!
# The full nonnegative core-E charge, including opposite individual signs

Uncompiled source. The two actual primary errors are kept signed. A
concave first harmonic gives the smaller endpoint when both are positive.
For opposite signs, the negative-DE orientation is the worse one, and its
entire interval is bounded by the same intrinsic zero-error endpoint.
The conclusion applies to the original true-core E point.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.CoreECharge
open PositiveScalarTransfer

def pairDeficit (a b u v : ℝ) : ℝ :=
  edgeWidth u+edgeWidth v-2-a*(Real.sin u+Real.sin v)-b*(Real.cos u-Real.cos v)

def ehCharge (a b e : ℝ) : ℝ :=
  (1/2-a)*Real.sin e-(1/2+b)*(1-Real.cos e)
def deCharge (a b e : ℝ) : ℝ :=
  (1/2-a)*Real.sin e-(1/2-b)*(1-Real.cos e)
def cosineCoefficient (a b e : ℝ) : ℝ :=
  1-(1/2+b)*(1-Real.cos e)-(a-1/2)*Real.sin e
def sameSineCoefficient (a b e : ℝ) : ℝ :=
  (1/2+b)*Real.sin e-(a-1/2)*(1-Real.cos e)
def oppositeSineCoefficient (a b e : ℝ) : ℝ :=
  1-(1/2+b)*Real.sin e+(a-1/2)*(1-Real.cos e)

theorem coefficients {a b e : ℝ} (ha : 1/2≤a∧a≤7/12)
    (hb : 0≤b∧b≤a) (he : e∈Icc 0 frameCap) :
    0≤cosineCoefficient a b e ∧ cosineCoefficient a b e≤1 ∧
      0≤sameSineCoefficient a b e ∧
      (11/20)*(frameCap-e)≤oppositeSineCoefficient a b e := by
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig he
  have hphi := one_le_abs_cos_add_abs_sin e
  rw [abs_of_nonneg (by linarith : 0≤Real.cos e),abs_of_nonneg hs0] at hphi
  have hsin := Real.sin_le he.1
  have h1 := mul_le_mul_of_nonneg_right (show 1/2+b≤(13/12 : ℝ) by linarith)
    (sub_nonneg.mpr hc1)
  have h2 := mul_le_mul_of_nonneg_right (show a-1/2≤(1/12 : ℝ) by linarith) hs0
  have h3 := mul_nonneg (show 0≤1/2+b by linarith) (sub_nonneg.mpr hc1)
  have h4 := mul_nonneg (show 0≤a-1/2 by linarith) hs0
  have h5 := mul_le_mul_of_nonneg_right (show a-1/2≤(1/12 : ℝ) by linarith)
    (sub_nonneg.mpr hc1)
  have h6 := mul_nonneg hb.1 hs0
  have h7 := mul_le_mul_of_nonneg_right (show 1/2+b≤(13/12 : ℝ) by linarith) hs0
  have h8 := mul_nonneg (show 0≤a-1/2 by linarith) (sub_nonneg.mpr hc1)
  dsimp [cosineCoefficient,sameSineCoefficient,oppositeSineCoefficient,frameCap]
  exact ⟨by nlinarith,by nlinarith,by nlinarith,by nlinarith [he.2]⟩

theorem intrinsic_charge_lower {a b e : ℝ} (ha : a≤7/12) (hb : b≤7/12)
    (he : e∈Icc 0 frameCap) : J e≤ehCharge a b e := by
  have ht := transport_trig he
  have hsin := mul_le_mul_of_nonneg_right (show -(1/12 : ℝ)≤1/2-a by linarith) ht.2.2.1
  have hcos := mul_le_mul_of_nonneg_right (show 1/2+b≤(13/12 : ℝ) by linarith)
    (sub_nonneg.mpr ht.2.1)
  dsimp [J,ehCharge]
  linarith

theorem sole_de_charge_lower {a b e : ℝ} (ha : a≤7/12) (hb : 0≤b∧b≤7/12)
    (he : e∈Icc 0 frameCap) : J e≤deCharge a b e := by
  have h := intrinsic_charge_lower ha hb.2 he
  have hm := mul_nonneg hb.1 (sub_nonneg.mpr (Real.cos_le_one e))
  dsimp [ehCharge,deCharge] at *
  linarith

theorem same_harmonic_identity {a b e u : ℝ} (he : e∈Icc 0 frameCap)
    (hu : u∈Icc 0 e) :
    pairDeficit a b u (e-u)=
      harmonic (cosineCoefficient a b e) (sameSineCoefficient a b e) u-1 := by
  have hv : e-u∈Icc 0 frameCap := ⟨by linarith [hu.2],by linarith [he.2,hu.1]⟩
  rw [pairDeficit,edgeWidth_positive_formula ⟨hu.1,hu.2.trans he.2⟩,
    edgeWidth_positive_formula hv]
  simp only [Real.sin_sub,Real.cos_sub,harmonic,cosineCoefficient,sameSineCoefficient]
  ring

theorem same_endpoint_comparison {a b e : ℝ} (hb : 0≤b) :
    cosineCoefficient a b e≤
      harmonic (cosineCoefficient a b e) (sameSineCoefficient a b e) e := by
  have heq : harmonic (cosineCoefficient a b e) (sameSineCoefficient a b e) e-
      cosineCoefficient a b e=2*b*(1-Real.cos e) := by
    dsimp [harmonic,cosineCoefficient,sameSineCoefficient]
    linear_combination (1/2+b)*(Real.sin_sq_add_cos_sq e)
  have hm := mul_nonneg hb (sub_nonneg.mpr (Real.cos_le_one e))
  linarith

theorem same_sign_pair {a b e u : ℝ} (ha : 1/2≤a∧a≤7/12)
    (hb : 0≤b∧b≤a) (he : e∈Icc 0 frameCap) (hu : u∈Icc 0 e) :
    J e≤pairDeficit a b u (e-u) := by
  have hc := coefficients ha hb he
  have hconc : ConcaveOn ℝ (Icc 0 e)
      (harmonic (cosineCoefficient a b e) (sameSineCoefficient a b e)) := by
    apply harmonic_concave
    intro t ht
    exact harmonic_nonneg hc.1 hc.2.2.1
      ⟨ht.1,by linarith [ht.2,he.2,Real.pi_gt_three]⟩
  have hmin := hconc.min_le_of_mem_Icc (left_mem_Icc.mpr he.1)
    (right_mem_Icc.mpr he.1) hu
  have hend := same_endpoint_comparison (a := a) (e := e) hb.1
  simp only [harmonic,Real.cos_zero,Real.sin_zero,mul_one,mul_zero,add_zero] at hmin
  rw [min_eq_left hend] at hmin
  have hcharge := intrinsic_charge_lower ha.2 (hb.2.trans ha.2) he
  rw [same_harmonic_identity he hu]
  dsimp [ehCharge,cosineCoefficient] at *
  linarith

theorem opposite_harmonic_identity {a b e n : ℝ}
    (he : e∈Icc 0 frameCap) (hn : n∈Icc 0 (frameCap-e)) :
    pairDeficit a b (-n) (e+n)=
      harmonic (cosineCoefficient a b e) (oppositeSineCoefficient a b e) n-1 := by
  have hncap : n∈Icc 0 frameCap := ⟨hn.1,by linarith [hn.2,he.1]⟩
  have hv : e+n∈Icc 0 frameCap := ⟨by linarith [he.1,hn.1],by linarith [hn.2]⟩
  rw [pairDeficit,edgeWidth_negative_formula hncap,edgeWidth_positive_formula hv]
  simp only [Real.sin_neg,Real.cos_neg,Real.sin_add,Real.cos_add,
    harmonic,cosineCoefficient,oppositeSineCoefficient]
  ring

theorem opposite_endpoint_comparison {a b e : ℝ} (ha : 1/2≤a∧a≤7/12)
    (hb : 0≤b∧b≤a) (he : e∈Icc 0 frameCap) :
    cosineCoefficient a b e≤
      harmonic (cosineCoefficient a b e) (oppositeSineCoefficient a b e) (frameCap-e) := by
  have hc := coefficients ha hb he
  have hw : frameCap-e∈Icc 0 frameCap := ⟨by linarith [he.2],by linarith [he.1]⟩
  have hangle : 0≤frameCap-e∧frameCap-e≤4/5 := by
    constructor <;> dsimp [frameCap] at * <;> linarith [hw.1,hw.2]
  have hratio := halfRatio_upper hangle
  have hid := (halfRatio_identities hangle).2
  have hs := (transport_trig hw).2.2.1
  have h1 := mul_le_mul_of_nonneg_right hratio hs
  have h2 := mul_le_mul_of_nonneg_right hc.2.2.2 hs
  have h3 := mul_le_mul_of_nonpos_right hc.2.1
    (show Real.cos (frameCap-e)-1≤0 by linarith [Real.cos_le_one (frameCap-e)])
  dsimp [harmonic]
  nlinarith

theorem opposite_pair {a b e n : ℝ} (ha : 1/2≤a∧a≤7/12)
    (hb : 0≤b∧b≤a) (he : e∈Icc 0 frameCap) (hn : n∈Icc 0 (frameCap-e)) :
    J e≤pairDeficit a b (-n) (e+n) := by
  have hc := coefficients ha hb he
  have hB : 0≤oppositeSineCoefficient a b e := by
    have hh : 0≤(11/20 : ℝ)*(frameCap-e) := by positivity
    exact hh.trans hc.2.2.2
  have hconc : ConcaveOn ℝ (Icc 0 (frameCap-e))
      (harmonic (cosineCoefficient a b e) (oppositeSineCoefficient a b e)) := by
    apply harmonic_concave
    intro t ht
    exact harmonic_nonneg hc.1 hB
      ⟨ht.1,by linarith [ht.2,he.1,Real.pi_gt_three]⟩
  have hlen : 0≤frameCap-e := by linarith [he.2]
  have hmin := hconc.min_le_of_mem_Icc (left_mem_Icc.mpr hlen)
    (right_mem_Icc.mpr hlen) hn
  have hend := opposite_endpoint_comparison ha hb he
  simp only [harmonic,Real.cos_zero,Real.sin_zero,mul_one,mul_zero,add_zero] at hmin
  rw [min_eq_left hend] at hmin
  have hcharge := intrinsic_charge_lower ha.2 (hb.2.trans ha.2) he
  rw [opposite_harmonic_identity he hn]
  dsimp [ehCharge,cosineCoefficient] at *
  linarith

theorem pair_swap_comparison {a b e n : ℝ} (hb : 0≤b)
    (he : e∈Icc 0 frameCap) (hn : n∈Icc 0 (frameCap-e)) :
    pairDeficit a b (-n) (e+n)≤pairDeficit a b (e+n) (-n) := by
  have hcos : Real.cos (e+n)≤Real.cos n :=
    Real.cos_le_cos_of_nonneg_of_le_pi hn.1
      (by linarith [hn.2,Real.pi_gt_three]) (by linarith [he.1])
  have hm := mul_nonneg hb (sub_nonneg.mpr hcos)
  dsimp [pairDeficit]
  rw [Real.cos_neg]
  nlinarith

/-- The whole signed pair domain. A negative individual error is allowed
on either edge; only the actual sum is assumed nonnegative. -/
theorem signed_pair_lower {a b u v : ℝ} (ha : 1/2≤a∧a≤7/12)
    (hb : 0≤b∧b≤a) (hu : |u|≤frameCap) (hv : |v|≤frameCap)
    (he : u+v∈Icc 0 frameCap) : J (u+v)≤pairDeficit a b u v := by
  by_cases hu0 : 0≤u
  · by_cases hv0 : 0≤v
    · simpa using same_sign_pair ha hb he (show u∈Icc 0 (u+v) by constructor <;> linarith)
    · have hn : -v∈Icc 0 (frameCap-(u+v)) := by
        constructor
        · linarith
        · linarith [(le_abs_self u).trans hu]
      have hh := opposite_pair ha hb he hn
      have hs := pair_swap_comparison (a := a) hb.1 he hn
      have h1 : -(-v)=v := by ring
      have h2 : u+v+-v=u := by ring
      simpa only [h1,h2] using hh.trans hs
  · have hn : -u∈Icc 0 (frameCap-(u+v)) := by
      constructor
      · linarith
      · linarith [(le_abs_self v).trans hv]
    have hh := opposite_pair ha hb he hn
    have h1 : -(-u)=u := by ring
    have h2 : u+v+-u=v := by ring
    simpa only [h1,h2] using hh

theorem actual_core_pair {E : SignedPoint} {u v : ℝ}
    (hs : E.Sorted) (hc : E.Core) (hy : E.y≤0)
    (hu : |u|≤frameCap) (hv : |v|≤frameCap) (he : u+v∈Icc 0 frameCap) :
    J (u+v)≤pairDeficit E.a (-E.y) u v := by
  apply signed_pair_lower
  · exact ⟨(SignedPoint.primary_gt_half hs hc.ge).le,SignedPoint.core_primary_le hs hc⟩
  · exact ⟨by linarith,by simpa [abs_of_nonpos hy] using hs.2⟩
  · exact hu
  · exact hv
  · exact he

/-- Exchanging the two incident errors reverses only the signed transverse
coefficient. The same charge therefore applies to either original E sign. -/
theorem actual_core_pair_signed {E : SignedPoint} {u v : ℝ}
    (hs : E.Sorted) (hc : E.Core)
    (hu : |u|≤frameCap) (hv : |v|≤frameCap) (he : u+v∈Icc 0 frameCap) :
    J (u+v)≤pairDeficit E.a (-E.y) u v := by
  by_cases hy : E.y≤0
  · exact actual_core_pair hs hc hy hu hv he
  · have hy0 : 0≤E.y := (lt_of_not_ge hy).le
    have hh := signed_pair_lower
      (a := E.a) (b := E.y) (u := v) (v := u)
      ⟨(SignedPoint.primary_gt_half hs hc.ge).le,SignedPoint.core_primary_le hs hc⟩
      ⟨hy0,by simpa [abs_of_nonneg hy0] using hs.2⟩ hv hu
      (by simpa [add_comm] using he)
    have hid : pairDeficit E.a E.y v u=pairDeficit E.a (-E.y) u v := by
      dsimp [pairDeficit]
      ring
    simpa only [hid,add_comm] using hh

theorem J_hasDerivAt (e : ℝ) :
    HasDerivAt J (-Real.cos e/12-(13/12)*Real.sin e) e := by
  convert ((Real.hasDerivAt_sin e).neg.div_const 12).sub
    (((hasDerivAt_const e (1:ℝ)).sub (Real.hasDerivAt_cos e)).const_mul (13/12 : ℝ)) using 1
  · rfl
  · ring

theorem J_concave : ConcaveOn ℝ (Icc 0 frameCap) J := by
  apply concave_of_deriv2 (f' := fun e => -Real.cos e/12-(13/12)*Real.sin e)
    (f'' := fun e => Real.sin e/12-(13/12)*Real.cos e)
  · intro e _; exact J_hasDerivAt e
  · intro e _
    convert ((Real.hasDerivAt_cos e).neg.div_const 12).sub
      ((Real.hasDerivAt_sin e).const_mul (13/12 : ℝ)) using 1 <;> ring
  · intro e he
    obtain ⟨hc,hcu,hs0,hs,hsc⟩ := transport_trig he
    linarith

theorem J_linear_lower {e : ℝ} (he : e∈Icc 0 frameCap) :
    -(783/1000)*e≤J e := by
  have h := derivative_reserve (f := J)
    (df := fun t => -Real.cos t/12-(13/12)*Real.sin t) (k := -(783/1000 : ℝ))
    (by dsimp [J]; fun_prop) (fun t _ => J_hasDerivAt t)
    (fun t ht => by
      obtain ⟨hc,hcu,hs0,hs,hsc⟩ := transport_trig (Ioo_subset_Icc_self ht)
      linarith)
    (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) he he.1
  simpa [J] using h

theorem charge_gain_junction {lambda t d : ℝ}
    (hl : 1111/1250≤lambda) (he : t-d∈Icc 0 frameCap) :
    lambda*d≤J (t-d)+lambda*t := by
  have hh := J_linear_lower he
  have hm := mul_nonneg (show 0≤lambda-783/1000 by linarith) he.1
  nlinarith

end SquaresInCircles.Eight.TableFree.CoreECharge

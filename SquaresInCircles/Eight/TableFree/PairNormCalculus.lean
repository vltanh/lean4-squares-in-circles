module

public import SquaresInCircles.Eight.TableFree.PositiveAngularEnvelope

/-!
# Whole-interval curvature of an ordinary two-angle force

Uncompiled source draft of the calculus in
HAND_G3_HIGH_GA_LOW_EH_TD2_ANGLE_CONCENTRATION.md, Section 3.
All four derivatives are identities for the actual force norm. The
curvature increases on the entire signed interval and lies below its
tangent at zero on the entire positive interval. The ratio restriction
is used only for the fourth derivative sign.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.PairNormCalculus
open PositiveAngularEnvelope

def pairEnergy (p q : ℝ) : ℝ := p^2+q^2
def pairProduct (p q : ℝ) : ℝ := p*q

def normD1 (p q t : ℝ) : ℝ :=
  pairProduct p q*Real.cos t/pairNorm p q t

def normD2 (p q t : ℝ) : ℝ :=
  -pairProduct p q*(pairEnergy p q*Real.sin t+
    pairProduct p q*(1+(Real.sin t)^2))/(pairNorm p q t)^3

def normD3 (p q t : ℝ) : ℝ :=
  -pairProduct p q*Real.cos t*
    ((pairEnergy p q)^2-3*(pairProduct p q)^2+
      pairEnergy p q*pairProduct p q*Real.sin t+
      (pairProduct p q)^2*(Real.sin t)^2)/(pairNorm p q t)^5

def normD4 (p q t : ℝ) : ℝ :=
  pairProduct p q*
    (pairProduct p q*(4*(pairEnergy p q)^2-15*(pairProduct p q)^2)+
      pairEnergy p q*((pairEnergy p q)^2-2*(pairProduct p q)^2)*Real.sin t+
      pairProduct p q*(10*(pairProduct p q)^2-(pairEnergy p q)^2)*(Real.sin t)^2+
      2*pairEnergy p q*(pairProduct p q)^2*(Real.sin t)^3+
      (pairProduct p q)^3*(Real.sin t)^4)/(pairNorm p q t)^7

theorem pairEnergy_ge_twice (p q : ℝ) : 2*pairProduct p q≤pairEnergy p q := by
  dsimp [pairProduct,pairEnergy]
  nlinarith [sq_nonneg (p-q)]

theorem pairEnergy_le_five_halves {p q : ℝ}
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p) :
    2*pairEnergy p q≤5*pairProduct p q := by
  have hprod := mul_nonneg (show 0≤2*p-q by linarith)
    (show 0≤2*q-p by linarith)
  dsimp [pairProduct,pairEnergy]
  nlinarith

theorem pair_radicand_pos {p q t : ℝ} (hp : 0<p) (hq : 0<q)
    (ht : |t|≤frameCap) : 0<p^2+q^2+2*p*q*Real.sin t := by
  have hs := (abs_le.mp (small_angle ht).2).1
  have hB : 0<p*q := mul_pos hp hq
  have hbase := sq_nonneg (p-q)
  have hm := mul_le_mul_of_nonneg_left hs hB.le
  dsimp [frameCap] at hs
  nlinarith

theorem pairNorm_pos {p q t : ℝ} (hp : 0<p) (hq : 0<q)
    (ht : |t|≤frameCap) : 0<pairNorm p q t :=
  Real.sqrt_pos.mpr (pair_radicand_pos hp hq ht)

theorem pairNorm_sq {p q t : ℝ} (hp : 0<p) (hq : 0<q)
    (ht : |t|≤frameCap) :
    (pairNorm p q t)^2=pairEnergy p q+2*pairProduct p q*Real.sin t := by
  simpa only [pairNorm,pairEnergy,pairProduct,mul_assoc] using
    Real.sq_sqrt (pair_radicand_pos hp hq ht).le

theorem pairNorm_power_reduce {p q t : ℝ} (hp : 0<p) (hq : 0<q)
    (ht : |t|≤frameCap) (n : ℕ) :
    (pairNorm p q t)^(n+2)=(pairNorm p q t)^n*
      (pairEnergy p q+2*pairProduct p q*Real.sin t) := by
  rw [pow_add,pairNorm_sq hp hq ht]

theorem pairNorm_hasDerivAt {p q t : ℝ} (hp : 0<p) (hq : 0<q)
    (ht : |t|≤frameCap) : HasDerivAt (pairNorm p q) (normD1 p q t) t := by
  have hr := ((hasDerivAt_const t (p^2+q^2)).add
    ((Real.hasDerivAt_sin t).const_mul (2*p*q))).sqrt
      (pair_radicand_pos hp hq ht).ne'
  convert hr using 1
  · rfl
  · dsimp [normD1,pairProduct,pairNorm]
    ring

theorem normD1_hasDerivAt {p q t : ℝ} (hp : 0<p) (hq : 0<q)
    (ht : |t|≤frameCap) : HasDerivAt (normD1 p q) (normD2 p q t) t := by
  have hN := pairNorm_hasDerivAt hp hq ht
  have hne := (pairNorm_pos hp hq ht).ne'
  have hraw := ((Real.hasDerivAt_cos t).const_mul (pairProduct p q)).div hN hne
  have hsq := pairNorm_sq hp hq ht
  have hu := Real.sin_sq_add_cos_sq t
  convert hraw using 1
  · rfl
  · dsimp only [normD1,normD2]
    field_simp
    linear_combination (pairProduct p q*Real.sin t)*hsq+(pairProduct p q)^2*hu

theorem normD2_hasDerivAt {p q t : ℝ} (hp : 0<p) (hq : 0<q)
    (ht : |t|≤frameCap) : HasDerivAt (normD2 p q) (normD3 p q t) t := by
  have hN := pairNorm_hasDerivAt hp hq ht
  have hne := (pairNorm_pos hp hq ht).ne'
  have hnum := (((Real.hasDerivAt_sin t).const_mul (pairEnergy p q)).add
    (((hasDerivAt_const t (1:ℝ)).add ((Real.hasDerivAt_sin t).pow 2)).const_mul
      (pairProduct p q))).const_mul (-pairProduct p q)
  have hraw := hnum.div (hN.pow 3) (pow_ne_zero 3 hne)
  have hsq := pairNorm_sq hp hq ht
  have hu := Real.sin_sq_add_cos_sq t
  convert hraw using 1
  · rfl
  · simp only [Pi.pow_apply,Pi.add_apply]
    norm_num
    dsimp only [normD1,normD2,normD3]
    field_simp
    linear_combination (pairProduct p q*Real.cos t*(pairEnergy p q+2*pairProduct p q*Real.sin t))*hsq

theorem normD3_hasDerivAt {p q t : ℝ} (hp : 0<p) (hq : 0<q)
    (ht : |t|≤frameCap) : HasDerivAt (normD3 p q) (normD4 p q t) t := by
  have hN := pairNorm_hasDerivAt hp hq ht
  have hne := (pairNorm_pos hp hq ht).ne'
  have hpoly := ((hasDerivAt_const t
      ((pairEnergy p q)^2-3*(pairProduct p q)^2)).add
    ((Real.hasDerivAt_sin t).const_mul (pairEnergy p q*pairProduct p q))).add
      (((Real.hasDerivAt_sin t).pow 2).const_mul ((pairProduct p q)^2))
  have hnum := ((Real.hasDerivAt_cos t).const_mul (-pairProduct p q)).mul hpoly
  have hraw := hnum.div (hN.pow 5) (pow_ne_zero 5 hne)
  have hsq := pairNorm_sq hp hq ht
  have hu := Real.sin_sq_add_cos_sq t
  convert hraw using 1
  · rfl
  · simp only [Pi.pow_apply,Pi.add_apply,Pi.mul_apply]
    norm_num
    dsimp only [normD1,normD3,normD4]
    field_simp
    linear_combination (pairProduct p q*(Real.cos t^2*pairEnergy p q*pairProduct p q+2*Real.cos t^2*pairProduct p q^2*Real.sin t-pairEnergy p q^2*Real.sin t-
        pairEnergy p q*pairProduct p q*Real.sin t^2-pairProduct p q^2*Real.sin t^3+3*pairProduct p q^2*Real.sin t))*hsq-
      (pairProduct p q^2*(4*pairEnergy p q^2+pairEnergy p q*pairProduct p q*Real.sin t+pairProduct p q^2*Real.sin t^2-15*pairProduct p q^2))*hu

/-- The third derivative sign needs no upper coefficient-ratio bound. -/
theorem normD3_nonpos {p q t : ℝ} (hp : 0<p) (hq : 0<q)
    (ht : |t|≤frameCap) : normD3 p q t≤0 := by
  have hB : 0<pairProduct p q := mul_pos hp hq
  have hA := pairEnergy_ge_twice p q
  have hs := (abs_le.mp (small_angle ht).2).1
  have hm := mul_le_mul_of_nonneg_left hs hB.le
  have hfactor : 0≤pairEnergy p q+2*pairProduct p q+
      pairProduct p q*Real.sin t := by
    dsimp [frameCap] at hs hm
    nlinarith
  have hpoly : 0≤(pairEnergy p q)^2-3*(pairProduct p q)^2+
      pairEnergy p q*pairProduct p q*Real.sin t+
      (pairProduct p q)^2*(Real.sin t)^2 := by
    have hid : (pairEnergy p q)^2-3*(pairProduct p q)^2+
        pairEnergy p q*pairProduct p q*Real.sin t+
        (pairProduct p q)^2*(Real.sin t)^2=
      (pairEnergy p q-2*pairProduct p q)*
        (pairEnergy p q+2*pairProduct p q+pairProduct p q*Real.sin t)+
        (pairProduct p q)^2*(1+Real.sin t)^2 := by ring
    rw [hid]
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr hA) hfactor) (by positivity)
  unfold normD3
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hB.le)
        (transport_cos_pos ht).le) hpoly)
    (pow_nonneg (pairNorm_pos hp hq ht).le 5)

theorem normD4_nonneg {p q t : ℝ} (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p)
    (ht : t∈Icc 0 frameCap) : 0≤normD4 p q t := by
  have hq : 0<q := hp.trans_le hpq
  have hB : 0<pairProduct p q := mul_pos hp hq
  have hA0 : 0≤pairEnergy p q := by dsimp [pairEnergy]; positivity
  have hA := pairEnergy_ge_twice p q
  have hAu := pairEnergy_le_five_halves hp hpq hqp
  have hlo : 4*(pairProduct p q)^2≤(pairEnergy p q)^2 := by nlinarith
  have hhi : (pairEnergy p q)^2≤(25/4)*(pairProduct p q)^2 := by nlinarith
  have h₀ : 0≤4*(pairEnergy p q)^2-15*(pairProduct p q)^2 := by nlinarith
  have h₁ : 0≤(pairEnergy p q)^2-2*(pairProduct p q)^2 := by nlinarith
  have h₂ : 0≤10*(pairProduct p q)^2-(pairEnergy p q)^2 := by nlinarith
  have hs := (transport_trig ht).2.2.1
  have hN := pairNorm_pos hp hq (by rw [abs_of_nonneg ht.1]; exact ht.2)
  unfold normD4
  positivity

def curvature (R p q t : ℝ) : ℝ := -R*normD2 p q t
def curvatureD (R p q t : ℝ) : ℝ := -R*normD3 p q t
def curvatureZero (R p q : ℝ) : ℝ :=
  R*(pairProduct p q)^2/(pairNorm p q 0)^3
def curvatureSlope (R p q : ℝ) : ℝ :=
  R*pairProduct p q*((pairEnergy p q)^2-3*(pairProduct p q)^2)/
    (pairNorm p q 0)^5

@[simp] theorem curvature_zero (R p q : ℝ) : curvature R p q 0=curvatureZero R p q := by
  simp [curvature,normD2,curvatureZero]
  ring

@[simp] theorem curvatureD_zero (R p q : ℝ) : curvatureD R p q 0=curvatureSlope R p q := by
  simp [curvatureD,normD3,curvatureSlope]
  ring

theorem curvature_hasDerivAt {R p q t : ℝ} (hp : 0<p) (hq : 0<q)
    (ht : |t|≤frameCap) :
    HasDerivAt (curvature R p q) (curvatureD R p q t) t :=
  (normD2_hasDerivAt hp hq ht).const_mul (-R)

theorem curvatureD_hasDerivAt {R p q t : ℝ} (hp : 0<p) (hq : 0<q)
    (ht : |t|≤frameCap) :
    HasDerivAt (curvatureD R p q) (-R*normD4 p q t) t :=
  (normD3_hasDerivAt hp hq ht).const_mul (-R)

theorem curvature_monotone {R p q : ℝ} (hR : 0≤R) (hp : 0<p) (hq : 0<q) :
    MonotoneOn (curvature R p q) (Icc (-frameCap) frameCap) := by
  apply monoOn_of_hasDeriv_nonneg
  · intro t ht
    exact (curvature_hasDerivAt hp hq (abs_le.mpr ht)).continuousAt.continuousWithinAt
  · intro t ht
    exact curvature_hasDerivAt hp hq (abs_le.mpr ⟨ht.1.le,ht.2.le⟩)
  · intro t ht
    exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hR)
      (normD3_nonpos hp hq (abs_le.mpr ⟨ht.1.le,ht.2.le⟩))

theorem curvature_negative_upper {R p q t : ℝ}
    (hR : 0≤R) (hp : 0<p) (hq : 0<q) (ht : t∈Icc (-frameCap) 0) :
    curvature R p q t≤curvatureZero R p q := by
  have hz : (0:ℝ)∈Icc (-frameCap) frameCap := by norm_num [frameCap]
  simpa using curvature_monotone hR hp hq
    ⟨ht.1,ht.2.trans hz.2⟩ hz ht.2

theorem curvatureD_antitone {R p q : ℝ} (hR : 0≤R)
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p) :
    AntitoneOn (curvatureD R p q) (Icc 0 frameCap) := by
  have hq : 0<q := hp.trans_le hpq
  apply antiOn_of_hasDeriv_nonpos
  · intro t ht
    exact (curvatureD_hasDerivAt hp hq
      (by rw [abs_of_nonneg ht.1]; exact ht.2)).continuousAt.continuousWithinAt
  · intro t ht
    exact curvatureD_hasDerivAt hp hq
      (by rw [abs_of_pos ht.1]; exact ht.2.le)
  · intro t ht
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hR)
      (normD4_nonneg hp hpq hqp (Ioo_subset_Icc_self ht))

/-- The tangent bound is global on `[0,7/10]`. -/
theorem curvature_positive_upper {R p q t : ℝ} (hR : 0≤R)
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p) (ht : t∈Icc 0 frameCap) :
    curvature R p q t≤curvatureZero R p q+curvatureSlope R p q*t := by
  have hq : 0<q := hp.trans_le hpq
  have hz : (0:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hdc (x : ℝ) (hx : x∈Icc 0 frameCap) :=
    curvature_hasDerivAt (R := R) hp hq (by rw [abs_of_nonneg hx.1]; exact hx.2)
  have hbound (x : ℝ) (hx : x∈Icc 0 frameCap) :
      curvatureD R p q x≤curvatureSlope R p q := by
    simpa using curvatureD_antitone hR hp hpq hqp hz hx hx.1
  have h := derivative_reserve
    (f := fun x => -curvature R p q x) (df := fun x => -curvatureD R p q x)
    (k := -curvatureSlope R p q)
    (fun x hx => (hdc x hx).neg.continuousAt.continuousWithinAt)
    (fun x hx => (hdc x (Ioo_subset_Icc_self hx)).neg)
    (fun x hx => neg_le_neg (hbound x (Ioo_subset_Icc_self hx)))
    hz ht ht.1
  rw [curvature_zero] at h
  linarith

end SquaresInCircles.Eight.TableFree.PairNormCalculus

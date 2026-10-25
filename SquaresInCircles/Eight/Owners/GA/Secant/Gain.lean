module

public import SquaresInCircles.Eight.Owners.CircleGeometry
public import SquaresInCircles.Eight.Owners.TrigonometricReserves

/-!
# Eight squares: the common secant gain in the high-GA exclusion

The proof is uniform on the whole frame interval and for every `k ≥ 13/20`. It proves the slightly
stronger derivative reserve `23/25` (`secantGainDeriv_gt`), hence the gain `9/10` with a remaining
displacement reserve. The squared radius may be any value between `0` and `qCap`.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA

def gainRadicand (k x : ℝ) : ℝ := 1+k^2*(Real.cos x)^2

/-- The common gain after writing both secants over the positive cosine. -/
def secantGain (q k x : ℝ) : ℝ :=
  (1+(13/12 : ℝ)*Real.sin x-
      Real.sqrt q*Real.sqrt (gainRadicand k x))/Real.cos x-
    1+Real.sqrt q*Real.sqrt (1+k^2)

def secantGainDeriv (q k x : ℝ) : ℝ :=
  ((13/12 : ℝ)+Real.sin x-
      Real.sqrt q*Real.sin x/Real.sqrt (gainRadicand k x))/(Real.cos x)^2

theorem gainRadicand_pos (k x : ℝ) : 0<gainRadicand k x := by
  unfold gainRadicand
  positivity

theorem secantGain_zero (q k : ℝ) : secantGain q k 0=0 := by
  simp [secantGain,gainRadicand]

theorem gainRadicand_hasDerivAt (k x : ℝ) :
    HasDerivAt (gainRadicand k)
      (-2*k^2*Real.cos x*Real.sin x) x := by
  have hd := (hasDerivAt_const x (1:ℝ)).add
    (((Real.hasDerivAt_cos x).pow 2).const_mul (k^2))
  convert hd using 1
  · funext y
    simp only [gainRadicand,Pi.add_apply,Pi.pow_apply]
  · norm_num
    ring

theorem secantGain_hasDerivAt (q k : ℝ) {x : ℝ}
    (hc : Real.cos x≠0) :
    HasDerivAt (secantGain q k) (secantGainDeriv q k x) x := by
  have hp := gainRadicand_pos k x
  have hs := (gainRadicand_hasDerivAt k x).sqrt hp.ne'
  have hroot : Real.sqrt (gainRadicand k x)≠0 :=
    ne_of_gt (Real.sqrt_pos.mpr hp)
  have hid := Real.sq_sqrt hp.le
  have hunit := Real.sin_sq_add_cos_sq x
  have h := ((((hasDerivAt_const x (1:ℝ)).add
    ((Real.hasDerivAt_sin x).const_mul (13/12 : ℝ))).sub
      (hs.const_mul (Real.sqrt q))).div (Real.hasDerivAt_cos x) hc).sub_const 1
  have h' := h.add_const (Real.sqrt q*Real.sqrt (1+k^2))
  convert h' using 1
  · rfl
  · simp only [secantGainDeriv,Pi.add_apply,Pi.sub_apply]
    field_simp [hc,hroot]
    have hid' : Real.sqrt (gainRadicand k x)^2=1+k^2*Real.cos x^2 := hid
    linear_combination (-13*Real.sqrt (gainRadicand k x))*hunit+
      (12*Real.sin x*Real.sqrt q)*hid'

/-- `secantGain` agrees with the secant and tangent form of the support gain. -/
theorem secantGain_eq_secant_expression (q k : ℝ) {x : ℝ}
    (hc : 0<Real.cos x) :
    secantGain q k x =
      1/Real.cos x+(13/12 : ℝ)*Real.tan x-
        Real.sqrt q*Real.sqrt ((1/Real.cos x)^2+k^2)-
        1+Real.sqrt q*Real.sqrt (1+k^2) := by
  have hp : 0≤(1/Real.cos x)^2+k^2 := by positivity
  have hsq :
      (Real.sqrt ((1/Real.cos x)^2+k^2)*Real.cos x)^2=gainRadicand k x := by
    rw [mul_pow,Real.sq_sqrt hp]
    dsimp [gainRadicand]
    field_simp [hc.ne']
  have he : Real.sqrt ((1/Real.cos x)^2+k^2)*Real.cos x=
      Real.sqrt (gainRadicand k x) := by
    nlinarith [Real.sq_sqrt (gainRadicand_pos k x).le,
      Real.sqrt_nonneg (gainRadicand k x),
      mul_nonneg (Real.sqrt_nonneg ((1/Real.cos x)^2+k^2)) hc.le]
  have hroot : Real.sqrt ((1/Real.cos x)^2+k^2)=
      Real.sqrt (gainRadicand k x)/Real.cos x :=
    (eq_div_iff hc.ne').2 he
  rw [hroot,Real.tan_eq_sin_div_cos]
  unfold secantGain
  ring

/-- A direct positive square comparison, without a radius enclosure or an
angle subdivision. Only the smallest possible k and largest sine matter. -/
theorem radius_over_gain_root_lt {q k x : ℝ}
    (hq : 0≤q) (hQ : q≤qCap) (hk : 13/20≤k)
    (hx : x∈Icc 0 frameCap) :
    Real.sqrt q/Real.sqrt (gainRadicand k x)<1773/1000 := by
  obtain ⟨hc,hcu,hs0,hs,hsc⟩ := transport_trig hx
  have hsbound : Real.sin x≤129/200 := by linarith
  have hs2 : (Real.sin x)^2≤(129/200 : ℝ)^2 :=
    pow_le_pow_left₀ hs0 hsbound 2
  have hk0 : 0≤k := by linarith
  have hk2 : (13/20 : ℝ)^2≤k^2 := pow_le_pow_left₀ (by norm_num) hk 2
  have hc2 : 1-(129/200 : ℝ)^2≤(Real.cos x)^2 := by
    nlinarith [Real.sin_sq_add_cos_sq x]
  have hprod := mul_le_mul hk2 hc2
    (by norm_num : 0≤1-(129/200 : ℝ)^2) (sq_nonneg k)
  have hrad :
      1+(13/20 : ℝ)^2*(1-(129/200 : ℝ)^2)≤gainRadicand k x := by
    dsimp [gainRadicand]
    linarith
  have hreserve : qCap<
      (1773/1000 : ℝ)^2*(1+(13/20 : ℝ)^2*(1-(129/200 : ℝ)^2)) := by
    norm_num [qCap]
  have hstrict : q<(1773/1000 : ℝ)^2*gainRadicand k x :=
    hQ.trans_lt (hreserve.trans_le
      (mul_le_mul_of_nonneg_left hrad (by norm_num)))
  have hroot := Real.sqrt_pos.mpr (gainRadicand_pos k x)
  apply (div_lt_iff₀ hroot).2
  have hrq := Real.sq_sqrt hq
  have hrA := Real.sq_sqrt (gainRadicand_pos k x).le
  nlinarith [Real.sqrt_nonneg q,
    mul_nonneg (by norm_num : (0:ℝ)≤1773/1000) hroot.le]

/-- The discriminant of the quadratic leaves a positive reserve. -/
theorem common_gain_quadratic_pos (y : ℝ) :
    0<(23/25 : ℝ)*y^2-(773/1000 : ℝ)*y+13/12-23/25 := by
  nlinarith [sq_nonneg (y-(773/1840 : ℝ))]

theorem secantGainDeriv_gt {q k x : ℝ}
    (hq : 0≤q) (hQ : q≤qCap) (hk : 13/20≤k)
    (hx : x∈Icc 0 frameCap) : 23/25<secantGainDeriv q k x := by
  obtain ⟨hc,hcu,hs0,hs,hsc⟩ := transport_trig hx
  have hcpos : 0<Real.cos x := by linarith
  have hr := radius_over_gain_root_lt hq hQ hk hx
  have hm := mul_le_mul_of_nonneg_right hr.le hs0
  have hquad := common_gain_quadratic_pos (Real.sin x)
  have hunit := Real.sin_sq_add_cos_sq x
  unfold secantGainDeriv
  apply (lt_div_iff₀ (sq_pos_of_pos hcpos)).2
  have he : Real.sqrt q*Real.sin x/Real.sqrt (gainRadicand k x)=
      (Real.sqrt q/Real.sqrt (gainRadicand k x))*Real.sin x := by ring
  rw [he]
  nlinarith

end SquaresInCircles.Eight.GlobalGA

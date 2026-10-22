module

public import SquaresInCircles.Eight.TableFree.GlobalGASecantGain
public import SquaresInCircles.Eight.TableFree.HighOrderTaylor

/-!
# The secant gains of a negative core-E primary

Uncompiled transcription of the whole-interval gain estimates in
`HAND_G3_CORE_E_NEGATIVE_DE3_SECANT_D_SUPPORT.md`, Section 4, and
`HAND_G3_CORE_E_NEGATIVE_EH1_SECANT_H_SUPPORT.md`, Section 3.

The DE estimate retains the exact 1/390 reserve after the 21/20
angular charge. The EH estimate retains 1/625 after the 103/100
charge. The latter includes the actual change of the H circle norm,
not just its tangent/secant lower model.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeESecant
open Arithmetic

def K : ℝ := 13/12

def gain (b s : ℝ) : ℝ :=
  (K*Real.sin s-b*(1-Real.cos s))/Real.cos s

def gainD (b s : ℝ) : ℝ := (K-b*Real.sin s)/Real.cos s^2

def gainDD (b s : ℝ) : ℝ :=
  (2*K*Real.sin s-b*(1+Real.sin s^2))/Real.cos s^3

theorem cos_pos {s : ℝ} (hs : s∈Icc 0 frameCap) : 0<Real.cos s :=
  transport_cos_pos (by rw [abs_of_nonneg hs.1]; exact hs.2)

theorem gain_secant (b : ℝ) {s : ℝ} (hs : s∈Icc 0 frameCap) :
    gain b s=K*Real.tan s-b*(1/Real.cos s-1) := by
  rw [Real.tan_eq_sin_div_cos]
  dsimp [gain]
  field_simp [(cos_pos hs).ne']
  ring

@[simp] theorem gain_zero (b : ℝ) : gain b 0=0 := by simp [gain]

theorem gain_hasDerivAt (b : ℝ) {s : ℝ} (hs : s∈Icc 0 frameCap) :
    HasDerivAt (gain b) (gainD b s) s := by
  have hc := (cos_pos hs).ne'
  have hd := (((Real.hasDerivAt_sin s).const_mul K).sub
    (((Real.hasDerivAt_cos s).const_sub 1).const_mul b)).div
      (Real.hasDerivAt_cos s) hc
  convert hd using 1
  · rfl
  · dsimp [gainD]
    field_simp [hc]
    nlinarith only [congrArg (fun z : ℝ => K*z) (Real.sin_sq_add_cos_sq s)]

theorem gainD_hasDerivAt (b : ℝ) {s : ℝ} (hs : s∈Icc 0 frameCap) :
    HasDerivAt (gainD b) (gainDD b s) s := by
  have hc := (cos_pos hs).ne'
  have hd := (((Real.hasDerivAt_sin s).const_mul b).const_sub K).
    div ((Real.hasDerivAt_cos s).pow 2) (pow_ne_zero 2 hc)
  convert hd using 1
  · rfl
  · dsimp [gainDD]
    field_simp [hc]
    nlinarith only [congrArg (fun z : ℝ => b*Real.cos s*z)
      (Real.sin_sq_add_cos_sq s)]

theorem gain_antitone_coefficient {b c s : ℝ} (hbc : b≤c)
    (hs : s∈Icc 0 frameCap) : gain c s≤gain b s := by
  have hcos := Real.cos_le_one s
  have hp := mul_le_mul_of_nonneg_right hbc (by linarith : 0≤1-Real.cos s)
  exact div_le_div_of_nonneg_right (by dsimp [gain] at *; linarith) (cos_pos hs).le

/-- The polynomial is the exact cosine-multiplied DE reserve divided
by its angle. Its negative high powers are bounded on the whole interval. -/
def dePolynomial (s : ℝ) : ℝ :=
  1/30-s/5+(31/90)*s^2+(1/60)*s^3-(5/144)*s^4-(1/1800)*s^5+
    ((21/20)/720-K/5040)*s^6-((21/20)/40320)*s^8

theorem dePolynomial_lower {s : ℝ} (hs : s∈Icc 0 frameCap) :
    (1/390:ℝ)≤dePolynomial s := by
  have h2 : s^2≤(7/10:ℝ)^2 := pow_le_pow_left₀ hs.1 hs.2 2
  have h3 : s^3≤(7/10:ℝ)^3 := pow_le_pow_left₀ hs.1 hs.2 3
  have h6 : s^6≤(7/10:ℝ)^6 := pow_le_pow_left₀ hs.1 hs.2 6
  have h4 : s^4≤(7/10:ℝ)^2*s^2 := by
    calc s^4=s^2*s^2 := by ring
         _≤(7/10:ℝ)^2*s^2 := mul_le_mul_of_nonneg_right h2 (sq_nonneg s)
  have h5 : s^5≤(7/10:ℝ)^3*s^2 := by
    calc s^5=s^3*s^2 := by ring
         _≤(7/10:ℝ)^3*s^2 := mul_le_mul_of_nonneg_right h3 (sq_nonneg s)
  have h8 : s^8≤(7/10:ℝ)^6*s^2 := by
    calc s^8=s^6*s^2 := by ring
         _≤(7/10:ℝ)^6*s^2 := mul_le_mul_of_nonneg_right h6 (sq_nonneg s)
  have hquadratic : (1/390:ℝ)≤1/30-s/5+(13/40)*s^2 := by
    nlinarith [sq_nonneg (s-(4/13:ℝ))]
  have hpoly : 1/30-s/5+(13/40)*s^2≤dePolynomial s := by
    dsimp [dePolynomial,K]
    nlinarith only [h4,h5,h8,pow_nonneg hs.1 3,pow_nonneg hs.1 6,sq_nonneg s]
  exact hquadratic.trans hpoly

theorem de_cosine_reserve {s : ℝ} (hs : s∈Icc 0 frameCap) :
    s/390≤K*Real.sin s+(2/5)*(Real.cos s-1)-(21/20)*s*Real.cos s := by
  have hsin : sin7 s≤Real.sin s := sin_lower_seven hs.1
  have hcos := cos_lower_six hs.1
  have hupper := cos_le_cos8 hs.1
  have h1 := mul_le_mul_of_nonneg_left hsin (by norm_num [K] : 0≤K)
  have h2 := mul_le_mul_of_nonneg_left hcos (by norm_num : (0:ℝ)≤2/5)
  have h3 := mul_le_mul_of_nonneg_left hupper
    (mul_nonneg (by norm_num : (0:ℝ)≤21/20) hs.1)
  have he : K*sin7 s+(2/5)*(1-s^2/2+s^4/24-s^6/720-1)-
      (21/20)*s*cos8 s=s*dePolynomial s := by
    dsimp [sin7,cos8,dePolynomial,K]
    ring
  have hp := mul_le_mul_of_nonneg_left (dePolynomial_lower hs) hs.1
  nlinarith only [h1,h2,h3,he,hp]

theorem de_gain_lower {b s : ℝ} (hb : b≤2/5)
    (hs : s∈Icc 0 frameCap) :
    ((21/20:ℝ)+1/390)*s≤gain b s := by
  have hbase : ((21/20:ℝ)+1/390)*s≤gain (2/5) s := by
    have hres := de_cosine_reserve hs
    have hm := mul_le_mul_of_nonneg_left (Real.cos_le_one s)
      (div_nonneg hs.1 (by norm_num : (0:ℝ)≤390))
    dsimp [gain]
    apply (le_div_iff₀ (cos_pos hs)).2
    nlinarith only [hres,hm]
  exact hbase.trans (gain_antitone_coefficient hb hs)

theorem de_secant_range {s : ℝ} (hs : s∈Icc 0 frameCap) :
    1≤1/Real.cos s ∧ 1/Real.cos s≤327/250 := by
  have ht := transport_trig hs
  have hc := cos_pos hs
  constructor
  · apply (le_div_iff₀ hc).2
    simpa using Real.cos_le_one s
  · apply (div_le_iff₀ hc).2
    linarith [ht.1]

theorem eh_short_subset {s : ℝ} (hs : s∈Icc 0 (1/4:ℝ)) :
    s∈Icc 0 frameCap := ⟨hs.1,by dsimp [frameCap]; linarith [hs.2]⟩

theorem eh_secant_range {s : ℝ} (hs : s∈Icc 0 (1/4:ℝ)) :
    1≤1/Real.cos s ∧ 1/Real.cos s≤1033/1000 := by
  have hc := cos_pos (eh_short_subset hs)
  have ht := trig_bracket (l := 0) (u := (1/4:ℝ))
    (by norm_num) (by linarith [Real.pi_gt_three]) hs
  constructor
  · apply (le_div_iff₀ hc).2
    simpa using Real.cos_le_one s
  · apply (div_le_iff₀ hc).2
    norm_num at ht
    linarith [ht.2.2.1]

/-- The lower EH model is concave up to its genuine-EH cutoff. -/
theorem eh_gain_curvature {s : ℝ} (hs : s∈Icc 0 (1/4:ℝ)) :
    gainDD (29/50) s≤0 := by
  have hsupper : Real.sin s≤1/4 := (Real.sin_le hs.1).trans hs.2
  have hnum : 2*K*Real.sin s-(29/50)*(1+Real.sin s^2)≤-(23/600:ℝ) := by
    dsimp [K]
    nlinarith [sq_nonneg (Real.sin s)]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith)
    (pow_nonneg (cos_pos (eh_short_subset hs)).le 3)

theorem eh_cap_gain :
    ((103/100:ℝ)+1/625)*(1/4)≤gain (29/50) (1/4) := by
  have hsin := sin_lower_seven (by norm_num : (0:ℝ)≤1/4)
  have hcos := cos_lower_six (by norm_num : (0:ℝ)≤1/4)
  have hmul := mul_le_mul_of_nonneg_left hcos
    (by norm_num : (0:ℝ)≤29/50-(103/100)*(1/4))
  have hs := mul_le_mul_of_nonneg_left hsin (by norm_num [K] : 0≤K)
  have hres : (1/2500:ℝ)<
      K*Real.sin (1/4)+(29/50-(103/100)*(1/4))*Real.cos (1/4)-29/50 := by
    norm_num [K] at hs hmul
    linarith
  have hc := cos_pos (eh_short_subset (by norm_num : (1/4:ℝ)∈Icc 0 (1/4)))
  dsimp [gain]
  apply (le_div_iff₀ hc).2
  nlinarith [Real.cos_le_one (1/4:ℝ)]

theorem eh_model_gain_lower {s : ℝ} (hs : s∈Icc 0 (1/4:ℝ)) :
    ((103/100:ℝ)+1/625)*s≤gain (29/50) s := by
  let f : ℝ→ℝ := fun t => gain (29/50) t-((103/100:ℝ)+1/625)*t
  have hconc : ConcaveOn ℝ (Icc 0 (1/4:ℝ)) f := by
    apply concave_of_deriv2
      (f' := fun t => gainD (29/50) t-((103/100:ℝ)+1/625))
      (f'' := gainDD (29/50))
    · intro t ht
      exact (gain_hasDerivAt (29/50) (eh_short_subset ht)).sub
        ((hasDerivAt_id t).const_mul ((103/100:ℝ)+1/625))
    · intro t ht
      exact (gainD_hasDerivAt (29/50) (eh_short_subset ht)).sub_const _
    · exact fun t ht => eh_gain_curvature ht
  have hmin := concave_endpoint_reserve (f := f) (k := 0) (by norm_num) hs
    (by simpa using hconc)
  have h0 : f 0=0 := by simp [f]
  have hcap : 0≤f (1/4) := by dsimp [f]; linarith [eh_cap_gain]
  have hmin0 : 0≤min (f 0) (f (1/4)) := le_min (by rw [h0]) hcap
  dsimp [f] at hmin
  nlinarith

/-- The exact positive-square comparison used to bound the H norm change. -/
theorem eh_root_slope {u : ℝ} (hu : u∈Icc 1 (1033/1000:ℝ)) :
    Real.sqrt qCap*u≤(79/50)*Real.sqrt (u^2+(39/50:ℝ)^2) := by
  have hu0 : 0≤u := by linarith [hu.1]
  have hu2 : u^2≤(1033/1000:ℝ)^2 := pow_le_pow_left₀ hu0 hu.2 2
  have hp : 0≤u^2+(39/50:ℝ)^2 := by positivity
  have hsq := Real.sq_sqrt hp
  have hR := Real.sq_sqrt (by norm_num [qCap] : 0≤qCap)
  have htarget : qCap*u^2<(79/50:ℝ)^2*(u^2+(39/50:ℝ)^2) := by
    dsimp [qCap]
    nlinarith only [hu2]
  have hleft := mul_nonneg (Real.sqrt_nonneg qCap) hu0
  have hright := Real.sqrt_nonneg (u^2+(39/50:ℝ)^2)
  have hleftsq : (Real.sqrt qCap*u)^2=qCap*u^2 := by rw [mul_pow,hR]
  nlinarith only [hleft,hright,hleftsq,hsq,htarget]

theorem eh_root_difference {u : ℝ} (hu : u∈Icc 1 (1033/1000:ℝ)) :
    Real.sqrt qCap*(Real.sqrt (u^2+(39/50:ℝ)^2)-
      Real.sqrt (1+(39/50:ℝ)^2))≤(79/50)*(u-1) := by
  let r := Real.sqrt (u^2+(39/50:ℝ)^2)
  let r0 := Real.sqrt (1+(39/50:ℝ)^2)
  have hr : r^2=u^2+(39/50:ℝ)^2 := Real.sq_sqrt (by positivity)
  have hr0 : r0^2=1+(39/50:ℝ)^2 := Real.sq_sqrt (by norm_num)
  have hsum : 0<r+r0 := add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _)
    (Real.sqrt_pos.mpr (by norm_num))
  have h1 := eh_root_slope hu
  have h0 := eh_root_slope (u := 1) (by norm_num)
  have hbound : Real.sqrt qCap*(u+1)≤(79/50)*(r+r0) := by
    dsimp [r,r0]
    norm_num at h0
    linarith
  have hm := mul_le_mul_of_nonneg_right hbound (sub_nonneg.mpr hu.1)
  have hid : Real.sqrt qCap*(r-r0)*(r+r0)=Real.sqrt qCap*(u+1)*(u-1) := by
    have he : (r-r0)*(r+r0)=(u+1)*(u-1) := by nlinarith only [hr,hr0]
    nlinarith only [congrArg (fun z : ℝ => Real.sqrt qCap*z) he]
  apply (mul_le_mul_right hsum).mp
  change Real.sqrt qCap*(r-r0)*(r+r0)≤(79/50)*(u-1)*(r+r0)
  rw [hid]
  nlinarith only [hm]

/-- The actual H norm gain is bounded, including its secant multiplier. -/
theorem eh_gain_lower {s : ℝ} (hs : s∈Icc 0 (1/4:ℝ)) :
    ((103/100:ℝ)+1/625)*s≤secantGain qCap (39/50) s := by
  have hmodel := eh_model_gain_lower hs
  have hsec := eh_secant_range hs
  have hnorm := eh_root_difference hsec
  have hformula := secantGain_eq_secant_expression qCap (39/50)
    (cos_pos (eh_short_subset hs))
  have hgain := gain_secant (29/50) (eh_short_subset hs)
  dsimp [K] at hgain
  nlinarith only [hmodel,hnorm,hformula,hgain]

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeESecant

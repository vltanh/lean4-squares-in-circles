module

public import SquaresInCircles.Eight.TableFree.GlobalGASecantDPositiveEndpointBounds

/-!
# The intrinsic equal-angle minimum of the positive D alternative

Uncompiled completion of Section 2 of
`HAND_G3_SECANT_D_SINGLE_ANGLE_COMPARISON.md`. The two support formulas
have matching values at sec s=c. Each smooth penalized branch has the
proved positive derivative reserve on the whole interval. The continuous
switch uses 1-c cos s, so no global continuity of secant is assumed.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.SecantD.PositiveEndpoint
open Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PositiveBT3

abbrev sec : ℝ → ℝ := NegativeELargeA.secant

def correction (c s : ℝ) : ℝ :=
  (sec s-1)/2+(13/12)*Real.tan s-(sortedSupport (sec s) c-sortedSupport 1 c)
def fullCorrection (c s : ℝ) : ℝ :=
  secantGain qCap c s+sortedSupport 1 c-fullSupport 1 c
def diagonalPenalty (c θ s : ℝ) : ℝ :=
  NegativeESecant.gain (GlobalGA.Secondary.diagonal-1/2) s-slope*c*(s-θ)
def fullPenalty (c θ s : ℝ) : ℝ := fullCorrection c s-slope*sec s*(s-θ)
def penalty (c θ s : ℝ) : ℝ := correction c s-slope*max (sec s) c*(s-θ)
def fullPenaltyD (c θ s : ℝ) : ℝ :=
  secantGainDeriv qCap c s-slope*((Real.sin s/Real.cos s^2)*(s-θ)+sec s)

theorem coefficient_domain {c : ℝ} (hc : c∈Icc d cUpper) :
    c∈Icc cLower cUpper := ⟨by dsimp [d,cLower] at *; linarith [hc.1],hc.2⟩

theorem correction_diagonal {c s : ℝ} (hc : c∈Icc d cUpper)
    (hs : s∈Icc 0 frameCap) (hsc : sec s≤c) :
    correction c s=NegativeESecant.gain (GlobalGA.Secondary.diagonal-1/2) s := by
  have h1c : 1≤c := (NegativeELargeA.secant_range hs).1.trans hsc
  rw [correction,sortedSupport_diagonal hsc,sortedSupport_diagonal h1c,
    NegativeESecant.gain_secant _ hs]
  dsimp [sec,NegativeELargeA.secant,diagonalSupport,NegativeESecant.K]
  ring

theorem correction_full {c s : ℝ} (hc : c∈Icc d cUpper)
    (hs : s∈Icc 0 frameCap) (hcs : c≤ sec s) :
    correction c s=fullCorrection c s := by
  have hq : sec s∈Icc 1 qUpper := NegativeELargeA.secant_range hs
  rw [correction,baseline_full hq (coefficient_domain hc) hcs,
    fullCorrection,secantGain_eq_secant_expression qCap c (NegativeESecant.cos_pos hs)]
  dsimp [sec,NegativeELargeA.secant,fullSupport]
  norm_num only [one_pow]
  ring

theorem fullPenalty_hasDerivAt {c θ s : ℝ} (hs : s∈Icc 0 frameCap) :
    HasDerivAt (fullPenalty c θ) (fullPenaltyD c θ s) s := by
  have hfirst := ((secantGain_hasDerivAt qCap c (NegativeESecant.cos_pos hs).ne').add_const
    (sortedSupport 1 c)).sub_const (fullSupport 1 c)
  have hsecond := ((NegativeELargeA.secant_hasDerivAt hs).mul
    ((hasDerivAt_id' s).sub_const θ)).const_mul slope
  convert hfirst.sub hsecond using 1
  · funext x; simp only [fullPenalty,fullCorrection,Pi.sub_apply,Pi.mul_apply,sec]; ring
  · simp only [fullPenaltyD,sec]; ring

theorem fullPenalty_derivative {c θ s : ℝ} (hc : d≤c) (hθ : 0≤θ)
    (hs : s∈Icc 0 frameCap) : reserve<fullPenaltyD c θ s := by
  have hcos := NegativeESecant.cos_pos hs
  have hcos2 : 0<Real.cos s^2 := sq_pos_of_pos hcos
  have hsmall : Real.cos s^2≤1 := by
    nlinarith [Real.sin_sq_add_cos_sq s,sq_nonneg (Real.sin s)]
  have hroot := Real.sqrt_pos.mpr (gainRadicand_pos c s)
  have hid : fullPenaltyD c θ s*Real.cos s^2=H c s+slope*θ*Real.sin s := by
    dsimp [fullPenaltyD,secantGainDeriv,H,sec,NegativeELargeA.secant]
    field_simp [hcos.ne',hroot.ne']
    ring
  have hθsin := mul_nonneg (mul_nonneg (by norm_num [slope] : 0 ≤ slope) hθ)
    (transport_trig hs).2.2.1
  have hreserve := mul_le_mul_of_nonneg_left hsmall (show 0≤reserve by norm_num [reserve])
  have hH := H_lower hc hs
  have hmul : reserve*Real.cos s^2<fullPenaltyD c θ s*Real.cos s^2 := by
    rw [hid]
    nlinarith
  exact lt_of_mul_lt_mul_right hmul hcos2.le

theorem diagonalPenalty_hasDerivAt (c θ : ℝ) {s : ℝ} (hs : s∈Icc 0 frameCap) :
    HasDerivAt (diagonalPenalty c θ)
      (NegativeESecant.gainD (GlobalGA.Secondary.diagonal-1/2) s-slope*c) s := by
  have h := (NegativeESecant.gain_hasDerivAt (GlobalGA.Secondary.diagonal-1/2) hs).sub
    (((hasDerivAt_id' s).sub_const θ).const_mul (slope*c))
  convert h using 1
  · funext x; simp only [diagonalPenalty,Pi.sub_apply]
  · ring

theorem diagonalPenalty_derivative {c s : ℝ} (hc : c≤cUpper)
    (hs : s∈Icc 0 frameCap) :
    reserve<NegativeESecant.gainD (GlobalGA.Secondary.diagonal-1/2) s-slope*c := by
  have hd := NegativeELargeA.diagonal_derivative_lower hs
  have hm := mul_le_mul_of_nonneg_left hc (show 0≤ slope by norm_num [slope])
  dsimp [reserve,slope,cUpper,NegativeELargeA.M] at *
  linarith

theorem switch_identity {c θ s : ℝ} (hc : c∈Icc d cUpper)
    (hs : s∈Icc 0 frameCap) :
    (if 1-c*Real.cos s≤0 then diagonalPenalty c θ s-reserve*s
      else fullPenalty c θ s-reserve*s)=penalty c θ s-reserve*s := by
  have hcos := NegativeESecant.cos_pos hs
  by_cases he : 1-c*Real.cos s≤0
  · have hsc : sec s≤c := (div_le_iff₀ hcos).2 (by linarith)
    simp only [if_pos he,penalty,correction_diagonal hc hs hsc,max_eq_right hsc,
      diagonalPenalty]
  · have hcs : c≤ sec s := (le_div_iff₀ hcos).2 (by linarith)
    simp only [if_neg he,penalty,correction_full hc hs hcs,max_eq_left hcs,
      fullPenalty]

/-- A positive reserve holds across the exact support transition, not
just on either open branch. -/
theorem penalty_growth {c θ x y : ℝ} (hc : c∈Icc d cUpper) (hθ : 0≤θ)
    (hx : x∈Icc 0 frameCap) (hy : y∈Icc 0 frameCap) (hxy : x≤y) :
    reserve*(y-x)≤penalty c θ y-penalty c θ x := by
  have hf : MonotoneOn (fun s => diagonalPenalty c θ s-reserve*s) (Icc 0 frameCap) := by
    apply monoOn_of_hasDeriv_nonneg
    · intro s hs
      exact ((diagonalPenalty_hasDerivAt c θ hs).sub
        ((hasDerivAt_id s).const_mul reserve)).continuousAt.continuousWithinAt
    · intro s hs
      exact (diagonalPenalty_hasDerivAt c θ (Ioo_subset_Icc_self hs)).sub
        ((hasDerivAt_id s).const_mul reserve)
    · intro s hs
      linarith [diagonalPenalty_derivative hc.2 (Ioo_subset_Icc_self hs)]
  have hg : MonotoneOn (fun s => fullPenalty c θ s-reserve*s) (Icc 0 frameCap) := by
    apply monoOn_of_hasDeriv_nonneg
    · intro s hs
      exact ((fullPenalty_hasDerivAt hs).sub
        ((hasDerivAt_id s).const_mul reserve)).continuousAt.continuousWithinAt
    · intro s hs
      exact (fullPenalty_hasDerivAt (Ioo_subset_Icc_self hs)).sub
        ((hasDerivAt_id s).const_mul reserve)
    · intro s hs
      linarith [fullPenalty_derivative hc.1 hθ (Ioo_subset_Icc_self hs)]
  have hm := monotone_continuous_switch (e:=fun s => 1-c*Real.cos s)
    (by fun_prop) hf hg (fun s hs he => by
      have hsc : sec s=c := (div_eq_iff (NegativeESecant.cos_pos hs).ne').2 (by linarith)
      have hcE := correction_diagonal hc hs hsc.le
      have hfE := correction_full hc hs hsc.ge
      dsimp [diagonalPenalty,fullPenalty]
      rw [hsc]
      linarith)
  have hh := hm hx hy hxy
  dsimp only at hh
  rw [switch_identity hc hx,switch_identity hc hy] at hh
  linarith

theorem penalty_strictMono {c θ : ℝ} (hc : c∈Icc d cUpper) (hθ : 0≤θ) :
    StrictMonoOn (penalty c θ) (Icc 0 frameCap) := by
  intro x hx y hy hxy
  have hg := penalty_growth hc hθ hx hy hxy.le
  have hp := mul_pos (show 0<reserve by norm_num [reserve]) (sub_pos.mpr hxy)
  linarith

/-- The positive-D pure alternative is bounded by its actual intrinsic
endpoint s=θ. This is a scalar reduction only. -/
theorem intrinsic_lower {c θ s : ℝ} (hc : c∈Icc d cUpper)
    (hθ : θ∈Icc 0 frameCap) (hs : s∈Icc θ frameCap) :
    correction c θ≤correction c s-slope*max (sec s) c*(s-θ) := by
  have hh := penalty_growth hc hθ.1 hθ ⟨hθ.1.trans hs.1,hs.2⟩ hs.1
  have hp := mul_nonneg (show 0≤reserve by norm_num [reserve]) (sub_nonneg.mpr hs.1)
  simp only [penalty,sub_self,mul_zero,sub_zero] at hh
  linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.SecantD.PositiveEndpoint

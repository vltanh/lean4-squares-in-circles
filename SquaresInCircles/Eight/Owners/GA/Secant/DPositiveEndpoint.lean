module

public import SquaresInCircles.Eight.Frames.Ordinary.PositiveEnvelope
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2NegativeSlopes
public import SquaresInCircles.Eight.Owners.GA.Negative.ELargeADCorrection
public import SquaresInCircles.Eight.Owners.GA.Positive.BT3DEnvelopeGeometry
public import SquaresInCircles.Eight.Owners.GA.Secant.Gain

/-!
# Eight squares: the intrinsic equal-angle minimum of the positive D alternative

The two support formulas
have matching values at sec s=c. Each smooth penalized branch has the
proved positive derivative reserve on the whole interval. The continuous
switch uses 1-c cos s, so no global continuity of secant is assumed.
-/

section
/-!
## One signed D angle with its secant coefficient

The support is the sorted outer-circle support. The positive branch keeps its coefficient
`max q c`; neither the secant coefficient nor the remaining angle of the cycle changes
(`positive_lower`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.SecantD
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PositiveBT3

abbrev slope : ℝ := 109/200
abbrev qUpper : ℝ := 327/250
abbrev cLower : ℝ := 7/10
abbrev cUpper : ℝ := 7/5

def increment (q c t : ℝ) : ℝ :=
  c*(edgeWidth t-1)+sortedSupport q c-
    sortedSupport (q+c*Real.sin t) (c*Real.cos t)

def actualIncrement (q c t : ℝ) (P : SignedPoint) : ℝ :=
  c*(edgeWidth t-1)+sortedSupport q c-
    ((q+c*Real.sin t)*P.a+(c*Real.cos t)*(-P.y))

theorem coefficient_pos {q c : ℝ} (hq : q∈Icc 1 qUpper)
    (hc : c∈Icc cLower cUpper) : 0<q ∧ 0<c ∧ q≤2*c := by
  dsimp [qUpper,cLower,cUpper] at *
  exact ⟨by linarith [hq.1],by linarith [hc.1],by linarith [hq.2,hc.1]⟩

theorem forces_positive {q c t : ℝ} (hq : q∈Icc 1 qUpper)
    (hc : c∈Icc cLower cUpper) (ht : |t|≤frameCap) :
    0<q+c*Real.sin t ∧ 0<c*Real.cos t := by
  have htrig := signed_trig ht
  have hs : -(6443/10000:ℝ)<Real.sin t := neg_lt_of_abs_lt htrig.2
  have hp := coefficient_pos hq hc
  have hm := mul_lt_mul_of_pos_left hs hp.2.1
  have hu := mul_le_mul_of_nonneg_right hc.2 (by norm_num : (0:ℝ)≤6443/10000)
  dsimp [cUpper] at hu
  exact ⟨by linarith [hq.1],mul_pos hp.2.1 (by linarith [htrig.1])⟩

theorem baseline_no_axis {q c : ℝ} (hq : q∈Icc 1 qUpper)
    (hc : c∈Icc cLower cUpper) : q/2<(axial+1/2)*c := by
  have hp := coefficient_pos hq hc
  have hm := mul_le_mul_of_nonneg_left hc.1
    (show 0≤axial+1/2 by linarith [axial_bounds.1])
  dsimp [qUpper,cLower] at *
  nlinarith [axial_bounds.1,hq.2]

theorem baseline_clipped {q c : ℝ} (hq : q∈Icc 1 qUpper)
    (hc : c∈Icc cLower cUpper) : sortedSupport q c=clippedSupport q c := by
  have hn := not_le.mpr (baseline_no_axis hq hc)
  simp only [sortedSupport,clippedSupport,hn,↓reduceIte]

theorem baseline_full {q c : ℝ} (hq : q∈Icc 1 qUpper)
    (hc : c∈Icc cLower cUpper) (hcq : c≤q) :
    sortedSupport q c=fullSupport q c := by
  have hp := coefficient_pos hq hc
  exact sortedSupport_full_of_between hp.1 hp.2.1 hcq (baseline_no_axis hq hc).le

theorem force_norm (q c t : ℝ) :
    Real.sqrt ((q+c*Real.sin t)^2+(c*Real.cos t)^2)=pairNorm c q t := by
  unfold pairNorm
  congr 1
  linear_combination c^2*Real.sin_sq_add_cos_sq t

theorem full_increment_positive {q c t : ℝ} (ht : t∈Icc 0 frameCap) :
    c*(edgeWidth t-1)+fullSupport q c-
      fullSupport (q+c*Real.sin t) (c*Real.cos t)=U R c q t := by
  rw [edgeWidth_positive_formula ht]
  have hzero : Real.sqrt (q^2+c^2)=pairNorm c q 0 := by
    simp [pairNorm,add_comm]
  dsimp [fullSupport,U,PositiveAngularEnvelope.phi]
  rw [force_norm,hzero]
  ring

theorem positive_below {q c t : ℝ} (hq : q∈Icc 1 qUpper)
    (hc : c∈Icc cLower cUpper) (ht : t∈Icc 0 frameCap) (hcq : c≤q) :
    -slope*q*t≤ increment q c t := by
  have hp := coefficient_pos hq hc
  have hU := OrdinaryPositiveEnvelope.U_lower (Real.sqrt_nonneg qCap)
    radius_sq.le hp.2.1 hcq hp.2.2 ht
  have hs := sortedSupport_le_full (f:=q+c*Real.sin t) (g:=c*Real.cos t)
  have he := full_increment_positive (q:=q) (c:=c) ht
  dsimp [increment,slope]
  rw [baseline_full hq hc hcq]
  linarith

/-- The support point selected by the final force has primary coordinate at least the diagonal
coordinate; this is the integrated form of the nonpositive derivative in `q/c`. -/
theorem positive_above {q c t : ℝ} (hq : q∈Icc 1 qUpper)
    (hc : c∈Icc cLower cUpper) (ht : t∈Icc 0 frameCap) (hqc : q≤c) :
    -slope*c*t≤ increment q c t := by
  have hp := coefficient_pos hq hc
  have hf := forces_positive hq hc (by rw [abs_of_nonneg ht.1]; exact ht.2)
  obtain ⟨a,b,ha,hb,hab,hcircle,hsupport⟩ := sortedSupport_attained hf.1 hf.2
  have hda : GlobalGA.Secondary.diagonal≤a := by
    nlinarith [diagonal_circle,diagonal_bounds.1]
  have hbase := raw_full_support (a:=a) (b:=b) (f:=1+Real.sin t)
    (g:=Real.cos t) hcircle.le
  have hm := mul_le_mul_of_nonneg_left hbase hp.2.1.le
  have hd := mul_le_mul_of_nonpos_left hda (sub_nonpos.mpr hqc)
  have hnorm : (2:ℝ)*GlobalGA.Secondary.diagonal=fullSupport 1 1 := by
    have hh := full_at_diagonal (f:=1) (g:=1) rfl (by norm_num)
    simp only [diagonalSupport] at hh
    rw [hh]; ring
  have he := full_increment_positive (q:=1) (c:=1) ht
  norm_num only [one_mul] at he
  have hU := OrdinaryPositiveEnvelope.U_lower (p:=1) (q:=1)
    (Real.sqrt_nonneg qCap) radius_sq.le (by norm_num) le_rfl (by norm_num) ht
  have hUc := mul_le_mul_of_nonneg_left hU hp.2.1.le
  dsimp [increment,slope]
  rw [sortedSupport_diagonal hqc,hsupport]
  dsimp [diagonalSupport]
  rw [←hnorm] at he
  nlinarith

theorem positive_lower {q c t : ℝ} (hq : q∈Icc 1 qUpper)
    (hc : c∈Icc cLower cUpper) (ht : t∈Icc 0 frameCap) :
    -slope*max q c*t≤ increment q c t := by
  by_cases hqc : q≤c
  · simpa [max_eq_right hqc] using positive_above hq hc ht hqc
  · have hcq := (lt_of_not_ge hqc).le
    simpa [max_eq_left hcq] using positive_below hq hc ht hcq

end SquaresInCircles.Eight.GlobalGA.SecantD
end
end
end

section
/-!
## The exact far-end reserve for the secant-D positive alternative

The complete angle interval is controlled by monotonicity
of H at c=.862. The sole rational endpoint is the stated positive-square
certificate, using C10/C12 and S11/S9 in their required directions.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.SecantD.PositiveEndpoint
open Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open NegativeAPositiveTD.NegativeSlope

abbrev d : ℝ := 431/500
abbrev reserve : ℝ := 33/50000

def H (c s : ℝ) : ℝ :=
  13/12+Real.sin s-R*Real.sin s/Real.sqrt (gainRadicand c s)-
    slope*(Real.cos s+s*Real.sin s)

def Hd (c s : ℝ) : ℝ :=
  Real.cos s*(1-slope*s-R*(1+c^2)/(Real.sqrt (gainRadicand c s))^3)

theorem H_hasDerivAt (c s : ℝ) : HasDerivAt (H c) (Hd c s) s := by
  have hg := gainRadicand_pos c s
  have hroot : 0<Real.sqrt (gainRadicand c s) := Real.sqrt_pos.mpr hg
  have hroot2 := Real.sq_sqrt hg.le
  have hrootD := (gainRadicand_hasDerivAt c s).sqrt hg.ne'
  have hfirst := (Real.hasDerivAt_sin s).const_add (13/12:ℝ)
  have hsecond := ((Real.hasDerivAt_sin s).const_mul R).div hrootD hroot.ne'
  have hthird := ((Real.hasDerivAt_cos s).add
    ((hasDerivAt_id s).mul (Real.hasDerivAt_sin s))).const_mul slope
  convert (hfirst.sub hsecond).sub hthird using 1
  · rfl
  · set r := Real.sqrt (gainRadicand c s) with hr
    have hr0 : r≠0 := hroot.ne'
    have hg' : r^2=1+c^2*Real.cos s^2 := hroot2
    have e1 : (R*Real.cos s*r-R*Real.sin s*(-2*c^2*Real.cos s*Real.sin s/(2*r)))/r^2=
        R*Real.cos s*(r^2+c^2*Real.sin s^2)/r^3 := by
      field_simp
      ring
    have e2 : r^2+c^2*Real.sin s^2=1+c^2 := by
      rw [hg']; linear_combination c^2*Real.sin_sq_add_cos_sq s
    rw [e1,e2]
    simp only [Hd,id]
    field_simp
    ring

theorem H_monotone_coefficient {c s : ℝ} (hc : d≤c)
    (hs : s∈Icc 0 frameCap) : H d s≤H c s := by
  have hr₀ := Real.sqrt_pos.mpr (gainRadicand_pos d s)
  have hr₁ := Real.sqrt_pos.mpr (gainRadicand_pos c s)
  have hrad : gainRadicand d s≤gainRadicand c s := by
    have hc0 : 0≤c := by dsimp [d] at *; linarith
    have hsq : d^2≤c^2 := pow_le_pow_left₀ (by norm_num [d]) hc 2
    exact by dsimp [gainRadicand]; nlinarith [mul_nonneg (sub_nonneg.mpr hsq) (sq_nonneg (Real.cos s))]
  have hfrac := div_le_div_of_nonneg_left
    (mul_nonneg (Real.sqrt_nonneg qCap) (transport_trig hs).2.2.1)
    hr₀ (Real.sqrt_le_sqrt hrad)
  dsimp [H]
  linarith

theorem H_antitone : AntitoneOn (H d) (Icc 0 frameCap) := by
  apply antiOn_of_hasDeriv_nonpos
    (fun s hs => (H_hasDerivAt d s).continuousAt.continuousWithinAt)
    (fun s hs => H_hasDerivAt d s)
  intro s hs
  have ht := transport_trig (Ioo_subset_Icc_self hs)
  have hroot := Real.sqrt_pos.mpr (gainRadicand_pos d s)
  have hroot2 := Real.sq_sqrt (gainRadicand_pos d s).le
  have hupper : gainRadicand d s≤1+d^2 := by
    dsimp [gainRadicand]
    nlinarith [Real.sin_sq_add_cos_sq s,sq_nonneg (Real.sin s)]
  have hU := Real.sqrt_pos.mpr (show 0<1+d^2 by positivity)
  have hU2 := Real.sq_sqrt (show 0≤1+d^2 by positivity)
  have hUR : Real.sqrt (1+d^2)<R :=
    Real.sqrt_lt_sqrt (by positivity) (by norm_num [d,qCap])
  have hcube : (Real.sqrt (gainRadicand d s))^3< R*(1+d^2) := by
    have hmul := mul_le_mul hupper (Real.sqrt_le_sqrt hupper) hroot.le
      (show 0≤1+d^2 by positivity)
    have hstrict := mul_lt_mul_of_pos_left hUR (show 0<1+d^2 by positivity)
    calc
      (Real.sqrt (gainRadicand d s))^3=
          gainRadicand d s*Real.sqrt (gainRadicand d s) := by rw [pow_succ,hroot2]
      _≤(1+d^2)*Real.sqrt (1+d^2) := hmul
      _<R*(1+d^2) := by simpa [mul_comm] using hstrict
  have hratio : 1<R*(1+d^2)/(Real.sqrt (gainRadicand d s))^3 :=
    (one_lt_div (pow_pos hroot 3)).2 hcube
  have hslope : 0 ≤ slope*s := mul_nonneg (by norm_num [slope]) hs.1.le
  have hX : 1-slope*s-R*(1+d^2)/(Real.sqrt (gainRadicand d s))^3≤0 := by
    generalize R*(1+d^2)/(Real.sqrt (gainRadicand d s))^3=X at hratio ⊢
    generalize slope*s=Y at hslope ⊢
    linarith
  simp only [Hd]
  exact mul_nonpos_of_nonneg_of_nonpos (by linarith [ht.1]) hX

namespace Certificate

def A : ℚ := 13/12-(109/200)*cosHi (7/10)+
  (1-(109/200)*(7/10))*sinLo (7/10)
def D : ℚ := 1+(431/500)^2*(cosLo (7/10))^2

theorem cap_reserve : 1<A ∧ (41/5000000:ℚ)<
    (A-33/50000)^2*D-(9789/2500)*(sinHi (7/10))^2 := by
  norm_num [A,D,sinLo,sinHi,cosLo,cosHi,PositiveTD.Certificate.S11,
    PositiveTD.Certificate.S9,PositiveTD.Certificate.S5,PositiveTD.Certificate.C12,
    PositiveTD.Certificate.C10,PositiveTD.Certificate.C4]

end Certificate

theorem H_cap : reserve<H d frameCap := by
  obtain ⟨hs,hS,hc,hC⟩ := rational_taylor (t:=7/10) (by norm_num [frameCap])
  have h7 : ((7/10:ℚ):ℝ)=frameCap := by norm_num [frameCap]
  rw [h7] at hs hS hc hC
  have hA : (1:ℝ)<(Certificate.A:ℝ) := by exact_mod_cast Certificate.cap_reserve.1
  have hcert : (41/5000000:ℝ)<
      ((Certificate.A:ℝ)-reserve)^2*(Certificate.D:ℝ)-qCap*(sinHi (7/10):ℝ)^2 := by
    have h := (Rat.cast_lt (K:=ℝ)).mpr Certificate.cap_reserve.2
    push_cast at h
    simp only [reserve,qCap]
    linarith
  have hCL : (0:ℝ)≤(cosLo (7/10):ℝ) := by
    norm_num [cosLo,PositiveTD.Certificate.C10,PositiveTD.Certificate.C4]
  have hSH : (0:ℝ)≤(sinHi (7/10):ℝ) := by
    norm_num [sinHi,PositiveTD.Certificate.S9,PositiveTD.Certificate.S5]
  have hD : (0:ℝ)<(Certificate.D:ℝ) := by
    norm_num [Certificate.D,cosLo,PositiveTD.Certificate.C10,PositiveTD.Certificate.C4]
  have hroot := Real.sqrt_pos.mpr hD
  have hroot2 := Real.sq_sqrt hD.le
  have hrad : (Certificate.D:ℝ)≤gainRadicand d frameCap := by
    have hsquare := pow_le_pow_left₀ hCL hc 2
    have hD' : (Certificate.D:ℝ)=1+(431/500)^2*(cosLo (7/10):ℝ)^2 := by
      simp only [Certificate.D]; push_cast; ring
    rw [hD']
    simp only [gainRadicand,d]
    nlinarith
  have hnum : (R*(sinHi (7/10):ℝ))^2=qCap*(sinHi (7/10):ℝ)^2 := by
    rw [mul_pow,radius_sq]
  have htarget : 0≤((Certificate.A:ℝ)-reserve)*Real.sqrt (Certificate.D:ℝ) := by
    exact mul_nonneg (by simp only [reserve]; linarith) hroot.le
  have hcross : R*(sinHi (7/10):ℝ)<
      ((Certificate.A:ℝ)-reserve)*Real.sqrt (Certificate.D:ℝ) := by
    have hsq : (((Certificate.A:ℝ)-reserve)*Real.sqrt (Certificate.D:ℝ))^2=
        ((Certificate.A:ℝ)-reserve)^2*(Certificate.D:ℝ) := by rw [mul_pow,hroot2]
    have hlt : (R*(sinHi (7/10):ℝ))^2<
        (((Certificate.A:ℝ)-reserve)*Real.sqrt (Certificate.D:ℝ))^2 := by
      rw [hnum,hsq]; linarith
    exact lt_of_pow_lt_pow_left₀ 2 htarget hlt
  have hfrac : R*(sinHi (7/10):ℝ)/Real.sqrt (Certificate.D:ℝ)<
      (Certificate.A:ℝ)-reserve := (div_lt_iff₀ hroot).2 hcross
  have hrootActual := Real.sqrt_pos.mpr (gainRadicand_pos d frameCap)
  have hfracActual : R*Real.sin frameCap/Real.sqrt (gainRadicand d frameCap)≤
      R*(sinHi (7/10):ℝ)/Real.sqrt (Certificate.D:ℝ) := by
    have h₁ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hS (Real.sqrt_nonneg qCap)) hrootActual.le
    have h₂ := div_le_div_of_nonneg_left (mul_nonneg (Real.sqrt_nonneg qCap) hSH)
      hroot (Real.sqrt_le_sqrt hrad)
    exact h₁.trans h₂
  have hbase : (Certificate.A:ℝ)≤13/12-slope*Real.cos frameCap+
      (1-slope*frameCap)*Real.sin frameCap := by
    have h₁ := mul_le_mul_of_nonneg_left hC (show 0 ≤ slope by norm_num [slope])
    have h₂ := mul_le_mul_of_nonneg_left hs
      (show 0≤1-slope*frameCap by norm_num [slope,frameCap])
    have hA' : (Certificate.A:ℝ)=13/12-(109/200)*(cosHi (7/10):ℝ)+
        (1-(109/200)*(7/10))*(sinLo (7/10):ℝ) := by
      simp only [Certificate.A]; push_cast; ring
    rw [hA']
    simp only [slope,frameCap] at h₁ h₂ ⊢
    linarith
  have hH : H d frameCap=13/12-slope*Real.cos frameCap+(1-slope*frameCap)*Real.sin frameCap-
      R*Real.sin frameCap/Real.sqrt (gainRadicand d frameCap) := by
    simp only [H]; ring
  rw [hH]
  linarith

theorem H_lower {c s : ℝ} (hc : d≤c) (hs : s∈Icc 0 frameCap) :
    reserve<H c s := by
  have hm := H_antitone hs (show frameCap∈Icc 0 frameCap by norm_num [frameCap]) hs.2
  exact H_cap.trans_le (hm.trans (H_monotone_coefficient hc hs))

end SquaresInCircles.Eight.GlobalGA.SecantD.PositiveEndpoint
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.SecantD.PositiveEndpoint
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

theorem correction_diagonal {c s : ℝ} (_hc : c∈Icc d cUpper)
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
    simp only [ite_eq_left he,penalty,correction_diagonal hc hs hsc,max_eq_right hsc,
      diagonalPenalty]
  · have hcs : c≤ sec s := (le_div_iff₀ hcos).2 (by linarith)
    simp only [ite_eq_right he,penalty,correction_full hc hs hcs,max_eq_left hcs,
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

/-- The positive-D pure alternative is bounded by its actual intrinsic
endpoint s=θ. This is a scalar reduction only. -/
theorem intrinsic_lower {c θ s : ℝ} (hc : c∈Icc d cUpper)
    (hθ : θ∈Icc 0 frameCap) (hs : s∈Icc θ frameCap) :
    correction c θ≤correction c s-slope*max (sec s) c*(s-θ) := by
  have hh := penalty_growth hc hθ.1 hθ ⟨hθ.1.trans hs.1,hs.2⟩ hs.1
  have hp := mul_nonneg (show 0≤reserve by norm_num [reserve]) (sub_nonneg.mpr hs.1)
  simp only [penalty,sub_self,mul_zero,sub_zero] at hh
  linarith

end SquaresInCircles.Eight.GlobalGA.SecantD.PositiveEndpoint
end
end
end

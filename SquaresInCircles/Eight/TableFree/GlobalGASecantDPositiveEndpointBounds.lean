module

public import SquaresInCircles.Eight.TableFree.GlobalGASecantDSingleAngle
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeELargeADCorrection
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeATD2NegativeSlopes

/-!
# The exact far-end reserve for the secant-D positive alternative

Uncompiled transcription of (16)--(19) in the single-angle secant-D
companion. The complete angle interval is controlled by monotonicity
of H at c=.862. The sole rational endpoint is the stated positive-square
certificate, using C10/C12 and S11/S9 in their required directions.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.SecantD.PositiveEndpoint
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
  · dsimp [Hd]
    field_simp [hroot.ne']
    dsimp [gainRadicand] at hroot2
    nlinarith [Real.sin_sq_add_cos_sq s,
      congrArg (fun v : ℝ => R*c^2*Real.cos s*v) (Real.sin_sq_add_cos_sq s),
      congrArg (fun v : ℝ => Real.cos s*v) hroot2]

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
  have hUR : Real.sqrt (1+d^2)<R := by
    have hR := radius_sq
    norm_num [d,qCap] at hR hU2
    nlinarith [Real.sqrt_nonneg qCap]
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
  have hslope : 0≤slope*s := mul_nonneg (by norm_num [slope]) hs.1.le
  dsimp [Hd]
  exact mul_nonpos_of_nonneg_of_nonpos (by linarith [ht.1]) (by linarith)

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
  have hh : (7/10:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  obtain ⟨hs,hS,hc,hC⟩ := rational_taylor (t:=7/10) hh
  have hA : (1:ℝ)<(Certificate.A:ℝ) := by exact_mod_cast Certificate.cap_reserve.1
  have hcert : (41/5000000:ℝ)<
      ((Certificate.A:ℝ)-reserve)^2*(Certificate.D:ℝ)-qCap*(sinHi (7/10):ℝ)^2 := by
    exact_mod_cast Certificate.cap_reserve.2
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
    dsimp [Certificate.D,gainRadicand,d,frameCap]
    push_cast
    nlinarith
  have hnum : (R*(sinHi (7/10):ℝ))^2=qCap*(sinHi (7/10):ℝ)^2 := by
    rw [mul_pow,radius_sq]
  have htarget : 0≤((Certificate.A:ℝ)-reserve)*Real.sqrt (Certificate.D:ℝ) := by
    exact mul_nonneg (by dsimp [reserve]; linarith) hroot.le
  have hcross : R*(sinHi (7/10):ℝ)<
      ((Certificate.A:ℝ)-reserve)*Real.sqrt (Certificate.D:ℝ) := by
    have hsq : (((Certificate.A:ℝ)-reserve)*Real.sqrt (Certificate.D:ℝ))^2=
        ((Certificate.A:ℝ)-reserve)^2*(Certificate.D:ℝ) := by rw [mul_pow,hroot2]
    nlinarith [mul_nonneg (Real.sqrt_nonneg qCap) hSH]
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
    have h₁ := mul_le_mul_of_nonneg_left hC (show 0≤slope by norm_num [slope])
    have h₂ := mul_le_mul_of_nonneg_left hs
      (show 0≤1-slope*frameCap by norm_num [slope,frameCap])
    dsimp [Certificate.A,slope,frameCap]
    push_cast
    linarith
  dsimp [H]
  nlinarith

theorem H_lower {c s : ℝ} (hc : d≤c) (hs : s∈Icc 0 frameCap) :
    reserve<H c s := by
  have hm := H_antitone hs (show frameCap∈Icc 0 frameCap by norm_num [frameCap]) hs.2
  exact H_cap.trans_le (hm.trans (H_monotone_coefficient hc hs))

end SquaresInCircles.Eight.TableFree.GlobalGA.SecantD.PositiveEndpoint

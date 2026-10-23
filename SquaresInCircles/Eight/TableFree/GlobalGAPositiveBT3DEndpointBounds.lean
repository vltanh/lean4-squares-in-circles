module

public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveBT3DEndpointPolynomial
public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveBT3SortedSupport

/-!
# The radical and tangent-zero bounds at the sorted-D endpoint

Uncompiled transcription of (3), (9), and (10) of the independent
endpoint note. The change at n=3/8 is justified by the actual force
ratio and its derivative. All radical bounds follow from positive
squaring of the displayed rational constants.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.PositiveBT3.DEndpoint
open Candidate Secondary Polynomial PositiveAngularEnvelope OrdinaryAngleConcavity PairNormCalculus
open PositiveTD.Certificate (S9 S11 C10 C12 taylor_bounds)

theorem coefficient_domain (e : End) : (coefficient e:ℝ)∈Icc 1 Cmax := by
  cases e <;> norm_num [coefficient,Cmax]

theorem radical_bounds : (cLower:ℝ)<diagonal ∧ axial<(aUpper:ℝ) ∧
    R*pairNorm K 1 0<(Tzero:ℝ) := by
  have hd := diagonal_circle
  have ha := axial_circle
  have hdb := diagonal_bounds
  have hab := axial_bounds
  have hN0 : 0≤pairNorm K 1 0 := Real.sqrt_nonneg _
  have hN2 : (pairNorm K 1 0)^2=K^2+1 := by
    rw [pairNorm_zero]
    exact Real.sq_sqrt (by positivity)
  have hR : 0≤R := Real.sqrt_nonneg qCap
  have hprod : (R*pairNorm K 1 0)^2=qCap*(K^2+1) := by
    rw [mul_pow,radius_sq,hN2]
  norm_num [qCap,K,cLower,aUpper,Tzero] at hd ha hprod ⊢
  exact ⟨by nlinarith,by nlinarith,by nlinarith [mul_nonneg hR hN0]⟩

theorem sine9_hasDerivAt (x : ℝ) : HasDerivAt Arithmetic.sin9 (Arithmetic.cos8 x) x := by
  have hd : Differentiable ℝ Arithmetic.sin9 := by dsimp [Arithmetic.sin9,Arithmetic.sin7]; fun_prop
  convert (hd x).hasDerivAt using 1
  simp (disch := fun_prop) [Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos8]
  ring

theorem sine9_range {x : ℝ} (hx : x∈Icc 0 frameCap) :
    0≤aeval x S9 ∧ aeval x S9<(129/200:ℝ) := by
  have hm : MonotoneOn Arithmetic.sin9 (Icc (0:ℝ) frameCap) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun x _ => (sine9_hasDerivAt x).continuousAt.continuousWithinAt)
      (fun x _ => sine9_hasDerivAt x)
    intro x hx
    have hh := Arithmetic.cos_le_cos8 hx.1.le
    have hc := (transport_trig (Ioo_subset_Icc_self hx)).1
    linarith
  have h0 := hm (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hx hx.1
  have h1 := hm hx (show frameCap∈Icc 0 frameCap by norm_num [frameCap]) hx.2
  have he : Arithmetic.sin9 frameCap<(129/200:ℝ) := by
    norm_num [Arithmetic.sin9,Arithmetic.sin7,frameCap]
  simp only [PositiveTD.Certificate.S9_eval]
  exact ⟨by simpa [Arithmetic.sin9,Arithmetic.sin7] using h0,h1.trans_lt he⟩

theorem norm_polynomial_bounds (e : End) {n : ℝ} (hn : n∈Icc 0 frameCap) :
    0≤aeval n (P e) ∧ (29/50:ℝ)<aeval n H ∧
    pairNorm 1 (coefficient e:ℝ) (frameCap-n)≤Real.sqrt (aeval n (P e)) ∧
    Real.sqrt (aeval n H)≤pairNorm K 1 (-n) := by
  have hother : frameCap-n∈Icc 0 frameCap := ⟨by linarith [hn.2],by linarith [hn.1]⟩
  have hs := sine9_range hn
  have hso := sine9_range hother
  have hta := (taylor_bounds hother).2.2.1
  have htn := (taylor_bounds hn).2.2.1
  have hc := coefficient_domain e
  have hP : aeval n (P e)=1+(coefficient e:ℝ)^2+
      2*(coefficient e:ℝ)*aeval (frameCap-n) S9 := by
    simp [P,aeval_comp,h,frameCap]
  have hH : aeval n H=1+K^2-2*K*aeval n S9 := by simp [H,kstar,K]
  have hP0 : 0≤aeval n (P e) := by rw [hP]; positivity
  have hH0 : (29/50:ℝ)<aeval n H := by
    rw [hH]
    norm_num [K] at ⊢
    nlinarith [hs.2]
  refine ⟨hP0,hH0,?_,?_⟩
  · apply Real.sqrt_le_sqrt
    rw [hP]
    have hh := mul_le_mul_of_nonneg_left hta
      (show 0≤2*(coefficient e:ℝ) by linarith [hc.1])
    dsimp [pairNorm]
    nlinarith
  · apply Real.sqrt_le_sqrt
    rw [hH]
    simp only [pairNorm,Real.sin_neg]
    have hh := mul_le_mul_of_nonneg_left htn (by norm_num [K] : (0:ℝ)≤2*K)
    nlinarith

def axisRatio (n : ℝ) : ℝ := forceB 1 frameCap (-n)/forceA 1 frameCap (-n)

theorem axisRatio_hasDerivAt {n : ℝ} (hn : n∈Icc 0 frameCap) :
    HasDerivAt axisRatio ((-1+Real.sin (n-frameCap))/(forceA 1 frameCap (-n))^2) n := by
  have hp := force_positive (c:=1) (by norm_num [Cmax])
    (by norm_num [frameCap]) (by rw [abs_neg,abs_of_nonneg hn.1]; exact hn.2)
  have hden : forceA 1 frameCap (-n)≠0 := hp.1.ne'
  have hF : HasDerivAt (fun n => forceA 1 frameCap (-n)) (-Real.sin n) n := by
    simpa [forceA] using (Real.hasDerivAt_cos n).const_add (Real.sin frameCap)
  have hG : HasDerivAt (fun n => forceB 1 frameCap (-n)) (-Real.cos n) n := by
    simpa [forceB] using (Real.hasDerivAt_sin n).const_sub (Real.cos frameCap)
  convert hG.div hF hden using 1
  · rfl
  · dsimp [forceA,forceB]
    simp only [Real.cos_neg,Real.sin_neg,one_mul,Real.sin_sub]
    field_simp [hden]
    nlinarith [Real.sin_sq_add_cos_sq n]

theorem axisRatio_antitone : AntitoneOn axisRatio (Icc (0:ℝ) frameCap) := by
  apply antiOn_of_hasDeriv_nonpos
    (fun n hn => (axisRatio_hasDerivAt hn).continuousAt.continuousWithinAt)
    (fun n hn => axisRatio_hasDerivAt (Ioo_subset_Icc_self hn))
  intro n hn
  have hs : Real.sin (n-frameCap)≤0 := by
    have hh := (transport_trig
      (show frameCap-n∈Icc 0 frameCap from ⟨by linarith [hn.2],by linarith [hn.1]⟩)).2.2.1
    rw [show n-frameCap=-(frameCap-n) by ring,Real.sin_neg]
    linarith
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem axis_transition_reserve :
    (121/5000:ℚ)<(C10.eval cut+S11.eval h)/2-
      (aUpper+1/2)*(C12.eval h-S11.eval cut) := by decide

theorem axis_at_cut :
    (axial+1/2)*forceB 1 frameCap (-(3/8))<forceA 1 frameCap (-(3/8))/2 := by
  have hh := taylor_bounds (show frameCap∈Icc 0 frameCap by norm_num [frameCap])
  have hb := taylor_bounds (show (3/8:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
  have hp := force_positive (c:=1) (by norm_num [Cmax])
    (by norm_num [frameCap]) (by norm_num [frameCap] : |-(3/8:ℝ)|≤frameCap)
  have hflow : ((C10.eval cut+S11.eval h:ℚ):ℝ)≤forceA 1 frameCap (-(3/8)) := by
    rw [Rat.cast_add,← rational_aeval,← rational_aeval]
    norm_num [cut,h,frameCap,forceA]
    linarith [hb.2.2.2.2.1,hh.2.1]
  have hghi : forceB 1 frameCap (-(3/8))≤((C12.eval h-S11.eval cut:ℚ):ℝ) := by
    rw [Rat.cast_sub,← rational_aeval,← rational_aeval]
    norm_num [cut,h,frameCap,forceB]
    linarith [hh.2.2.2.2.2,hb.2.1]
  have hfirst := mul_le_mul_of_nonneg_right radical_bounds.2.1.le hp.2.le
  have hsecond := mul_le_mul_of_nonneg_left hghi
    (show 0≤(aUpper:ℝ)+1/2 by norm_num [aUpper])
  have hr : (121/5000:ℝ)<((C10.eval cut+S11.eval h:ℚ):ℝ)/2-
      ((aUpper:ℝ)+1/2)*((C12.eval h-S11.eval cut:ℚ):ℝ) := by
    exact_mod_cast axis_transition_reserve
  nlinarith

theorem axis_force {n : ℝ} (hn : n∈Icc (3/8:ℝ) frameCap) :
    (axial+1/2)*forceB 1 frameCap (-n)≤forceA 1 frameCap (-n)/2 := by
  have hn0 : n∈Icc 0 frameCap := ⟨by linarith [hn.1],hn.2⟩
  have hb : (3/8:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hp := force_positive (c:=1) (by norm_num [Cmax])
    (by norm_num [frameCap]) (by rw [abs_neg,abs_of_nonneg hn0.1]; exact hn0.2)
  have hpb := force_positive (c:=1) (by norm_num [Cmax])
    (by norm_num [frameCap]) (by norm_num [frameCap] : |-(3/8:ℝ)|≤frameCap)
  have hm := axisRatio_antitone hb hn0 hn.1
  have hA : 0<axial+1/2 := by linarith [axial_bounds.1]
  have hscaled := mul_le_mul_of_nonneg_left hm hA.le
  have hcut : (axial+1/2)*axisRatio (3/8)<1/2 := by
    dsimp [axisRatio]
    rw [← mul_div_assoc,div_lt_iff₀ hpb.1]
    linarith [axis_at_cut]
  have hbound : (axial+1/2)*axisRatio n≤1/2 := by linarith
  dsimp [axisRatio] at hbound
  rw [← mul_div_assoc,div_le_iff₀ hp.1] at hbound
  linarith

theorem axis_support {n : ℝ} (hn : n∈Icc (3/8:ℝ) frameCap) :
    sortedSupport (forceA 1 frameCap (-n)) (forceB 1 frameCap (-n))=
      axial*forceA 1 frameCap (-n) := by
  have hn0 : n∈Icc 0 frameCap := ⟨by linarith [hn.1],hn.2⟩
  have hp := force_positive (c:=1) (by norm_num [Cmax])
    (by norm_num [frameCap]) (by rw [abs_neg,abs_of_nonneg hn0.1]; exact hn0.2)
  simpa only [mul_comm] using sortedSupport_axis hp.2 (axis_force hn)

end SquaresInCircles.Eight.TableFree.GlobalGA.PositiveBT3.DEndpoint

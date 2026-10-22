module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDETD2OrdinarySlopes
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeATD2SecantCoordinate
public import SquaresInCircles.Eight.TableFree.GlobalGASecantGain

/-!
# The actual right endpoint derivative of each high negative-DE pure block

Uncompiled transcription of the two reciprocal-norm certificates in
Section 10.  The H and G numerator polynomials are transferred to their
actual circle norms before the B comparison.  The resulting secant
coordinate derivative is strictly negative at the original total angle.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveTD.HighDerivative
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PairNormCalculus
open OrdinaryNegativeSlope Polynomial
open NegativeAPositiveTD (SecantBaseline SecantCoordinate)
open PositiveTD.Certificate (C10 C12 S9 S11 taylor_bounds)

theorem reciprocal_minorant {n r P : ℝ} (hn : 0<n) (hr : 0<r)
    (hP : n^2≤P) : 2*r/(P+r^2)≤1/n := by
  have hden : 0<P+r^2 := by nlinarith [sq_pos_of_pos hn,sq_nonneg r]
  apply (div_le_div_iff₀ hden hn).2
  nlinarith [sq_nonneg (n-r)]

/-- The sine in the second reciprocal term may be enlarged independently
of the upper Taylor sine in the subtracted numerator. -/
theorem derivative_transfer {n h r d P Q f u v y s Y a b : ℝ}
    (hn : 0<n) (hh : 0<h) (hr : 0<r) (hd : 0<d)
    (hP : n^2≤P) (hQ : h^2≤Q) (hf : 0≤f)
    (hu : 0≤u) (huv : u≤v) (hy : 0≤y) (hys : y≤s) (hsY : s≤Y)
    (ha : 0≤a) (hab : a≤b)
    (hpoly : 0<2*a*r*f*u*(Q+d^2)+2*a*d*y*(P+r^2)-
      (13/12+Y)*(P+r^2)*(Q+d^2)) :
    13/12+s<b*f*v/n+b*s/h := by
  have hA : 0<P+r^2 := by nlinarith [sq_pos_of_pos hn,sq_nonneg r]
  have hD : 0<Q+d^2 := by nlinarith [sq_pos_of_pos hh,sq_nonneg d]
  have hraw : 13/12+Y<a*f*u*(2*r/(P+r^2))+a*y*(2*d/(Q+d^2)) := by
    have he : a*f*u*(2*r/(P+r^2))+a*y*(2*d/(Q+d^2))=
        (2*a*r*f*u*(Q+d^2)+2*a*d*y*(P+r^2))/((P+r^2)*(Q+d^2)) := by
      field_simp [hA.ne',hD.ne']
      ring
    rw [he]
    apply (lt_div_iff₀ (mul_pos hA hD)).2
    nlinarith only [hpoly]
  have hrec₁ := reciprocal_minorant hn hr hP
  have hrec₂ := reciprocal_minorant hh hd hQ
  have hb : 0≤b := ha.trans hab
  have hv : 0≤v := hu.trans huv
  have hs : 0≤s := hy.trans hys
  have hcoef₁ : a*f*u≤b*f*v :=
    mul_le_mul (mul_le_mul_of_nonneg_right hab hf) huv hu (mul_nonneg hb hf)
  have hcoef₂ : a*y≤b*s := mul_le_mul hab hys hy hb
  have h₁ := mul_le_mul hcoef₁ hrec₁ (div_nonneg (by linarith) hA.le)
    (mul_nonneg (mul_nonneg hb hf) hv)
  have h₂ := mul_le_mul hcoef₂ hrec₂ (div_nonneg (by linarith) hD.le)
    (mul_nonneg hb hs)
  have he₁ : b*f*v*(1/n)=b*f*v/n := by ring
  have he₂ : b*s*(1/h)=b*s/h := by ring
  rw [he₁] at h₁
  rw [he₂] at h₂
  linarith

theorem zero_slope (p q : ℝ) : Vd R p q 0=R*(p*q)/pairNorm p q 0 := by
  simp [Vd,mixedNDerivative,normD1,pairProduct]
  ring

theorem H_G_endpoint (atH : Bool) {θ : ℝ}
    (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    secantGainDeriv qCap (Explicit.c .high θ) θ<
      Vd R (Explicit.k .high θ) (if atH then 1 else Explicit.l .high θ) 0 := by
  let p : ℝ := Explicit.k .high θ
  let q : ℝ := if atH then 1 else Explicit.l .high θ
  let P : ℚ[X] := if atH then Certificate.PH .high else Certificate.PG .high
  let r : ℚ[X] := if atH then Certificate.RH .high else Certificate.RG .high
  have hfam := Certificate.family_frame_domain .high hθ
  have hpos := Certificate.split_positive .high .atA hθ
  have hp : 0<p := hpos.1
  have hq : 0<q := by
    cases atH
    · exact hpos.2.1
    · norm_num [q]
  have hn := pairNorm_pos hp hq (by norm_num [frameCap])
  have hnorm : (pairNorm p q 0)^2≤aeval θ P := by
    have hh := Certificate.ordinary_norm_bounds .high .atA hθ
    cases atH
    · simpa [p,q,P] using hh.2.1
    · simpa [p,q,P] using hh.1
  have hr : 0<aeval θ r := by
    cases atH
    · simpa [r,Certificate.highAuxiliary] using Certificate.high_auxiliary_positive .atA 1 hθ
    · simpa [r,Certificate.highAuxiliary] using Certificate.high_auxiliary_positive .atA 0 hθ
  have hd : 0<aeval θ Certificate.secantR := by
    simpa [Certificate.highAuxiliary] using Certificate.high_auxiliary_positive .atA 10 hθ
  have hden := SecantBaseline.denominator_pos (Explicit.c .high θ) θ
  have hden2 := SecantBaseline.denominator_sq (Explicit.c .high θ) θ
  have ht := taylor_bounds hfam
  have hcos : 0<Real.cos θ := by linarith [(transport_trig hfam).1]
  have hC10 : 0≤aeval θ C10 := by linarith [ht.2.2.2.1]
  have hC10sq := pow_le_pow_left₀ hC10 ht.2.2.2.2.1 2
  have hC12sq := Certificate.cosine_square_upper hfam
  have hD : (SecantBaseline.denominator (Explicit.c .high θ) θ)^2≤
      aeval θ (1+(Certificate.c .high)^2*C12^2) := by
    have hh := mul_le_mul_of_nonneg_left hC12sq (sq_nonneg (Explicit.c .high θ))
    simp only [map_add,map_mul,map_pow,map_one,Certificate.c_eval]
    linarith
  have hR : (Certificate.Rlo:ℝ)≤R := by
    have hs : R^2=qCap := Real.sq_sqrt (by norm_num [qCap])
    have hr0 : 0≤R := Real.sqrt_nonneg qCap
    norm_num [Certificate.Rlo,qCap] at hs ⊢
    nlinarith
  have hpoly : 0<2*(Certificate.Rlo:ℝ)*aeval θ r*(p*q)*(aeval θ C10)^2*
      (aeval θ (1+(Certificate.c .high)^2*C12^2)+(aeval θ Certificate.secantR)^2)+
      2*(Certificate.Rlo:ℝ)*aeval θ Certificate.secantR*aeval θ S11*
        (aeval θ P+(aeval θ r)^2)-
      (13/12+aeval θ S9)*(aeval θ P+(aeval θ r)^2)*
        (aeval θ (1+(Certificate.c .high)^2*C12^2)+(aeval θ Certificate.secantR)^2) := by
    have hh : 0<aeval θ (Certificate.derivativeNumerator atH) := by
      cases atH
      · have h := Certificate.direct_positive .derivativeG hθ
        norm_num [Certificate.directReserve,Certificate.directPolynomial] at h
        linarith
      · have h := Certificate.direct_positive .derivativeH hθ
        norm_num [Certificate.directReserve,Certificate.directPolynomial] at h
        linarith
    cases atH <;>
      simpa [Certificate.derivativeNumerator,Certificate.K,P,r,p,q,
        Certificate.Rlo] using hh
  have hb := derivative_transfer hn hden hr hd hnorm hD (mul_nonneg hp.le hq.le)
    (sq_nonneg _) hC10sq ht.1 ht.2.1 ht.2.2.1
    (by norm_num [Certificate.Rlo] : (0:ℝ)≤(Certificate.Rlo:ℝ)) hR hpoly
  rw [zero_slope]
  change (13/12+Real.sin θ-R*Real.sin θ/SecantBaseline.denominator
    (Explicit.c .high θ) θ)/Real.cos θ^2<R*(p*q)/pairNorm p q 0
  apply (div_lt_iff₀ (sq_pos_of_pos hcos)).2
  nlinarith only [hb]

theorem zero_slope_first_mono {p p' q : ℝ}
    (hp : 0<p) (hpp' : p≤p') (hq : 0<q) : Vd R p q 0≤Vd R p' q 0 := by
  have hp' := hp.trans_le hpp'
  have hn := pairNorm_pos hp hq (by norm_num [frameCap])
  have hn' := pairNorm_pos hp' hq (by norm_num [frameCap])
  have hn2 := pairNorm_sq hp hq (by norm_num [frameCap])
  have hn2' := pairNorm_sq hp' hq (by norm_num [frameCap])
  simp only [pairEnergy,pairProduct,Real.sin_zero,mul_zero,add_zero] at hn2 hn2'
  have hsq := pow_le_pow_left₀ hp.le hpp' 2
  have hprod := mul_le_mul_of_nonneg_right hsq (sq_nonneg q)
  have hcross : p*pairNorm p' q 0≤p'*pairNorm p q 0 := by
    have he : (p'*pairNorm p q 0)^2-(p*pairNorm p' q 0)^2=(p'^2-p^2)*q^2 := by
      rw [mul_pow,mul_pow,hn2,hn2']
      ring
    nlinarith [mul_pos hp hn',mul_pos hp' hn]
  have hquot := (div_le_div_iff₀ hn hn').2 hcross
  have hh := mul_le_mul_of_nonneg_left hquot
    (mul_nonneg (Real.sqrt_nonneg qCap) hq.le)
  rw [zero_slope,zero_slope]
  nlinarith only [hh]

theorem high_D_below_zero_slope {θ z : ℝ}
    (hθ : θ∈Icc (1/6:ℝ) (7/10)) (hz : z∈Icc 0 θ) (i : Fin 3) :
    secantGainDeriv qCap (Explicit.c .high θ) θ<
      Vd R (Explicit.p .high θ z i) (Explicit.q .high θ z i) 0 := by
  have hpos := Explicit.family_positive .high hθ hz
  have hm := Explicit.high_tilted hθ hz
  fin_cases i
  · simpa [Explicit.p,Explicit.q] using H_G_endpoint true hθ
  · simpa [Explicit.p,Explicit.q] using H_G_endpoint false hθ
  · have hB := zero_slope_first_mono hpos.1 hm.1.le hpos.2.1
    have hG := H_G_endpoint false hθ
    simp only [Bool.false_eq_true,↓reduceIte] at hG
    have hs : Vd R (min (Explicit.l .high θ) (Explicit.m .high θ z))
        (max (Explicit.l .high θ) (Explicit.m .high θ z)) 0=
        Vd R (Explicit.m .high θ z) (Explicit.l .high θ) 0 := by
      rcases le_total (Explicit.l .high θ) (Explicit.m .high θ z) with hh | hh
      · rw [min_eq_left hh,max_eq_right hh,zero_slope,zero_slope,pairNorm_symm]
        ring
      · rw [min_eq_right hh,max_eq_left hh]
    simpa only [Explicit.p,Explicit.q,Matrix.cons_val_succ,Matrix.cons_val_zero,hs]
      using hG.trans_le hB

theorem baseFirst_tan {c θ : ℝ} (hθ : θ∈Icc 0 frameCap) :
    SecantCoordinate.baseFirst c (Real.tan θ)=
      secantGainDeriv qCap c θ/(1+Real.tan θ^2) := by
  have hc : 0<Real.cos θ := by linarith [(transport_trig hθ).1]
  have ha := SecantCoordinate.arctan_tan hθ
  have he : (fun x => SecantNormCurvature.normalized R c (Real.arctan x))=
      (fun x => SecantCoordinate.base c x-SecantCoordinate.base c 0) :=
    funext (SecantCoordinate.normalized_arctan c)
  have hd := (SecantNormCurvature.normalized_hasDerivAt (R:=R) (a:=c)
    (s:=Real.arctan (Real.tan θ)) (by simpa only [ha] using hc)).comp
    (Real.tan θ) (Real.hasDerivAt_arctan (Real.tan θ))
  rw [he] at hd
  have hid := hd.unique ((SecantCoordinate.base_hasDerivAt c (Real.tan θ)).sub_const
    (SecantCoordinate.base c 0))
  have hs := SecantBaseline.angleSlope_eq (l:=1) (r:=c) hc
  have hs' : SecantNormCurvature.gainFirst R c θ=secantGainDeriv qCap c θ := by
    simpa only [SecantBaseline.angleSlope,one_mul,secantGainDeriv,
      SecantBaseline.denominator,gainRadicand] using hs
  simpa only [ha,hs',div_eq_mul_inv,one_div] using hid.symm

theorem high_pure_first_right_negative {θ z : ℝ}
    (hθ : θ∈Icc (1/6:ℝ) (7/10)) (hz : z∈Icc 0 θ) (i : Fin 3) :
    SecantCoordinate.pureFirst 1 (Explicit.c .high θ)
      (Explicit.p .high θ z i) (Explicit.q .high θ z i) θ (Real.tan θ)<0 := by
  have hf := Certificate.family_frame_domain .high hθ
  have hh := high_D_below_zero_slope hθ hz i
  have hd : 0<1+Real.tan θ^2 := by positivity
  simp only [SecantCoordinate.pureFirst,one_mul,SecantCoordinate.arctan_tan hf,
    sub_self,baseFirst_tan hf]
  exact sub_neg.mpr (div_lt_div_of_pos_right hh hd)

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveTD.HighDerivative

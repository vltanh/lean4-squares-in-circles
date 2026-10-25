module

public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2AffectedNegativeCurves
public import SquaresInCircles.Eight.Owners.GA.Negative.DETD2HighSecant
public import SquaresInCircles.Eight.Owners.GA.Negative.DETD2OriginalStress

/-!
# Eight squares: the negative-EH1 / TD2 stress and its four blocks

The EH multiplier is in the block of the H circle (`hBlock`). Its zero-angle support loss appears
exactly once, in `ehGain`. The nominal H block has the same angle and only accounts for the signed
masses. DE2 is never erased; only the selected A arguments, TD and the negative EH argument are
removed.
-/

section
/-!
## The actual right endpoint derivative of each high negative-DE pure block

The H and G numerator polynomials are transferred to their
actual circle norms before the B comparison.  The resulting secant
coordinate derivative is strictly negative at the original total angle.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.HighDerivative
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PairNormCalculus
open OrdinaryNegativeSlope Polynomial

open PositiveTD.Certificate (C10 C12 S9 S11 taylor_bounds)

private theorem r74_high {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    θ∈Icc ((Certificate.left .high:ℚ):ℝ) ((Certificate.right .high:ℚ):ℝ) := by
  simpa [Certificate.left,Certificate.right,PositiveTD.Certificate.L,
    PositiveTD.Certificate.h] using hθ

theorem reciprocal_minorant {n r P : ℝ} (hn : 0<n) (_hr : 0<r)
    (hP : n^2≤P) : 2*r/(P+r^2)≤1/n := by
  have hden : 0<P+r^2 := by nlinarith [sq_pos_of_pos hn,sq_nonneg r]
  apply (div_le_div_iff₀ hden hn).2
  nlinarith [sq_nonneg (n-r)]

/-- The sine in the second reciprocal term may be enlarged independently
of the upper Taylor sine in the subtracted numerator. -/
theorem derivative_transfer {n h r d P Q f u v y s Y a b : ℝ}
    (hn : 0<n) (hh : 0<h) (hr : 0<r) (hd : 0<d)
    (hP : n^2≤P) (hQ : h^2≤Q) (hf : 0≤f)
    (hu : 0≤u) (huv : u≤v) (hy : 0≤y) (hys : y≤ s) (hsY : s≤Y)
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
    rw [he]
    apply (lt_div_iff₀ (mul_pos hA hD)).2
    nlinarith only [hpoly]
  have hrec₁ := reciprocal_minorant hn hr hP
  have hrec₂ := reciprocal_minorant hh hd hQ
  have hb : 0≤b := ha.trans hab
  have hv : 0≤v := hu.trans huv
  have hs : 0 ≤ s := hy.trans hys
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
  have hfam := Certificate.family_frame_domain .high (r74_high hθ)
  have hpos := Certificate.split_positive .high .atA (r74_high hθ)
  have hp : 0<p := hpos.1
  have hq : 0<q := by
    cases atH
    · exact hpos.2.1
    · norm_num [q]
  have hn := pairNorm_pos (t:=0) hp hq (by norm_num [frameCap])
  have hnorm : (pairNorm p q 0)^2≤aeval θ P := by
    have hh := Certificate.ordinary_norm_bounds .high .atA (r74_high hθ)
    cases atH
    · simpa [p,q,P] using hh.2.1
    · simpa [p,q,P] using hh.1
  have hr : 0<aeval θ r := by
    cases atH
    · simpa [r,Certificate.highAuxiliary] using Certificate.high_auxiliary_positive .atA 1 hθ
    · simpa [r,Certificate.highAuxiliary] using Certificate.high_auxiliary_positive .atA 0 hθ
  have hd : 0<aeval θ Certificate.secantR := by
    simpa [Certificate.highAuxiliary] using Certificate.high_auxiliary_positive .atA 10 hθ
  have hden := NegativeAPositiveTD.SecantBaseline.denominator_pos (Explicit.c .high θ) θ
  have hden2 := NegativeAPositiveTD.SecantBaseline.denominator_sq (Explicit.c .high θ) θ
  have ht := taylor_bounds hfam
  have hcos : 0<Real.cos θ := by linarith [(transport_trig hfam).1]
  have hC10 : 0≤aeval θ C10 := by linarith [ht.2.2.2.1]
  have hC10sq := pow_le_pow_left₀ hC10 ht.2.2.2.2.1 2
  have hC12sq := Certificate.cosine_square_upper hfam
  have hD : (NegativeAPositiveTD.SecantBaseline.denominator (Explicit.c .high θ) θ)^2≤
      aeval θ (1+(Certificate.c .high)^2*C12^2) := by
    have hh := mul_le_mul_of_nonneg_left hC12sq (sq_nonneg (Explicit.c .high θ))
    simp only [map_add,map_mul,map_pow,map_one,Certificate.c_eval]
    linarith
  have hR : (Certificate.Rlo:ℝ)≤R :=
    Real.le_sqrt_of_sq_le (by norm_num [Certificate.Rlo,qCap])
  have hpoly : 0<2*(Certificate.Rlo:ℝ)*aeval θ r*(p*q)*(aeval θ C10)^2*
      (aeval θ (1+(Certificate.c .high)^2*C12^2)+(aeval θ Certificate.secantR)^2)+
      2*(Certificate.Rlo:ℝ)*aeval θ Certificate.secantR*aeval θ S11*
        (aeval θ P+(aeval θ r)^2)-
      (13/12+aeval θ S9)*(aeval θ P+(aeval θ r)^2)*
        (aeval θ (1+(Certificate.c .high)^2*C12^2)+(aeval θ Certificate.secantR)^2) := by
    have hh : 0<aeval θ (Certificate.derivativeNumerator atH) := by
      cases atH
      · have h := Certificate.direct_positive .derivativeG (r74_high hθ)
        simp only [Certificate.directReserve,Certificate.directPolynomial] at h
        exact lt_trans (by norm_num) h
      · have h := Certificate.direct_positive .derivativeH (r74_high hθ)
        simp only [Certificate.directReserve,Certificate.directPolynomial] at h
        exact lt_trans (by norm_num) h
    convert hh using 1
    cases atH <;>
      simp only [Certificate.derivativeNumerator,Certificate.K,P,r,p,q,Certificate.Rlo,
        Bool.false_eq_true,↓reduceIte,map_add,map_sub,map_mul,map_pow,map_one,aeval_C,
        eq_ratCast,Certificate.k_eval,Certificate.l_eval] <;>
      push_cast <;> ring
  have hb := derivative_transfer hn hden hr hd hnorm hD (mul_nonneg hp.le hq.le)
    (sq_nonneg _) hC10sq ht.1 ht.2.1 ht.2.2.1
    (by norm_num [Certificate.Rlo] : (0:ℝ)≤(Certificate.Rlo:ℝ)) hR hpoly
  rw [zero_slope]
  change (13/12+Real.sin θ-R*Real.sin θ/NegativeAPositiveTD.SecantBaseline.denominator
    (Explicit.c .high θ) θ)/Real.cos θ^2<R*(p*q)/pairNorm p q 0
  apply (div_lt_iff₀ (sq_pos_of_pos hcos)).2
  generalize R = R' at hb ⊢
  have e : R'*(p*q)*Real.cos θ^2/pairNorm p q 0=R'*(p*q)/pairNorm p q 0*Real.cos θ^2 := by
    ring
  rw [e] at hb
  linarith only [hb]

theorem zero_slope_first_mono {p p' q : ℝ}
    (hp : 0<p) (hpp' : p≤p') (hq : 0<q) : Vd R p q 0≤Vd R p' q 0 := by
  have hp' := hp.trans_le hpp'
  have hn := pairNorm_pos (t:=0) hp hq (by norm_num [frameCap])
  have hn' := pairNorm_pos (t:=0) hp' hq (by norm_num [frameCap])
  have hn2 := pairNorm_sq (t:=0) hp hq (by norm_num [frameCap])
  have hn2' := pairNorm_sq (t:=0) hp' hq (by norm_num [frameCap])
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
  have e : ∀ x n : ℝ, R*(x*q)/n=(R*q)*(x/n) := by intros; ring
  rw [e,e]
  exact mul_le_mul_of_nonneg_left hquot (mul_nonneg (Real.sqrt_nonneg _) hq.le)

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
    change secantGainDeriv qCap (Explicit.c .high θ) θ<
      Vd R (min (Explicit.l .high θ) (Explicit.m .high θ z))
        (max (Explicit.l .high θ) (Explicit.m .high θ z)) 0
    rw [hs]
    exact hG.trans_le hB

theorem baseFirst_tan {c θ : ℝ} (hθ : θ∈Icc 0 frameCap) :
    NegativeAPositiveTD.SecantCoordinate.baseFirst c (Real.tan θ)=
      secantGainDeriv qCap c θ/(1+Real.tan θ^2) := by
  have hc : 0<Real.cos θ := by linarith [(transport_trig hθ).1]
  have ha := NegativeAPositiveTD.SecantCoordinate.arctan_tan hθ
  have he : (fun x => SecantNormCurvature.normalized R c (Real.arctan x))=
      (fun x => NegativeAPositiveTD.SecantCoordinate.base c x-NegativeAPositiveTD.SecantCoordinate.base c 0) :=
    funext (NegativeAPositiveTD.SecantCoordinate.normalized_arctan c)
  have hd0 := (SecantNormCurvature.normalized_hasDerivAt (R:=R) (a:=c)
    (s:=Real.arctan (Real.tan θ)) (by simpa only [ha] using hc)).comp
    (Real.tan θ) (Real.hasDerivAt_arctan (Real.tan θ))
  have hd : HasDerivAt (fun x => NegativeAPositiveTD.SecantCoordinate.base c x-
      NegativeAPositiveTD.SecantCoordinate.base c 0)
      (SecantNormCurvature.gainFirst R c (Real.arctan (Real.tan θ))*
        (1/(1+Real.tan θ^2))) (Real.tan θ) := by
    rw [←he]
    exact hd0
  have hid := hd.unique ((NegativeAPositiveTD.SecantCoordinate.base_hasDerivAt c (Real.tan θ)).sub_const
    (NegativeAPositiveTD.SecantCoordinate.base c 0))
  have hs := NegativeAPositiveTD.SecantBaseline.angleSlope_eq (l:=1) (r:=c) hc
  have hs' : SecantNormCurvature.gainFirst R c θ=secantGainDeriv qCap c θ := by
    simpa only [NegativeAPositiveTD.SecantBaseline.angleSlope,one_mul,secantGainDeriv,
      NegativeAPositiveTD.SecantBaseline.denominator,gainRadicand] using hs
  simpa only [ha,hs',div_eq_mul_inv,one_div,one_mul] using hid.symm

theorem high_pure_first_right_negative {θ z : ℝ}
    (hθ : θ∈Icc (1/6:ℝ) (7/10)) (hz : z∈Icc 0 θ) (i : Fin 3) :
    NegativeAPositiveTD.SecantCoordinate.pureFirst 1 (Explicit.c .high θ)
      (Explicit.p .high θ z i) (Explicit.q .high θ z i) θ (Real.tan θ)<0 := by
  have hf := Certificate.family_frame_domain .high (r74_high hθ)
  have hh := high_D_below_zero_slope hθ hz i
  have hd : 0<1+Real.tan θ^2 := by positivity
  simp only [NegativeAPositiveTD.SecantCoordinate.pureFirst,one_mul,NegativeAPositiveTD.SecantCoordinate.arctan_tan hf,
    sub_self,baseFirst_tan hf]
  exact sub_neg.mpr (div_lt_div_of_pos_right hh hd)

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.HighDerivative
end
end
end

section
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeEHPositiveTD.Source
open Candidate Secondary PositiveAngularEnvelope ActualOrdinaryBlocks PairedE
open NegativePrimary (erase)

abbrev aTotal := LowA.aTotal
abbrev selectedA := NegativeELargeA.Source.selectedA

def total (C : SignedCycle) (ga ab : Bool) : ℝ := aTotal C ga ab+delta C.theta T
def magnitude (C : SignedCycle) : ℝ := -delta C.theta E

def owners (hg ga ab : Bool) : Vertex→Fin 4 :=
  ![if hg then 2 else 0,if ga then 3 else 2,if ab then 2 else 0,2,2,2,1]
def weights (C : SignedCycle) (k l c u : ℝ) : Vertex→ℝ :=
  ![k,l,l,PositiveTD.tilted c (delta C.theta T),c,1,u]
def stress (C : SignedCycle) (hg ga ab : Bool) (k l c u : ℝ) : ℝ :=
  ∑i,weights C k l c u i*(edgeWidth (delta C.theta i)-C.edge i (owners hg ga ab i))

/-- The nominal coefficients affect neither signed mass. -/
def blocks (C : SignedCycle) (hg ga ab : Bool) (k l c : ℝ) : Fin 4→Block :=
  ![⟨k,1,erase (!hg) (delta C.theta H),0⟩,
    ⟨k,l,erase hg (delta C.theta H),erase ga (delta C.theta G)⟩,
    ⟨l,PositiveTD.tilted c (delta C.theta T),erase ab (delta C.theta A),delta C.theta B⟩,
    ⟨k,1,delta C.theta D,0⟩]

def hBlock (C : SignedCycle) (hg : Bool) (k u : ℝ) : Block :=
  ⟨k,u,erase (!hg) (delta C.theta H),0⟩
def actualBlocks (C : SignedCycle) (hg ga ab : Bool) (k l c u : ℝ) : Fin 4→ℝ :=
  ![PositiveTD.actualPairIncrement (hBlock C hg k u) (C.point H),
    PositiveTD.actualPairIncrement (blocks C hg ga ab k l c 1) (C.point G).reflect,
    PositiveTD.actualPairIncrement (blocks C hg ga ab k l c 2) (C.point B).reflect,
    PositiveTD.actualDIncrement c (delta C.theta D) (C.point D).reflect]

def ehGain (C : SignedCycle) (k u : ℝ) : ℝ :=
  u*edgeWidth (delta C.theta E)-1-u*(C.point E).a*Real.sin (delta C.theta E)+
    (1-u*Real.cos (delta C.theta E))*(C.point E).y-
      (fullSupport u k-fullSupport 1 k)

/-- Every term is evaluated at the points and frames of the cycle. -/
theorem decomposition (C : SignedCycle) (hg ga ab : Bool) (k l c u : ℝ) :
    stress C hg ga ab k l c u=PositiveTD.baseline k l c (delta C.theta T)+
      (∑i,actualBlocks C hg ga ab k l c u i)+
      l*primaryGain (C.point A) ga ab (delta C.theta G) (delta C.theta A)+
      PositiveTD.tReserve C c+ehGain C k u := by
  cases hg <;> cases ga <;> cases ab <;>
    simp [stress,weights,owners,blocks,hBlock,actualBlocks,ehGain,
      PositiveTD.baseline,PositiveTD.actualPairIncrement,PositiveTD.actualDIncrement,
      PositiveTD.tReserve,PositiveTD.tilted,pairF,pairG,primaryGain,erase,
      SignedCycle.edge,zeroProjection,quarterProjection,Fin.sum_univ_succ,
      word,delta,next,H,G,A,B,T,D,E,SignedPoint.reflect] <;> ring

theorem sum_parts (C : SignedCycle) (hg ga ab : Bool) (k l c : ℝ)
    (f : ℝ→ℝ) (hf : f 0=0) :
    (∑i,(f (blocks C hg ga ab k l c i).u+f (blocks C hg ga ab k l c i).v))=
      (∑i,f (delta C.theta i))-selectedA C ga ab f-
        f (delta C.theta T)-f (delta C.theta E) := by
  cases hg <;> cases ga <;> cases ab <;>
    simp [blocks,erase,selectedA,NegativeELargeA.Source.selectedA,selected,
      Fin.sum_univ_succ,H,G,A,B,T,D,E,hf] <;> ring

structure Budgets (C : SignedCycle) (hg ga ab : Bool) (k l c : ℝ) : Prop where
  total_domain : total C ga ab∈Icc 0 frameCap
  a_domain : aTotal C ga ab∈Icc 0 (total C ga ab)
  td_domain : delta C.theta T∈Icc 0 (total C ga ab)
  eh_domain : magnitude C∈Icc 0 frameCap
  positive_bound : (∑i,(blocks C hg ga ab k l c i).P)≤frameCap-total C ga ab
  negative_bound : (∑i,(blocks C hg ga ab k l c i).N)≤frameCap-magnitude C
  balance : (∑i,(blocks C hg ga ab k l c i).N)-(∑i,(blocks C hg ga ab k l c i).P)=
    total C ga ab-magnitude C

theorem budgets {C : SignedCycle} (hg ga ab : Bool) (k l c : ℝ)
    (hvar : positiveVariation C.theta≤frameCap) (ha : 0≤aTotal C ga ab)
    (hz : 0≤delta C.theta T) (hs : delta C.theta E≤0) : Budgets C hg ga ab k l c := by
  have hp := sum_parts C hg ga ab k l c positivePart positivePart_zero
  have hn := sum_parts C hg ga ab k l c negativePart negativePart_zero
  have hA := NegativeELargeA.Source.selectedA_signed C ga ab
  have hAP := NegativeELargeA.Source.selectedA_nonnegative C ga ab positivePart positivePart_nonneg
  have hAN := NegativeELargeA.Source.selectedA_nonnegative C ga ab negativePart negativePart_nonneg
  have hzP : positivePart (delta C.theta T)=delta C.theta T := max_eq_left hz
  have hzN : negativePart (delta C.theta T)=0 := max_eq_right (by linarith)
  have hsP : positivePart (delta C.theta E)=0 := max_eq_right hs
  have hsN : negativePart (delta C.theta E)=magnitude C := max_eq_left (neg_nonneg.mpr hs)
  have hP : (∑i,(blocks C hg ga ab k l c i).P)=
      positiveVariation C.theta-selectedA C ga ab positivePart-delta C.theta T := by
    simpa only [Block.P,hzP,hsP,sub_zero,positiveVariation] using hp
  have hN : (∑i,(blocks C hg ga ab k l c i).N)=
      negativeVariation C.theta-selectedA C ga ab negativePart-magnitude C := by
    simpa only [Block.N,hzN,hsN,sub_zero,negativeVariation] using hn
  have hP0 := Finset.sum_nonneg (s:=Finset.univ)
    (fun i _ => (blocks C hg ga ab k l c i).P_nonneg)
  have hN0 := Finset.sum_nonneg (s:=Finset.univ)
    (fun i _ => (blocks C hg ga ab k l c i).N_nonneg)
  have heq := variations_equal C.theta
  have hs0 : 0≤ magnitude C := neg_nonneg.mpr hs
  change selectedA C ga ab positivePart-selectedA C ga ab negativePart=aTotal C ga ab at hA
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · dsimp [total]; exact ⟨add_nonneg ha hz,by linarith⟩
  · dsimp [total]; exact ⟨ha,by linarith⟩
  · dsimp [total]; exact ⟨hz,by linarith⟩
  · exact ⟨hs0,by linarith⟩
  · dsimp [total]; linarith
  · linarith
  · dsimp [total]; linarith

theorem block_coefficients {C : SignedCycle} (hg ga ab : Bool) {k l c : ℝ}
    (hk : k≤1) (hl : k≤l) (i : Fin 4) :
    (blocks C hg ga ab k l c i).p=(![k,k,min l (PositiveTD.tilted c (delta C.theta T)),k] : Fin 4→ℝ) i ∧
    (blocks C hg ga ab k l c i).q=(![1,l,max l (PositiveTD.tilted c (delta C.theta T)),1] : Fin 4→ℝ) i := by
  fin_cases i <;> simp [blocks,Block.p,Block.q,min_eq_left hk,max_eq_right hk,
    min_eq_left hl,max_eq_right hl]

theorem block_budgets {C : SignedCycle} (hg ga ab : Bool) (k l c : ℝ)
    (hvar : positiveVariation C.theta≤frameCap) (ha : 0≤aTotal C ga ab)
    (hz : 0≤delta C.theta T) (hs : delta C.theta E≤0) (i : Fin 4) :
    (blocks C hg ga ab k l c i).P≤frameCap ∧ (blocks C hg ga ab k l c i).N≤frameCap := by
  have hb := budgets hg ga ab k l c hvar ha hz hs
  have hp := Finset.single_le_sum (s:=Finset.univ)
    (fun j _ => (blocks C hg ga ab k l c j).P_nonneg) (Finset.mem_univ i)
  have hn := Finset.single_le_sum (s:=Finset.univ)
    (fun j _ => (blocks C hg ga ab k l c j).N_nonneg) (Finset.mem_univ i)
  exact ⟨by linarith [hb.positive_bound,hb.total_domain.1],
    by linarith [hb.negative_bound,hb.eh_domain.1]⟩

end SquaresInCircles.Eight.GlobalGA.NegativeEHPositiveTD.Source
end
end
end

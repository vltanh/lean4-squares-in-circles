module

public import SquaresInCircles.Eight.Frames.Ordinary.AngleConcentration
public import SquaresInCircles.Eight.Owners.WholeIntervalBernstein
public import SquaresInCircles.Eight.Owners.Positive.ScalarPolynomials
public import SquaresInCircles.Eight.Owners.Sole.OrdinaryData
public import SquaresInCircles.Eight.Owners.Sole.NormGain
public import SquaresInCircles.Eight.Owners.Sole.EndpointSupport

/-!
# Eight squares: complete signed ordinary-angle envelope with a positive T primary

Continuous concentration applies to the original
positive and negative ordinary budgets. Every separated and same-anchor
endpoint lies above a pure charge; no ordering of the ordinary angles
or strict owner selection is assumed.
-/

section
/-!
## The remaining DE low-family terminal chord

The original two-positive-square argument is proved
on the entire interval [0,.35]. The radius is the rational lower radius,
so the resulting chord transfers to every original working radius.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.SolePositiveTDEChord
open Polynomial WholeIntervalPolynomial
open SolePositiveTGrowth

def sineUpper : ℚ[X] := PositiveScalarPolynomials.sine+C (1/1307674368000)*X^15
def cosineUpper : ℚ[X] := PositiveScalarPolynomials.cosine
def capSine : ℚ := PositiveScalarPolynomials.sine.eval (7/10)
def capCosine : ℚ :=
  (PositiveScalarPolynomials.cosine-C (1/20922789888000)*X^16).eval (7/10)
def a : ℚ[X] := C (903/1000)*(C (5/8)+C (27/100)*X)
def b : ℚ := 903/1000
def capSquare : ℚ[X] := a^2+C (b^2)-C (2*b*capSine)*a
def squareDifference : ℚ[X] := C (2*b)*a*(C capSine-sineUpper)
def A : ℚ[X] := C (7/10)*(C (7/10)-X)+C b*(cosineUpper-C capCosine)
def B : ℚ[X] := C (lowerRadius^2)*squareDifference-A^2
def P : ℚ[X] := B^2-C (4*lowerRadius^2)*A^2*capSquare

open WholeIntervalPolynomial.Certificate in
/-- Build a `Scaled` representation of a polynomial written with `+`, `-`, `*`,
powers, `C`, `X` and numerals, following its syntax; local hypotheses
`Scaled.Rep _ q` are used for the pieces `q` they name. -/
local syntax "r64_repT" : tactic
open WholeIntervalPolynomial.Certificate in
local macro_rules | `(tactic| r64_repT) => `(tactic| first
  | with_reducible assumption
  | (with_reducible apply Scaled.Rep.mul; r64_repT; r64_repT)
  | (with_reducible apply Scaled.Rep.add; r64_repT; r64_repT)
  | (with_reducible apply Scaled.Rep.sub; r64_repT; r64_repT)
  | (with_reducible apply Scaled.Rep.pow; r64_repT)
  | (with_reducible apply Scaled.Rep.neg; r64_repT)
  | with_reducible exact Scaled.rep_const _
  | with_reducible exact Scaled.rep_var
  | with_reducible exact Scaled.rep_zero
  | with_reducible exact Scaled.rep_one
  | with_reducible exact Scaled.rep_ofNat _
  | with_reducible exact Scaled.rep_natCast _)

private theorem r64_capSine_eq :
    capSine=1562944261619609101762963/2426112000000000000000000 := by
  norm_num [capSine,PositiveScalarPolynomials.sine]

private theorem r64_capCosine_eq :
    capCosine=136076805969657256004599/177914880000000000000000 := by
  norm_num [capCosine,PositiveScalarPolynomials.cosine]

open WholeIntervalPolynomial.Certificate in
/-- One kernel check gives the expansion identity and the reserve. -/
private theorem r64_cert {c : Scaled} {a b ρ : ℚ} {p : ℚ[X]} {D : ℕ}
    (hc : c.Rep (centered a b p))
    (h : c.s≠0 ∧ c.l.length≤D+1 ∧
      ρ<(lowerZ D (fun j => (chebList c.l).getD j 0):ℚ)/(c.s*2^c.l.length/2)) :
    centered a b p=expansion D (centered a b p) ∧ ρ<lowerOn D a b p := by
  refine ⟨hc.eq_expansion h.1 h.2.1,?_⟩
  rw [lowerOn_eq_of_rep hc h.1 h.2.1]
  exact h.2.2

open WholeIntervalPolynomial.Certificate in
private theorem r64_certs :
    (centered 0 (7/20) A=expansion 16 (centered 0 (7/20) A) ∧ (2/5:ℚ)<lowerOn 16 0 (7/20) A) ∧
    (centered 0 (7/20) B=expansion 32 (centered 0 (7/20) B) ∧ (6/5:ℚ)<lowerOn 32 0 (7/20) B) ∧
    (centered 0 (7/20) P=expansion 64 (centered 0 (7/20) P) ∧ (1/4:ℚ)<lowerOn 64 0 (7/20) P) := by
  have hs := (by simp only [sineUpper,PositiveScalarPolynomials.sine]; r64_repT :
    Scaled.Rep _ sineUpper)
  have hA := (by
    simp only [A,cosineUpper,PositiveScalarPolynomials.cosine,b,r64_capCosine_eq]; r64_repT :
    Scaled.Rep _ A)
  have hd := (by simp only [squareDifference,a,b,r64_capSine_eq]; r64_repT :
    Scaled.Rep _ squareDifference)
  have hB := (by simp only [B,lowerRadius]; r64_repT : Scaled.Rep _ B)
  have hq := (by simp only [capSquare,a,b,r64_capSine_eq]; r64_repT : Scaled.Rep _ capSquare)
  have hP := (by simp only [P,lowerRadius]; r64_repT : Scaled.Rep _ P)
  refine ⟨r64_cert (hA.centered 7 40 1 1 (by norm_num) (by norm_num) (by norm_num))
      (by decide +kernel),
    r64_cert (hB.centered 7 40 1 1 (by norm_num) (by norm_num) (by norm_num))
      (by decide +kernel),
    r64_cert (hP.centered 7 40 1 1 (by norm_num) (by norm_num) (by norm_num))
      (by decide +kernel)⟩

theorem identities :
    centered 0 (7/20) A=expansion 16 (centered 0 (7/20) A) ∧
    centered 0 (7/20) B=expansion 32 (centered 0 (7/20) B) ∧
    centered 0 (7/20) P=expansion 64 (centered 0 (7/20) P) :=
  ⟨r64_certs.1.1,r64_certs.2.1.1,r64_certs.2.2.1⟩

theorem reserves :
    (2/5:ℚ)<lowerOn 16 0 (7/20) A ∧
    (6/5:ℚ)<lowerOn 32 0 (7/20) B ∧
    (1/4:ℚ)<lowerOn 64 0 (7/20) P :=
  ⟨r64_certs.1.2,r64_certs.2.1.2,r64_certs.2.2.2⟩

open Set PositiveAngularEnvelope PairNormCalculus OrdinaryAngleConcavity
open OrdinaryNegativeEnvelope SingleAngleConcavity VaryingBFunctions

theorem polynomial_values (t : ℝ) :
    aeval t sineUpper=HighOrderTaylor.S13 t ∧
    aeval t cosineUpper=HighOrderTaylor.C16 t ∧
    (capSine:ℝ)=HighOrderTaylor.S15 frameCap ∧
    (capCosine:ℝ)=HighOrderTaylor.C14 frameCap := by
  refine ⟨?_,?_,?_,?_⟩
  · simp only [sineUpper,PositiveScalarPolynomials.sine,map_add,map_sub,map_mul,map_pow,
      aeval_C,aeval_X,eq_ratCast]
    simp only [HighOrderTaylor.S13,HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7]
    push_cast
    ring
  · simp only [cosineUpper,PositiveScalarPolynomials.cosine,map_add,map_sub,map_mul,map_pow,
      map_one,aeval_C,aeval_X,eq_ratCast]
    simp only [HighOrderTaylor.C16,HighOrderTaylor.C14,HighOrderTaylor.C12,Arithmetic.cos10,
      Arithmetic.cos8]
    push_cast
    ring
  · rw [r64_capSine_eq]
    norm_num [HighOrderTaylor.S15,HighOrderTaylor.S13,HighOrderTaylor.S11,Arithmetic.sin9,
      Arithmetic.sin7,frameCap]
  · rw [r64_capCosine_eq]
    norm_num [HighOrderTaylor.C14,HighOrderTaylor.C12,Arithmetic.cos10,Arithmetic.cos8,frameCap]

theorem positive_values {t : ℝ} (ht : t∈Icc 0 (7/20:ℝ)) :
    0<aeval t A ∧ 0<aeval t B ∧ 0<aeval t P := by
  have ht' : t∈Icc ((0:ℚ):ℝ) ((7/20:ℚ):ℝ) := by
    push_cast
    exact ht
  have hA := positive_on_interval (by norm_num : (0:ℚ)<7/20) identities.1 reserves.1 ht'
  have hB := positive_on_interval (by norm_num : (0:ℚ)<7/20) identities.2.1 reserves.2.1 ht'
  have hP := positive_on_interval (by norm_num : (0:ℚ)<7/20) identities.2.2 reserves.2.2 ht'
  push_cast at hA hB hP
  exact ⟨by linarith,by linarith,by linarith⟩

theorem chord {t : ℝ} (ht : t∈Icc 0 (7/20:ℝ)) :
    (7/10)*(frameCap-t)<(903/1000)*
      (V (lowerRadius:ℝ) (5/8+27/100*t) 1 frameCap-
        V (lowerRadius:ℝ) (5/8+27/100*t) 1 t) := by
  have ht' : t∈Icc 0 frameCap := ⟨ht.1,by simp only [frameCap]; linarith [ht.2]⟩
  obtain ⟨α,hαd⟩ : ∃ α : ℝ,α=(903/1000)*(5/8+27/100*t) := ⟨_,rfl⟩
  obtain ⟨β,hβd⟩ : ∃ β : ℝ,β=903/1000 := ⟨_,rfl⟩
  have hα : 0<α := by rw [hαd]; nlinarith [ht.1]
  have hβ : 0<β := by rw [hβd]; norm_num
  have htabs : |-t|≤frameCap := by rw [abs_neg,abs_of_nonneg ht.1]; exact ht'.2
  have hhabs : |-frameCap|≤frameCap := by
    rw [abs_neg,abs_of_nonneg (by norm_num [frameCap])]
  obtain ⟨N,hNd⟩ : ∃ N : ℝ,N=pairNorm α β (-t) := ⟨_,rfl⟩
  obtain ⟨H,hHd⟩ : ∃ H : ℝ,H=pairNorm α β (-frameCap) := ⟨_,rfl⟩
  have hN : 0<N := hNd ▸ pairNorm_pos hα hβ htabs
  have hH : 0<H := hHd ▸ pairNorm_pos hα hβ hhabs
  have hN2 : N^2=α^2+β^2-2*α*β*Real.sin t := by
    rw [hNd,pairNorm_sq hα hβ htabs]
    simp only [pairEnergy,pairProduct,Real.sin_neg]
    ring
  have hH2 : H^2=α^2+β^2-2*α*β*Real.sin frameCap := by
    rw [hHd,pairNorm_sq hα hβ hhabs]
    simp only [pairEnergy,pairProduct,Real.sin_neg]
    ring
  have hS0 := HighOrderTaylor.S15_le_sin (show (0:ℝ)≤frameCap by norm_num [frameCap])
  have hS1 := HighOrderTaylor.sin_le_S13 ht.1
  have hC0 := HighOrderTaylor.C14_le_cos (show (0:ℝ)≤frameCap by norm_num [frameCap])
  have hC1 := HighOrderTaylor.cos_le_C16 ht.1
  obtain ⟨hv1,hv2,hv3,hv4⟩ := polynomial_values t
  have hR : (0:ℝ)<(lowerRadius:ℝ) := by norm_num [lowerRadius]
  have ha : aeval t a=α := by
    simp only [a,map_add,map_mul,aeval_C,aeval_X,eq_ratCast]
    rw [hαd]
    push_cast
    ring
  have hcapS : aeval t capSquare=α^2+β^2-2*β*HighOrderTaylor.S15 frameCap*α := by
    simp only [capSquare,map_add,map_sub,map_mul,map_pow,aeval_C,eq_ratCast,ha]
    rw [← hv3,hβd]
    simp only [b]
    push_cast
    ring
  have hsdS : aeval t squareDifference=
      2*β*α*(HighOrderTaylor.S15 frameCap-HighOrderTaylor.S13 t) := by
    simp only [squareDifference,map_mul,map_sub,aeval_C,eq_ratCast,ha,hv1]
    rw [← hv3,hβd]
    simp only [b]
    push_cast
    ring
  have hAS : aeval t A=(7/10)*(7/10-t)+
      β*(HighOrderTaylor.C16 t-HighOrderTaylor.C14 frameCap) := by
    simp only [A,map_add,map_mul,map_sub,aeval_C,aeval_X,eq_ratCast,hv2]
    rw [← hv4,hβd]
    simp only [b]
    push_cast
    ring
  have hcap : H^2≤aeval t capSquare := by
    have hm := mul_le_mul_of_nonneg_left hS0 (show 0≤2*α*β by positivity)
    rw [hcapS,hH2]
    linarith
  have hdiff : aeval t squareDifference≤N^2-H^2 := by
    have hsd : HighOrderTaylor.S15 frameCap-HighOrderTaylor.S13 t≤
        Real.sin frameCap-Real.sin t := by linarith
    have hm := mul_le_mul_of_nonneg_left hsd (show 0≤2*α*β by positivity)
    rw [hsdS,hN2,hH2]
    linarith
  have hAupper : (7/10)*(frameCap-t)+β*(Real.cos t-Real.cos frameCap)≤aeval t A := by
    have hm := mul_le_mul_of_nonneg_left
      (show Real.cos t-Real.cos frameCap≤
        HighOrderTaylor.C16 t-HighOrderTaylor.C14 frameCap by linarith) hβ.le
    rw [hAS]
    simp only [frameCap] at hm ⊢
    linarith
  rcases positive_values ht with ⟨hA,hB,hP⟩
  have hBid : aeval t B=(lowerRadius:ℝ)^2*aeval t squareDifference-(aeval t A)^2 := by
    simp only [B,map_sub,map_mul,map_pow,aeval_C,eq_ratCast]
  have hPid : aeval t P=(aeval t B)^2-
      4*(lowerRadius:ℝ)^2*(aeval t A)^2*aeval t capSquare := by
    simp only [P,map_sub,map_mul,map_pow,aeval_C,eq_ratCast]
    push_cast
    ring
  have hcapmul := mul_le_mul_of_nonneg_left hcap
    (show 0≤4*(lowerRadius:ℝ)^2*(aeval t A)^2 by positivity)
  have hcross : 2*(lowerRadius:ℝ)*aeval t A*H<aeval t B := by
    have hsq : (2*(lowerRadius:ℝ)*aeval t A*H)^2<(aeval t B)^2 := by
      have he : (2*(lowerRadius:ℝ)*aeval t A*H)^2=4*(lowerRadius:ℝ)^2*(aeval t A)^2*H^2 := by
        ring
      rw [he]
      linarith
    exact lt_of_pow_lt_pow_left₀ 2 hB.le hsq
  have hdiffmul := mul_le_mul_of_nonneg_left hdiff (sq_nonneg (lowerRadius:ℝ))
  have hrootcross : (lowerRadius:ℝ)*H+aeval t A<(lowerRadius:ℝ)*N := by
    have hn : 0≤(lowerRadius:ℝ)*N := mul_nonneg hR.le hN.le
    have hsq : ((lowerRadius:ℝ)*H+aeval t A)^2<((lowerRadius:ℝ)*N)^2 := by
      have he1 : ((lowerRadius:ℝ)*H+aeval t A)^2=
          (lowerRadius:ℝ)^2*H^2+2*(lowerRadius:ℝ)*aeval t A*H+(aeval t A)^2 := by ring
      have he2 : ((lowerRadius:ℝ)*N)^2=(lowerRadius:ℝ)^2*N^2 := by ring
      rw [he1,he2]
      have he3 : (lowerRadius:ℝ)^2*(N^2-H^2)=(lowerRadius:ℝ)^2*N^2-(lowerRadius:ℝ)^2*H^2 := by
        ring
      linarith
    exact lt_of_pow_lt_pow_left₀ 2 hn hsq
  have hraw : (7/10)*(frameCap-t)<V (lowerRadius:ℝ) α β frameCap-V (lowerRadius:ℝ) α β t := by
    simp only [V]
    rw [← hNd,← hHd]
    linarith
  have hhom (u : ℝ) : V (lowerRadius:ℝ) α β u=
      (903/1000)*V (lowerRadius:ℝ) (5/8+27/100*t) 1 u := by
    rw [hαd,hβd]
    simpa only [mul_one] using
      V_homogeneous (by norm_num : (0:ℝ)≤903/1000) (lowerRadius:ℝ) (5/8+27/100*t) 1 u
  rw [hhom,hhom] at hraw
  linarith

theorem growth {R p q nu t : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (hp : 0<p) (hpq : p≤q)
    (hratio : (5/8+27/100*t)*q≤p) (hq : 903/1000≤q) (hnu : nu≤q)
    (ht : t∈Icc 0 (7/20:ℝ)) :
    (7/10)*(frameCap-t)≤Vnu R p q nu frameCap-Vnu R p q nu t := by
  have ht' : t∈Icc 0 frameCap := ⟨ht.1,by norm_num [frameCap]; linarith [ht.2]⟩
  have hch := chord ht
  have hlen : 0≤frameCap-t := by linarith [ht'.2]
  have hv : 0≤V (lowerRadius:ℝ) (5/8+27/100*t) 1 frameCap-
      V (lowerRadius:ℝ) (5/8+27/100*t) 1 t := by
    nlinarith [mul_nonneg (by norm_num : (0:ℝ)≤7/10) hlen]
  have hscale := mul_le_mul_of_nonneg_right hq hv
  have htransfer := normalized_growth (radius_le hR hQL) hp hpq
    (show 0<5/8+27/100*t by linarith [ht.1]) hratio hnu ht'
    (show frameCap∈Icc 0 frameCap by norm_num [frameCap]) ht'.2
  linarith

end SquaresInCircles.Eight.SolePositiveTDEChord
end
end
end

section
/-!
## Same-anchor alternatives for every positive-T family

The original norm cancels in the comparison. The
low EH ratio dominates the existing correlated whole-interval ratio.
The two remaining low ratios follow from one half-angle inequality.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SolePositiveTSameBlock
open PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryAngleConcentration

theorem from_bracket {R p q r t : ℝ} (hq : 0≤q) (hr : r*q≤p)
    (ht : t∈Icc 0 frameCap)
    (hbracket : 0≤r*(PositiveAngularEnvelope.phi (frameCap-t)-1)+Real.cos frameCap-Real.cos t) :
    V R p q t≤M R p q t := by
  have ha : frameCap-t∈Icc 0 frameCap := ⟨by linarith [ht.2],by linarith [ht.1]⟩
  have hphi := sub_nonneg.mpr (CorrelatedSameBlock.one_le_phi ha)
  have hm := mul_le_mul_of_nonneg_right hr hphi
  have hb := mul_nonneg hq hbracket
  dsimp [V,M]
  nlinarith

theorem half_angle_bracket {r t : ℝ} (ht : t∈Icc 0 frameCap)
    (hr : r≤Real.cos frameCap)
    (hreserve : 0≤r-Real.sin frameCap+
      (Real.cos frameCap-r)*(frameCap-t)/2) :
    0≤r*(PositiveAngularEnvelope.phi (frameCap-t)-1)+Real.cos frameCap-Real.cos t := by
  let a := frameCap-t
  have ha : a∈Icc 0 frameCap := ⟨by dsimp [a]; linarith [ht.2],
    by dsimp [a]; linarith [ht.1]⟩
  have hh := mul_le_mul_of_nonneg_left (CorrelatedSameBlock.half_angle_lower ha)
    (sub_nonneg.mpr hr)
  have hs := mul_nonneg (transport_trig ha).2.2.1 hreserve
  have hid : Real.cos t=Real.cos frameCap*Real.cos a+Real.sin frameCap*Real.sin a := by
    rw [← Real.cos_sub]
    congr 1
    dsimp [a]
    ring
  rw [hid]
  dsimp [PositiveAngularEnvelope.phi,a] at *
  nlinarith

theorem EH_low {R p q t : ℝ} (hq : 0≤q)
    (hr : (117/200+3/10*t)*q≤p) (ht : t∈Icc 0 frameCap) :
    V R p q t≤M R p q t := by
  have hcor : PositiveStressCoefficients.ratio t*q≤p := by
    have hh := mul_nonneg ht.1 hq
    dsimp [PositiveStressCoefficients.ratio]
    nlinarith
  have hh := CorrelatedSameBlock.negative_surplus (R:=R) hq hcor ht
    (show (0:ℝ)∈Icc 0 t from ⟨le_rfl,ht.1⟩)
  have hid : mixedBlock R p q (frameCap-t) frameCap=M R p q t := by
    simpa only [show t+(frameCap-t)=frameCap by ring] using mixedBlock_saturated R p q t
  simpa only [sub_zero,hid] using hh

theorem EH_middle {R p q t : ℝ} (hq : 0≤q)
    (hr : (13/20)*q≤p) (ht : t∈Icc 0 frameCap) :
    V R p q t≤M R p q t := by
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have hc := (transport_trig hh).1
  have hs := (transport_trig hh).2.2.2.1
  apply from_bracket hq hr ht
  apply half_angle_bracket ht (by linarith)
  have hm := mul_nonneg (show 0≤Real.cos frameCap-13/20 by linarith)
    (show 0≤frameCap-t by linarith [ht.2])
  linarith

theorem DE_low_B {R p q t : ℝ} (hq : 0≤q)
    (hr : (5/8)*q≤p) (ht : t∈Icc 0 (7/20:ℝ)) :
    V R p q t≤M R p q t := by
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have hc := (transport_trig hh).1
  have hs := (transport_trig hh).2.2.2.1
  have ht' : t∈Icc 0 frameCap := ⟨ht.1,by norm_num [frameCap]; linarith [ht.2]⟩
  apply from_bracket hq hr ht'
  apply half_angle_bracket ht' (by linarith)
  have hlen : (7/20:ℝ)≤frameCap-t := by norm_num [frameCap]; linarith [ht.2]
  have hm := mul_le_mul (by linarith : (699/5000:ℝ)≤Real.cos frameCap-5/8)
    hlen (by norm_num) (by linarith)
  linarith

end SquaresInCircles.Eight.SolePositiveTSameBlock
end
end
end

section
/-!
## The fixed-coordinate split is necessary for the original weak owners

At the original primary split, the weighted seven
weak separators give a nonpositive relaxed stress. Only the G and E
works are bounded here: the H/A/B/D coordinates remain original.
Sole-EH allows either E sign; sole-DE retains E.y<=0 explicitly.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.SoleSplitSupport
open Candidate SignedStress SoleECoefficients SoleOriginalBlocks SoleSplitModel
open SoleResiduals SecondaryEStress ActualCoreEBlocks

def forceData (C : SignedCycle) (ab : Fin 4) (b : Band) (de : Bool) (t x e : ℝ) : Vertex → Point :=
  SoleEStress.forces C ab 2 0 (deOwner de) (ehOwner de)
    (n b t x) (k b t) (ell b t) (c b t) (c b t)
    (eMultiplier b de t e) (hMultiplier b de e)

def variableDemand (C : SignedCycle) (b : Band) (de : Bool) (t x e : ℝ) : ℝ :=
  n b t x*edgeWidth (delta C.theta H)+k b t*edgeWidth x+
    ell b t*edgeWidth (delta C.theta A)+c b t*edgeWidth (delta C.theta B)+
    c b t*edgeWidth (delta C.theta T)+
    eMultiplier b de t e*edgeWidth (if de then e else delta C.theta D)+
    hMultiplier b de e*edgeWidth (if de then delta C.theta E else e)

def anchorWork (C : SignedCycle) (ab : Fin 4) (b : Band) (de : Bool) (t x e : ℝ) : ℝ :=
  work (forceData C ab b de t x e H) (C.point H)+
    work (forceData C ab b de t x e A) (C.point A)+
    work (forceData C ab b de t x e B) (C.point B)+
    work (forceData C ab b de t x e D) (C.point D)

def stress (C : SignedCycle) (ab : Fin 4) (b : Band) (de : Bool) (R M t x e : ℝ) : ℝ :=
  variableDemand C b de t x e-anchorWork C ab b de t x e-
    k b t*sigma R (g b t)*Real.sin x-eBound C b de R M t e

theorem value_eq_stress {C : SignedCycle} {ab : Fin 4} {b : Band} (de : Bool)
    (R M : ℝ) {t x : ℝ} (hab : ab=0 ∨ ab=2) (ht : t∈domain b) (hx : x∈Icc 0 t)
    (hn : C.NormalAnchors) :
    SoleSplitModel.value C ab b de R M t x=stress C ab b de R M t x (t-x) := by
  have hH : |(C.point 0).y|=(C.point 0).y := abs_of_nonneg hn.H_nonneg
  have hD : |(C.point 5).y|=-(C.point 5).y := abs_of_nonpos hn.D_nonpos
  rw [SoleSplitModel.formula ab de R M ht hx]
  rcases hab with rfl | rfl <;> cases de <;>
    simp [stress,variableDemand,anchorWork,constant,transverse,radial,forceData,
      SoleEStress.forces,SoleEStress.weights,CoreEStress.owners,force,previous,
      source,target,word,add,scale,work,SignedCycle.edge,zeroProjection,quarterProjection,
      H,A,B,T,D,E,next,deOwner,ehOwner,eMultiplier,hMultiplier,hH,hD] <;> ring

theorem original_demand (C : SignedCycle) (b : Band) (de : Bool) (t : ℝ) :
    variableDemand C b de t (delta C.theta G) (primary C de)=
      demand C (SoleEStress.weights (n b t (delta C.theta G)) (k b t) (ell b t)
        (c b t) (c b t) (eMultiplier b de t (primary C de)) (hMultiplier b de (primary C de))) := by
  rw [SoleEStress.demand_eq]
  cases de <;> simp [variableDemand,primary]

theorem E_force (C : SignedCycle) (ab : Fin 4) (b : Band) (de : Bool) (t x : ℝ) :
    forceData C ab b de t x (primary C de) E=
      if de then (Real.sin (primary C de),hMultiplier b de (primary C de)-Real.cos (primary C de))
      else (Real.sin (primary C de),Real.cos (primary C de)-eMultiplier b de t (primary C de)) := by
  unfold forceData
  rw [SoleEStress.force_E (deOwner_cases de) (ehOwner_cases de)]
  cases de <;> simp [deOwner,ehOwner,primaryDE,primaryEH,primary,eMultiplier,hMultiplier]

theorem E_work_le {C : SignedCycle} (ab : Fin 4) {b : Band} (de : Bool) {R M t x : ℝ}
    (hR : 0≤R) (ht : t∈domain b) (he : primary C de∈Icc 0 t)
    (hs : (C.point E).Sorted) (hc : (C.point E).Contained (R^2))
    (ha : (C.point E).a≤M) (hsign : de=true → (C.point E).y≤0) :
    work (forceData C ab b de t x (primary C de) E) (C.point E)≤
      eBound C b de R M t (primary C de) := by
  have he' : primary C de∈Icc 0 frameCap := ⟨he.1,he.2.trans (angle ht).2⟩
  have hsin := (transport_trig he').2.2.1
  have hcos := Real.cos_le_one (primary C de)
  rw [E_force]
  cases de
  · simp only [Bool.false_eq_true,↓reduceIte]
    by_cases hb : b=.high
    · subst b
      have hy := mul_le_mul_of_nonpos_left (neg_abs_le (C.point E).y)
        (show Real.cos (primary C false)-1≤0 by linarith)
      simp only [eBound,↓reduceIte,Bool.false_eq_true,eMultiplier,p,work]
      linarith
    · have heta := (SoleECoefficients.positive ht).2.2.2.2
      have hh := work_le_circleSupport hR hs hc
        (Real.sin (primary C false),-Real.sin (primary C false)*eta b t)
      have hcirc := (scaled_primary_support (R := R) hsin heta).1
      rw [hcirc] at hh
      simp only [eBound,hb,↓reduceIte,Bool.false_eq_true,eMultiplier,p,work,sigma] at *
      linarith
  · simp only [↓reduceIte]
    have hy := hsign rfl
    have hvertical : 0≤hMultiplier b true (primary C true)-Real.cos (primary C true) := by
      cases b <;> simp [hMultiplier,r] <;> linarith
    have hm := mul_nonpos_of_nonneg_of_nonpos hvertical hy
    have ha' := mul_le_mul_of_nonneg_right ha hsin
    simp [eBound,work] at *
    nlinarith

theorem G_work_le {C : SignedCycle} (ab : Fin 4) {b : Band} (de : Bool) {R t e : ℝ}
    (hR : 0≤R) (ht : t∈domain b) (hx : delta C.theta G∈Icc 0 t)
    (hs : (C.point G).Sorted) (hc : (C.point G).Contained (R^2)) :
    work (forceData C ab b de t (delta C.theta G) e G) (C.point G)≤
      k b t*sigma R (g b t)*Real.sin (delta C.theta G) := by
  have hp := SoleECoefficients.positive ht
  have hx' : delta C.theta G∈Icc 0 frameCap := ⟨hx.1,hx.2.trans (angle ht).2⟩
  have hh := work_le_circleSupport hR hs hc (forceData C ab b de t (delta C.theta G) e G)
  have hfd : forceData C ab b de t (delta C.theta G) e G=
      SecondaryEStress.forces C ab 2 0 (tiltedWeight (k b t) (g b t) (delta C.theta G))
        (k b t) (ell b t) (c b t) (c b t) G := by
    unfold forceData
    rw [SoleEStress.force_G]
    rfl
  have hsup := positive_G_support (R := R) (ab := ab) (bt := 2) (td := 0)
    (l := ell b t) (b := c b t) (t := c b t) hp.1.le hp.2.2.2.1 hx'
  rw [hfd,hsup] at hh
  rw [hfd]
  have hq : primarySupport R (k b t) (g b t) (delta C.theta G)=
      k b t*sigma R (g b t)*Real.sin (delta C.theta G) := by
    simp only [primarySupport,sigma]
    ring
  linarith

theorem T_force (C : SignedCycle) (ab : Fin 4) (b : Band) (de : Bool) (t x e : ℝ) :
    forceData C ab b de t x e T=(0,0) := by
  unfold forceData
  rw [SoleEStress.force_T,force_T_secondary]
  simp

/-- This uses only the original seven weak witnesses. The lower-radius
bound needed for positivity is deliberately absent from necessity. -/
theorem necessary {C : SignedCycle} {ab : Fin 4} {b : Band} (de : Bool) {R M t : ℝ}
    (hab : ab=0 ∨ ab=2) (hR : 0≤R) (ht : t∈domain b)
    (hG : 0≤delta C.theta G) (hE : 0≤primary C de)
    (htotal : delta C.theta G+primary C de=t)
    (hs : ∀ i,(C.point i).Sorted) (hc : ∀ i,(C.point i).Contained (R^2))
    (hn : C.NormalAnchors) (ha : (C.point E).a≤M)
    (hsign : de=true → (C.point E).y≤0)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 2 0 (deOwner de) (ehOwner de) i)) :
    SoleSplitModel.value C ab b de R M t (delta C.theta G)≤0 := by
  have hx : delta C.theta G∈Icc 0 t := ⟨hG,by linarith⟩
  have he : primary C de∈Icc 0 t := ⟨hE,by linarith⟩
  have hxe : t-delta C.theta G=primary C de := by linarith
  obtain ⟨hk,hl,hc0,hg,heta⟩ := SoleECoefficients.positive ht
  obtain ⟨hn0,hp0,hr0⟩ := weights_positive ht hx he
  have hw : ∀ i,0≤SoleEStress.weights (n b t (delta C.theta G)) (k b t) (ell b t) (c b t)
      (c b t) (eMultiplier b de t (primary C de)) (hMultiplier b de (primary C de)) i := by
    intro i
    fin_cases i <;> cases de <;>
      simp [SoleEStress.weights,eMultiplier,hMultiplier,hn0.le,hk.le,hl.le,hc0.le,hp0.le,hr0.le]
  have hT := T_force C ab b de t (delta C.theta G) (primary C de)
  have hbound : ∀ i,work (forceData C ab b de t (delta C.theta G) (primary C de) i) (C.point i)≤
      (![work (forceData C ab b de t (delta C.theta G) (primary C de) H) (C.point H),
        k b t*sigma R (g b t)*Real.sin (delta C.theta G),
        work (forceData C ab b de t (delta C.theta G) (primary C de) A) (C.point A),
        work (forceData C ab b de t (delta C.theta G) (primary C de) B) (C.point B),0,
        work (forceData C ab b de t (delta C.theta G) (primary C de) D) (C.point D),
        eBound C b de R M t (primary C de)] : Vertex → ℝ) i := by
    intro i
    fin_cases i
    · exact le_rfl
    · exact G_work_le ab de hR ht hx (hs G) (hc G)
    · exact le_rfl
    · exact le_rfl
    · simp only [T] at hT
      simp [hT,work]
    · exact le_rfl
    · exact E_work_le ab de hR ht he (hs E) (hc E) ha hsign
  have hsep := weighted_separation_le hw hf hbound
  rw [value_eq_stress de R M hab ht hx hn,hxe]
  have hd := original_demand C b de t
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,Matrix.cons_val_zero,Matrix.cons_val_succ,
    add_zero] at hsep
  simp only [stress,anchorWork,hd]
  linarith

end SquaresInCircles.Eight.SoleSplitSupport
end
end
end

section
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.SolePositiveTEnvelope
open SoleTScalarModel SolePositiveTCoefficients SolePositiveTOrdinaryData
open PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryAngleConcentration
open SingleAngleConcavity SolePositiveTGrowth

theorem growth_pays (s : ScalarCase) {R t z : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (ht : t∈domain s.family) (hz : z∈Icc 0 t) (i : Fin 4) :
    (109/200)*(SolePositiveTCoefficients.cap s.family:ℝ)*(frameCap-t)≤
      pure (single s i) R (small s t z i) (large s t z i) (actualNu s t z i) frameCap-
        pure (single s i) R (small s t z i) (large s t z i) (actualNu s t z i) t := by
  rw [pure_eq s ht hz,pure_eq s ht hz]
  have hp := small_pos s ht hz i
  have hpq := small_le_large s t z i
  have hq := hp.trans_le hpq
  have hnu := (nu_between s t z i).2
  have hr := ratio_lower s ht hz i
  change ratio s.family t i*large s t z i≤ small s t z i at hr
  have hlo := larger_lower s ht hz i
  change (largeFloor s.family:ℝ)≤ large s t z i at hlo
  have hsmall := smaller_lower s ht hz i
  change (smallFloor s.family:ℝ)≤ small s t z i at hsmall
  have ht' := angle ht
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have hlen : 0≤ frameCap-t := by linarith [ht'.2]
  obtain ⟨cp,hcp⟩ : ∃ cp : ℝ,cp=(SolePositiveTCoefficients.cap s.family:ℝ) := ⟨_,rfl⟩
  rw [← hcp]
  cases hf : s.family
  · have hratio : (117/200)*large s t z i≤ small s t z i := by
      simp [ratio,hf] at hr
      nlinarith [mul_nonneg ht'.1 hq.le]
    have htg : t∈Icc 0 (1/5:ℝ) := by simpa [domain,hf,left,right] using ht
    have hfloor : 431/500≤ large s t z i := by simpa [largeFloor,hf] using hlo
    have hg := low_growth hR hQL hp hpq hratio hfloor hnu htg
    have hc : (109/200)*cp ≤ 121/200 := by rw [hcp,hf]; norm_num [cap]
    exact (mul_le_mul_of_nonneg_right hc hlen).trans hg
  · have hratio : (13/20)*large s t z i≤ small s t z i := by simpa [ratio,hf] using hr
    have htg : t∈Icc 0 (7/20:ℝ) := by
      have hu := ht.2
      norm_num [domain,hf,right] at hu
      exact ⟨ht'.1,hu⟩
    have hfloor : 923/1000≤ large s t z i := by simpa [largeFloor,hf] using hlo
    have hg := middle_growth hR hQL hp hpq hratio hfloor hnu htg
    have hc : (109/200)*cp ≤ 7/10 := by rw [hcp,hf]; norm_num [cap]
    exact (mul_le_mul_of_nonneg_right hc hlen).trans hg
  · have hratio : (18/25)*large s t z i≤ small s t z i := by simpa [ratio,hf] using hr
    have hg := high_growth hR hQL hQU hp hpq hratio hnu ht' hh ht'.2
    have hc : (109/200)*cp ≤ small s t z i := by
      norm_num [smallFloor,hf] at hsmall
      rw [hcp,hf]
      norm_num [cap]
      linarith
    exact (mul_le_mul_of_nonneg_right hc hlen).trans hg
  · have htg : t∈Icc 0 (7/20:ℝ) := by simpa [domain,hf,left,right] using ht
    by_cases hA : i=1
    · subst i
      obtain ⟨hs,hl,hn,hrA⟩ := DE_A_data s hf ht hz
      have hd := de_A s hf ht hz
      have hg := DE_A_growth hR hQL hQU hd.1
        (by rw [← hs,← hl]; exact hpq) hrA ht'
      rw [hs,hl,hn]
      have hc : (109/200)*cp ≤ 18/25 := by rw [hcp,hf]; norm_num [cap]
      exact (mul_le_mul_of_nonneg_right hc hlen).trans hg
    · by_cases hB : i=2
      · subst i
        have hratio : (5/8+27/100*t)*large s t z 2≤ small s t z 2 := by
          simpa [ratio,hf] using hr
        have hg := SolePositiveTDEChord.growth hR hQL hp hpq hratio
          (DE_B_large s hf ht hz) hnu htg
        have hc : (109/200)*cp ≤ 7/10 := by rw [hcp,hf]; norm_num [cap]
        exact (mul_le_mul_of_nonneg_right hc hlen).trans hg
      · have hi : i=0 ∨ i=3 := by fin_cases i <;> simp_all
        have hratio : (18/25)*large s t z i≤ small s t z i := by
          simpa [ratio,hf,hA,hB] using hr
        have hg := high_growth hR hQL hQU hp hpq hratio hnu ht' hh ht'.2
        have hsmall := DE_outer_small s hf ht hz i hi
        have hc : (109/200)*cp ≤ small s t z i := by
          rw [hcp,hf]
          norm_num [cap]
          linarith
        exact (mul_le_mul_of_nonneg_right hc hlen).trans hg
  · have hratio : (18/25)*large s t z i≤ small s t z i := by simpa [ratio,hf] using hr
    have hg := high_growth hR hQL hQU hp hpq hratio hnu ht' hh ht'.2
    have hc : (109/200)*cp ≤ small s t z i := by
      norm_num [smallFloor,hf] at hsmall
      rw [hcp,hf]
      norm_num [cap]
      linarith
    exact (mul_le_mul_of_nonneg_right hc hlen).trans hg


theorem same_block (s : ScalarCase) {R t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Icc 0 t) (i : Fin 4) (hi : single s i=false) :
    pure (single s i) R (small s t z i) (large s t z i) (actualNu s t z i) t≤
      M R (small s t z i) (large s t z i) t := by
  simp only [SingleAngleConcavity.pure,hi,Bool.false_eq_true,↓reduceIte]
  have hp := small_pos s ht hz i
  have hq := hp.trans_le (small_le_large s t z i)
  have hr := ratio_lower s ht hz i
  change ratio s.family t i*large s t z i≤ small s t z i at hr
  have ht' := angle ht
  cases hf : s.family
  · apply SolePositiveTSameBlock.EH_low hq.le _ ht'
    simpa [ratio,hf] using hr
  · apply SolePositiveTSameBlock.EH_middle hq.le _ ht'
    simpa [ratio,hf] using hr
  · apply M_ge_V hp.le hq.le _ ht'
    simp [ratio,hf] at hr
    linarith
  · have hindices : i=0 ∨ i=2 := by
      fin_cases i <;> simp_all [single,isDE]
    rcases hindices with rfl | rfl
    · apply M_ge_V hp.le hq.le _ ht'
      simp [ratio,hf] at hr
      linarith
    · apply SolePositiveTSameBlock.DE_low_B hq.le
        (by simp [ratio,hf] at hr; nlinarith [mul_nonneg ht'.1 hq.le])
      simpa [domain,hf,left,right] using ht
  · apply M_ge_V hp.le hq.le _ ht'
    simp [ratio,hf] at hr
    linarith


theorem ordinary_lower (s : ScalarCase) (P N : Fin 4 → ℝ) {R t z L : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (ht : t∈domain s.family) (hz : z∈Icc 0 t)
    (hP : ∀ i,0≤P i) (hN : ∀ i,0≤N i)
    (hbudget : (∑i,P i)≤frameCap-t) (hbalance : (∑i,N i)=t+∑i,P i)
    (hsingle : ∀ i,single s i=true → P i=0 ∨ N i=0)
    (hpure : ∀ i,L≤pure (single s i) R (small s t z i) (large s t z i) (actualNu s t z i) t) :
    L≤∑i,F (single s i) R (small s t z i) (large s t z i) (actualNu s t z i) (P i) (N i) := by
  have hhalf (i : Fin 4) : large s t z i≤2*small s t z i := half_ratio s ht hz i
  apply SingleAngleConcentration.lower_from_endpoints (single s) R
    (small s t z) (large s t z) (actualNu s t z) P N hR hQU
    (small_pos s ht hz) (small_le_large s t z) hhalf
    (fun i => (nu_between s t z i).1) hP hN (angle ht) hbudget hbalance hsingle hpure
  · intro i hi
    exact (hpure i).trans (same_block s ht hz i hi)
  · intro i j _
    have hlen : 0≤ frameCap-t := by linarith [(angle ht).2]
    have hU := OrdinaryPositiveEnvelope.U_lower hR hQU (small_pos s ht hz i)
      (small_le_large s t z i) (hhalf i)
      (show frameCap-t∈Icc 0 frameCap from ⟨hlen,by linarith [(angle ht).1]⟩)
    have hV := growth_pays s hR hQL hQU ht hz j
    have hcap := pair_upper s ht hz i
    change large s t z i≤(SolePositiveTCoefficients.cap s.family:ℝ) at hcap
    have hpay := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcap (by norm_num : (0:ℝ)≤109/200)) hlen
    linarith [hpure j]

end SquaresInCircles.Eight.SolePositiveTEnvelope
end
end
end

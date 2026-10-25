module

public import SquaresInCircles.Eight.Owners.Positive.ScalarPolynomials
public import SquaresInCircles.Eight.Owners.Sole.PositiveTGrowth

/-!
# Eight squares: the remaining DE low-family terminal chord

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

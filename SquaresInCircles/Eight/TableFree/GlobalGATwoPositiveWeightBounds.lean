module

public import SquaresInCircles.Eight.TableFree.GlobalGATwoPositiveHighPolynomial
public import SquaresInCircles.Eight.TableFree.PolynomialCertificates

/-!
# The explicit high split family stays in its analytic domain

Endpoint quotients retain the monotonic directions of the cubic
weights.  The A/T auxiliary masses have a common positive lower
bound.  The B coefficient cap is proved on the whole interval by
one completed square, including its interior minimum.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalGA.TwoPositive.Certificate

open Polynomial WholeIntervalPolynomial
open PositiveTD.Certificate (L h)

def kRight : ℚ[X] := (highK-C (highK.eval h)).divByMonic (X-C h)
def lRight : ℚ[X] := -((highL-C (highL.eval h)).divByMonic (X-C h))
def cLeft : ℚ[X] := -((highC-C (highC.eval L)).divByMonic (X-C L))
def cRight : ℚ[X] := -((highC-C (highC.eval h)).divByMonic (X-C h))
def rangePoly : Fin 7→ℚ[X] :=
  ![highK,kRight,lRight,cLeft,cRight,highC-C (9/10)*highL,C (11/10)*highL-highC]
def rangeReserve : Fin 7→ℚ := ![669/1000,1/10,1/100,1/100,1/100,2/25,2/25]
def mass (e : Endpoint) : Fin 7→ℚ[X] :=
  ![highRH,highRG,highRD,highRB e,highRHminus,highRGminus,highRBminus e]
def gapCentered : ℚ[X] := DirectedPowerBounds.shift (13/30) highQGap
def gapCurvature : ℚ := gapCentered.coeff 2-PowerTailBounds.norm gapCentered 3 6 (4/15)
def gapReserve : ℚ := gapCentered.coeff 0-(gapCentered.coeff 1)^2/(4*gapCurvature)


/-! ## Certificate helpers -/

section r47
open WholeIntervalPolynomial.Certificate
open PositiveTD.Certificate (C4 S5)

private def r47_k (n : ℤ) (d : ℕ) : Scaled := ⟨[n],d⟩

private theorem r47_rep_frac {q : ℚ} {n : ℤ} {d : ℕ} (hd : d≠0) (hq : q=n/d) :
    (r47_k n d).Rep (C q) := by
  unfold r47_k Scaled.Rep
  simp only [toPoly,mul_zero,add_zero,← map_mul]
  congr 1
  rw [hq]
  field_simp

private theorem r47_lt_div {ρ : ℚ} {num Z M : ℤ} {den : ℕ} (hρ : ρ=num/den) (hden : 0<den)
    (hM : 0<M) (hlt : num*M<2*den*Z) : ρ<(Z:ℚ)/((M:ℚ)/2) := by
  have hd : (0:ℚ)<den := by exact_mod_cast hden
  have hM' : (0:ℚ)<M := by exact_mod_cast hM
  have hq : ((num*M:ℤ):ℚ)<((2*den*Z:ℤ):ℚ) := by exact_mod_cast hlt
  push_cast at hq
  rw [lt_div_iff₀ (by positivity),hρ,div_mul_eq_mul_div,div_lt_iff₀ hd]
  linarith

/-- Centering on `[L,h]=[1/6,7/10]`: midpoint `13/30`, half-width `8/30`. -/
private theorem r47_center {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) :
    (c.center 1 30 13 8).Rep (centered L h p) :=
  hc.centered 1 30 13 8 (by norm_num) (by norm_num) (by norm_num)

private theorem r47_id {c : Scaled} {p : ℚ[X]} (hc : c.Rep p)
    (hs : (c.center 1 30 13 8).s≠0) {D : ℕ} (hl : (c.center 1 30 13 8).l.length≤D+1) :
    centered L h p=expansion D (centered L h p) :=
  (r47_center hc).eq_expansion hs hl

private theorem r47_low {c : Scaled} {p : ℚ[X]} (hc : c.Rep p)
    (hs : (c.center 1 30 13 8).s≠0) {D : ℕ} (hl : (c.center 1 30 13 8).l.length≤D+1)
    {ρ : ℚ} {num : ℤ} {den : ℕ} (hρ : ρ=num/den) (hden : 0<den)
    (hlt : num*(((c.center 1 30 13 8).s*2^(c.center 1 30 13 8).l.length : ℕ):ℤ)<
      2*den*lowerZ D (fun j => (chebList (c.center 1 30 13 8).l).getD j 0)) :
    ρ<lowerOn D L h p := by
  rw [lowerOn_eq_of_rep (r47_center hc) hs hl]
  have he : ((c.center 1 30 13 8).s:ℚ)*2^(c.center 1 30 13 8).l.length/2=
      ((((c.center 1 30 13 8).s*2^(c.center 1 30 13 8).l.length : ℕ):ℤ):ℚ)/2 := by
    push_cast
    ring
  rw [he]
  exact r47_lt_div hρ hden (by have := Nat.pos_of_ne_zero hs; positivity) hlt

/-- `p - p(a)` is divisible by `X - a`. -/
private theorem r47_root (p : ℚ[X]) (a : ℚ) :
    p=C (p.eval a)+(X-C a)*((p-C (p.eval a)) /ₘ (X-C a)) := by
  rw [(mul_divByMonic_eq_iff_isRoot (p := p-C (p.eval a)) (a := a)).2 (by simp [IsRoot])]
  ring

private def r47_pKR : ℚ[X] := C (149089/375000)-C (6391/12500)*X+C (527/1250)*X^2
private def r47_pLR : ℚ[X] := C (306/3125)+C (1047/1250)*X-C (639/500)*X^2
private def r47_pCL : ℚ[X] := C (48527/30000)*X-C (75461/360000)-C (14069/10000)*X^2
private def r47_pCR : ℚ[X] := C (383537/3000000)+C (43361/50000)*X-C (14069/10000)*X^2

private theorem r47_kRight : kRight=r47_pKR := by
  have hv : highK.eval h=7104683/8437500 := by norm_num [highK,t]
  have hid : highK-C (7104683/8437500)=(X-C h)*r47_pKR := by
    apply Polynomial.funext
    intro r
    simp only [highK,t,r47_pKR,eval_sub,eval_add,eval_mul,eval_C,eval_X,eval_pow,L,h]
    ring
  rw [kRight,hv,hid,mul_divByMonic_cancel_left _ (monic_X_sub_C h)]

private theorem r47_lRight : lRight=r47_pLR := by
  have hv : highL.eval h=27883/31250 := by norm_num [highL,t]
  have hid : highL-C (27883/31250)=(X-C h)*(-r47_pLR) := by
    apply Polynomial.funext
    intro r
    simp only [highL,t,r47_pLR,eval_sub,eval_add,eval_mul,eval_C,eval_X,eval_pow,eval_neg,
      eval_one,L,h]
    ring
  rw [lRight,hv,hid,mul_divByMonic_cancel_left _ (monic_X_sub_C h),neg_neg]

private theorem r47_cLeft : cLeft=r47_pCL := by
  have hv : highC.eval L=10163/10000 := by norm_num [highC,t]
  have hid : highC-C (10163/10000)=(X-C L)*(-r47_pCL) := by
    apply Polynomial.funext
    intro r
    simp only [highC,t,r47_pCL,eval_sub,eval_add,eval_mul,eval_C,eval_X,eval_pow,eval_neg,L]
    ring
  rw [cLeft,hv,hid,mul_divByMonic_cancel_left _ (monic_X_sub_C L),neg_neg]

private theorem r47_cRight : cRight=r47_pCR := by
  have hv : highC.eval h=30100693/33750000 := by norm_num [highC,t]
  have hid : highC-C (30100693/33750000)=(X-C h)*(-r47_pCR) := by
    apply Polynomial.funext
    intro r
    simp only [highC,t,r47_pCR,eval_sub,eval_add,eval_mul,eval_C,eval_X,eval_pow,eval_neg,L,h]
    ring
  rw [cRight,hv,hid,mul_divByMonic_cancel_left _ (monic_X_sub_C h),neg_neg]

private def r47_cT : Scaled :=
  (Scaled.var).sub (r47_k (1) 6)
private theorem r47_rT : r47_cT.Rep t :=
  (Scaled.rep_var).sub (r47_rep_frac (q := 1/6) (n := 1) (d := 6) (by norm_num) (by norm_num))

private def r47_cK : Scaled :=
  (((r47_k (1673) 2500).add ((r47_k (2609) 5000).mul (r47_cT))).sub ((r47_k (1489) 2500).mul ((r47_cT).pow 2))).add ((r47_k (527) 1250).mul ((r47_cT).pow 3))
private theorem r47_rK : r47_cK.Rep highK :=
  (((r47_rep_frac (q := 1673/2500) (n := 1673) (d := 2500) (by norm_num) (by norm_num)).add ((r47_rep_frac (q := 2609/5000) (n := 2609) (d := 5000) (by norm_num) (by norm_num)).mul (r47_rT))).sub ((r47_rep_frac (q := 1489/2500) (n := 1489) (d := 2500) (by norm_num) (by norm_num)).mul ((r47_rT).pow 2))).add ((r47_rep_frac (q := 527/1250) (n := 527) (d := 1250) (by norm_num) (by norm_num)).mul ((r47_rT).pow 3))

private def r47_cL : Scaled :=
  (((Scaled.ofNat 1).add ((r47_k (7) 400).mul (r47_cT))).sub ((r47_k (2733) 2500).mul ((r47_cT).pow 2))).add ((r47_k (639) 500).mul ((r47_cT).pow 3))
private theorem r47_rL : r47_cL.Rep highL :=
  (((Scaled.rep_one).add ((r47_rep_frac (q := 7/400) (n := 7) (d := 400) (by norm_num) (by norm_num)).mul (r47_rT))).sub ((r47_rep_frac (q := 2733/2500) (n := 2733) (d := 2500) (by norm_num) (by norm_num)).mul ((r47_rT).pow 2))).add ((r47_rep_frac (q := 639/500) (n := 639) (d := 500) (by norm_num) (by norm_num)).mul ((r47_rT).pow 3))

private def r47_cC : Scaled :=
  (((r47_k (10163) 10000).sub ((r47_k (209) 10000).mul (r47_cT))).sub ((r47_k (5743) 5000).mul ((r47_cT).pow 2))).add ((r47_k (14069) 10000).mul ((r47_cT).pow 3))
private theorem r47_rC : r47_cC.Rep highC :=
  (((r47_rep_frac (q := 10163/10000) (n := 10163) (d := 10000) (by norm_num) (by norm_num)).sub ((r47_rep_frac (q := 209/10000) (n := 209) (d := 10000) (by norm_num) (by norm_num)).mul (r47_rT))).sub ((r47_rep_frac (q := 5743/5000) (n := 5743) (d := 5000) (by norm_num) (by norm_num)).mul ((r47_rT).pow 2))).add ((r47_rep_frac (q := 14069/10000) (n := 14069) (d := 10000) (by norm_num) (by norm_num)).mul ((r47_rT).pow 3))

private def r47_cC4 : Scaled :=
  ((Scaled.ofNat 1).sub ((r47_k (1) 2).mul ((Scaled.var).pow 2))).add ((r47_k (1) 24).mul ((Scaled.var).pow 4))
private theorem r47_rC4 : r47_cC4.Rep C4 :=
  ((Scaled.rep_one).sub ((r47_rep_frac (q := 1/2) (n := 1) (d := 2) (by norm_num) (by norm_num)).mul ((Scaled.rep_var).pow 2))).add ((r47_rep_frac (q := 1/24) (n := 1) (d := 24) (by norm_num) (by norm_num)).mul ((Scaled.rep_var).pow 4))

private def r47_cS5 : Scaled :=
  ((Scaled.var).sub ((r47_k (1) 6).mul ((Scaled.var).pow 3))).add ((r47_k (1) 120).mul ((Scaled.var).pow 5))
private theorem r47_rS5 : r47_cS5.Rep S5 :=
  ((Scaled.rep_var).sub ((r47_rep_frac (q := 1/6) (n := 1) (d := 6) (by norm_num) (by norm_num)).mul ((Scaled.rep_var).pow 3))).add ((r47_rep_frac (q := 1/120) (n := 1) (d := 120) (by norm_num) (by norm_num)).mul ((Scaled.rep_var).pow 5))

private def r47_cMu : Scaled :=
  (r47_cC).mul ((r47_cC4).add ((r47_k (293) 1000).mul (r47_cS5)))
private theorem r47_rMu : r47_cMu.Rep (highMu .atT) :=
  (r47_rC).mul ((r47_rC4).add ((r47_rep_frac (q := 293/1000) (n := 293) (d := 1000) (by norm_num) (by norm_num)).mul (r47_rS5)))

private def r47_cQ : Scaled :=
  (r47_cL).add ((r47_k (3) 20).mul ((r47_k (7) 10).sub (Scaled.var)))
private theorem r47_rQ : r47_cQ.Rep highQ :=
  (r47_rL).add ((r47_rep_frac (q := 3/20) (n := 3) (d := 20) (by norm_num) (by norm_num)).mul ((r47_rep_frac (q := 7/10) (n := 7) (d := 10) (by norm_num) (by norm_num)).sub (Scaled.rep_var)))

private def r47_cKR : Scaled :=
  ((r47_k (149089) 375000).sub ((r47_k (6391) 12500).mul (Scaled.var))).add ((r47_k (527) 1250).mul ((Scaled.var).pow 2))
private theorem r47_rKR : r47_cKR.Rep r47_pKR :=
  ((r47_rep_frac (q := 149089/375000) (n := 149089) (d := 375000) (by norm_num) (by norm_num)).sub ((r47_rep_frac (q := 6391/12500) (n := 6391) (d := 12500) (by norm_num) (by norm_num)).mul (Scaled.rep_var))).add ((r47_rep_frac (q := 527/1250) (n := 527) (d := 1250) (by norm_num) (by norm_num)).mul ((Scaled.rep_var).pow 2))

private def r47_cLR : Scaled :=
  ((r47_k (306) 3125).add ((r47_k (1047) 1250).mul (Scaled.var))).sub ((r47_k (639) 500).mul ((Scaled.var).pow 2))
private theorem r47_rLR : r47_cLR.Rep r47_pLR :=
  ((r47_rep_frac (q := 306/3125) (n := 306) (d := 3125) (by norm_num) (by norm_num)).add ((r47_rep_frac (q := 1047/1250) (n := 1047) (d := 1250) (by norm_num) (by norm_num)).mul (Scaled.rep_var))).sub ((r47_rep_frac (q := 639/500) (n := 639) (d := 500) (by norm_num) (by norm_num)).mul ((Scaled.rep_var).pow 2))

private def r47_cCL : Scaled :=
  (((r47_k (48527) 30000).mul (Scaled.var)).sub (r47_k (75461) 360000)).sub ((r47_k (14069) 10000).mul ((Scaled.var).pow 2))
private theorem r47_rCL : r47_cCL.Rep r47_pCL :=
  (((r47_rep_frac (q := 48527/30000) (n := 48527) (d := 30000) (by norm_num) (by norm_num)).mul (Scaled.rep_var)).sub (r47_rep_frac (q := 75461/360000) (n := 75461) (d := 360000) (by norm_num) (by norm_num))).sub ((r47_rep_frac (q := 14069/10000) (n := 14069) (d := 10000) (by norm_num) (by norm_num)).mul ((Scaled.rep_var).pow 2))

private def r47_cCR : Scaled :=
  ((r47_k (383537) 3000000).add ((r47_k (43361) 50000).mul (Scaled.var))).sub ((r47_k (14069) 10000).mul ((Scaled.var).pow 2))
private theorem r47_rCR : r47_cCR.Rep r47_pCR :=
  ((r47_rep_frac (q := 383537/3000000) (n := 383537) (d := 3000000) (by norm_num) (by norm_num)).add ((r47_rep_frac (q := 43361/50000) (n := 43361) (d := 50000) (by norm_num) (by norm_num)).mul (Scaled.rep_var))).sub ((r47_rep_frac (q := 14069/10000) (n := 14069) (d := 10000) (by norm_num) (by norm_num)).mul ((Scaled.rep_var).pow 2))

private def r47_cR5 : Scaled :=
  (r47_cC).sub ((r47_k (9) 10).mul (r47_cL))
private theorem r47_rR5 : r47_cR5.Rep (highC-C (9/10)*highL) :=
  (r47_rC).sub ((r47_rep_frac (q := 9/10) (n := 9) (d := 10) (by norm_num) (by norm_num)).mul (r47_rL))

private def r47_cR6 : Scaled :=
  ((r47_k (11) 10).mul (r47_cL)).sub (r47_cC)
private theorem r47_rR6 : r47_cR6.Rep (C (11/10)*highL-highC) :=
  ((r47_rep_frac (q := 11/10) (n := 11) (d := 10) (by norm_num) (by norm_num)).mul (r47_rL)).sub (r47_rC)

private def r47_cRH : Scaled :=
  (r47_k (4) 5).add ((r47_k (3) 5).mul (r47_cK))
private theorem r47_rRH : r47_cRH.Rep highRH :=
  (r47_rep_frac (q := 4/5) (n := 4) (d := 5) (by norm_num) (by norm_num)).add ((r47_rep_frac (q := 3/5) (n := 3) (d := 5) (by norm_num) (by norm_num)).mul (r47_rK))

private def r47_cRG : Scaled :=
  ((r47_k (31) 50).mul (r47_cK)).add ((r47_k (3923) 5000).mul (r47_cL))
private theorem r47_rRG : r47_cRG.Rep highRG :=
  ((r47_rep_frac (q := 31/50) (n := 31) (d := 50) (by norm_num) (by norm_num)).mul (r47_rK)).add ((r47_rep_frac (q := 3923/5000) (n := 3923) (d := 5000) (by norm_num) (by norm_num)).mul (r47_rL))

private def r47_cRD : Scaled :=
  (r47_k (18) 25).add ((r47_k (347) 500).mul (r47_cC))
private theorem r47_rRD : r47_cRD.Rep highRD :=
  (r47_rep_frac (q := 18/25) (n := 18) (d := 25) (by norm_num) (by norm_num)).add ((r47_rep_frac (q := 347/500) (n := 347) (d := 500) (by norm_num) (by norm_num)).mul (r47_rC))

private def r47_cRBT : Scaled :=
  (r47_k (7071) 10000).mul ((r47_cL).add (r47_cMu))
private theorem r47_rRBT : r47_cRBT.Rep (highRB .atT) :=
  (r47_rep_frac (q := 7071/10000) (n := 7071) (d := 10000) (by norm_num) (by norm_num)).mul ((r47_rL).add (r47_rMu))

private def r47_cRBA : Scaled :=
  (r47_k (7071) 10000).mul ((r47_cL).add (r47_cC))
private theorem r47_rRBA : r47_cRBA.Rep (highRB .atA) :=
  (r47_rep_frac (q := 7071/10000) (n := 7071) (d := 10000) (by norm_num) (by norm_num)).mul ((r47_rL).add (r47_rC))

private def r47_cRHm : Scaled :=
  ((r47_k (89) 100).mul (r47_cC4)).add ((r47_k (57) 125).mul ((r47_cK).sub (r47_cS5)))
private theorem r47_rRHm : r47_cRHm.Rep highRHminus :=
  ((r47_rep_frac (q := 89/100) (n := 89) (d := 100) (by norm_num) (by norm_num)).mul (r47_rC4)).add ((r47_rep_frac (q := 57/125) (n := 57) (d := 125) (by norm_num) (by norm_num)).mul ((r47_rK).sub (r47_rS5)))

private def r47_cRGm : Scaled :=
  (((r47_k (89) 100).mul (r47_cL)).mul (r47_cC4)).add ((r47_k (57) 125).mul ((r47_cK).sub ((r47_cL).mul (r47_cS5))))
private theorem r47_rRGm : r47_cRGm.Rep highRGminus :=
  (((r47_rep_frac (q := 89/100) (n := 89) (d := 100) (by norm_num) (by norm_num)).mul (r47_rL)).mul (r47_rC4)).add ((r47_rep_frac (q := 57/125) (n := 57) (d := 125) (by norm_num) (by norm_num)).mul ((r47_rK).sub ((r47_rL).mul (r47_rS5))))

private def r47_cRBmT : Scaled :=
  (((r47_k (83) 100).mul (r47_cL)).mul (r47_cC4)).add ((r47_k (14) 25).mul ((r47_cMu).sub ((r47_cL).mul (r47_cS5))))
private theorem r47_rRBmT : r47_cRBmT.Rep (highRBminus .atT) :=
  (((r47_rep_frac (q := 83/100) (n := 83) (d := 100) (by norm_num) (by norm_num)).mul (r47_rL)).mul (r47_rC4)).add ((r47_rep_frac (q := 14/25) (n := 14) (d := 25) (by norm_num) (by norm_num)).mul ((r47_rMu).sub ((r47_rL).mul (r47_rS5))))

private def r47_cRBmA : Scaled :=
  (((r47_k (83) 100).mul (r47_cL)).mul (r47_cC4)).add ((r47_k (14) 25).mul ((r47_cC).sub ((r47_cL).mul (r47_cS5))))
private theorem r47_rRBmA : r47_cRBmA.Rep (highRBminus .atA) :=
  (((r47_rep_frac (q := 83/100) (n := 83) (d := 100) (by norm_num) (by norm_num)).mul (r47_rL)).mul (r47_rC4)).add ((r47_rep_frac (q := 14/25) (n := 14) (d := 25) (by norm_num) (by norm_num)).mul ((r47_rC).sub ((r47_rL).mul (r47_rS5))))

private def r47_cQC : Scaled :=
  (r47_cQ).sub (r47_cC)
private theorem r47_rQC : r47_cQC.Rep (highQ-highC) :=
  (r47_rQ).sub (r47_rC)

private def r47_cGap : Scaled :=
  (r47_cQ).sub ((r47_cC).mul ((r47_cC4).add ((r47_k (293) 1000).mul (r47_cS5))))
private theorem r47_rGap : r47_cGap.Rep highQGap :=
  (r47_rQ).sub ((r47_rC).mul ((r47_rC4).add ((r47_rep_frac (q := 293/1000) (n := 293) (d := 1000) (by norm_num) (by norm_num)).mul (r47_rS5))))


private theorem r47_rKRight : r47_cKR.Rep kRight := by rw [r47_kRight]; exact r47_rKR
private theorem r47_rLRight : r47_cLR.Rep lRight := by rw [r47_lRight]; exact r47_rLR
private theorem r47_rCLeft : r47_cCL.Rep cLeft := by rw [r47_cLeft]; exact r47_rCL
private theorem r47_rCRight : r47_cCR.Rep cRight := by rw [r47_cRight]; exact r47_rCR

private theorem r47_cast_lt {a b : ℚ} {c : ℝ} (hab : a<b) (hc : (b:ℝ)=c) : (a:ℝ)<c :=
  hc ▸ Rat.cast_lt.mpr hab

private theorem r47_lt_cast {a b : ℚ} {c : ℝ} (hab : a<b) (hc : (a:ℝ)=c) : c<(b:ℝ) :=
  hc ▸ Rat.cast_lt.mpr hab

private theorem r47_mem {z : ℝ} (hz : z∈Icc (1/6:ℝ) (7/10:ℝ)) : z∈Icc (L:ℝ) (h:ℝ) := by
  simp only [L,h]
  push_cast
  exact hz

/-- `gapCentered` is the recentring of `highQGap` at `13/30` with half-width one. -/
private theorem r47_gap_centered : gapCentered=centered (-17/30) (43/30) highQGap := by
  simp only [gapCentered,DirectedPowerBounds.shift,centered,affine]
  congr 1
  norm_num

private theorem r47_rGapC : (r47_cGap.center 1 30 13 30).Rep gapCentered := by
  rw [r47_gap_centered]
  exact r47_rGap.centered 1 30 13 30 (by norm_num) (by norm_num) (by norm_num)

private theorem r47_gap_list : (r47_cGap.center 1 30 13 30).l=
    [152510652260952065054842237747200000000000000000000000,1176975157352626588763634794496000000000000000000000000,9710529435340682462097372610560000000000000000000000000,-9224475516833305404484111564800000000000000000000000000,4171342304465857687566090240000000000000000000000000000,18210399438438800914816696320000000000000000000000000000,-924444453641786098148966400000000000000000000000000000,-1629000506123127339024384000000000000000000000000000000,-84777066429306079150080000000000000000000000000000000] := by
  decide +kernel

private theorem r47_gap_scale : (r47_cGap.center 1 30 13 30).s=
    24679069470425088000000000000000000000000000000000000000 := by
  decide +kernel

private theorem r47_gap_coeff (i : ℕ) :
    gapCentered.coeff i=(([152510652260952065054842237747200000000000000000000000,1176975157352626588763634794496000000000000000000000000,9710529435340682462097372610560000000000000000000000000,-9224475516833305404484111564800000000000000000000000000,4171342304465857687566090240000000000000000000000000000,18210399438438800914816696320000000000000000000000000000,-924444453641786098148966400000000000000000000000000000,-1629000506123127339024384000000000000000000000000000000,-84777066429306079150080000000000000000000000000000000] : List ℤ).getD i 0:ℚ)/(24679069470425088000000000000000000000000000000000000000:ℕ) := by
  rw [r47_rGapC.coeff (by rw [r47_gap_scale]; norm_num) i,r47_gap_list,r47_gap_scale]

private theorem r47_split8 {p : ℚ[X]} (hp : p.natDegree≤8) :
    p=C (p.coeff 0)+C (p.coeff 1)*X+C (p.coeff 2)*X^2+PowerTailBounds.tail p 3 6 := by
  conv_lhs => rw [p.as_sum_range_C_mul_X_pow' (n:=9) (by omega)]
  simp only [PowerTailBounds.tail,Finset.sum_range_succ,Finset.sum_range_zero,Fin.sum_univ_succ,
    Fin.sum_univ_zero,Fin.val_zero,Fin.val_succ]
  ring

private theorem r47_idRH :
    centered L h highRH=expansion 8 (centered L h highRH) :=
  r47_id r47_rRH (by decide +kernel) (by decide +kernel)

private theorem r47_idRG :
    centered L h highRG=expansion 8 (centered L h highRG) :=
  r47_id r47_rRG (by decide +kernel) (by decide +kernel)

private theorem r47_idRD :
    centered L h highRD=expansion 8 (centered L h highRD) :=
  r47_id r47_rRD (by decide +kernel) (by decide +kernel)

private theorem r47_idRHm :
    centered L h highRHminus=expansion 8 (centered L h highRHminus) :=
  r47_id r47_rRHm (by decide +kernel) (by decide +kernel)

private theorem r47_idRGm :
    centered L h highRGminus=expansion 8 (centered L h highRGminus) :=
  r47_id r47_rRGm (by decide +kernel) (by decide +kernel)

private theorem r47_idRBT :
    centered L h (highRB .atT)=expansion 8 (centered L h (highRB .atT)) :=
  r47_id r47_rRBT (by decide +kernel) (by decide +kernel)

private theorem r47_idRBA :
    centered L h (highRB .atA)=expansion 8 (centered L h (highRB .atA)) :=
  r47_id r47_rRBA (by decide +kernel) (by decide +kernel)

private theorem r47_idRBmT :
    centered L h (highRBminus .atT)=expansion 8 (centered L h (highRBminus .atT)) :=
  r47_id r47_rRBmT (by decide +kernel) (by decide +kernel)

private theorem r47_idRBmA :
    centered L h (highRBminus .atA)=expansion 8 (centered L h (highRBminus .atA)) :=
  r47_id r47_rRBmA (by decide +kernel) (by decide +kernel)

private theorem r47_lowRH : (7/10:ℚ)<lowerOn 8 L h highRH :=
  r47_low r47_rRH (by decide +kernel) (by decide +kernel) (ρ := 7/10) (num := 7) (den := 10)
      (by norm_num) (by norm_num) (by decide +kernel)

private theorem r47_lowRG : (7/10:ℚ)<lowerOn 8 L h highRG :=
  r47_low r47_rRG (by decide +kernel) (by decide +kernel) (ρ := 7/10) (num := 7) (den := 10)
      (by norm_num) (by norm_num) (by decide +kernel)

private theorem r47_lowRD : (7/10:ℚ)<lowerOn 8 L h highRD :=
  r47_low r47_rRD (by decide +kernel) (by decide +kernel) (ρ := 7/10) (num := 7) (den := 10)
      (by norm_num) (by norm_num) (by decide +kernel)

private theorem r47_lowRHm : (7/10:ℚ)<lowerOn 8 L h highRHminus :=
  r47_low r47_rRHm (by decide +kernel) (by decide +kernel) (ρ := 7/10) (num := 7) (den := 10)
      (by norm_num) (by norm_num) (by decide +kernel)

private theorem r47_lowRGm : (7/10:ℚ)<lowerOn 8 L h highRGminus :=
  r47_low r47_rRGm (by decide +kernel) (by decide +kernel) (ρ := 7/10) (num := 7) (den := 10)
      (by norm_num) (by norm_num) (by decide +kernel)

private theorem r47_lowRBT : (7/10:ℚ)<lowerOn 8 L h (highRB .atT) :=
  r47_low r47_rRBT (by decide +kernel) (by decide +kernel) (ρ := 7/10) (num := 7) (den := 10)
      (by norm_num) (by norm_num) (by decide +kernel)

private theorem r47_lowRBA : (7/10:ℚ)<lowerOn 8 L h (highRB .atA) :=
  r47_low r47_rRBA (by decide +kernel) (by decide +kernel) (ρ := 7/10) (num := 7) (den := 10)
      (by norm_num) (by norm_num) (by decide +kernel)

private theorem r47_lowRBmT : (7/10:ℚ)<lowerOn 8 L h (highRBminus .atT) :=
  r47_low r47_rRBmT (by decide +kernel) (by decide +kernel) (ρ := 7/10) (num := 7) (den := 10)
      (by norm_num) (by norm_num) (by decide +kernel)

private theorem r47_lowRBmA : (7/10:ℚ)<lowerOn 8 L h (highRBminus .atA) :=
  r47_low r47_rRBmA (by decide +kernel) (by decide +kernel) (ρ := 7/10) (num := 7) (den := 10)
      (by norm_num) (by norm_num) (by decide +kernel)

private theorem r47_id3K :
    centered L h highK=expansion 3 (centered L h highK) :=
  r47_id r47_rK (by decide +kernel) (by decide +kernel)

private theorem r47_low3K : (669/1000:ℚ)<lowerOn 3 L h highK :=
  r47_low r47_rK (by decide +kernel) (by decide +kernel) (num := 669) (den := 1000)
    (by norm_num) (by norm_num) (by decide +kernel)

private theorem r47_id3KRight :
    centered L h kRight=expansion 3 (centered L h kRight) :=
  r47_id r47_rKRight (by decide +kernel) (by decide +kernel)

private theorem r47_low3KRight : (1/10:ℚ)<lowerOn 3 L h kRight :=
  r47_low r47_rKRight (by decide +kernel) (by decide +kernel) (num := 1) (den := 10)
    (by norm_num) (by norm_num) (by decide +kernel)

private theorem r47_id3LRight :
    centered L h lRight=expansion 3 (centered L h lRight) :=
  r47_id r47_rLRight (by decide +kernel) (by decide +kernel)

private theorem r47_low3LRight : (1/100:ℚ)<lowerOn 3 L h lRight :=
  r47_low r47_rLRight (by decide +kernel) (by decide +kernel) (num := 1) (den := 100)
    (by norm_num) (by norm_num) (by decide +kernel)

private theorem r47_id3CLeft :
    centered L h cLeft=expansion 3 (centered L h cLeft) :=
  r47_id r47_rCLeft (by decide +kernel) (by decide +kernel)

private theorem r47_low3CLeft : (1/100:ℚ)<lowerOn 3 L h cLeft :=
  r47_low r47_rCLeft (by decide +kernel) (by decide +kernel) (num := 1) (den := 100)
    (by norm_num) (by norm_num) (by decide +kernel)

private theorem r47_id3CRight :
    centered L h cRight=expansion 3 (centered L h cRight) :=
  r47_id r47_rCRight (by decide +kernel) (by decide +kernel)

private theorem r47_low3CRight : (1/100:ℚ)<lowerOn 3 L h cRight :=
  r47_low r47_rCRight (by decide +kernel) (by decide +kernel) (num := 1) (den := 100)
    (by norm_num) (by norm_num) (by decide +kernel)

private theorem r47_id3R5 :
    centered L h (highC-C (9/10)*highL)=expansion 3 (centered L h (highC-C (9/10)*highL)) :=
  r47_id r47_rR5 (by decide +kernel) (by decide +kernel)

private theorem r47_low3R5 : (2/25:ℚ)<lowerOn 3 L h (highC-C (9/10)*highL) :=
  r47_low r47_rR5 (by decide +kernel) (by decide +kernel) (num := 2) (den := 25)
    (by norm_num) (by norm_num) (by decide +kernel)

private theorem r47_id3R6 :
    centered L h (C (11/10)*highL-highC)=expansion 3 (centered L h (C (11/10)*highL-highC)) :=
  r47_id r47_rR6 (by decide +kernel) (by decide +kernel)

private theorem r47_low3R6 : (2/25:ℚ)<lowerOn 3 L h (C (11/10)*highL-highC) :=
  r47_low r47_rR6 (by decide +kernel) (by decide +kernel) (num := 2) (den := 25)
    (by norm_num) (by norm_num) (by decide +kernel)

end r47
theorem range_identities (i : Fin 7) :
    centered L h (rangePoly i)=expansion 3 (centered L h (rangePoly i)) := by
  fin_cases i
  · exact r47_id3K
  · exact r47_id3KRight
  · exact r47_id3LRight
  · exact r47_id3CLeft
  · exact r47_id3CRight
  · exact r47_id3R5
  · exact r47_id3R6

theorem range_reserves (i : Fin 7) :
    rangeReserve i<lowerOn 3 L h (rangePoly i) := by
  fin_cases i
  · exact r47_low3K
  · exact r47_low3KRight
  · exact r47_low3LRight
  · exact r47_low3CLeft
  · exact r47_low3CRight
  · exact r47_low3R5
  · exact r47_low3R6

theorem range_lower (i : Fin 7) {z : ℝ} (hz : z∈Icc (1/6:ℝ) (7/10:ℝ)) :
    (rangeReserve i:ℝ)<aeval z (rangePoly i) :=
  positive_on_interval (by norm_num [L,h]) (range_identities i) (range_reserves i) (r47_mem hz)

theorem weight_endpoint_identities :
    highK=C (highK.eval h)+(X-C h)*kRight ∧
    highL=C (highL.eval h)+(C h-X)*lRight ∧
    highC=C (highC.eval L)-(X-C L)*cLeft ∧
    highC=C (highC.eval h)+(C h-X)*cRight := by
  refine ⟨r47_root highK h,?_,?_,?_⟩
  · have e := r47_root highL h
    rw [lRight]
    linear_combination e
  · have e := r47_root highC L
    rw [cLeft]
    linear_combination e
  · have e := r47_root highC h
    rw [cRight]
    linear_combination e

theorem weight_endpoint_reserves :
    highK.eval h<(843/1000:ℚ) ∧ (89/100:ℚ)<highL.eval h ∧
      (89/100:ℚ)<highC.eval h ∧ highC.eval L=10163/10000 := by
  refine ⟨?_,?_,?_,?_⟩ <;> norm_num [highK,highL,highC,t]

theorem highL_upper {z : ℝ} (hz : z∈Icc (1/6:ℝ) (7/10:ℝ)) :
    aeval z highL<(5001/5000:ℝ) := by
  let u : ℝ := z-1/6
  have hu : u∈Icc 0 (8/15:ℝ) := ⟨by dsimp [u]; linarith [hz.1],
    by dsimp [u]; linarith [hz.2]⟩
  have hcube : u^3≤(8/15)*u^2 := by
    nlinarith [mul_le_mul_of_nonneg_right hu.2 (sq_nonneg u)]
  have he : aeval z highL=1+(7/400)*u-(2733/2500)*u^2+(639/500)*u^3 := by
    simp [highL,t,u,L]
  rw [he]
  nlinarith [sq_nonneg (u-(7/400)/(2*(1029/2500)))]

/-- Every inequality holds throughout the one high interval. -/
theorem high_ranges {z : ℝ} (hz : z∈Icc (1/6:ℝ) (7/10:ℝ)) :
    (669/1000:ℝ)<aeval z highK ∧ aeval z highK<843/1000 ∧
      (89/100:ℝ)<aeval z highL ∧ aeval z highL<5001/5000 ∧
      (89/100:ℝ)<aeval z highC ∧ aeval z highC≤10163/10000 ∧
      (9/10)*aeval z highL<aeval z highC ∧
      aeval z highC<(11/10)*aeval z highL := by
  have h0 := range_lower 0 hz
  have h1 := range_lower 1 hz
  have h2 := range_lower 2 hz
  have h3 := range_lower 3 hz
  have h4 := range_lower 4 hz
  have h5 := range_lower 5 hz
  have h6 := range_lower 6 hz
  norm_num [rangePoly,rangeReserve] at h0 h1 h2 h3 h4 h5 h6
  have eK := congrArg (fun f : ℚ[X] => aeval z f) weight_endpoint_identities.1
  have eL := congrArg (fun f : ℚ[X] => aeval z f) weight_endpoint_identities.2.1
  have eC0 := congrArg (fun f : ℚ[X] => aeval z f) weight_endpoint_identities.2.2.1
  have eCh := congrArg (fun f : ℚ[X] => aeval z f) weight_endpoint_identities.2.2.2
  simp only [map_add,map_sub,map_mul,aeval_C,aeval_X,eq_ratCast] at eK eL eC0 eCh
  have hK : ((highK.eval h:ℚ):ℝ)<843/1000 :=
    r47_cast_lt weight_endpoint_reserves.1 (by norm_num)
  have hL : (89/100:ℝ)<((highL.eval h:ℚ):ℝ) :=
    r47_lt_cast weight_endpoint_reserves.2.1 (by norm_num)
  have hC : (89/100:ℝ)<((highC.eval h:ℚ):ℝ) :=
    r47_lt_cast weight_endpoint_reserves.2.2.1 (by norm_num)
  have hC0 : ((highC.eval L:ℚ):ℝ)=10163/10000 := by
    rw [weight_endpoint_reserves.2.2.2]
    norm_num
  have pK := mul_nonpos_of_nonpos_of_nonneg
    (show z-(h:ℝ)≤0 by norm_num [h]; linarith [hz.2]) (show 0≤aeval z kRight by linarith)
  have pL := mul_nonneg (show 0≤(h:ℝ)-z by norm_num [h]; linarith [hz.2])
    (show 0≤aeval z lRight by linarith)
  have pC0 := mul_nonneg (show 0≤z-(L:ℝ) by norm_num [L]; linarith [hz.1])
    (show 0≤aeval z cLeft by linarith)
  have pCh := mul_nonneg (show 0≤(h:ℝ)-z by norm_num [h]; linarith [hz.2])
    (show 0≤aeval z cRight by linarith)
  exact ⟨h0,by linarith,by linarith,highL_upper hz,by linarith,by linarith,
    by linarith,by linarith⟩

theorem mass_identities (e : Endpoint) (i : Fin 7) :
    centered L h (mass e i)=expansion 8 (centered L h (mass e i)) := by
  cases e <;> fin_cases i
  · exact r47_idRH
  · exact r47_idRG
  · exact r47_idRD
  · exact r47_idRBT
  · exact r47_idRHm
  · exact r47_idRGm
  · exact r47_idRBmT
  · exact r47_idRH
  · exact r47_idRG
  · exact r47_idRD
  · exact r47_idRBA
  · exact r47_idRHm
  · exact r47_idRGm
  · exact r47_idRBmA

theorem mass_reserves (e : Endpoint) (i : Fin 7) :
    (7/10:ℚ)<lowerOn 8 L h (mass e i) := by
  cases e <;> fin_cases i
  · exact r47_lowRH
  · exact r47_lowRG
  · exact r47_lowRD
  · exact r47_lowRBT
  · exact r47_lowRHm
  · exact r47_lowRGm
  · exact r47_lowRBmT
  · exact r47_lowRH
  · exact r47_lowRG
  · exact r47_lowRD
  · exact r47_lowRBA
  · exact r47_lowRHm
  · exact r47_lowRGm
  · exact r47_lowRBmA

theorem masses_positive (e : Endpoint) (i : Fin 7) {z : ℝ}
    (hz : z∈Icc (1/6:ℝ) (7/10:ℝ)) : 0<aeval z (mass e i) := by
  have hh := positive_on_interval (by norm_num [L,h] : L<h)
    (mass_identities e i) (mass_reserves e i) (r47_mem hz)
  push_cast at hh
  linarith

theorem gap_identity :
    gapCentered=C (gapCentered.coeff 0)+C (gapCentered.coeff 1)*X+
      C (gapCentered.coeff 2)*X^2+PowerTailBounds.tail gapCentered 3 6 :=
  r47_split8 ((r47_rGapC.natDegree_le (by rw [r47_gap_scale]; norm_num)).trans
    (by rw [r47_gap_list]; simp))

theorem gap_reserves : (107/400:ℚ)<gapCurvature ∧ (1/250:ℚ)<gapReserve := by
  simp only [gapReserve,gapCurvature,PowerTailBounds.norm,Fin.sum_univ_six,r47_gap_coeff]
  norm_num

theorem highQGap_positive {z : ℝ} (hz : z∈Icc (1/6:ℝ) (7/10:ℝ)) :
    0<aeval z highQGap := by
  have hx : |z-13/30|≤((4/15:ℚ):ℝ) := by
    push_cast
    exact abs_le.mpr ⟨by linarith [hz.1],by linarith [hz.2]⟩
  have hb := PowerTailBounds.quadratic_lower (r := 4/15) gap_identity (by norm_num) hx
  have hc : (0:ℝ)<(gapCurvature:ℝ) := by
    exact_mod_cast (lt_trans (by norm_num : (0:ℚ)<107/400) gap_reserves.1)
  have hm := ChebyshevLeadingBounds.quadratic_min
    (a:=(gapCentered.coeff 0:ℝ)) (b:=(gapCentered.coeff 1:ℝ)) (x:=z-13/30) hc
  have he : aeval (z-13/30) gapCentered=aeval z highQGap := by
    simp [gapCentered]
  rw [he] at hb
  have hr : (1/250:ℝ)<(gapReserve:ℝ) := r47_lt_cast gap_reserves.2 (by norm_num)
  dsimp [gapReserve,gapCurvature] at hr hm hc
  push_cast at hr hm hc
  linarith

theorem highQ_C_identity :
    centered L h (highQ-highC)=expansion 3 (centered L h (highQ-highC)) :=
  r47_id r47_rQC (by decide +kernel) (by decide +kernel)

theorem highQ_C_reserve : (1/3000:ℚ)<lowerOn 3 L h (highQ-highC) :=
  r47_low r47_rQC (by decide +kernel) (by decide +kernel) (ρ := 1/3000) (num := 1) (den := 3000)
      (by norm_num) (by norm_num) (by decide +kernel)

theorem highQ_C_positive {z : ℝ} (hz : z∈Icc (1/6:ℝ) (7/10:ℝ)) :
    aeval z highC<aeval z highQ := by
  have hh := positive_on_interval (by norm_num [L,h] : L<h)
    highQ_C_identity highQ_C_reserve (r47_mem hz)
  simp only [map_sub] at hh
  push_cast at hh
  linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.TwoPositive.Certificate

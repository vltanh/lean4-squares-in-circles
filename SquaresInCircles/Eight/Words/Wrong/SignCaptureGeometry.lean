module

public import SquaresInCircles.Eight.Owners.Endpoint.BudgetScalars
public import SquaresInCircles.Eight.Owners.PowerTailBounds
public import SquaresInCircles.Eight.Words.Middle.Stress
public import SquaresInCircles.Eight.Words.Wrong.WordCircleSupport

/-!
# Eight squares: the complete three-frame hull comparison for wrong signs

The weights are selected once at the original
three-frame hull width.  Every exterior frame sector decreases to one
of the two scalar endpoints, and the interior sector is bounded by
convexity on a single segment.  No square is moved in this argument.
-/

section
/-!
## Exact whole-interval coefficients for small wrong signs

The middle and last weight families are explicit polynomials (`middleA`, `middleB`, `lastB`).
Each radical is bounded by its positive quadratic tangent, so each comparison is a single
rational polynomial (`middleT`, `middleG`, `lastT`). Centered power norms prove positivity on each
analytic range (`middleT_positive`, `middleG_positive`, `lastT_positive`).

For the G middle family, expansion at its right endpoint gives a direct one-sided linear lower
bound (`shiftedG_positive`).
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.WrongSignWeightPolynomial
open Polynomial PowerTailBounds

def Rbar : ℚ := 494697/250000
def Sbar : ℚ := 259391/625000
def limit : ℚ := 518907/1250000
def charge : ℚ := 50/49

def S7 (z : ℚ[X]) : ℚ[X] := z-C (1/6)*z^3+C (1/120)*z^5-C (1/5040)*z^7
def C6 (z : ℚ[X]) : ℚ[X] := 1-C (1/2)*z^2+C (1/24)*z^4-C (1/720)*z^6

def radicandT (a b z : ℚ[X]) : ℚ[X] := a^2+b^2-C 2*a*b*S7 z
def radicandG (b z : ℚ[X]) : ℚ[X] := 1+b^2-C 2*b*S7 z
def targetT (a b z : ℚ[X]) : ℚ[X] :=
  C limit+C (2/5)*a+C (8/5)+C 2*b+a*C6 z-C charge*z
def targetG (a b z : ℚ[X]) : ℚ[X] :=
  C limit+C (7/5)*a+C (3/5)+C 2*b+C6 z-C charge*z

def T (a b z r₁ r₂ : ℚ[X]) : ℚ[X] :=
  C 2*r₁*r₂*targetT a b z-
    C Rbar*(r₂*(radicandT a b z+r₁^2)+r₁*(1+b^2+r₂^2))

def G (a b z r₁ r₂ : ℚ[X]) : ℚ[X] :=
  C 2*r₁*r₂*targetG a b z-
    C Rbar*(r₂*(a^2+b^2+r₁^2)+r₁*(radicandG b z+r₂^2))

def middleRho : ℚ[X] := C (9/20)+X
def middleA : ℚ[X] := C (2397/2500)+C (42/25)*X+C (3/4)*X^2
def middleB : ℚ[X] := C (15717/20000)+C (67/50)*X+X^2
def middleT1 : ℚ[X] := C (938801/1000000)+C (182059/200000)*X-C (86707/250000)*X^2
def middleT2 : ℚ[X] := C (635921/500000)+C (165379/200000)*X+C (100681/100000)*X^2
def middleG1 : ℚ[X] := C (12397/10000)+C (2148807/1000000)*X+C (303977/250000)*X^2
def middleG2 : ℚ[X] := C (60401/62500)-C (123829/500000)*X+C (92273/1000000)*X^2

def middleT : ℚ[X] := T middleA middleB middleRho middleT1 middleT2
def middleG : ℚ[X] := G middleA middleB middleRho middleG1 middleG2
def shiftedT : ℚ[X] := middleT.comp (C (1/200)+X)
def shiftedG : ℚ[X] := middleG.comp (C (1/50)+X)

def lastRho : ℚ[X] := C (47/100)+X
def lastB : ℚ[X] := C (153/250)+C (87/200)*lastRho
def lastT1 : ℚ[X] := C (240711/250000)-C (118317/200000)*X-
  C (297613/1000000)*X^2+C (67787/1000000)*X^3
def lastT2 : ℚ[X] := C (258193/200000)+C (275113/1000000)*X+
  C (43889/1000000)*X^2-C (8793/1000000)*X^3
def lastT : ℚ[X] := T 1 lastB lastRho lastT1 lastT2

/-- A polynomial of degree below `s + c` is its first `s` monomials plus `tail p s c`. -/
private theorem r31_expand (p : ℚ[X]) (s c : ℕ) (h : p.natDegree < s + c) :
    p = (∑ i ∈ Finset.range s, C (p.coeff i) * X ^ i) + tail p s c := by
  conv_lhs => rw [p.as_sum_range_C_mul_X_pow' h, Finset.sum_range_add]
  rw [tail, Fin.sum_univ_eq_sum_range (fun j => C (p.coeff (j + s)) * X ^ (j + s)) c]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by rw [add_comm s j]

private theorem r31_sT_eq : shiftedT =
      C (768272796084644279869212807915534004761/4587520000000000000000000000000000000000000)+
      C (-(356653375525789652213994215400022424247/160563200000000000000000000000000000000000))*X+
      C (771698847811514546608108954444351724317/501760000000000000000000000000000000000)*X^2+
      C (14253225627718656576872390189647752921/5017600000000000000000000000000000000)*X^3+
      C (925938873946843978587463611783852929/301056000000000000000000000000000000)*X^4+
      C (607679828531431986995345221078133/215040000000000000000000000000000)*X^5+
      C (-(42868609043691450963696759233/19200000000000000000000000000))*X^6+
      C (-(128604680716394252607655037/48000000000000000000000000))*X^7+
      C (-(6062379415052052263737853/3840000000000000000000000))*X^8+
      C (-(1859559305914164712979/19200000000000000000000))*X^9+
      C (632050752778741589/6000000000000000000)*X^10+
      C (1286507875568489/120000000000000000)*X^11+
      C (-(9092393863909/2400000000000000))*X^12+
      C (-(2371742317/4000000000000))*X^13 := by
  apply Polynomial.funext
  intro r
  simp only [shiftedT, middleT, T, targetT, radicandT, S7, C6, middleA, middleB, middleRho,
    middleT1, middleT2, Rbar, limit, charge, eval_comp, eval_add, eval_sub, eval_mul, eval_pow,
    eval_C, eval_X, eval_one]
  ring

private theorem r31_sG_eq : shiftedG =
      C (17217376670427398546995115571057231/6125000000000000000000000000000000000)+
      C (-(59476159648918866991992955406869989/122500000000000000000000000000000000))*X+
      C (-(174299457393168678646917422645129/122500000000000000000000000000000))*X^2+
      C (-(67404810198613437607983499319281/11025000000000000000000000000000))*X^3+
      C (-(366569486218688341719561252571/27562500000000000000000000000))*X^4+
      C (-(7857984412307491082214861697/612500000000000000000000000))*X^5+
      C (-(2950016838597586202192803/562500000000000000000000))*X^6+
      C (-(158104359378031525477/562500000000000000000))*X^7+
      C (1461962993170251143/7500000000000000000)*X^8+
      C (9394376990982271/450000000000000000)*X^9+
      C (-(14615871115507/2250000000000000))*X^10+
      C (-(7160786189/7500000000000))*X^11 := by
  apply Polynomial.funext
  intro r
  simp only [shiftedG, middleG, G, targetG, radicandG, S7, C6, middleA, middleB, middleRho,
    middleG1, middleG2, Rbar, limit, charge, eval_comp, eval_add, eval_sub, eval_mul, eval_pow,
    eval_C, eval_X, eval_one]
  ring

private theorem r31_lT_eq : lastT =
      C (274338781832597237060523956477/588000000000000000000000000000000)+
      C (169626927125896190404086767458357/2940000000000000000000000000000000)*X+
      C (882677395316708875688519731833463/8820000000000000000000000000000000)*X^2+
      C (-(71095566902797545982475678751159/980000000000000000000000000000000))*X^3+
      C (-(127923788690572265863654675249/918750000000000000000000000000))*X^4+
      C (-(18116771389399562856182998993/220500000000000000000000000000))*X^5+
      C (-(115697534675281171678061551/5880000000000000000000000000))*X^6+
      C (193536444714517761745367/29400000000000000000000000)*X^7+
      C (8529233974354156784513/4500000000000000000000000)*X^8+
      C (46705750140807672157/375000000000000000000000)*X^9+
      C (-(140917169642201/1200000000000000000))*X^10+
      C (-(17686856851/2250000000000000))*X^11+
      C (66227899/40000000000000)*X^12 := by
  apply Polynomial.funext
  intro r
  simp only [lastT, T, targetT, radicandT, S7, C6, lastB, lastRho, lastT1, lastT2, Rbar, limit,
    charge, eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_X, eval_one]
  ring

theorem shiftedT_expansion :
    shiftedT=C (shiftedT.coeff 0)+C (shiftedT.coeff 1)*X+
      C (shiftedT.coeff 2)*X^2+tail shiftedT 3 11 := by
  have h := r31_expand shiftedT 3 11
    (lt_of_le_of_lt (by rw [r31_sT_eq]; compute_degree!) (by norm_num : 13 < 3 + 11))
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, mul_one,
    pow_one] at h
  exact h

theorem shiftedG_expansion :
    shiftedG=C (shiftedG.coeff 0)+C (shiftedG.coeff 1)*X+tail shiftedG 2 10 := by
  have h := r31_expand shiftedG 2 10
    (lt_of_le_of_lt (by rw [r31_sG_eq]; compute_degree!) (by norm_num : 11 < 2 + 10))
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, mul_one,
    pow_one] at h
  exact h

theorem lastT_expansion :
    lastT=C (lastT.coeff 0)+C (lastT.coeff 1)*X+tail lastT 2 11 := by
  have h := r31_expand lastT 2 11
    (lt_of_le_of_lt (by rw [r31_lT_eq]; compute_degree!) (by norm_num : 12 < 2 + 11))
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, mul_one,
    pow_one] at h
  exact h

theorem middleT_reserves :
    (167/1000000 : ℚ)<shiftedT.coeff 0 ∧
      |shiftedT.coeff 1|<1111/500000 ∧
      (6/5 : ℚ)<shiftedT.coeff 2-norm shiftedT 3 11 (21/200) := by
  rw [r31_sT_eq]
  simp only [PowerTailBounds.norm, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero,
    Fin.val_succ, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  norm_num

theorem middleG_reserves :
    (7/2500 : ℚ)<shiftedG.coeff 0 ∧
      shiftedG.coeff 1+norm shiftedG 2 10 (3/25)< -(1/5 : ℚ) := by
  rw [r31_sG_eq]
  simp only [PowerTailBounds.norm, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero,
    Fin.val_succ, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  norm_num

theorem lastT_reserves :
    (23/50000 : ℚ)<lastT.coeff 0 ∧
      (1/50 : ℚ)<lastT.coeff 1-norm lastT 2 11 (23/100) := by
  rw [r31_lT_eq]
  simp only [PowerTailBounds.norm, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero,
    Fin.val_succ, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  norm_num

theorem shiftedT_positive {x : ℝ} (hx : |x|≤(21/200 : ℝ)) :
    0<aeval x shiftedT := by
  have hbound := quadratic_lower shiftedT_expansion (by norm_num : (0:ℚ)≤21/200)
    (show |x|≤((21/200 : ℚ) : ℝ) by push_cast; exact hx)
  have hc0 : (167/1000000 : ℝ)<(shiftedT.coeff 0:ℝ) := by
    have h := (Rat.cast_lt (K := ℝ)).mpr middleT_reserves.1
    push_cast at h
    exact h
  have hc1 : |(shiftedT.coeff 1:ℝ)|<1111/500000 := by
    have h := (Rat.cast_lt (K := ℝ)).mpr middleT_reserves.2.1
    push_cast at h
    exact h
  have hc2 : (6/5 : ℝ)<(shiftedT.coeff 2:ℝ)-(norm shiftedT 3 11 (21/200):ℝ) := by
    have h := (Rat.cast_lt (K := ℝ)).mpr middleT_reserves.2.2
    push_cast at h
    exact h
  have hlinear : -(1111/500000)*|x|≤(shiftedT.coeff 1:ℝ)*x := by
    have hm := mul_le_mul_of_nonneg_right hc1.le (abs_nonneg x)
    rw [← abs_mul] at hm
    linarith [(abs_le.mp hm).1]
  have hquadratic := mul_le_mul_of_nonneg_right hc2.le (sq_nonneg x)
  nlinarith [sq_nonneg (|x|-(1111/1200000 : ℝ)),sq_abs x]

theorem middleT_positive {x : ℝ} (hx : x∈Set.Icc (-(1/10) : ℝ) (1/50)) :
    0<aeval x middleT := by
  have hb : |x-(1/200 : ℝ)|≤21/200 := by
    rw [abs_le]
    constructor <;> linarith [hx.1,hx.2]
  have hh := shiftedT_positive hb
  have he : aeval (x-(1/200 : ℝ)) shiftedT=aeval x middleT := by
    rw [shiftedT,aeval_comp]
    congr 1
    simp
  rwa [he] at hh

theorem shiftedG_positive {x : ℝ} (hx : x∈Set.Icc (-(3/25) : ℝ) 0) :
    0<aeval x shiftedG := by
  have hb : |x|≤(3/25 : ℝ) := by rw [abs_of_nonpos hx.2]; linarith [hx.1]
  have hbound := linear_lower shiftedG_expansion (by norm_num : (0:ℚ)≤3/25)
    (show |x|≤((3/25 : ℚ) : ℝ) by push_cast; exact hb)
  have hc0 : (7/2500 : ℝ)<(shiftedG.coeff 0:ℝ) := by
    have h := (Rat.cast_lt (K := ℝ)).mpr middleG_reserves.1
    push_cast at h
    exact h
  have hc1 : (shiftedG.coeff 1:ℝ)+(norm shiftedG 2 10 (3/25):ℝ)< -(1/5 : ℝ) := by
    have h := (Rat.cast_lt (K := ℝ)).mpr middleG_reserves.2
    push_cast at h
    exact h
  have hm := mul_nonneg
    (show 0≤-((shiftedG.coeff 1:ℝ)+(norm shiftedG 2 10 (3/25):ℝ)) by linarith)
    (neg_nonneg.mpr hx.2)
  rw [abs_of_nonpos hx.2] at hbound
  nlinarith

theorem middleG_positive {x : ℝ} (hx : x∈Set.Icc (-(1/10) : ℝ) (1/50)) :
    0<aeval x middleG := by
  have hb : x-(1/50 : ℝ)∈Set.Icc (-(3/25) : ℝ) 0 := by
    constructor <;> linarith [hx.1,hx.2]
  have hh := shiftedG_positive hb
  have he : aeval (x-(1/50 : ℝ)) shiftedG=aeval x middleG := by
    rw [shiftedG,aeval_comp]
    congr 1
    simp
  rwa [he] at hh

theorem lastT_positive {x : ℝ} (hx : x∈Set.Icc 0 (23/100 : ℝ)) :
    0<aeval x lastT := by
  have hb : |x|≤(23/100 : ℝ) := by rw [abs_of_nonneg hx.1]; exact hx.2
  have hbound := linear_lower lastT_expansion (by norm_num : (0:ℚ)≤23/100)
    (show |x|≤((23/100 : ℚ) : ℝ) by push_cast; exact hb)
  have hc0 : (23/50000 : ℝ)<(lastT.coeff 0:ℝ) := by
    have h := (Rat.cast_lt (K := ℝ)).mpr lastT_reserves.1
    push_cast at h
    exact h
  have hc1 : (1/50 : ℝ)<(lastT.coeff 1:ℝ)-(norm lastT 2 11 (23/100):ℝ) := by
    have h := (Rat.cast_lt (K := ℝ)).mpr lastT_reserves.2
    push_cast at h
    exact h
  have hm := mul_nonneg
    (show 0≤(lastT.coeff 1:ℝ)-(norm lastT 2 11 (23/100):ℝ) by linarith) hx.1
  rw [abs_of_nonneg hx.1] at hbound
  nlinarith

end SquaresInCircles.Eight.WrongSignWeightPolynomial
end
end
end

section
/-!
## Actual radical endpoint bounds for small wrong intermediate signs

The auxiliary quadratic tangents and every
weight are the printed exact rational polynomials.  Their whole-interval
positivity is transferred to the original trigonometric radical formulas.
No numerical enclosure or polynomial comparison is assumed as an input
to any concrete weight-family result.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.WrongSignCaptureScalars
open PositiveAngularEnvelope PairNormCalculus EndpointRotationPenalty EndpointBudgetScalars
open Polynomial

def U_T (rho a b : ℝ) : ℝ :=
  R*(pairNorm a b (-rho)+pairNorm 1 b 0)-2*a/5-8/5-2*b-a*Real.cos rho+charge*rho
def U_G (rho a b : ℝ) : ℝ :=
  R*(pairNorm a b 0+pairNorm 1 b (-rho))-7*a/5-3/5-2*b-Real.cos rho+charge*rho

def Admissible (a b : ℝ) : Prop :=
  a∈Icc (3/4 : ℝ) 1 ∧ b∈Icc (13/20 : ℝ) (23/25) ∧ b≤(23/25)*a

def sine7 (t : ℝ) : ℝ := t-t^3/6+t^5/120-t^7/5040
def cosine6 (t : ℝ) : ℝ := 1-t^2/2+t^4/24-t^6/720

theorem radius_reserves :
    R<(WrongSignWeightPolynomial.Rbar:ℝ) ∧
      (WrongSignWeightPolynomial.Sbar:ℝ)<S0 ∧
      (WrongSignWeightPolynomial.limit:ℝ)<S0+(1/10000 : ℝ) := by
  have hR := R_sq
  have hS := Real.sq_sqrt (show 0≤qCap-1 by norm_num [qCap])
  have hS0 := Real.sqrt_nonneg (qCap-1)
  dsimp [WrongSignWeightPolynomial.Rbar,WrongSignWeightPolynomial.Sbar,
    WrongSignWeightPolynomial.limit,S0,qCap] at *
  constructor
  · nlinarith [R_nonneg]
  constructor <;> nlinarith

@[simp] theorem S7_eval (z : ℚ[X]) (x : ℝ) :
    aeval x (WrongSignWeightPolynomial.S7 z)=sine7 (aeval x z) := by
  simp [WrongSignWeightPolynomial.S7,sine7]
  ring

@[simp] theorem C6_eval (z : ℚ[X]) (x : ℝ) :
    aeval x (WrongSignWeightPolynomial.C6 z)=cosine6 (aeval x z) := by
  simp [WrongSignWeightPolynomial.C6,cosine6]
  ring

theorem T_eval (a b z r₁ r₂ : ℚ[X]) (x : ℝ) :
    aeval x (WrongSignWeightPolynomial.T a b z r₁ r₂)=
      2*aeval x r₁*aeval x r₂*((WrongSignWeightPolynomial.limit:ℝ)+
        2*aeval x a/5+8/5+2*aeval x b+aeval x a*cosine6 (aeval x z)-charge*aeval x z)-
      (WrongSignWeightPolynomial.Rbar:ℝ)*
        (aeval x r₂*((aeval x a)^2+(aeval x b)^2-
          2*aeval x a*aeval x b*sine7 (aeval x z)+(aeval x r₁)^2)+
          aeval x r₁*(1+(aeval x b)^2+(aeval x r₂)^2)) := by
  simp only [WrongSignWeightPolynomial.T,WrongSignWeightPolynomial.targetT,
    WrongSignWeightPolynomial.radicandT,map_add,map_sub,map_mul,map_pow,map_one,aeval_C,
    S7_eval,C6_eval,eq_ratCast,WrongSignWeightPolynomial.charge,charge]
  push_cast
  ring

theorem G_eval (a b z r₁ r₂ : ℚ[X]) (x : ℝ) :
    aeval x (WrongSignWeightPolynomial.G a b z r₁ r₂)=
      2*aeval x r₁*aeval x r₂*((WrongSignWeightPolynomial.limit:ℝ)+
        7*aeval x a/5+3/5+2*aeval x b+cosine6 (aeval x z)-charge*aeval x z)-
      (WrongSignWeightPolynomial.Rbar:ℝ)*
        (aeval x r₂*((aeval x a)^2+(aeval x b)^2+(aeval x r₁)^2)+
          aeval x r₁*(1+(aeval x b)^2-
            2*aeval x b*sine7 (aeval x z)+(aeval x r₂)^2)) := by
  simp only [WrongSignWeightPolynomial.G,WrongSignWeightPolynomial.targetG,
    WrongSignWeightPolynomial.radicandG,map_add,map_sub,map_mul,map_pow,map_one,aeval_C,
    S7_eval,C6_eval,eq_ratCast,WrongSignWeightPolynomial.charge,charge]
  push_cast
  ring

/-- Two positive scalar tangents bound the actual pair of norms. -/
theorem two_norms {n₁ n₂ A B e r₁ r₂ : ℝ}
    (hn₁ : 0≤n₁) (hn₂ : 0≤n₂) (hA : n₁^2≤A) (hB : n₂^2≤B)
    (hr₁ : 0<r₁) (hr₂ : 0<r₂)
    (hcertificate : 0<2*r₁*r₂*e-(WrongSignWeightPolynomial.Rbar:ℝ)*
      (r₂*(A+r₁^2)+r₁*(B+r₂^2))) :
    R*(n₁+n₂)<e := by
  have hRbar : 0≤(WrongSignWeightPolynomial.Rbar:ℝ) := by
    norm_num [WrongSignWeightPolynomial.Rbar]
  have h₁ : 2*r₁*n₁≤A+r₁^2 := by linarith [sq_nonneg (n₁-r₁)]
  have h₂ : 2*r₂*n₂≤B+r₂^2 := by linarith [sq_nonneg (n₂-r₂)]
  have h₁w := mul_le_mul_of_nonneg_left h₁ (mul_nonneg hRbar hr₂.le)
  have h₂w := mul_le_mul_of_nonneg_left h₂ (mul_nonneg hRbar hr₁.le)
  have hR := mul_le_mul_of_nonneg_right radius_reserves.1.le (add_nonneg hn₁ hn₂)
  have hscale : 0<2*r₁*r₂ := by positivity
  have hRw := mul_le_mul_of_nonneg_left hR hscale.le
  refine lt_of_mul_lt_mul_left ?_ hscale.le
  linarith

theorem negative_norm_upper {a b rho : ℝ} (ha : 0<a) (hb : 0<b)
    (hrho : rho∈Icc 0 frameCap) :
    (pairNorm a b (-rho))^2≤a^2+b^2-2*a*b*sine7 rho := by
  have hρ : |-rho|≤frameCap := by rw [abs_neg,abs_of_nonneg hrho.1]; exact hrho.2
  have hN := pairNorm_sq ha hb hρ
  have hs := sin_lower_seven hrho.1
  have hm := mul_le_mul_of_nonneg_left hs (show 0≤2*a*b by positivity)
  dsimp [sine7]
  simp only [pairEnergy,pairProduct,Real.sin_neg] at hN
  nlinarith

theorem T_transfer {a b z r₁ r₂ : ℚ[X]} {x : ℝ}
    (ha : 0<aeval x a) (hb : 0<aeval x b)
    (hz : aeval x z∈Icc 0 frameCap) (hr₁ : 0<aeval x r₁) (hr₂ : 0<aeval x r₂)
    (hP : 0<aeval x (WrongSignWeightPolynomial.T a b z r₁ r₂)) :
    U_T (aeval x z) (aeval x a) (aeval x b)<(WrongSignWeightPolynomial.limit:ℝ) := by
  have hA := negative_norm_upper ha hb hz
  have hB : (pairNorm 1 (aeval x b) 0)^2=1+(aeval x b)^2 := by
    simpa [pairEnergy,pairProduct] using pairNorm_sq (show (0:ℝ)<1 by norm_num) hb
      (show |(0:ℝ)|≤frameCap by norm_num [frameCap])
  rw [T_eval] at hP
  have hnorm := two_norms (n₁ := pairNorm (aeval x a) (aeval x b) (-aeval x z))
    (n₂ := pairNorm 1 (aeval x b) 0)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hA hB.le hr₁ hr₂ hP
  have hcos := mul_le_mul_of_nonneg_left (cos_lower_six hz.1) ha.le
  dsimp [U_T,cosine6] at *
  linarith

theorem G_transfer {a b z r₁ r₂ : ℚ[X]} {x : ℝ}
    (ha : 0<aeval x a) (hb : 0<aeval x b)
    (hz : aeval x z∈Icc 0 frameCap) (hr₁ : 0<aeval x r₁) (hr₂ : 0<aeval x r₂)
    (hP : 0<aeval x (WrongSignWeightPolynomial.G a b z r₁ r₂)) :
    U_G (aeval x z) (aeval x a) (aeval x b)<(WrongSignWeightPolynomial.limit:ℝ) := by
  have hA : (pairNorm (aeval x a) (aeval x b) 0)^2=(aeval x a)^2+(aeval x b)^2 := by
    simpa [pairEnergy,pairProduct] using pairNorm_sq ha hb
      (show |(0:ℝ)|≤frameCap by norm_num [frameCap])
  have hB : (pairNorm 1 (aeval x b) (-aeval x z))^2≤
      1+(aeval x b)^2-2*aeval x b*sine7 (aeval x z) := by
    simpa only [one_pow,one_mul,mul_one] using
      negative_norm_upper (show (0:ℝ)<1 by norm_num) hb hz
  rw [G_eval] at hP
  have hnorm := two_norms (n₁ := pairNorm (aeval x a) (aeval x b) 0)
    (n₂ := pairNorm 1 (aeval x b) (-aeval x z))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hA.le hB hr₁ hr₂ hP
  have hcos := cos_lower_six hz.1
  dsimp [U_G,cosine6] at *
  linarith

theorem middle_admissible {x : ℝ} (hx : x∈Icc (-(1/10) : ℝ) (1/50)) :
    Admissible (aeval x WrongSignWeightPolynomial.middleA)
      (aeval x WrongSignWeightPolynomial.middleB) := by
  have hx2 : x^2≤(1/100 : ℝ) := by
    have hh : |x|≤(1/10 : ℝ) := abs_le.mpr ⟨hx.1,by linarith [hx.2]⟩
    nlinarith [pow_le_pow_left₀ (abs_nonneg x) hh 2,sq_abs x]
  have hprod := mul_nonneg (show 0≤x+1/10 by linarith [hx.1])
    (show 0≤1/50-x by linarith [hx.2])
  simp only [Admissible,WrongSignWeightPolynomial.middleA,WrongSignWeightPolynomial.middleB,
    map_add,map_mul,map_pow,aeval_C,aeval_X,mem_Icc]
  norm_num
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,?_⟩ <;> nlinarith [sq_nonneg x]

theorem middle_auxiliaries {x : ℝ} (hx : x∈Icc (-(1/10) : ℝ) (1/50)) :
    (4/5 : ℝ)<aeval x WrongSignWeightPolynomial.middleT1 ∧
      (4/5 : ℝ)<aeval x WrongSignWeightPolynomial.middleT2 ∧
      (4/5 : ℝ)<aeval x WrongSignWeightPolynomial.middleG1 ∧
      (4/5 : ℝ)<aeval x WrongSignWeightPolynomial.middleG2 := by
  have hx2 : x^2≤(1/100 : ℝ) := by
    have hh : |x|≤(1/10 : ℝ) := abs_le.mpr ⟨hx.1,by linarith [hx.2]⟩
    nlinarith [pow_le_pow_left₀ (abs_nonneg x) hh 2,sq_abs x]
  simp only [WrongSignWeightPolynomial.middleT1,WrongSignWeightPolynomial.middleT2,
    WrongSignWeightPolynomial.middleG1,WrongSignWeightPolynomial.middleG2,
    map_add,map_sub,map_mul,map_pow,aeval_C,aeval_X]
  norm_num
  refine ⟨?_,?_,?_,?_⟩ <;> nlinarith [sq_nonneg x,hx.1,hx.2]

theorem middle_family {rho : ℝ} (hrho : rho∈Icc (7/20 : ℝ) (47/100)) :
    ∃ a b,Admissible a b ∧ U_T rho a b<(WrongSignWeightPolynomial.limit:ℝ) ∧
      U_G rho a b<(WrongSignWeightPolynomial.limit:ℝ) := by
  let x : ℝ := rho-9/20
  have hx : x∈Icc (-(1/10) : ℝ) (1/50) := by
    dsimp [x]
    constructor <;> linarith [hrho.1,hrho.2]
  have hadm := middle_admissible hx
  have haux := middle_auxiliaries hx
  have hz : aeval x WrongSignWeightPolynomial.middleRho=rho := by
    simp [WrongSignWeightPolynomial.middleRho,x]
  have hzdom : aeval x WrongSignWeightPolynomial.middleRho∈Icc 0 frameCap := by
    rw [hz]
    exact ⟨by linarith [hrho.1],by simp only [frameCap]; linarith [hrho.2]⟩
  have ha : 0<aeval x WrongSignWeightPolynomial.middleA := by linarith [hadm.1.1]
  have hb : 0<aeval x WrongSignWeightPolynomial.middleB := by linarith [hadm.2.1.1]
  have hT := T_transfer ha hb hzdom (by linarith [haux.1]) (by linarith [haux.2.1])
    (WrongSignWeightPolynomial.middleT_positive hx)
  have hG := G_transfer ha hb hzdom (by linarith [haux.2.2.1]) (by linarith [haux.2.2.2])
    (WrongSignWeightPolynomial.middleG_positive hx)
  rw [hz] at hT hG
  exact ⟨_,_,hadm,hT,hG⟩

theorem last_admissible {x : ℝ} (hx : x∈Icc 0 (23/100 : ℝ)) :
    Admissible 1 (aeval x WrongSignWeightPolynomial.lastB) := by
  refine ⟨⟨by norm_num,by norm_num⟩,⟨?_,?_⟩,?_⟩
  all_goals
    simp only [WrongSignWeightPolynomial.lastB,WrongSignWeightPolynomial.lastRho,
      map_add,map_mul,aeval_C,aeval_X]
    norm_num
    linarith [hx.1,hx.2]

theorem last_auxiliaries {x : ℝ} (hx : x∈Icc 0 (23/100 : ℝ)) :
    (4/5 : ℝ)<aeval x WrongSignWeightPolynomial.lastT1 ∧
      (4/5 : ℝ)<aeval x WrongSignWeightPolynomial.lastT2 := by
  have hx2 := pow_le_pow_left₀ hx.1 hx.2 2
  have hx3 := pow_le_pow_left₀ hx.1 hx.2 3
  simp only [WrongSignWeightPolynomial.lastT1,WrongSignWeightPolynomial.lastT2,
    map_add,map_sub,map_mul,map_pow,aeval_C,aeval_X]
  norm_num
  constructor <;> nlinarith [sq_nonneg x,pow_nonneg hx.1 3,hx.1,hx.2]

theorem U_equal_at_one (rho b : ℝ) : U_G rho 1 b=U_T rho 1 b := by
  simp only [U_G,U_T]
  ring

theorem last_family {rho : ℝ} (hrho : rho∈Icc (47/100 : ℝ) frameCap) :
    ∃ a b,Admissible a b ∧ U_T rho a b<(WrongSignWeightPolynomial.limit:ℝ) ∧
      U_G rho a b<(WrongSignWeightPolynomial.limit:ℝ) := by
  let x : ℝ := rho-47/100
  have hx : x∈Icc 0 (23/100 : ℝ) := by
    dsimp [x,frameCap] at *
    constructor <;> linarith [hrho.1,hrho.2]
  have hadm := last_admissible hx
  have haux := last_auxiliaries hx
  have hz : aeval x WrongSignWeightPolynomial.lastRho=rho := by
    simp [WrongSignWeightPolynomial.lastRho,x]
  have hzdom : aeval x WrongSignWeightPolynomial.lastRho∈Icc 0 frameCap := by
    rw [hz]
    exact ⟨by linarith [hrho.1],hrho.2⟩
  have ha : 0<aeval x (1:ℚ[X]) := by simp
  have hb : 0<aeval x WrongSignWeightPolynomial.lastB := by linarith [hadm.2.1.1]
  have hT := T_transfer ha hb hzdom (by linarith [haux.1]) (by linarith [haux.2])
    (WrongSignWeightPolynomial.lastT_positive hx)
  rw [hz] at hT
  simp only [map_one] at hT
  refine ⟨1,_,hadm,hT,?_⟩
  rw [U_equal_at_one]
  exact hT

theorem first_norm_bounds :
    pairNorm (4/5) (13/20) 0<(1030777/1000000 : ℝ) ∧
      pairNorm 1 (13/20) 0<(1192687/1000000 : ℝ) ∧
      pairNorm (4/5) (13/20) (-(7/20))<(840171/1000000 : ℝ) ∧
      pairNorm 1 (13/20) (-(7/20))<(494149/500000 : ℝ) := by
  have hr : |-(7/20 : ℝ)|≤frameCap := by norm_num [frameCap]
  have h₃ := pairNorm_sq (show (0:ℝ)<4/5 by norm_num) (show (0:ℝ)<13/20 by norm_num) hr
  have h₄ := pairNorm_sq (show (0:ℝ)<1 by norm_num) (show (0:ℝ)<13/20 by norm_num) hr
  have hs := sin_lower_seven (show (0:ℝ)≤7/20 by norm_num)
  simp only [pairEnergy,pairProduct,Real.sin_neg] at h₃ h₄
  refine ⟨?_,?_,?_,?_⟩
  · rw [pairNorm_zero,Real.sqrt_lt' (by norm_num)]
    norm_num
  · rw [pairNorm_zero,Real.sqrt_lt' (by norm_num)]
    norm_num
  · apply lt_of_pow_lt_pow_left₀ 2 (by norm_num)
    rw [h₃]
    linarith
  · apply lt_of_pow_lt_pow_left₀ 2 (by norm_num)
    rw [h₄]
    linarith

theorem first_at_zero :
    U_T 0 (4/5) (13/20)<(WrongSignWeightPolynomial.limit:ℝ) ∧
      U_G 0 (4/5) (13/20)<(WrongSignWeightPolynomial.limit:ℝ) := by
  have hn : pairNorm (4/5) (13/20) 0+pairNorm 1 (13/20) 0≤
      (1030777/1000000 : ℝ)+1192687/1000000 := by
    linarith [first_norm_bounds.1,first_norm_bounds.2.1]
  have hm := mul_le_mul_of_nonneg_left hn R_nonneg
  have hr := mul_lt_mul_of_pos_right radius_reserves.1
    (show (0:ℝ)<1030777/1000000+1192687/1000000 by norm_num)
  have hlim : (WrongSignWeightPolynomial.limit:ℝ)=518907/1250000 := by
    norm_num [WrongSignWeightPolynomial.limit]
  have hRbar : (WrongSignWeightPolynomial.Rbar:ℝ)=494697/250000 := by
    norm_num [WrongSignWeightPolynomial.Rbar]
  rw [hRbar] at hr
  simp only [U_T,U_G,neg_zero,Real.cos_zero,mul_one,mul_zero,add_zero,hlim]
  constructor <;> linarith

theorem first_at_cap :
    U_T (7/20) (4/5) (13/20)<(WrongSignWeightPolynomial.limit:ℝ) ∧
      U_G (7/20) (4/5) (13/20)<(WrongSignWeightPolynomial.limit:ℝ) := by
  have hnT : pairNorm (4/5) (13/20) (-(7/20))+pairNorm 1 (13/20) 0≤
      (840171/1000000 : ℝ)+1192687/1000000 := by
    linarith [first_norm_bounds.2.2.1,first_norm_bounds.2.1]
  have hnG : pairNorm (4/5) (13/20) 0+pairNorm 1 (13/20) (-(7/20))≤
      (1030777/1000000 : ℝ)+494149/500000 := by
    linarith [first_norm_bounds.1,first_norm_bounds.2.2.2]
  have hmT := mul_le_mul_of_nonneg_left hnT R_nonneg
  have hmG := mul_le_mul_of_nonneg_left hnG R_nonneg
  have hrT := mul_lt_mul_of_pos_right radius_reserves.1
    (show (0:ℝ)<840171/1000000+1192687/1000000 by norm_num)
  have hrG := mul_lt_mul_of_pos_right radius_reserves.1
    (show (0:ℝ)<1030777/1000000+494149/500000 by norm_num)
  have hc := cos_lower_six (show (0:ℝ)≤7/20 by norm_num)
  have hlim : (WrongSignWeightPolynomial.limit:ℝ)=518907/1250000 := by
    norm_num [WrongSignWeightPolynomial.limit]
  have hRbar : (WrongSignWeightPolynomial.Rbar:ℝ)=494697/250000 := by
    norm_num [WrongSignWeightPolynomial.Rbar]
  rw [hRbar] at hrT hrG
  simp only [U_T,U_G,charge,hlim]
  constructor <;> linarith

end SquaresInCircles.Eight.WrongSignCaptureScalars
end
end
end

section
/-!
## All admissible analytic capture weights

Convexity handles the first constant family from its two rational endpoint bounds
(`first_family`). The middle and last families use their exact polynomial radical comparisons
(`WrongSignWeightPolynomial`). The three intrinsic ranges exhaust every three-frame hull width
(`weights`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.WrongSignCaptureWeights
open PositiveAngularEnvelope EndpointRotationPenalty WrongSignCaptureScalars

theorem convex_segment_upper {f : ℝ → ℝ} {u x : ℝ}
    (hf : ConvexOn ℝ (Icc 0 frameCap) f)
    (hu : u∈Icc 0 frameCap) (hx : x∈Icc 0 u) :
    f x≤ max (f 0) (f u) := by
  by_cases hu0 : u=0
  · have hx0 : x=0 := by linarith [hx.1,hx.2]
    simp [hu0,hx0]
  · have hup : 0<u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
    let a : ℝ := (u-x)/u
    let b : ℝ := x/u
    have ha : 0≤a := div_nonneg (sub_nonneg.mpr hx.2) hu.1
    have hb : 0≤b := div_nonneg hx.1 hu.1
    have hab : a+b=1 := by dsimp [a,b]; field_simp [hu0]; ring
    have harg : a*0+b*u=x := by
      simp only [b,mul_zero,zero_add]
      exact div_mul_cancel₀ x hu0
    have hh := hf.2 (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hu ha hb hab
    simp only [smul_eq_mul,harg] at hh
    have hL := mul_le_mul_of_nonneg_left (le_max_left (f 0) (f u)) ha
    have hU := mul_le_mul_of_nonneg_left (le_max_right (f 0) (f u)) hb
    have hweight := congrArg (fun z : ℝ => z*max (f 0) (f u)) hab
    linarith

theorem convex_translate_lt {f : ℝ → ℝ} {u x c L : ℝ}
    (hf : ConvexOn ℝ (Icc 0 frameCap) f)
    (hu : u∈Icc 0 frameCap) (hx : x∈Icc 0 u)
    (hzero : f 0+c<L) (hend : f u+c<L) :
    f x+c<L := by
  have hh := convex_segment_upper hf hu hx
  rcases le_total (f 0) (f u) with h | h
  · rw [max_eq_right h] at hh
    linarith
  · rw [max_eq_left h] at hh
    linarith

theorem first_family {rho : ℝ} (hrho : rho∈Icc 0 (7/20 : ℝ)) :
    Admissible (4/5) (13/20) ∧
      U_T rho (4/5) (13/20)<(WrongSignWeightPolynomial.limit:ℝ) ∧
      U_G rho (4/5) (13/20)<(WrongSignWeightPolynomial.limit:ℝ) := by
  let cT : ℝ := R*pairNorm 1 (13/20) 0-2*(4/5)/5-8/5-2*(13/20)
  let cG : ℝ := R*pairNorm (4/5) (13/20) 0-7*(4/5)/5-3/5-2*(13/20)
  have heT (t : ℝ) : U_T t (4/5) (13/20)=WrongSignCaptureHull.F (4/5) (13/20) t+cT := by
    dsimp [U_T,WrongSignCaptureHull.F,WrongSignCaptureHull.R,WrongSignCaptureHull.p,cT]
    ring
  have heG (t : ℝ) : U_G t (4/5) (13/20)=WrongSignCaptureHull.F 1 (13/20) t+cG := by
    dsimp [U_G,WrongSignCaptureHull.F,WrongSignCaptureHull.R,WrongSignCaptureHull.p,cG]
    ring
  have hu : (7/20 : ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hT := convex_translate_lt
    (WrongSignCaptureHull.F_convex (show (0:ℝ)<13/20 by norm_num)
      (show (13/20 : ℝ)≤4/5 by norm_num)) hu hrho
    (show WrongSignCaptureHull.F (4/5) (13/20) 0+cT<(WrongSignWeightPolynomial.limit:ℝ) by
      rw [← heT]; exact first_at_zero.1)
    (show WrongSignCaptureHull.F (4/5) (13/20) (7/20)+cT<(WrongSignWeightPolynomial.limit:ℝ) by
      rw [← heT]; exact first_at_cap.1)
  have hG := convex_translate_lt
    (WrongSignCaptureHull.F_convex (show (0:ℝ)<13/20 by norm_num)
      (show (13/20 : ℝ)≤1 by norm_num)) hu hrho
    (show WrongSignCaptureHull.F 1 (13/20) 0+cG<(WrongSignWeightPolynomial.limit:ℝ) by
      rw [← heG]; exact first_at_zero.2)
    (show WrongSignCaptureHull.F 1 (13/20) (7/20)+cG<(WrongSignWeightPolynomial.limit:ℝ) by
      rw [← heG]; exact first_at_cap.2)
  rw [← heT] at hT
  rw [← heG] at hG
  exact ⟨by norm_num [Admissible],hT,hG⟩

/-- One admissible pair is chosen at the hull width; no weight varies during the later
convexity comparisons. -/
theorem weights {rho : ℝ} (hrho : rho∈Icc 0 frameCap) :
    ∃ a b,Admissible a b ∧ U_T rho a b<(WrongSignWeightPolynomial.limit:ℝ) ∧
      U_G rho a b<(WrongSignWeightPolynomial.limit:ℝ) := by
  by_cases hfirst : rho≤7/20
  · have hh := first_family (show rho∈Icc 0 (7/20 : ℝ) from ⟨hrho.1,hfirst⟩)
    exact ⟨4/5,13/20,hh⟩
  · by_cases hmiddle : rho≤47/100
    · exact middle_family ⟨by linarith,hmiddle⟩
    · exact last_family ⟨by linarith,hrho.2⟩

end SquaresInCircles.Eight.WrongSignCaptureWeights
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.WrongSignCaptureGeometry
open PositiveAngularEnvelope EndpointRotationPenalty WrongSignCaptureScalars
open WrongSignCaptureWeights

def hullWidth (x s : ℝ) : ℝ := max (-x) (max (-s) (-(x+s)))
def quarterWidth (b c s : ℝ) : ℝ :=
  if 0≤ s then c+b*PositiveAngularEnvelope.phi s else c*Real.cos s+b
def offset (alpha b : ℝ) : ℝ := -2*alpha/5-3/5-b
def angular (alpha a b c x s : ℝ) : ℝ :=
  R*(pairNorm a b x+pairNorm c b s)-a*(1+psi x)-quarterWidth b c s-
    charge*(x+s)+offset alpha b
def endpointT (alpha a b c rho : ℝ) : ℝ :=
  WrongSignCaptureHull.F a b rho+R*pairNorm c b 0-c-b+offset alpha b
def endpointG (alpha a b c rho : ℝ) : ℝ :=
  R*pairNorm a b 0-a+WrongSignCaptureHull.F c b rho-b+offset alpha b

theorem hull_mem {x s : ℝ} (hx : |x|≤frameCap) (hs : |s|≤frameCap)
    (ht : |x+s|≤frameCap) (hr : x+s≤0) : hullWidth x s∈Icc 0 frameCap := by
  have hlow : -(x+s)≤hullWidth x s :=
    (le_max_right (-s) (-(x+s))).trans (le_max_right (-x) (max (-s) (-(x+s))))
  refine ⟨by linarith,?_⟩
  exact max_le ((neg_le_abs x).trans hx)
    (max_le ((neg_le_abs s).trans hs) ((neg_le_abs (x+s)).trans ht))

theorem hull_below {x s : ℝ} (hs : 0≤ s) (hr : x+s≤0) : hullWidth x s= -x := by
  apply le_antisymm
  · exact max_le (le_refl _) (max_le (by linarith) (by linarith))
  · exact le_max_left _ _

theorem hull_above {x s : ℝ} (hx : 0≤x) (hr : x+s≤0) : hullWidth x s= -s := by
  apply le_antisymm
  · exact max_le (by linarith) (max_le (le_refl _) (by linarith))
  · exact (le_max_left _ _).trans (le_max_right _ _)

theorem hull_between {x s : ℝ} (hx : x≤0) (hs : s≤0) :
    hullWidth x s= -(x+s) := by
  apply le_antisymm
  · exact max_le (by linarith) (max_le (by linarith) (le_refl _))
  · exact (le_max_right _ _).trans (le_max_right _ _)

/-- The exact middle width minimum is multiplied only by a positive
actual stress coefficient. -/
theorem scaled_width {b c d v : ℝ} (hc : 0<c)
    (hr : b/c∈Icc (13/20 : ℝ) (23/25))
    (hd : |d|≤frameCap) (hv : |v|≤frameCap) (hs : |d+v|≤frameCap) :
    quarterWidth b c (d+v)≤b*(1+psi d)+c*(1+psi v) := by
  have hratio : b/c∈Icc (13/20 : ℝ) 1 := ⟨hr.1,by linarith [hr.2]⟩
  have hw := mul_le_mul_of_nonneg_left
    (MiddleAngularPenalty.signed_width hratio hd hv hs) hc.le
  have he : c*(b/c)=b := by field_simp [hc.ne']
  have hed := congrArg (fun z : ℝ => z*psi d) he
  by_cases hs0 : 0≤d+v
  · have hes := congrArg (fun z : ℝ => z*(PositiveAngularEnvelope.phi (d+v)-1)) he
    rw [quarterWidth,ite_eq_left hs0]
    rw [MiddleAngularPenalty.endpointWidth,ite_eq_left hs0] at hw
    nlinarith
  · rw [quarterWidth,ite_eq_right hs0]
    rw [MiddleAngularPenalty.endpointWidth,ite_eq_right hs0] at hw
    nlinarith

theorem convex_split {f g : ℝ → ℝ} {u v : ℝ}
    (hf : ConvexOn ℝ (Icc 0 frameCap) f) (hg : ConvexOn ℝ (Icc 0 frameCap) g)
    (hu : 0≤u) (hv : 0≤v) (hspan : u+v≤frameCap) :
    f u+g v≤ max (f 0+g (u+v)) (f (u+v)+g 0) := by
  by_cases hzero : u+v=0
  · have hu0 : u=0 := by linarith
    have hv0 : v=0 := by linarith
    simp [hu0,hv0]
  · have hpos : 0<u+v := lt_of_le_of_ne (add_nonneg hu hv) (Ne.symm hzero)
    let a : ℝ := v/(u+v)
    let b : ℝ := u/(u+v)
    have ha : 0≤a := div_nonneg hv hpos.le
    have hb : 0≤b := div_nonneg hu hpos.le
    have hab : a+b=1 := by dsimp [a,b]; field_simp [hzero]; ring
    have hargf : a*0+b*(u+v)=u := by
      simp only [b,mul_zero,zero_add]
      exact div_mul_cancel₀ u hzero
    have hargg : b*0+a*(u+v)=v := by
      simp only [a,mul_zero,zero_add]
      exact div_mul_cancel₀ v hzero
    have hz : (0:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
    have ht : u+v∈Icc 0 frameCap := ⟨by linarith,hspan⟩
    have hfc := hf.2 hz ht ha hb hab
    have hgc := hg.2 hz ht hb ha (by linarith : b+a=1)
    simp only [smul_eq_mul,hargf] at hfc
    simp only [smul_eq_mul,hargg] at hgc
    have hL := mul_le_mul_of_nonneg_left
      (le_max_left (f 0+g (u+v)) (f (u+v)+g 0)) ha
    have hU := mul_le_mul_of_nonneg_left
      (le_max_right (f 0+g (u+v)) (f (u+v)+g 0)) hb
    have hweight := congrArg
      (fun z : ℝ => z*max (f 0+g (u+v)) (f (u+v)+g 0)) hab
    linarith

theorem angular_hull {alpha a b c x s L : ℝ}
    (hb : 0<b) (hba : b≤a) (ha1 : a≤1) (hbc : b≤c) (hc1 : c≤1)
    (hratio : b/c∈Icc (13/20 : ℝ) (23/25))
    (hx : |x|≤frameCap) (hs : |s|≤frameCap) (ht : |x+s|≤frameCap) (hr : x+s≤0)
    (hT : endpointT alpha a b c (hullWidth x s)<L)
    (hG : endpointG alpha a b c (hullWidth x s)<L) :
    angular alpha a b c x s<L := by
  have ha : 0<a := hb.trans_le hba
  have hc : 0<c := hb.trans_le hbc
  have hz : (0:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  by_cases hs0 : 0≤ s
  · have hs' : s∈Icc 0 frameCap := ⟨hs0,(le_abs_self s).trans hs⟩
    have hx' : -x∈Icc 0 frameCap := ⟨by linarith,(neg_le_abs x).trans hx⟩
    have hpsi : psi x=Real.cos x-1 := by
      simpa only [neg_neg,Real.cos_neg] using psi_negative hx'
    have hB := (WrongSignCaptureHull.B_antitone hc hc1 hratio) hz hs' hs0
    have hB0 : WrongSignCaptureHull.B c b 0=R*pairNorm c b 0-b := by
      simp [WrongSignCaptureHull.B,WrongSignCaptureHull.R,WrongSignCaptureHull.p]
    have he : angular alpha a b c x s=
        WrongSignCaptureHull.F a b (-x)+WrongSignCaptureHull.B c b s-c+offset alpha b := by
      rw [angular,quarterWidth,ite_eq_left hs0,hpsi]
      simp only [WrongSignCaptureHull.F,WrongSignCaptureHull.B,WrongSignCaptureHull.R,
        WrongSignCaptureHull.p,neg_neg,Real.cos_neg]
      ring
    rw [hull_below hs0 hr] at hT
    rw [hB0] at hB
    rw [he]
    dsimp [endpointT] at hT
    linarith
  · have hsn : s≤0 := by linarith
    have hs' : -s∈Icc 0 frameCap := ⟨by linarith,(neg_le_abs s).trans hs⟩
    by_cases hx0 : 0≤x
    · have hx' : x∈Icc 0 frameCap := ⟨hx0,(le_abs_self x).trans hx⟩
      have hA := (WrongSignCaptureHull.A_antitone hb hba ha1) hz hx' hx0
      have hA0 : WrongSignCaptureHull.A a b 0=R*pairNorm a b 0-a := by
        simp [WrongSignCaptureHull.A,WrongSignCaptureHull.R,WrongSignCaptureHull.p]
      have he : angular alpha a b c x s=
          WrongSignCaptureHull.A a b x+WrongSignCaptureHull.F c b (-s)-b+offset alpha b := by
        rw [angular,quarterWidth,ite_eq_right hs0,psi_positive hx']
        simp only [WrongSignCaptureHull.F,WrongSignCaptureHull.A,WrongSignCaptureHull.R,
          WrongSignCaptureHull.p,neg_neg,Real.cos_neg]
        ring
      rw [hull_above hx0 hr] at hG
      rw [hA0] at hA
      rw [he]
      dsimp [endpointG] at hG
      linarith
    · have hx' : -x∈Icc 0 frameCap := ⟨by linarith,(neg_le_abs x).trans hx⟩
      have hspan : -x+-s≤frameCap := by
        have hh := (neg_le_abs (x+s)).trans ht
        linarith
      have hsplit := convex_split (WrongSignCaptureHull.F_convex hb hba)
        (WrongSignCaptureHull.F_convex hb hbc) hx'.1 hs'.1 hspan
      have hpsi : psi x=Real.cos x-1 := by
        simpa only [neg_neg,Real.cos_neg] using psi_negative hx'
      have he : angular alpha a b c x s=
          WrongSignCaptureHull.F a b (-x)+WrongSignCaptureHull.F c b (-s)-b+offset alpha b := by
        rw [angular,quarterWidth,ite_eq_right hs0,hpsi]
        simp only [WrongSignCaptureHull.F,WrongSignCaptureHull.R,WrongSignCaptureHull.p,
          neg_neg,Real.cos_neg]
        ring
      have hρ : hullWidth x s= -x+-s := by
        rw [hull_between (by linarith) hsn]
        ring
      rw [hρ] at hT hG
      have hzeroA : WrongSignCaptureHull.F a b 0=R*pairNorm a b 0-a := by
        simp [WrongSignCaptureHull.F,WrongSignCaptureHull.R,WrongSignCaptureHull.p]
      have hzeroC : WrongSignCaptureHull.F c b 0=R*pairNorm c b 0-c := by
        simp [WrongSignCaptureHull.F,WrongSignCaptureHull.R,WrongSignCaptureHull.p]
      have hleft : WrongSignCaptureHull.F a b 0+WrongSignCaptureHull.F c b (-x+-s)-b+
          offset alpha b<L := by rw [hzeroA]; exact hG
      have hright : WrongSignCaptureHull.F a b (-x+-s)+WrongSignCaptureHull.F c b 0-b+
          offset alpha b<L := by rw [hzeroC]; dsimp [endpointT] at hT; linarith
      rw [he]
      rcases le_total
          (WrongSignCaptureHull.F a b 0+WrongSignCaptureHull.F c b (-x+-s))
          (WrongSignCaptureHull.F a b (-x+-s)+WrongSignCaptureHull.F c b 0) with h | h
      · rw [max_eq_right h] at hsplit
        linarith
      · rw [max_eq_left h] at hsplit
        linarith

theorem admissible_domains {a b : ℝ} (h : Admissible a b) :
    0<a ∧ 0<b ∧ b≤a ∧ b≤1 ∧ b/a∈Icc (13/20 : ℝ) (23/25) := by
  have ha : 0<a := by linarith [h.1.1]
  have hb : 0<b := by linarith [h.2.1.1]
  refine ⟨ha,hb,by nlinarith [h.2.2],by linarith [h.2.1.2],?_⟩
  constructor
  · apply (le_div_iff₀ ha).2
    linarith [h.1.2,h.2.1.1]
  · exact (div_le_iff₀ ha).2 h.2.2

theorem selected_endpoints (alpha b rho : ℝ) :
    endpointT alpha alpha b 1 rho=U_T rho alpha b ∧
      endpointG alpha alpha b 1 rho=U_G rho alpha b ∧
      endpointT alpha 1 b alpha rho=U_G rho alpha b ∧
      endpointG alpha 1 b alpha rho=U_T rho alpha b := by
  dsimp [endpointT,endpointG,U_T,U_G,offset,WrongSignCaptureHull.F,
    WrongSignCaptureHull.R,WrongSignCaptureHull.p]
  refine ⟨?_,?_,?_,?_⟩ <;> ring

/-- At every actual reversed total, one admissible weight pair controls
both possible wrong signs on the original middle path. -/
theorem angular_bounds {x s : ℝ} (hx : |x|≤frameCap) (hs : |s|≤frameCap)
    (ht : |x+s|≤frameCap) (hr : x+s≤0) :
    ∃ alpha b,Admissible alpha b ∧
      angular alpha alpha b 1 x s<(WrongSignWeightPolynomial.limit:ℝ) ∧
      angular alpha 1 b alpha x s<(WrongSignWeightPolynomial.limit:ℝ) := by
  obtain ⟨alpha,b,hadm,hT,hG⟩ := weights (hull_mem hx hs ht hr)
  obtain ⟨ha,hb,hba,hb1,hratio⟩ := admissible_domains hadm
  have hends := selected_endpoints alpha b (hullWidth x s)
  refine ⟨alpha,b,hadm,?_,?_⟩
  · exact angular_hull hb hba hadm.1.2 hb1 (by norm_num)
      (by simpa using hadm.2.1) hx hs ht hr
      (by rw [hends.1]; exact hT) (by rw [hends.2.1]; exact hG)
  · exact angular_hull hb hb1 (by norm_num) hba hadm.1.2 hratio hx hs ht hr
      (by rw [hends.2.2.1]; exact hG) (by rw [hends.2.2.2]; exact hT)

end SquaresInCircles.Eight.WrongSignCaptureGeometry
end
end
end

module

public import SquaresInCircles.Eight.TableFree.PowerTailBounds

/-!
# Exact whole-interval coefficients for small wrong signs

Uncompiled source draft.  These are the explicitly defined middle and
last weight families from the hand proof.  Each radical is bounded by
its positive quadratic tangent, so the desired comparison is a single
rational polynomial.  Centered power norms establish positivity on each
complete analytic range; no pointwise samples or acceptance tables enter.

For the G middle family, expansion at its right endpoint gives a direct
one-sided linear lower bound.  This is equivalent to the hand note's
derivative comparison and avoids a separate polynomial-calculus step.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.WrongSignWeightPolynomial
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

end SquaresInCircles.Eight.TableFree.WrongSignWeightPolynomial

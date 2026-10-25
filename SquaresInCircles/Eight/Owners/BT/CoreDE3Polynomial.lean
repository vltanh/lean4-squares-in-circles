module

public import SquaresInCircles.Eight.Owners.BT.CoreDE3Data
public import SquaresInCircles.Eight.Owners.BT.TailPolynomials
public import SquaresInCircles.Eight.Arithmetic.PolynomialCertificates

/-!
# Eight squares: whole-interval bounds for the core-E DE3 scalars

The small-DE prefix polynomial and the saturated aligned prefix polynomial have positive Bernstein
coefficients on their intervals, `[0, 7/10]` and `[1/5, 7/10]` (`PrefixPolynomial.positive`,
`BasePolynomial.positive`).
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalBT.CoreDE3

open Polynomial PowerTailBounds FrameCircleArc

namespace PrefixPolynomial

def c : ℚ[X] := C (3/5)+C (2/5)*X
def P1 : ℚ[X] := C (1149087/1000000)-C (308159/1000000)*X-C (293179/1000000)*X^2
def P2 : ℚ[X] := C (1149087/1000000)+C (210926/1000000)*X+C (41598/1000000)*X^2
def X1 : ℚ[X] := C ((49/50)^2)+c^2-C (2*(49/50))*c*TailPolynomial.S7
def X2 : ℚ[X] := C ((49/50)^2)+c^2
def L : ℚ[X] := C (314159/100000+3*(49/50)-16761/4520)-X+C 2*c+
  C (49/50)*TailPolynomial.C6
def H : ℚ[X] := C 2*P1*P2*L-C (1979/1000)*(P2*(X1+P1^2)+P1*(X2+P2^2))


@[simp] theorem c_eval (p : ℝ) : aeval p c=weight p := by simp [c,weight,slope]

/-- `H` has positive Bernstein coefficients of degree `10` on `[0, 7/10]`: it is a positive
combination of the products `p^i (7/10 - p)^(10-i)`, which `linarith` finds. -/
theorem positive {p : ℝ} (hp : p∈Icc 0 frameCap) : 0<aeval p H := by
  have h1 : 0≤7/10-p := sub_nonneg.2 hp.2
  have hb (i j : ℕ) : 0≤p^i*(7/10-p)^j := mul_nonneg (pow_nonneg hp.1 i) (pow_nonneg h1 j)
  simp only [H,P1,P2,L,X1,X2,c,TailPolynomial.S7,TailPolynomial.C6,map_add,map_sub,map_mul,
    map_pow,map_one,aeval_C,aeval_X,eq_ratCast]
  push_cast
  linarith [hb 10 0,hb 9 1,hb 8 2,hb 7 3,hb 6 4,hb 5 5,hb 4 6,hb 3 7,hb 2 8,hb 1 9,hb 0 10]

theorem envelopes_positive {p : ℝ} (hp : p∈Icc 0 frameCap) :
    (3/4:ℝ)<aeval p P1 ∧ 1<aeval p P2 := by
  have h2 := pow_le_pow_left₀ hp.1 hp.2 2
  dsimp [frameCap] at hp h2
  norm_num [P1,P2]
  constructor <;> nlinarith [hp.1,hp.2,sq_nonneg p]

end PrefixPolynomial

namespace BasePolynomial

def P : ℚ[X] := C (3083/2500)-C (73/500)*X^2+C (4/125)*X^4
def coefficient : ℚ[X] :=
  C (314159/100000+(5/2)*(49/50)+6/5-11369/5000-16761/4520+(269343/250000)/2)-X
def U : ℚ[X] := 1-C (1/2)*X^2+C (1/24)*X^4
def L : ℚ[X] := coefficient*TailPolynomial.C6+
  C (269343/250000)*(1+C (13/12)*TailPolynomial.S7)
def energy : ℚ[X] := C ((269343/250000)^2)+C (9/25)*U^2
def H : ℚ[X] := C 2*P*L-C (1979/1000)*(energy+P^2)

/-- `H` has positive Bernstein coefficients of degree `11` on `[1/5, 7/10]`. -/
theorem positive {t : ℝ} (ht : t∈Icc (1/5:ℝ) frameCap) : 0<aeval t H := by
  have h0 : 0≤t-1/5 := sub_nonneg.2 ht.1
  have h1 : 0≤7/10-t := sub_nonneg.2 ht.2
  have hb (i j : ℕ) : 0≤(t-1/5)^i*(7/10-t)^j := mul_nonneg (pow_nonneg h0 i) (pow_nonneg h1 j)
  simp only [H,P,L,coefficient,energy,U,TailPolynomial.S7,TailPolynomial.C6,map_add,map_sub,
    map_mul,map_pow,map_one,aeval_C,aeval_X,eq_ratCast]
  push_cast
  linarith [hb 11 0,hb 10 1,hb 9 2,hb 8 3,hb 7 4,hb 6 5,hb 5 6,hb 4 7,hb 3 8,hb 2 9,hb 1 10,
    hb 0 11]

theorem envelope_positive {t : ℝ} (ht : t∈Icc 0 frameCap) : 1<aeval t P := by
  have h2 := pow_le_pow_left₀ ht.1 ht.2 2
  dsimp [frameCap] at ht h2
  norm_num [P]
  nlinarith [pow_nonneg (sq_nonneg t) 2]

theorem coefficient_positive {t : ℝ} (ht : t∈Icc 0 frameCap) :
    0<aeval t coefficient := by
  norm_num [coefficient]
  dsimp [frameCap] at ht
  linarith [ht.2]

end BasePolynomial

end SquaresInCircles.Eight.GlobalBT.CoreDE3

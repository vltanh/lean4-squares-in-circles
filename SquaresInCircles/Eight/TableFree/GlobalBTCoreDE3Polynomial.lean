module

public import SquaresInCircles.Eight.TableFree.GlobalBTCoreDE3Data

/-!
# Whole-interval certificates for the core-E DE3 scalars

The small-DE prefix uses one centered quadratic reserve.  The
saturated aligned prefix uses one centered coefficient norm on its
entire interval.  All certificates are fixed rational identities.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalBT.CoreDE3

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
def centered : ℚ[X] := shift (7/20) H

@[simp] theorem c_eval (p : ℝ) : aeval p c=weight p := by simp [c,weight,slope]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem centered_identity : centered=C (centered.coeff 0)+C (centered.coeff 1)*X+
    C (centered.coeff 2)*X^2+tail centered 3 8 := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem centered_reserves : 0<centered.coeff 2-norm centered 3 8 (7/20) ∧
    (centered.coeff 1)^2<4*(centered.coeff 0)*(centered.coeff 2-norm centered 3 8 (7/20)) := by
  decide

theorem positive {p : ℝ} (hp : p∈Icc 0 frameCap) : 0<aeval p H := by
  have hl := PowerTailBounds.quadratic_lower centered_identity
    (by norm_num : (0:ℚ)≤7/20) (TailPolynomial.centered_domain hp)
  have ha : 0<(centered.coeff 2:ℝ)-(norm centered 3 8 (7/20):ℝ) := by
    exact_mod_cast centered_reserves.1
  have hd : (centered.coeff 1:ℝ)^2<4*
      ((centered.coeff 2:ℝ)-(norm centered 3 8 (7/20):ℝ))*(centered.coeff 0:ℝ) := by
    have hh := centered_reserves.2
    exact_mod_cast (by nlinarith [hh] : (centered.coeff 1)^2<4*
      (centered.coeff 2-norm centered 3 8 (7/20))*(centered.coeff 0))
  have hpos := TailPolynomial.strict_quadratic (x := p-7/20) ha hd
  have he : aeval (p-7/20) centered=aeval p H := by simp [centered,shift_eval]
  rw [he] at hl
  linarith

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
def centered : ℚ[X] := shift (9/20) H

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem centered_identity : centered=C (centered.coeff 0)+tail centered 1 11 := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem centered_reserve : 0<centered.coeff 0-norm centered 1 11 (1/4) := by decide

theorem positive {t : ℝ} (ht : t∈Icc (1/5:ℝ) frameCap) : 0<aeval t H := by
  have hdom : |t-(9/20:ℝ)|≤1/4 := by
    rw [abs_le]
    dsimp [frameCap] at ht
    constructor <;> linarith [ht.1,ht.2]
  have hl := DirectedPowerBounds.constant_lower centered_identity hdom
  have hp : 0<(centered.coeff 0:ℝ)-(norm centered 1 11 (1/4):ℝ) := by
    exact_mod_cast centered_reserve
  have he : aeval (t-9/20) centered=aeval t H := by simp [centered,shift_eval]
  rw [he] at hl
  linarith

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

end SquaresInCircles.Eight.TableFree.GlobalBT.CoreDE3

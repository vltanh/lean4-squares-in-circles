module

public import SquaresInCircles.Eight.Owners.CenteredMonomialBounds
public import SquaresInCircles.Eight.Owners.DirectedPowerBounds
public import SquaresInCircles.Eight.Owners.BT.Markers

/-!
# Eight squares: the six complete DE2 tail polynomials

Three intrinsic E charts each give two one-variable endpoint scalars.
Every polynomial is positive on the full interval [0,.7], where its
Bernstein coefficients of degree ten are positive (`positive`).  All constants are rational consequences
of the displayed force norms.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalBT.TailPolynomial

open Polynomial PowerTailBounds DirectedPowerBounds

def e : Fin 3→ℚ := ![9449/10000,797/1000,16/25]
def m : Fin 3→ℚ := ![0,229/5000,67/500]
def initial : Fin 3→ℚ := ![567/1000,13/25,23/50]
def slope : Fin 3→ℚ := ![89/200,73/200,1/4]
def join : Fin 3→ℚ := ![33/445,16/73,14/25]
def weight (i : Fin 3) : ℚ[X] := C (initial i)+C (slope i)*X
def S7 : ℚ[X] := X-C (1/6)*X^3+C (1/120)*X^5-C (1/5040)*X^7
def C6 : ℚ[X] := 1-C (1/2)*X^2+C (1/24)*X^4-C (1/720)*X^6
def p1 (i : Fin 3) (last : Bool) : ℚ[X] :=
  if last then
    ![C (1132205/1000000)+C (225750/1000000)*X+C (52828/1000000)*X^2,
      C (1109414/1000000)+C (172770/1000000)*X+C (39524/1000000)*X^2,
      C (1082589/1000000)+C (106793/1000000)*X+C (21222/1000000)*X^2] i
  else
    ![C (1132205/1000000)-C (274033/1000000)*X-C (308441/1000000)*X^2,
      C (1109414/1000000)-C (291174/1000000)*X-C (290425/1000000)*X^2,
      C (1082589/1000000)-C (312978/1000000)*X-C (232552/1000000)*X^2] i
def p2 (i : Fin 3) (last : Bool) : ℚ[X] :=
  if last then
    ![C (1101964/1000000)-C (264348/1000000)*X-C (296959/1000000)*X^2,
      C (951635/1000000)-C (242875/1000000)*X-C (241022/1000000)*X^2,
      C (788162/1000000)-C (232523/1000000)*X-C (178814/1000000)*X^2] i
  else
    ![C (1101964/1000000)+C (232011/1000000)*X+C (52697/1000000)*X^2,
      C (951635/1000000)+C (201690/1000000)*X+C (39207/1000000)*X^2,
      C (788162/1000000)+C (146966/1000000)*X+C (21489/1000000)*X^2] i
def x1 (i : Fin 3) (last : Bool) : ℚ[X] :=
  C ((49/50)^2)+weight i^2-(if last then 0 else C (2*(49/50))*weight i*S7)
def x2 (i : Fin 3) (last : Bool) : ℚ[X] :=
  C (e i^2)+weight i^2-(if last then C (2*e i)*weight i*S7 else 0)
def cosinePart (i : Fin 3) (last : Bool) : ℚ[X] :=
  if last then C (49/50)+C (e i)*C6 else C (49/50)*C6+C (e i)
def distance (i : Fin 3) (last : Bool) : ℚ[X] :=
  C (314159/100000+(3/2)*(49/50)+(1/2)*e i+m i-16761/4520)-X+
    C 2*weight i+cosinePart i last
def certificate (i : Fin 3) (last : Bool) : ℚ[X] :=
  C 2*p1 i last*p2 i last*distance i last-C (1979/1000)*
    (p2 i last*(x1 i last+p1 i last^2)+p1 i last*(x2 i last+p2 i last^2))

@[simp] theorem weight_eval (i : Fin 3) (z : ℝ) :
    aeval z (weight i)=(initial i:ℝ)+(slope i:ℝ)*z := by simp [weight]
@[simp] theorem S7_eval (z : ℝ) : aeval z S7=Arithmetic.sin7 z := by
  simp [S7,Arithmetic.sin7]
  ring
@[simp] theorem C6_eval (z : ℝ) : aeval z C6=1-z^2/2+z^4/24-z^6/720 := by
  simp [C6]
  ring

theorem rational_aeval (p : ℚ[X]) (r : ℚ) : aeval (r:ℝ) p=((p.eval r:ℚ):ℝ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp,hq]
  | monomial n a => simp

theorem centered_domain {z : ℝ} (hz : z∈Icc 0 frameCap) :
    |z-(7/20:ℝ)|≤7/20 := by
  rw [abs_le]
  dsimp [frameCap] at hz
  constructor <;> linarith [hz.1,hz.2]

theorem strict_quadratic {a b c x : ℝ} (ha : 0<a) (hd : b^2<4*a*c) :
    0<a*x^2+b*x+c := by
  have hh := sq_nonneg (2*a*x+b)
  have hmul : 0<4*a*(a*x^2+b*x+c) := by nlinarith only [hh,hd]
  exact (mul_pos_iff_of_pos_left (by positivity : 0<4*a)).1 hmul

/-- Each of the six polynomials has positive Bernstein coefficients of degree `10` on
`[0, 7/10]`: it is a positive combination of the products `z^i (7/10 - z)^(10-i)`, which
`linarith` finds. -/
local macro "tail_positive" : tactic => `(tactic| (
  intro z hz
  have h1 : 0≤7/10-z := sub_nonneg.2 hz.2
  have hb (i j : ℕ) : 0≤z^i*(7/10-z)^j := mul_nonneg (pow_nonneg hz.1 i) (pow_nonneg h1 j)
  simp only [certificate,p1,p2,x1,x2,cosinePart,distance,weight,e,m,initial,slope,S7,C6,
    Bool.false_eq_true,↓reduceIte,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,map_add,map_sub,
    map_mul,map_pow,map_one,map_zero,sub_zero,aeval_C,aeval_X,eq_ratCast]
  push_cast
  linarith [hb 10 0,hb 9 1,hb 8 2,hb 7 3,hb 6 4,hb 5 5,hb 4 6,hb 3 7,hb 2 8,hb 1 9,hb 0 10]))

private theorem positive_0_true : ∀ {z : ℝ},z∈Icc 0 frameCap → 0<aeval z (certificate 0 true) := by
  tail_positive
private theorem positive_0_false : ∀ {z : ℝ},z∈Icc 0 frameCap → 0<aeval z (certificate 0 false) := by
  tail_positive
private theorem positive_1_true : ∀ {z : ℝ},z∈Icc 0 frameCap → 0<aeval z (certificate 1 true) := by
  tail_positive
private theorem positive_1_false : ∀ {z : ℝ},z∈Icc 0 frameCap → 0<aeval z (certificate 1 false) := by
  tail_positive
private theorem positive_2_true : ∀ {z : ℝ},z∈Icc 0 frameCap → 0<aeval z (certificate 2 true) := by
  tail_positive
private theorem positive_2_false : ∀ {z : ℝ},z∈Icc 0 frameCap → 0<aeval z (certificate 2 false) := by
  tail_positive

theorem positive (i : Fin 3) (last : Bool) {z : ℝ} (hz : z∈Icc 0 frameCap) :
    0<aeval z (certificate i last) := by
  fin_cases i <;> cases last
  exacts [positive_0_false hz,positive_0_true hz,positive_1_false hz,positive_1_true hz,
    positive_2_false hz,positive_2_true hz]

theorem envelopes_positive (i : Fin 3) (last : Bool) {z : ℝ} (hz : z∈Icc 0 frameCap) :
    1/2<aeval z (p1 i last) ∧ 1/2<aeval z (p2 i last) := by
  obtain ⟨h0,h1⟩ := hz
  have h1' : z≤7/10 := h1
  have h2 : z^2≤(7/10)*z := by
    have hh := mul_le_mul_of_nonneg_left h1' h0
    nlinarith
  fin_cases i <;> cases last <;>
    simp only [p1,p2,Bool.false_eq_true,↓reduceIte,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,
      Matrix.tail_cons,map_add,map_sub,map_mul,map_pow,aeval_C,aeval_X,eq_ratCast,
      Rat.cast_div,Rat.cast_ofNat] <;>
    exact ⟨by linarith [sq_nonneg z],by linarith [sq_nonneg z]⟩

theorem weights_bounds (i : Fin 3) {z : ℝ} (hz : z∈Icc 0 frameCap) :
    0<aeval z (weight i) ∧ aeval z (weight i)≤kappa ∧ aeval z (weight i)≤(e i:ℝ) := by
  rw [weight_eval]
  dsimp [frameCap] at hz
  obtain ⟨h0,h1⟩ := hz
  fin_cases i <;> norm_num [initial,slope,e,kappa] <;>
    exact ⟨by linarith,by linarith,by linarith⟩

theorem chart_positive (i : Fin 3) : 0<(e i:ℝ) := by fin_cases i <;> norm_num [e]

theorem join_domain (i : Fin 3) : (join i:ℝ)∈Icc 0 frameCap := by
  fin_cases i <;> norm_num [join,frameCap]

theorem join_weight (i : Fin 3) : aeval (join i:ℝ) (weight i)=3/5 := by
  rw [weight_eval]
  fin_cases i <;> norm_num [initial,slope,join]

theorem constant_above_before_join (i : Fin 3) {z : ℝ} (hz : z≤(join i:ℝ)) :
    aeval z (weight i)≤3/5 := by
  rw [weight_eval]
  fin_cases i <;> norm_num [initial,slope,join] at hz ⊢ <;> linarith

theorem affine_above_after_join (i : Fin 3) {z : ℝ} (hz : (join i:ℝ)≤z) :
    3/5≤aeval z (weight i) := by
  rw [weight_eval]
  fin_cases i <;> norm_num [initial,slope,join] at hz ⊢ <;> linarith

end SquaresInCircles.Eight.GlobalBT.TailPolynomial

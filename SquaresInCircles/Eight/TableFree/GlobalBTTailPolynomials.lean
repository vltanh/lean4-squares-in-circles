module

public import SquaresInCircles.Eight.TableFree.GlobalBTTailNorm
public import SquaresInCircles.Eight.TableFree.DirectedPowerBounds
public import SquaresInCircles.Eight.TableFree.CenteredMonomialBounds

/-!
# The six complete DE2 tail polynomials

Three intrinsic E charts each give two one-variable endpoint scalars.
Every polynomial is certified on the full interval [0,.7]: the C/L
pair uses a centered quadratic, and the M/H pairs decrease to a
strictly positive endpoint.  All constants are rational consequences
of the displayed force norms.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalBT.TailPolynomial

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
def centered (last : Bool) : ℚ[X] := shift (7/20) (certificate 0 last)
def slopePoly (i : Fin 3) (last : Bool) : ℚ[X] := shift (7/20) (-(certificate i last).derivative)

@[simp] theorem weight_eval (i : Fin 3) (z : ℝ) :
    aeval z (weight i)=(initial i:ℝ)+(slope i:ℝ)*z := by simp [weight]
@[simp] theorem S7_eval (z : ℝ) : aeval z S7=Arithmetic.sin7 z := by
  simp [S7,Arithmetic.sin7]
  ring
@[simp] theorem C6_eval (z : ℝ) : aeval z C6=1-z^2/2+z^4/24-z^6/720 := by
  simp [C6]

theorem rational_aeval (p : ℚ[X]) (r : ℚ) : aeval (r:ℝ) p=(p.eval r:ℝ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp,hq]
  | monomial n a => simp

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem centered_identity (last : Bool) : centered last=C ((centered last).coeff 0)+
    C ((centered last).coeff 1)*X+C ((centered last).coeff 2)*X^2+
    tail (centered last) 3 8 := by cases last <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem centered_reserves (last : Bool) :
    0<(centered last).coeff 2-norm (centered last) 3 8 (7/20) ∧
    ((centered last).coeff 1)^2<4*((centered last).coeff 0)*
      ((centered last).coeff 2-norm (centered last) 3 8 (7/20)) := by
  cases last <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem slope_identity (i : Fin 3) (last : Bool) :
    slopePoly i last=C ((slopePoly i last).coeff 0)+tail (slopePoly i last) 1 9 := by
  fin_cases i <;> cases last <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem slope_reserve (i : Fin 3) (hi : i≠0) (last : Bool) :
    0<(slopePoly i last).coeff 0-norm (slopePoly i last) 1 9 (7/20) := by
  fin_cases i
  · exact (hi rfl).elim
  all_goals cases last <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem endpoint_reserve (i : Fin 3) (hi : i≠0) (last : Bool) :
    0<(certificate i last).eval (7/10) := by
  fin_cases i
  · exact (hi rfl).elim
  all_goals cases last <;> decide

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

theorem first_positive (last : Bool) {z : ℝ} (hz : z∈Icc 0 frameCap) :
    0<aeval z (certificate 0 last) := by
  have hl := PowerTailBounds.quadratic_lower (centered_identity last)
    (by norm_num : (0:ℚ)≤7/20) (centered_domain hz)
  have hc : 0<((centered last).coeff 2:ℝ)-(norm (centered last) 3 8 (7/20):ℝ) := by
    exact_mod_cast (centered_reserves last).1
  have hd : ((centered last).coeff 1:ℝ)^2<
      4*(((centered last).coeff 2:ℝ)-(norm (centered last) 3 8 (7/20):ℝ))*
        ((centered last).coeff 0:ℝ) := by
    have hh := (centered_reserves last).2
    exact_mod_cast (by nlinarith [hh] :
      ((centered last).coeff 1)^2<4*
        ((centered last).coeff 2-norm (centered last) 3 8 (7/20))*((centered last).coeff 0))
  have hpos := strict_quadratic (x := z-7/20) hc hd
  have he : aeval (z-7/20) (centered last)=aeval z (certificate 0 last) := by
    simp [centered,shift_eval]
  rw [he] at hl
  linarith

theorem derivative_negative (i : Fin 3) (hi : i≠0) (last : Bool)
    {z : ℝ} (hz : z∈Icc 0 frameCap) : aeval z (certificate i last).derivative<0 := by
  have hl := DirectedPowerBounds.constant_lower (slope_identity i last) (centered_domain hz)
  have hp : 0<((slopePoly i last).coeff 0:ℝ)-(norm (slopePoly i last) 1 9 (7/20):ℝ) := by
    exact_mod_cast slope_reserve i hi last
  have he : aeval (z-7/20) (slopePoly i last)= -aeval z (certificate i last).derivative := by
    simp [slopePoly,shift_eval]
  rw [he] at hl
  linarith

theorem positive (i : Fin 3) (last : Bool) {z : ℝ} (hz : z∈Icc 0 frameCap) :
    0<aeval z (certificate i last) := by
  by_cases hi : i=0
  · subst i
    exact first_positive last hz
  · have hm : AntitoneOn (fun z : ℝ => aeval z (certificate i last)) (Icc 0 frameCap) := by
      apply antiOn_of_hasDeriv_nonpos
      · exact fun z _ => (CenteredMonomialBounds.aeval_hasDerivAt (certificate i last) z).
          continuousAt.continuousWithinAt
      · exact fun z _ => CenteredMonomialBounds.aeval_hasDerivAt (certificate i last) z
      · exact fun z hz => (derivative_negative i hi last (Ioo_subset_Icc_self hz)).le
    have he : 0<aeval (frameCap:ℝ) (certificate i last) := by
      have hid : aeval (frameCap:ℝ) (certificate i last)=
          ((certificate i last).eval (7/10):ℝ) := by
        change aeval ((7/10:ℚ):ℝ) (certificate i last)=_
        exact rational_aeval _ _
      rw [hid]
      exact_mod_cast endpoint_reserve i hi last
    exact he.trans_le (hm hz ⟨by norm_num [frameCap],le_rfl⟩ hz.2)

theorem envelopes_positive (i : Fin 3) (last : Bool) {z : ℝ} (hz : z∈Icc 0 frameCap) :
    1/2<aeval z (p1 i last) ∧ 1/2<aeval z (p2 i last) := by
  have h2 := pow_le_pow_left₀ hz.1 hz.2 2
  dsimp [frameCap] at hz h2
  fin_cases i <;> cases last <;> norm_num [p1,p2] <;>
    constructor <;> nlinarith [hz.1,hz.2,sq_nonneg z]

theorem weights_bounds (i : Fin 3) {z : ℝ} (hz : z∈Icc 0 frameCap) :
    0<aeval z (weight i) ∧ aeval z (weight i)≤kappa ∧ aeval z (weight i)≤(e i:ℝ) := by
  rw [weight_eval]
  dsimp [frameCap] at hz
  fin_cases i <;> norm_num [initial,slope,e,kappa] <;>
    repeat' constructor <;> linarith [hz.1,hz.2]

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

end SquaresInCircles.Eight.TableFree.GlobalBT.TailPolynomial

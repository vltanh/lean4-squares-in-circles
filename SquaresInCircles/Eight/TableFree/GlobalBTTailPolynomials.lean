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

/-! Exact rational coefficient lists: `r33ev l` is the polynomial with coefficient list `l`.
Sums, products, shifts, derivatives and values of lists are computed by the kernel. -/
private def r33ev : List ℚ → ℚ[X]
  | [] => 0
  | a :: l => C a+X*r33ev l

private def r33add : List ℚ → List ℚ → List ℚ
  | [], m => m
  | a :: l, [] => a :: l
  | a :: l, b :: m => (a+b) :: r33add l m

private def r33smul (c : ℚ) : List ℚ → List ℚ
  | [] => []
  | a :: l => (c*a) :: r33smul c l

private def r33mul : List ℚ → List ℚ → List ℚ
  | [], _ => []
  | _, [] => []
  | a :: l, m => r33add (r33smul a m) (0 :: r33mul l m)

private def r33sub (l m : List ℚ) : List ℚ := r33add l (r33smul (-1) m)

private def r33shift (a : ℚ) : List ℚ → List ℚ
  | [] => []
  | c :: l => r33add [c] (r33mul [a,1] (r33shift a l))

private def r33deriv : List ℚ → List ℚ
  | [] => []
  | [_] => []
  | _ :: l => r33add l (0 :: r33deriv l)

private def r33eval (r : ℚ) : List ℚ → ℚ
  | [] => 0
  | c :: l => c+r*r33eval r l

private theorem r33ev_add (l m : List ℚ) : r33ev (r33add l m)=r33ev l+r33ev m := by
  induction l generalizing m with
  | nil => simp [r33add,r33ev]
  | cons a l ih =>
    cases m with
    | nil => simp [r33add,r33ev]
    | cons b m => simp only [r33add,r33ev,ih,map_add]; ring

private theorem r33ev_smul (c : ℚ) (l : List ℚ) : r33ev (r33smul c l)=C c*r33ev l := by
  induction l with
  | nil => simp [r33smul,r33ev]
  | cons a l ih => simp only [r33smul,r33ev,ih,map_mul]; ring

private theorem r33ev_mul (l m : List ℚ) : r33ev (r33mul l m)=r33ev l*r33ev m := by
  induction l with
  | nil => simp [r33mul,r33ev]
  | cons a l ih =>
    cases m with
    | nil => simp [r33mul,r33ev]
    | cons b m => simp only [r33mul,r33ev,r33ev_add,r33ev_smul,ih,map_zero]; ring

private theorem r33ev_sub (l m : List ℚ) : r33ev (r33sub l m)=r33ev l-r33ev m := by
  simp only [r33sub,r33ev_add,r33ev_smul,map_neg,map_one]; ring

private theorem r33ev_single (a : ℚ) : r33ev [a]=C a := by simp [r33ev]

private theorem r33ev_nil : r33ev []=0 := rfl

private theorem r33ev_shift (a : ℚ) (l : List ℚ) :
    r33ev (r33shift a l)=(r33ev l).comp (C a+X) := by
  induction l with
  | nil => simp [r33shift,r33ev]
  | cons c l ih =>
    simp only [r33shift,r33ev_add,r33ev_mul,ih,r33ev,add_comp,mul_comp,C_comp,X_comp,
      mul_zero,add_zero,map_one]
    ring

private theorem r33ev_deriv (l : List ℚ) : r33ev (r33deriv l)=derivative (r33ev l) := by
  induction l with
  | nil => simp [r33deriv,r33ev]
  | cons c l ih =>
    cases l with
    | nil => simp [r33deriv,r33ev]
    | cons d l =>
      have h1 : r33deriv (c :: d :: l)=r33add (d :: l) (0 :: r33deriv (d :: l)) := rfl
      have h2 : r33ev (0 :: r33deriv (d :: l))=C 0+X*r33ev (r33deriv (d :: l)) := rfl
      have h3 : r33ev (c :: d :: l)=C c+X*r33ev (d :: l) := rfl
      rw [h1,r33ev_add,h2,ih,h3]
      simp only [derivative_add,derivative_mul,derivative_C,derivative_X,map_zero]
      ring

private theorem r33ev_eval (r : ℚ) (l : List ℚ) : (r33ev l).eval r=r33eval r l := by
  induction l with
  | nil => simp [r33ev,r33eval]
  | cons c l ih => simp [r33ev,r33eval,ih]

private theorem r33_coeff (l : List ℚ) (n : ℕ) : (r33ev l).coeff n=l.getD n 0 := by
  induction l generalizing n with
  | nil => simp [r33ev]
  | cons a l ih =>
    cases n with
    | zero => simp [r33ev]
    | succ n => simp [r33ev,ih]

private theorem r33_natDegree (l : List ℚ) (n : ℕ) (h : l.length≤n+1) :
    (r33ev l).natDegree≤n := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [r33_coeff,List.getD_eq_getElem?_getD,List.getElem?_eq_none (by omega)]
  rfl

private def r33weightL (i : Fin 3) : List ℚ := [initial i,slope i]
private def r33S7L : List ℚ := [0,1,0,-(1/6),0,1/120,0,-(1/5040)]
private def r33C6L : List ℚ := [1,0,-(1/2),0,1/24,0,-(1/720)]
private def r33p1L (i : Fin 3) (last : Bool) : List ℚ :=
  if last then
    ![[1132205/1000000,225750/1000000,52828/1000000],
      [1109414/1000000,172770/1000000,39524/1000000],
      [1082589/1000000,106793/1000000,21222/1000000]] i
  else
    ![[1132205/1000000,-(274033/1000000),-(308441/1000000)],
      [1109414/1000000,-(291174/1000000),-(290425/1000000)],
      [1082589/1000000,-(312978/1000000),-(232552/1000000)]] i
private def r33p2L (i : Fin 3) (last : Bool) : List ℚ :=
  if last then
    ![[1101964/1000000,-(264348/1000000),-(296959/1000000)],
      [951635/1000000,-(242875/1000000),-(241022/1000000)],
      [788162/1000000,-(232523/1000000),-(178814/1000000)]] i
  else
    ![[1101964/1000000,232011/1000000,52697/1000000],
      [951635/1000000,201690/1000000,39207/1000000],
      [788162/1000000,146966/1000000,21489/1000000]] i
private def r33x1L (i : Fin 3) (last : Bool) : List ℚ :=
  r33sub (r33add [(49/50)^2] (r33mul (r33weightL i) (r33weightL i)))
    (if last then [] else r33mul (r33mul [2*(49/50)] (r33weightL i)) r33S7L)
private def r33x2L (i : Fin 3) (last : Bool) : List ℚ :=
  r33sub (r33add [e i^2] (r33mul (r33weightL i) (r33weightL i)))
    (if last then r33mul (r33mul [2*e i] (r33weightL i)) r33S7L else [])
private def r33cosL (i : Fin 3) (last : Bool) : List ℚ :=
  if last then r33add [49/50] (r33mul [e i] r33C6L) else r33add (r33mul [49/50] r33C6L) [e i]
private def r33distL (i : Fin 3) (last : Bool) : List ℚ :=
  r33add (r33add (r33sub [314159/100000+(3/2)*(49/50)+(1/2)*e i+m i-16761/4520] [0,1])
    (r33mul [2] (r33weightL i))) (r33cosL i last)
private def r33certL (i : Fin 3) (last : Bool) : List ℚ :=
  r33sub (r33mul (r33mul (r33mul [2] (r33p1L i last)) (r33p2L i last)) (r33distL i last))
    (r33mul [1979/1000] (r33add (r33mul (r33p2L i last)
      (r33add (r33x1L i last) (r33mul (r33p1L i last) (r33p1L i last))))
      (r33mul (r33p1L i last) (r33add (r33x2L i last) (r33mul (r33p2L i last) (r33p2L i last))))))

private theorem r33weight_ev (i : Fin 3) : weight i=r33ev (r33weightL i) := by
  simp only [weight,r33weightL,r33ev]; ring

private theorem r33S7_ev : S7=r33ev r33S7L := by
  simp only [S7,r33S7L,r33ev,map_zero,map_one,map_neg]; ring

private theorem r33C6_ev : C6=r33ev r33C6L := by
  simp only [C6,r33C6L,r33ev,map_zero,map_one,map_neg]; ring

private theorem r33p1_ev (i : Fin 3) (last : Bool) : p1 i last=r33ev (r33p1L i last) := by
  fin_cases i <;> cases last <;>
    simp only [p1,r33p1L,Bool.false_eq_true,↓reduceIte,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,
      Matrix.tail_cons,r33ev,map_neg] <;> ring

private theorem r33p2_ev (i : Fin 3) (last : Bool) : p2 i last=r33ev (r33p2L i last) := by
  fin_cases i <;> cases last <;>
    simp only [p2,r33p2L,Bool.false_eq_true,↓reduceIte,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,
      Matrix.tail_cons,r33ev,map_neg] <;> ring

private theorem r33x1_ev (i : Fin 3) (last : Bool) : x1 i last=r33ev (r33x1L i last) := by
  cases last <;>
    simp only [x1,r33x1L,Bool.false_eq_true,↓reduceIte,r33ev_sub,r33ev_add,r33ev_mul,
      r33ev_single,r33ev_nil,← r33weight_ev,← r33S7_ev] <;> ring

private theorem r33x2_ev (i : Fin 3) (last : Bool) : x2 i last=r33ev (r33x2L i last) := by
  cases last <;>
    simp only [x2,r33x2L,Bool.false_eq_true,↓reduceIte,r33ev_sub,r33ev_add,r33ev_mul,
      r33ev_single,r33ev_nil,← r33weight_ev,← r33S7_ev] <;> ring

private theorem r33dist_ev (i : Fin 3) (last : Bool) :
    distance i last=r33ev (r33distL i last) := by
  cases last <;>
    simp only [distance,cosinePart,r33distL,r33cosL,Bool.false_eq_true,↓reduceIte,
      r33ev_sub,r33ev_add,r33ev_mul,← r33weight_ev,← r33C6_ev,r33ev,
      map_zero,map_one,mul_zero,add_zero] <;> ring

private theorem r33cert_ev (i : Fin 3) (last : Bool) :
    certificate i last=r33ev (r33certL i last) := by
  simp only [certificate,r33certL,r33ev_sub,r33ev_add,r33ev_mul,r33ev_single,
    ← r33p1_ev,← r33p2_ev,← r33x1_ev,← r33x2_ev,← r33dist_ev]
  ring

private theorem r33centered_ev (last : Bool) :
    centered last=r33ev (r33shift (7/20) (r33certL 0 last)) := by
  rw [r33ev_shift,← r33cert_ev]
  rfl

private theorem r33slope_ev (i : Fin 3) (last : Bool) :
    slopePoly i last=r33ev (r33shift (7/20) (r33smul (-1) (r33deriv (r33certL i last)))) := by
  rw [r33ev_shift,r33ev_smul,r33ev_deriv,← r33cert_ev,map_neg,map_one,neg_one_mul]
  rfl

private theorem r33_quadratic_split (p : ℚ[X]) (h : p.natDegree<11) :
    p=C (p.coeff 0)+C (p.coeff 1)*X+C (p.coeff 2)*X^2+tail p 3 8 := by
  conv_lhs => rw [as_sum_range_C_mul_X_pow' p h]
  rw [show (11:ℕ)=3+8 from rfl,Finset.sum_range_add,tail,
    Fin.sum_univ_eq_sum_range (fun j => C (p.coeff (j+3))*X^(j+3)) 8]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,Nat.reduceAdd,pow_zero,pow_one,
    mul_one,zero_add]

private theorem r33_constant_split (p : ℚ[X]) (h : p.natDegree<10) :
    p=C (p.coeff 0)+tail p 1 9 := by
  conv_lhs => rw [as_sum_range_C_mul_X_pow' p h]
  rw [show (10:ℕ)=1+9 from rfl,Finset.sum_range_add,tail,
    Fin.sum_univ_eq_sum_range (fun j => C (p.coeff (j+1))*X^(j+1)) 9]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,Nat.reduceAdd,pow_zero,pow_one,
    mul_one,zero_add]

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

theorem centered_identity (last : Bool) : centered last=C ((centered last).coeff 0)+
    C ((centered last).coeff 1)*X+C ((centered last).coeff 2)*X^2+
    tail (centered last) 3 8 := by
  apply r33_quadratic_split
  rw [r33centered_ev]
  exact Nat.lt_succ_of_le (r33_natDegree _ 10 (by cases last <;> decide +kernel))

theorem centered_reserves (last : Bool) :
    0<(centered last).coeff 2-norm (centered last) 3 8 (7/20) ∧
    ((centered last).coeff 1)^2<4*((centered last).coeff 0)*
      ((centered last).coeff 2-norm (centered last) 3 8 (7/20)) := by
  rw [r33centered_ev]
  simp only [PowerTailBounds.norm,r33_coeff]
  cases last <;> decide +kernel

theorem slope_identity (i : Fin 3) (last : Bool) :
    slopePoly i last=C ((slopePoly i last).coeff 0)+tail (slopePoly i last) 1 9 := by
  apply r33_constant_split
  rw [r33slope_ev]
  exact Nat.lt_succ_of_le (r33_natDegree _ 9 (by fin_cases i <;> cases last <;> decide +kernel))

theorem slope_reserve (i : Fin 3) (hi : i≠0) (last : Bool) :
    0<(slopePoly i last).coeff 0-norm (slopePoly i last) 1 9 (7/20) := by
  rw [r33slope_ev]
  simp only [PowerTailBounds.norm,r33_coeff]
  fin_cases i
  · exact (hi rfl).elim
  all_goals cases last <;> decide +kernel

theorem endpoint_reserve (i : Fin 3) (hi : i≠0) (last : Bool) :
    0<(certificate i last).eval (7/10) := by
  rw [r33cert_ev,r33ev_eval]
  fin_cases i
  · exact (hi rfl).elim
  all_goals cases last <;> decide +kernel

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
  have hdom : |z-7/20|≤((7/20:ℚ):ℝ) := by
    push_cast
    exact centered_domain hz
  have hl := PowerTailBounds.quadratic_lower (centered_identity last)
    (by norm_num : (0:ℚ)≤7/20) hdom
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
  have hdom : |z-7/20|≤((7/20:ℚ):ℝ) := by
    push_cast
    exact centered_domain hz
  have hl := DirectedPowerBounds.constant_lower (slope_identity i last) hdom
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
      · exact fun z _ => (CenteredMonomialBounds.aeval_hasDerivAt (certificate i last) z
          ).continuousAt.continuousWithinAt
      · exact fun z _ => CenteredMonomialBounds.aeval_hasDerivAt (certificate i last) z
      · exact fun z hz => (derivative_negative i hi last (Ioo_subset_Icc_self hz)).le
    have he : 0<aeval (frameCap:ℝ) (certificate i last) := by
      have hid : aeval (frameCap:ℝ) (certificate i last)=
          (((certificate i last).eval (7/10):ℚ):ℝ) := by
        have h7 : (frameCap:ℝ)=((7/10:ℚ):ℝ) := by norm_num [frameCap]
        rw [h7]
        exact rational_aeval _ _
      rw [hid]
      exact_mod_cast endpoint_reserve i hi last
    exact he.trans_le (hm hz ⟨by norm_num [frameCap],le_rfl⟩ hz.2)

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

end SquaresInCircles.Eight.TableFree.GlobalBT.TailPolynomial

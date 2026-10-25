module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Rat.Star
public import SquaresInCircles.Eight.Owners.CenteredMonomialBounds
public import SquaresInCircles.Eight.Owners.ChebyshevLeadingBounds
public import SquaresInCircles.Eight.Owners.GA.Positive.TDPolynomialData
public import SquaresInCircles.Eight.Arithmetic.PolynomialCertificates

/-!
# Eight squares: the three independent sorted-D endpoint certificates

The two degree-eighteen polynomials retain the specified whole
interval coefficient bounds. The degree-twenty-four axis polynomial
retains its single translated quadratic and complete higher-order tail.
The exact rational reductions below are proof terms, not evaluations.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.PositiveBT3.DEndpoint
open Polynomial WholeIntervalPolynomial
open PositiveTD.Certificate (S9 S11 C10 C12)

inductive End where | one | upper
  deriving DecidableEq

instance : Fintype End where
  elems := {.one, .upper}
  complete x := by cases x <;> decide
def coefficient : End→ℚ | .one=>1 | .upper=>5821/5000
abbrev Q : ℚ := 9789/2500
abbrev kstar : ℚ := 1673/2500
abbrev h : ℚ := 7/10
abbrev cut : ℚ := 3/8
abbrev cLower : ℚ := 449607/500000
abbrev aUpper : ℚ := 1414575672/1000000000
abbrev Tzero : ℚ := 2380990934/1000000000
def phiLower : ℚ := C10.eval h+S11.eval h
def constant (e : End) : ℚ :=
  coefficient e*phiLower+1+(coefficient e+1)*(cLower-1/2)+(13/20)*h-Tzero
def P (e : End) : ℚ[X] :=
  C (1+(coefficient e)^2)+C (2*coefficient e)*S9.comp (C h-X)
def H : ℚ[X] := C (1+kstar^2)-C (2*kstar)*S9
def Z (e : End) : ℚ[X] :=
  C (4*(constant e)^2*Q)*H-(C Q*(P e-H)-C ((constant e)^2))^2
def axisConstant : ℚ :=
  (phiLower-1)/2-aUpper*S9.eval h+2*cLower+(13/20)*h+1/2-Tzero
def axisA : ℚ[X] := C axisConstant-C (aUpper+1/2)*C12+C (1/2)*S11
def Y : ℚ[X] := C Q*H-axisA^2
def shiftedY : ℚ[X] := Y.comp (C (9/20)+X)
def y (j : ℕ) : ℚ := shiftedY.coeff j
def tailBudget : ℚ := ∑ j : Fin 22,|y (j.val+3)| *(1/4)^(j.val+1)
def quadratic : ℚ := y 2-tailBudget
def monomialExpansion : ℚ[X] := C (y 0)+C (y 1)*X+C (y 2)*X^2+
  ∑ j : Fin 22,C (y (j.val+3))*X^(j.val+3)

theorem rational_aeval (p : ℚ[X]) (r : ℚ) : aeval (r:ℝ) p=((p.eval r:ℚ):ℝ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp,hq]
  | monomial n a => simp

/-! ### Kernel certificates

Each polynomial is represented by a scaled integer coefficient list
(`WholeIntervalPolynomial.Certificate`) built to mirror its definition; the
final comparisons are integer inequalities checked by the kernel. -/

open WholeIntervalPolynomial.Certificate in
private theorem r44_rep_C (n : ℤ) (d : ℕ) {q : ℚ} (hd : d≠0) (h : q=n/d) :
    (⟨[n],d⟩ : Scaled).Rep (C q) := by
  unfold Scaled.Rep
  have hd' : (d:ℚ)≠0 := by exact_mod_cast hd
  simp only [toPoly,mul_zero,add_zero,← map_mul]
  congr 1
  rw [h]
  field_simp

open WholeIntervalPolynomial.Certificate in
/-- The degree-nine sine polynomial composed with a represented polynomial. -/
private def r44_S9of (v : Scaled) : Scaled :=
  (((v.sub ((⟨[1],6⟩ : Scaled).mul (v.pow 3))).add
    ((⟨[1],120⟩ : Scaled).mul (v.pow 5))).sub
    ((⟨[1],5040⟩ : Scaled).mul (v.pow 7))).add
    ((⟨[1],362880⟩ : Scaled).mul (v.pow 9))

open WholeIntervalPolynomial.Certificate in
private theorem r44_rep_S9of {v : Scaled} {q : ℚ[X]} (hv : v.Rep q) :
    (r44_S9of v).Rep (S9.comp q) := by
  have e : S9.comp q=q-C (1/6)*q^3+C (1/120)*q^5-C (1/5040)*q^7+C (1/362880)*q^9 := by
    simp only [S9,PositiveTD.Certificate.S5,sub_comp,add_comp,mul_comp,C_comp,X_comp,
      pow_comp]
  rw [e]
  exact (((hv.sub ((r44_rep_C 1 6 (by norm_num) (by norm_num)).mul (hv.pow 3))).add
    ((r44_rep_C 1 120 (by norm_num) (by norm_num)).mul (hv.pow 5))).sub
    ((r44_rep_C 1 5040 (by norm_num) (by norm_num)).mul (hv.pow 7))).add
    ((r44_rep_C 1 362880 (by norm_num) (by norm_num)).mul (hv.pow 9))

open WholeIntervalPolynomial.Certificate in
private theorem r44_rep_S9 : (r44_S9of Scaled.var).Rep S9 := by
  simpa only [comp_X] using r44_rep_S9of Scaled.rep_var

open WholeIntervalPolynomial.Certificate in
private def r44_S11S : Scaled :=
  (r44_S9of Scaled.var).sub ((⟨[1],39916800⟩ : Scaled).mul (Scaled.var.pow 11))

open WholeIntervalPolynomial.Certificate in
private theorem r44_rep_S11 : r44_S11S.Rep S11 :=
  r44_rep_S9.sub ((r44_rep_C 1 39916800 (by norm_num) (by norm_num)).mul (Scaled.rep_var.pow 11))

open WholeIntervalPolynomial.Certificate in
private def r44_C12S : Scaled :=
  ((((((Scaled.ofNat 1).sub ((⟨[1],2⟩ : Scaled).mul (Scaled.var.pow 2))).add
    ((⟨[1],24⟩ : Scaled).mul (Scaled.var.pow 4))).sub
    ((⟨[1],720⟩ : Scaled).mul (Scaled.var.pow 6))).add
    ((⟨[1],40320⟩ : Scaled).mul (Scaled.var.pow 8))).sub
    ((⟨[1],3628800⟩ : Scaled).mul (Scaled.var.pow 10))).add
    ((⟨[1],479001600⟩ : Scaled).mul (Scaled.var.pow 12))

open WholeIntervalPolynomial.Certificate in
private theorem r44_rep_C12 : r44_C12S.Rep C12 :=
  (((((Scaled.rep_one.sub ((r44_rep_C 1 2 (by norm_num) (by norm_num)).mul
    (Scaled.rep_var.pow 2))).add
    ((r44_rep_C 1 24 (by norm_num) (by norm_num)).mul (Scaled.rep_var.pow 4))).sub
    ((r44_rep_C 1 720 (by norm_num) (by norm_num)).mul (Scaled.rep_var.pow 6))).add
    ((r44_rep_C 1 40320 (by norm_num) (by norm_num)).mul (Scaled.rep_var.pow 8))).sub
    ((r44_rep_C 1 3628800 (by norm_num) (by norm_num)).mul (Scaled.rep_var.pow 10))).add
    ((r44_rep_C 1 479001600 (by norm_num) (by norm_num)).mul (Scaled.rep_var.pow 12))

open WholeIntervalPolynomial.Certificate in
private def r44_HS : Scaled :=
  (⟨[9048929],6250000⟩ : Scaled).sub ((⟨[1673],1250⟩ : Scaled).mul (r44_S9of Scaled.var))

open WholeIntervalPolynomial.Certificate in
private theorem r44_rep_H : r44_HS.Rep H :=
  (r44_rep_C 9048929 6250000 (by norm_num) (by norm_num [kstar])).sub
    ((r44_rep_C 1673 1250 (by norm_num) (by norm_num [kstar])).mul r44_rep_S9)

open WholeIntervalPolynomial.Certificate in
private def r44_PS (a1 : ℤ) (d1 : ℕ) (a2 : ℤ) (d2 : ℕ) : Scaled :=
  (⟨[a1],d1⟩ : Scaled).add
    ((⟨[a2],d2⟩ : Scaled).mul (r44_S9of ((⟨[7],10⟩ : Scaled).sub Scaled.var)))

open WholeIntervalPolynomial.Certificate in
private theorem r44_rep_P (e : End) (a1 : ℤ) (d1 : ℕ) (a2 : ℤ) (d2 : ℕ) (hd1 : d1≠0) (hd2 : d2≠0)
    (h1 : 1+(coefficient e)^2=a1/d1) (h2 : 2*coefficient e=a2/d2) :
    (r44_PS a1 d1 a2 d2).Rep (P e) :=
  (r44_rep_C a1 d1 hd1 h1).add ((r44_rep_C a2 d2 hd2 h2).mul
    (r44_rep_S9of ((r44_rep_C 7 10 (by norm_num) (by norm_num [h])).sub Scaled.rep_var)))

open WholeIntervalPolynomial.Certificate in
private def r44_ZS (P : Scaled) (n1 : ℤ) (d1 : ℕ) (n2 : ℤ) (d2 : ℕ) : Scaled :=
  ((⟨[n1],d1⟩ : Scaled).mul r44_HS).sub
    ((((⟨[9789],2500⟩ : Scaled).mul (P.sub r44_HS)).sub (⟨[n2],d2⟩ : Scaled)).pow 2)

open WholeIntervalPolynomial.Certificate in
private theorem r44_rep_Z (e : End) {cP : Scaled} (hP : cP.Rep (P e)) (n1 : ℤ) (d1 : ℕ)
    (n2 : ℤ) (d2 : ℕ) (hd1 : d1≠0) (hd2 : d2≠0) (h1 : 4*(constant e)^2*Q=n1/d1)
    (h2 : (constant e)^2=n2/d2) :
    (r44_ZS cP n1 d1 n2 d2).Rep (Z e) :=
  ((r44_rep_C n1 d1 hd1 h1).mul r44_rep_H).sub
    ((((r44_rep_C 9789 2500 (by norm_num) (by norm_num [Q])).mul (hP.sub r44_rep_H)).sub
      (r44_rep_C n2 d2 hd2 h2)).pow 2)

private theorem r44_constant_one :
    constant .one=730760815346048981/570240000000000000 := by
  norm_num [constant,coefficient,phiLower,C10,PositiveTD.Certificate.C4,S11,S9,
    PositiveTD.Certificate.S5,h,cLower,Tzero]

private theorem r44_constant_upper :
    constant .upper=4500378304060406478401/2851200000000000000000 := by
  norm_num [constant,coefficient,phiLower,C10,PositiveTD.Certificate.C4,S11,S9,
    PositiveTD.Certificate.S5,h,cLower,Tzero]

open WholeIntervalPolynomial.Certificate in
private def r44_ZoneS : Scaled :=
  r44_ZS (r44_PS 2 1 2 1)
    1742479097847160351491383229620464471943 67744512000000000000000000000000000000
    534011369245222295890708927251138361 325173657600000000000000000000000000

open WholeIntervalPolynomial.Certificate in
private theorem r44_rep_Zone : r44_ZoneS.Rep (Z .one) :=
  r44_rep_Z .one (r44_rep_P .one 2 1 2 1 (by norm_num) (by norm_num) (by norm_num [coefficient])
    (by norm_num [coefficient]))
    1742479097847160351491383229620464471943 67744512000000000000000000000000000000
    534011369245222295890708927251138361 325173657600000000000000000000000000
    (by norm_num) (by norm_num)
    (by rw [r44_constant_one]; norm_num [Q]) (by rw [r44_constant_one]; norm_num)

open WholeIntervalPolynomial.Certificate in
private def r44_ZupperS : Scaled :=
  r44_ZS (r44_PS 58884041 25000000 5821 2500)
    66086860122322815448855028607496364594663321663
      1693612800000000000000000000000000000000000000
    20253404879657620425637458966440810479516801
      8129341440000000000000000000000000000000000

open WholeIntervalPolynomial.Certificate in
private theorem r44_rep_Zupper : r44_ZupperS.Rep (Z .upper) :=
  r44_rep_Z .upper (r44_rep_P .upper 58884041 25000000 5821 2500 (by norm_num) (by norm_num)
    (by norm_num [coefficient]) (by norm_num [coefficient]))
    66086860122322815448855028607496364594663321663
      1693612800000000000000000000000000000000000000
    20253404879657620425637458966440810479516801
      8129341440000000000000000000000000000000000
    (by norm_num) (by norm_num)
    (by rw [r44_constant_upper]; norm_num [Q]) (by rw [r44_constant_upper]; norm_num)

open WholeIntervalPolynomial.Certificate in
private theorem r44_rep_upper_centered :
    (r44_ZupperS.center 7 20 1 1).Rep (centered 0 h (Z .upper)) :=
  r44_rep_Zupper.centered 7 20 1 1 (by norm_num) (by norm_num [h]) (by norm_num [h])

open WholeIntervalPolynomial.Certificate in
/-- The coefficient list of the derivative. -/
private def r44_derivL : List ℤ → List ℤ
  | [] => []
  | [_] => []
  | _ :: b :: l => Certificate.add (b :: l) (0 :: r44_derivL (b :: l))

open WholeIntervalPolynomial.Certificate in
private theorem r44_toPoly_derivL : ∀ l : List ℤ,toPoly (r44_derivL l)=derivative (toPoly l)
  | [] => by simp [r44_derivL,toPoly]
  | [a] => by simp [r44_derivL,toPoly]
  | a :: b :: l => by
    rw [r44_derivL,toPoly_add]
    have ih := r44_toPoly_derivL (b :: l)
    simp only [toPoly] at ih ⊢
    rw [ih]
    simp only [Int.cast_zero,map_zero,zero_add,derivative_add,derivative_C,derivative_mul,
      derivative_X,one_mul]

open WholeIntervalPolynomial.Certificate in
private theorem r44_rep_derivative {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) :
    (⟨r44_derivL c.l,c.s⟩ : Scaled).Rep (derivative p) := by
  unfold Scaled.Rep at *
  rw [r44_toPoly_derivL,hc,derivative_C_mul]

open WholeIntervalPolynomial.Certificate in
private theorem r44_rep_one_derivative_centered :
    ((⟨r44_derivL r44_ZoneS.l,r44_ZoneS.s⟩ : Scaled).center 3 16 1 1).Rep
      (centered 0 cut (Z .one).derivative) :=
  (r44_rep_derivative r44_rep_Zone).centered 3 16 1 1 (by norm_num) (by norm_num [cut])
    (by norm_num [cut])

open WholeIntervalPolynomial.Certificate in
private theorem r44_rep_one_centered :
    (r44_ZoneS.center 3 8 1 1).Rep (centered 0 (3/4) (Z .one)) :=
  r44_rep_Zone.centered 3 8 1 1 (by norm_num) (by norm_num) (by norm_num)

private theorem r44_axisConstant :
    axisConstant=-23830875981954563397049/71280000000000000000000 := by
  norm_num [axisConstant,phiLower,C10,PositiveTD.Certificate.C4,S11,S9,
    PositiveTD.Certificate.S5,h,cLower,aUpper,Tzero]

open WholeIntervalPolynomial.Certificate in
private def r44_YS : Scaled :=
  ((⟨[9789],2500⟩ : Scaled).mul r44_HS).sub
    ((((⟨[-23830875981954563397049],71280000000000000000000⟩ : Scaled).sub
      ((⟨[239321959],125000000⟩ : Scaled).mul r44_C12S)).add
      ((⟨[1],2⟩ : Scaled).mul r44_S11S)).pow 2)

open WholeIntervalPolynomial.Certificate in
private theorem r44_rep_Y : r44_YS.Rep Y := by
  rw [Y,axisA,r44_axisConstant]
  exact ((r44_rep_C 9789 2500 (by norm_num) (by norm_num [Q])).mul r44_rep_H).sub
    ((((r44_rep_C (-23830875981954563397049) 71280000000000000000000 (by norm_num)
      (by norm_num)).sub ((r44_rep_C 239321959 125000000 (by norm_num)
        (by norm_num [aUpper])).mul r44_rep_C12)).add
      ((r44_rep_C 1 2 (by norm_num) (by norm_num)).mul r44_rep_S11)).pow 2)

private theorem r44_shifted : shiftedY=centered (-11/20) (29/20) Y := by
  rw [shiftedY,centered,affine]
  congr 1
  norm_num

open WholeIntervalPolynomial.Certificate in
private theorem r44_rep_shiftedY : (r44_YS.center 1 20 9 20).Rep shiftedY := by
  rw [r44_shifted]
  exact r44_rep_Y.centered 1 20 9 20 (by norm_num) (by norm_num) (by norm_num)

private theorem r44_tail_sum (L : ℕ → ℤ) {s : ℕ} (hs : 0<s) :
    ∑ j : Fin 22,|(L (j.val+3):ℚ)/s| *(1/4)^(j.val+1)=
      ((∑ j : Fin 22,|L (j.val+3)| *4^(21-j.val) : ℤ):ℚ)/((s:ℚ)*4^22) := by
  have hs' : (0:ℚ)<s := by exact_mod_cast hs
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hj := j.isLt
  have h4 : (4:ℚ)^22=4^(21-j.val)*4^(j.val+1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [abs_div,abs_of_pos hs',h4]
  field_simp
  rw [mul_assoc,← mul_pow]
  norm_num

private theorem r44_axis_of {L : ℕ → ℤ} {s : ℕ} (hs : 0<s) (hy : ∀ j,y j=(L j:ℚ)/s)
    (h1 : 877*((s:ℤ)*4^22)<500*(L 2*4^22-∑ j : Fin 22,|L (j.val+3)| *4^(21-j.val)))
    (h2 : 4*(s:ℤ)*(L 2*4^22-∑ j : Fin 22,|L (j.val+3)| *4^(21-j.val))<
      1000*(4*(L 2*4^22-∑ j : Fin 22,|L (j.val+3)| *4^(21-j.val))*L 0-4^22*(L 1)^2)) :
    (877/500:ℚ)<quadratic ∧ (1/1000:ℚ)<y 0-(y 1)^2/(4*quadratic) := by
  obtain ⟨T,hTd⟩ : ∃ T : ℤ,T=∑ j : Fin 22,|L (j.val+3)| *4^(21-j.val) := ⟨_,rfl⟩
  rw [← hTd] at h1 h2
  have hs' : (0:ℚ)<s := by exact_mod_cast hs
  have hT : tailBudget=(T:ℚ)/((s:ℚ)*4^22) := by
    unfold tailBudget
    simp only [hy]
    rw [hTd]
    exact r44_tail_sum L hs
  have h1' : (877:ℚ)*((s:ℚ)*4^22)<500*((L 2:ℚ)*4^22-T) := by
    have hh := (Int.cast_lt (R:=ℚ)).mpr h1
    simpa only [Int.cast_mul,Int.cast_sub,Int.cast_pow,Int.cast_ofNat,Int.cast_natCast] using hh
  have h2' : 4*(s:ℚ)*((L 2:ℚ)*4^22-T)<1000*(4*((L 2:ℚ)*4^22-T)*L 0-4^22*(L 1:ℚ)^2) := by
    have hh := (Int.cast_lt (R:=ℚ)).mpr h2
    simpa only [Int.cast_mul,Int.cast_sub,Int.cast_pow,Int.cast_ofNat,Int.cast_natCast] using hh
  generalize hM : (4:ℚ)^22=M at hT h1' h2'
  have hM0 : 0<M := by rw [← hM]; positivity
  have hsM : 0<(s:ℚ)*M := mul_pos hs' hM0
  have hQN : 0<(L 2:ℚ)*M-T := by linarith
  have hq : quadratic=((L 2:ℚ)*M-T)/((s:ℚ)*M) := by
    unfold quadratic
    rw [hT,hy 2]
    field_simp
  constructor
  · rw [hq,lt_div_iff₀ hsM]
    linarith
  · rw [hq,hy 0,hy 1]
    have hsne : (s:ℚ)≠0 := hs'.ne'
    have hMne : M≠0 := hM0.ne'
    have hQne : (L 2:ℚ)*M-T≠0 := hQN.ne'
    have key : (L 0:ℚ)/s-((L 1:ℚ)/s)^2/(4*(((L 2:ℚ)*M-T)/((s:ℚ)*M)))=
        (4*((L 2:ℚ)*M-T)*L 0-M*(L 1:ℚ)^2)/(4*s*((L 2:ℚ)*M-T)) := by
      field_simp
    rw [key,lt_div_iff₀ (by positivity)]
    linarith

/-- A rational number below a `lowerOn` value, from an integer inequality. -/
private theorem r44_lt_lower {r : ℚ} {a N : ℤ} {b s L : ℕ} (hr : r=a/b) (hb : 0<b) (hs : 0<s)
    (h : a*((s:ℤ)*2^L)<2*N*b) : r<(N:ℚ)/((s:ℚ)*2^L/2) := by
  have hb' : (0:ℚ)<b := by exact_mod_cast hb
  have hs' : (0:ℚ)<(s:ℚ)*2^L/2 := by positivity
  rw [hr,div_lt_div_iff₀ hb' hs']
  have h' : ((a*((s:ℤ)*2^L):ℤ):ℚ)<((2*N*b:ℤ):ℚ) := by exact_mod_cast h
  push_cast at h'
  linarith

/-- An `upperOn` value below a rational number, from an integer inequality. -/
private theorem r44_upper_lt {r : ℚ} {a N : ℤ} {b s L : ℕ} (hr : r=a/b) (hb : 0<b) (hs : 0<s)
    (h : 2*N*b<a*((s:ℤ)*2^L)) : (N:ℚ)/((s:ℚ)*2^L/2)<r := by
  have hb' : (0:ℚ)<b := by exact_mod_cast hb
  have hs' : (0:ℚ)<(s:ℚ)*2^L/2 := by positivity
  rw [hr,div_lt_div_iff₀ hs' hb']
  have h' : ((2*N*b:ℤ):ℚ)<((a*((s:ℤ)*2^L):ℤ):ℚ) := by exact_mod_cast h
  push_cast at h'
  linarith

/-- A rational number below a scaled integer, from an integer inequality. -/
private theorem r44_lt_scaled {r : ℚ} {a N : ℤ} {b s : ℕ} (hr : r=a/b) (hb : 0<b) (hs : 0<s)
    (h : a*s<N*b) : r<(N:ℚ)/s := by
  have hb' : (0:ℚ)<b := by exact_mod_cast hb
  have hs' : (0:ℚ)<s := by exact_mod_cast hs
  rw [hr,div_lt_div_iff₀ hb' hs']
  exact_mod_cast h

private theorem r44_eval_eq_coeff (a b : ℚ) (p : ℚ[X]) :
    p.eval ((a+b)/2)=(centered a b p).coeff 0 := by
  rw [coeff_zero_eq_eval_zero,centered,eval_comp,affine]
  simp

theorem positive_constants (e : End) : (32/25:ℚ)<constant e := by
  cases e <;>
    norm_num [constant,coefficient,phiLower,C10,PositiveTD.Certificate.C4,S11,S9,
      PositiveTD.Certificate.S5,h,cLower,Tzero]

theorem upper_expansion : centered 0 h (Z .upper)=expansion 18 (centered 0 h (Z .upper)) :=
  r44_rep_upper_centered.eq_expansion (by decide +kernel) (by decide +kernel)

theorem upper_reserve : (139/1000:ℚ)<lowerOn 18 0 h (Z .upper) := by
  rw [Certificate.lowerOn_eq_of_rep r44_rep_upper_centered (by decide +kernel)
    (by decide +kernel)]
  exact r44_lt_lower (a:=139) (b:=1000) (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel)

theorem one_derivative_expansion : centered 0 cut (Z .one).derivative=
    expansion 17 (centered 0 cut (Z .one).derivative) :=
  r44_rep_one_derivative_centered.eq_expansion (by decide +kernel) (by decide +kernel)

theorem one_derivative_reserve : upperOn 17 0 cut (Z .one).derivative< -(623/100:ℚ) := by
  rw [Certificate.upperOn_eq_of_rep r44_rep_one_derivative_centered (by decide +kernel)
    (by decide +kernel)]
  exact r44_upper_lt (a:=-623) (b:=100) (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel)

theorem one_endpoint : (57/250:ℚ)<(Z .one).eval cut := by
  have he : (Z .one).eval cut=(centered 0 (3/4) (Z .one)).coeff 0 := by
    rw [← r44_eval_eq_coeff]
    norm_num [cut]
  rw [he,r44_rep_one_centered.coeff (by decide +kernel) 0]
  exact r44_lt_scaled (a:=57) (b:=250) (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel)

theorem axis_expansion : shiftedY=monomialExpansion := by
  have hdeg : shiftedY.natDegree<25 :=
    lt_of_le_of_lt (r44_rep_shiftedY.natDegree_le (by decide +kernel)) (by decide +kernel)
  rw [monomialExpansion,Fin.sum_univ_eq_sum_range (fun j => C (y (j+3))*X^(j+3)) 22]
  conv_lhs => rw [shiftedY.as_sum_range_C_mul_X_pow' hdeg]
  rw [Finset.sum_range_succ',Finset.sum_range_succ',Finset.sum_range_succ']
  simp only [y,add_assoc,Nat.reduceAdd,zero_add,pow_zero,mul_one,pow_one]
  ring

theorem axis_reserve : (877/500:ℚ)<quadratic ∧
    (1/1000:ℚ)<y 0-(y 1)^2/(4*quadratic) := by
  have hs : (r44_YS.center 1 20 9 20).s≠0 := by decide +kernel
  exact r44_axis_of (L:=fun j => (r44_YS.center 1 20 9 20).l.getD j 0) (Nat.pos_of_ne_zero hs)
    (fun j => r44_rep_shiftedY.coeff hs j) (by decide +kernel) (by decide +kernel)

theorem upper_positive {n : ℝ} (hn : n∈Icc 0 (7/10:ℝ)) :
    (139/1000:ℝ)<aeval n (Z .upper) := by
  have hn' : n∈Icc ((0:ℚ):ℝ) ((h:ℚ):ℝ) := by
    norm_num [h]
    exact hn
  have hh := positive_on_interval (by norm_num [h]) upper_expansion upper_reserve hn'
  norm_num at hh
  exact hh

theorem one_derivative_negative {n : ℝ} (hn : n∈Icc 0 (3/8:ℝ)) :
    aeval n (Z .one).derivative< -(623/100:ℝ) := by
  have hn' : n∈Icc ((0:ℚ):ℝ) ((cut:ℚ):ℝ) := by
    norm_num [cut]
    exact hn
  have hb := (interval_bounds (by norm_num [cut] : (0:ℚ)<cut) one_derivative_expansion hn').2
  have hr : (upperOn 17 0 cut (Z .one).derivative:ℝ)< -(623/100:ℝ) := by
    have hh := (Rat.cast_lt (K:=ℝ)).mpr one_derivative_reserve
    norm_num at hh
    exact hh
  exact hb.trans_lt hr

theorem one_positive {n : ℝ} (hn : n∈Icc 0 (3/8:ℝ)) :
    (57/250:ℝ)<aeval n (Z .one) := by
  have ha : AntitoneOn (fun n : ℝ => aeval n (Z .one)) (Icc (0:ℝ) (3/8)) := by
    apply antiOn_of_hasDeriv_nonpos
      (fun n _ => (CenteredMonomialBounds.aeval_hasDerivAt (Z .one) n).continuousAt.continuousWithinAt)
      (fun n _ => CenteredMonomialBounds.aeval_hasDerivAt (Z .one) n)
    intro n hn
    linarith [one_derivative_negative (Ioo_subset_Icc_self hn)]
  have hh := ha hn (show (3/8:ℝ)∈Icc 0 (3/8) by norm_num) hn.2
  have he : (57/250:ℝ)<aeval (3/8:ℝ) (Z .one) := by
    have hr : (57/250:ℝ)<(((Z .one).eval cut:ℚ):ℝ) := by
      have hh := (Rat.cast_lt (K:=ℝ)).mpr one_endpoint
      norm_num at hh
      exact hh
    have hc : ((3/8:ℚ):ℝ)=(3/8:ℝ) := by norm_num
    rw [← rational_aeval,cut,hc] at hr
    exact hr
  exact he.trans_le hh

theorem axis_tail {z : ℝ} (hz : |z|≤1/4) (j : Fin 22) :
    -(|(y (j.val+3):ℝ)| *(1/4)^(j.val+1))*z^2≤
      (y (j.val+3):ℝ)*z^(j.val+3) := by
  have hp := pow_le_pow_left₀ (abs_nonneg z) hz (j.val+1)
  have hm := mul_le_mul_of_nonneg_left hp (abs_nonneg (y (j.val+3):ℝ))
  have hh : |(y (j.val+3):ℝ)*z^(j.val+1)|≤
      |(y (j.val+3):ℝ)| *(1/4)^(j.val+1) := by simpa [abs_mul,abs_pow] using hm
  have hlo := mul_le_mul_of_nonneg_right (abs_le.mp hh).1 (sq_nonneg z)
  have he : z^(j.val+3)=z^(j.val+1)*z^2 := by ring
  rw [he]
  nlinarith

theorem axis_quadratic_lower {z : ℝ} (hz : |z|≤1/4) :
    (y 0:ℝ)+(y 1:ℝ)*z+(quadratic:ℝ)*z^2≤aeval z shiftedY := by
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => axis_tail hz j)
  have he : ∑j:Fin 22,-(|(y (j.val+3):ℝ)| *(1/4)^(j.val+1))*z^2=
      -(tailBudget:ℝ)*z^2 := by
    simp [tailBudget,Finset.sum_mul,Finset.sum_neg_distrib]
  rw [he] at hs
  rw [axis_expansion]
  simp only [monomialExpansion,map_add,map_sum,map_mul,map_pow,aeval_C,aeval_X,eq_ratCast]
  dsimp [quadratic]
  push_cast
  linarith

theorem axis_positive {n : ℝ} (hn : n∈Icc (3/8:ℝ) (7/10:ℝ)) :
    (1/1000:ℝ)<aeval n Y := by
  let z : ℝ := n-9/20
  have hz : |z|≤1/4 := by
    dsimp [z]
    apply abs_le.mpr
    constructor <;> linarith [hn.1,hn.2]
  have hq : (0:ℝ)<(quadratic:ℝ) := by
    have hh := (Rat.cast_lt (K:=ℝ)).mpr axis_reserve.1
    norm_num at hh
    linarith
  have hr : (1/1000:ℝ)<(y 0:ℝ)-(y 1:ℝ)^2/(4*(quadratic:ℝ)) := by
    have hh := (Rat.cast_lt (K:=ℝ)).mpr axis_reserve.2
    push_cast at hh
    exact hh
  have hm := ChebyshevLeadingBounds.quadratic_min (a:=(y 0:ℝ)) (b:=(y 1:ℝ)) (x:=z) hq
  have hh := axis_quadratic_lower hz
  have he : aeval z shiftedY=aeval n Y := by
    rw [shiftedY,aeval_comp]
    congr 1
    simp [z]
  rw [he] at hh
  linarith

end SquaresInCircles.Eight.GlobalGA.PositiveBT3.DEndpoint

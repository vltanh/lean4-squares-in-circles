module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Rat.Star
public import Mathlib.Algebra.Ring.IsFormallyReal
public import SquaresInCircles.Eight.Arithmetic.PolynomialCertificates
public import SquaresInCircles.Eight.Owners.CenteredMonomialBounds
public import SquaresInCircles.Eight.Owners.ChebyshevLeadingBounds
public import SquaresInCircles.Eight.Owners.Contact.MinimumDerivatives
public import SquaresInCircles.Eight.Owners.GA.Positive.BT3SortedSupport
public import SquaresInCircles.Eight.Owners.GA.Positive.TDPolynomialData
public import SquaresInCircles.Eight.Owners.GA.Positive.TDScalarBounds

/-!
# Eight squares: the support and the intrinsic branch endpoints of the BT3 D minorant

The scalar support is attained on its sorted arc (`sortedSupport_attained`), and the concavity in
the weight follows from that support point (`D_weight_concave`). The branch endpoint principle
`branch_lower` treats the continuous support transitions on a compact interval, with no angle
mesh.
-/

section
/-!
## The three independent sorted-D endpoint certificates

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
end
end
end

section
/-!
## The radical and tangent-zero bounds at the sorted-D endpoint

The change at n=3/8 is justified by the actual force
ratio and its derivative. All radical bounds follow from positive
squaring of the displayed rational constants.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.PositiveBT3.DEndpoint
open Candidate Secondary Polynomial PositiveAngularEnvelope OrdinaryAngleConcavity PairNormCalculus
open PositiveTD.Certificate (S9 S11 C10 C12 taylor_bounds)

theorem coefficient_domain (e : End) : (coefficient e:ℝ)∈Icc 1 Cmax := by
  cases e <;> norm_num [coefficient,Cmax]

theorem radical_bounds : (cLower:ℝ)<GlobalGA.Secondary.diagonal ∧ axial<(aUpper:ℝ) ∧
    R*pairNorm K 1 0<(Tzero:ℝ) := by
  have hdb := diagonal_bounds
  have hN2 : (pairNorm K 1 0)^2=K^2+1 := by
    rw [pairNorm_zero,Real.sq_sqrt (by positivity)]
    ring
  have hprod : (R*pairNorm K 1 0)^2=qCap*(K^2+1) := by
    rw [mul_pow,radius_sq,hN2]
  have hax : Real.sqrt (qCap-1/4)<(aUpper:ℝ)+1/2 :=
    (Real.sqrt_lt' (by norm_num [aUpper])).mpr (by norm_num [qCap,aUpper])
  refine ⟨?_,?_,?_⟩
  · norm_num [cLower]
    linarith [hdb.1]
  · dsimp only [axial]
    linarith
  · apply lt_of_pow_lt_pow_left₀ 2 (by norm_num [Tzero])
    rw [hprod]
    norm_num [qCap,K,Tzero]

theorem sine9_hasDerivAt (x : ℝ) : HasDerivAt Arithmetic.sin9 (Arithmetic.cos8 x) x := by
  have h := ((((hasDerivAt_id' x).sub ((hasDerivAt_pow 3 x).div_const 6)).add
    ((hasDerivAt_pow 5 x).div_const 120)).sub ((hasDerivAt_pow 7 x).div_const 5040)).add
    ((hasDerivAt_pow 9 x).div_const 362880)
  refine h.congr_deriv ?_
  rw [Arithmetic.cos8]
  push_cast
  ring

theorem sine9_range {x : ℝ} (hx : x∈Icc 0 frameCap) :
    0≤aeval x S9 ∧ aeval x S9<(129/200:ℝ) := by
  have hm : MonotoneOn Arithmetic.sin9 (Icc (0:ℝ) frameCap) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun x _ => (sine9_hasDerivAt x).continuousAt.continuousWithinAt)
      (fun x _ => sine9_hasDerivAt x)
    intro x hx
    have hh := Arithmetic.cos_le_cos8 hx.1.le
    have hc := (transport_trig (Ioo_subset_Icc_self hx)).1
    linarith
  have h0 := hm (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hx hx.1
  have h1 := hm hx (show frameCap∈Icc 0 frameCap by norm_num [frameCap]) hx.2
  have he : Arithmetic.sin9 frameCap<(129/200:ℝ) := by
    norm_num [Arithmetic.sin9,Arithmetic.sin7,frameCap]
  simp only [PositiveTD.Certificate.S9_eval]
  exact ⟨by simpa [Arithmetic.sin9,Arithmetic.sin7] using h0,h1.trans_lt he⟩

theorem norm_polynomial_bounds (e : End) {n : ℝ} (hn : n∈Icc 0 frameCap) :
    0≤aeval n (P e) ∧ (29/50:ℝ)<aeval n H ∧
    pairNorm 1 (coefficient e:ℝ) (frameCap-n)≤Real.sqrt (aeval n (P e)) ∧
    Real.sqrt (aeval n H)≤pairNorm K 1 (-n) := by
  have hother : frameCap-n∈Icc 0 frameCap := ⟨by linarith [hn.2],by linarith [hn.1]⟩
  have hs := sine9_range hn
  have hso := sine9_range hother
  have hta := (taylor_bounds hother).2.2.1
  have htn := (taylor_bounds hn).2.2.1
  have hc := coefficient_domain e
  have hP : aeval n (P e)=1+(coefficient e:ℝ)^2+
      2*(coefficient e:ℝ)*aeval (frameCap-n) S9 := by
    simp [P,aeval_comp,h,frameCap]
  have hH : aeval n H=1+K^2-2*K*aeval n S9 := by simp [H,kstar,K]
  have hP0 : 0≤aeval n (P e) := by
    rw [hP]
    have := mul_nonneg (show 0≤2*(coefficient e:ℝ) by linarith [hc.1]) hso.1
    nlinarith [sq_nonneg (coefficient e:ℝ)]
  have hH0 : (29/50:ℝ)<aeval n H := by
    rw [hH]
    have hs2 := hs.2
    norm_num [K] at hs2 ⊢
    linarith
  refine ⟨hP0,hH0,?_,?_⟩
  · apply Real.sqrt_le_sqrt
    rw [hP]
    have hh := mul_le_mul_of_nonneg_left hta
      (show 0≤2*(coefficient e:ℝ) by linarith [hc.1])
    linarith
  · apply Real.sqrt_le_sqrt
    rw [hH]
    simp only [Real.sin_neg]
    have hh := mul_le_mul_of_nonneg_left htn (by norm_num [K] : (0:ℝ)≤2*K)
    linarith

def axisRatio (n : ℝ) : ℝ := forceB 1 frameCap (-n)/forceA 1 frameCap (-n)

theorem axisRatio_hasDerivAt {n : ℝ} (hn : n∈Icc 0 frameCap) :
    HasDerivAt axisRatio ((-1+Real.sin (n-frameCap))/(forceA 1 frameCap (-n))^2) n := by
  have hp := force_positive (c:=1) (x:=frameCap) (y:=-n) (by norm_num [Cmax])
    (by norm_num [frameCap]) (by rw [abs_neg,abs_of_nonneg hn.1]; exact hn.2)
  have hden : forceA 1 frameCap (-n)≠0 := hp.1.ne'
  have hF : HasDerivAt (fun n => forceA 1 frameCap (-n)) (-Real.sin n) n := by
    simpa [forceA] using (Real.hasDerivAt_cos n).const_add (Real.sin frameCap)
  have hG : HasDerivAt (fun n => forceB 1 frameCap (-n)) (-Real.cos n) n := by
    have hfun : (fun n => forceB 1 frameCap (-n))=fun n => Real.cos frameCap-Real.sin n := by
      funext m
      simp only [forceB,one_mul,Real.sin_neg,sub_eq_add_neg]
    rw [hfun]
    exact (Real.hasDerivAt_sin n).const_sub (Real.cos frameCap)
  convert hG.div hF hden using 1
  · funext m
    rfl
  rw [div_left_inj' (pow_ne_zero 2 hden)]
  simp only [forceA,forceB,Real.cos_neg,Real.sin_neg,one_mul,Real.sin_sub]
  linear_combination Real.sin_sq_add_cos_sq n

theorem axisRatio_antitone : AntitoneOn axisRatio (Icc (0:ℝ) frameCap) := by
  apply antiOn_of_hasDeriv_nonpos
    (fun n hn => (axisRatio_hasDerivAt hn).continuousAt.continuousWithinAt)
    (fun n hn => axisRatio_hasDerivAt (Ioo_subset_Icc_self hn))
  intro n hn
  have hs : Real.sin (n-frameCap)≤0 := by
    have hh := (transport_trig
      (show frameCap-n∈Icc 0 frameCap from ⟨by linarith [hn.2],by linarith [hn.1]⟩)).2.2.1
    rw [show n-frameCap=-(frameCap-n) by ring,Real.sin_neg]
    linarith
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)

theorem axis_transition_reserve :
    (121/5000:ℚ)<(C10.eval cut+S11.eval h)/2-
      (aUpper+1/2)*(C12.eval h-S11.eval cut) := by
  norm_num [C10,PositiveTD.Certificate.C4,S11,S9,PositiveTD.Certificate.S5,C12,cut,h,aUpper]

theorem axis_at_cut :
    (axial+1/2)*forceB 1 frameCap (-(3/8))<forceA 1 frameCap (-(3/8))/2 := by
  have hh := taylor_bounds (show frameCap∈Icc 0 frameCap by norm_num [frameCap])
  have hb := taylor_bounds (show (3/8:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
  have hp := force_positive (c:=1) (x:=frameCap) (y:=-(3/8)) (by norm_num [Cmax])
    (by norm_num [frameCap]) (by norm_num [frameCap] : |-(3/8:ℝ)|≤frameCap)
  have hcut : ((cut:ℚ):ℝ)=3/8 := by norm_num [cut]
  have hhh : ((h:ℚ):ℝ)=frameCap := by norm_num [h,frameCap]
  have hflow : ((C10.eval cut+S11.eval h:ℚ):ℝ)≤forceA 1 frameCap (-(3/8)) := by
    rw [Rat.cast_add,← rational_aeval,← rational_aeval,hcut,hhh]
    simp only [forceA,one_mul,Real.cos_neg]
    linarith [hb.2.2.2.2.1,hh.2.1]
  have hghi : forceB 1 frameCap (-(3/8))≤((C12.eval h-S11.eval cut:ℚ):ℝ) := by
    rw [Rat.cast_sub,← rational_aeval,← rational_aeval,hcut,hhh]
    simp only [forceB,one_mul,Real.sin_neg]
    linarith [hh.2.2.2.2.2,hb.2.1]
  have hfirst := mul_le_mul_of_nonneg_right radical_bounds.2.1.le hp.2.le
  have hsecond := mul_le_mul_of_nonneg_left hghi
    (show 0≤(aUpper:ℝ)+1/2 by norm_num [aUpper])
  have hr : (121/5000:ℝ)<((C10.eval cut+S11.eval h:ℚ):ℝ)/2-
      ((aUpper:ℝ)+1/2)*((C12.eval h-S11.eval cut:ℚ):ℝ) := by
    have hh := (Rat.cast_lt (K:=ℝ)).mpr axis_transition_reserve
    push_cast at hh ⊢
    linarith
  nlinarith

theorem axis_force {n : ℝ} (hn : n∈Icc (3/8:ℝ) frameCap) :
    (axial+1/2)*forceB 1 frameCap (-n)≤forceA 1 frameCap (-n)/2 := by
  have hn0 : n∈Icc 0 frameCap := ⟨by linarith [hn.1],hn.2⟩
  have hb : (3/8:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hp := force_positive (c:=1) (x:=frameCap) (y:=-n) (by norm_num [Cmax])
    (by norm_num [frameCap]) (by rw [abs_neg,abs_of_nonneg hn0.1]; exact hn0.2)
  have hpb := force_positive (c:=1) (x:=frameCap) (y:=-(3/8)) (by norm_num [Cmax])
    (by norm_num [frameCap]) (by norm_num [frameCap] : |-(3/8:ℝ)|≤frameCap)
  have hm := axisRatio_antitone hb hn0 hn.1
  have hA : 0<axial+1/2 := by linarith [axial_bounds.1]
  have hscaled := mul_le_mul_of_nonneg_left hm hA.le
  have hcut : (axial+1/2)*axisRatio (3/8)<1/2 := by
    dsimp [axisRatio]
    rw [← mul_div_assoc,div_lt_iff₀ hpb.1]
    linarith [axis_at_cut]
  have hbound : (axial+1/2)*axisRatio n≤1/2 := by linarith
  dsimp [axisRatio] at hbound
  rw [← mul_div_assoc,div_le_iff₀ hp.1] at hbound
  linarith

theorem axis_support {n : ℝ} (hn : n∈Icc (3/8:ℝ) frameCap) :
    sortedSupport (forceA 1 frameCap (-n)) (forceB 1 frameCap (-n))=
      axial*forceA 1 frameCap (-n) := by
  have hn0 : n∈Icc 0 frameCap := ⟨by linarith [hn.1],hn.2⟩
  have hp := force_positive (c:=1) (x:=frameCap) (y:=-n) (by norm_num [Cmax])
    (by norm_num [frameCap]) (by rw [abs_neg,abs_of_nonneg hn0.1]; exact hn0.2)
  simpa only [mul_comm] using sortedSupport_axis hp.2 (axis_force hn)

end SquaresInCircles.Eight.GlobalGA.PositiveBT3.DEndpoint
end
end
end

section
/-!
## Strict sorted-D endpoint positivity at c=1 and c=1.1642

The full-circle comparison is used on its two certified domains; the
remaining c=1 domain uses the proved tangent-zero support formula.
These endpoints are independent of the later signed-D minorant.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.PositiveBT3.DEndpoint
open Candidate Secondary Polynomial PositiveAngularEnvelope OrdinaryAngleConcavity
open PositiveTD.Certificate (S9 S11 C10 C12 taylor_bounds)

theorem phi_lower : (phiLower:ℝ)≤Real.cos frameCap+Real.sin frameCap := by
  have hh := taylor_bounds (show frameCap∈Icc 0 frameCap by norm_num [frameCap])
  have hhh : ((h:ℚ):ℝ)=frameCap := by norm_num [h,frameCap]
  rw [phiLower,Rat.cast_add,← rational_aeval,← rational_aeval,hhh]
  linarith [hh.2.2.2.2.1,hh.2.1]

theorem full_lower (e : End) {n : ℝ} (hn : n∈Icc 0 frameCap) :
    (constant e:ℝ)-R*Real.sqrt (aeval n (P e))+R*Real.sqrt (aeval n H)≤
      D (coefficient e:ℝ) frameCap (-n)+slope*frameCap-vstar n := by
  have hc := coefficient_domain e
  have hR : 0≤R := Real.sqrt_nonneg qCap
  have hnpoly := norm_polynomial_bounds e hn
  have hnormP := mul_le_mul_of_nonneg_left hnpoly.2.2.1 hR
  have hnormH := mul_le_mul_of_nonneg_left hnpoly.2.2.2 hR
  have hphi := mul_le_mul_of_nonneg_left phi_lower (by linarith [hc.1] : 0≤(coefficient e:ℝ))
  have hd := mul_le_mul_of_nonneg_left radical_bounds.1.le
    (by linarith [hc.1] : 0≤1+(coefficient e:ℝ))
  have hzero := radical_bounds.2.2
  have hfull := fullD_lower (c:=(coefficient e:ℝ)) (x:=frameCap) (y:=-n)
    (by norm_num [frameCap]) (by rw [abs_neg,abs_of_nonneg hn.1]; exact hn.2)
  rw [fullD_mixed (show frameCap∈Icc 0 frameCap by norm_num [frameCap]) hn] at hfull
  have hcst : (constant e:ℝ)=
      (coefficient e:ℝ)*(phiLower:ℝ)+1+
        ((coefficient e:ℝ)+1)*((cLower:ℝ)-1/2)+slope*frameCap-(Tzero:ℝ) := by
    simp [constant,slope,h,frameCap]
  rw [hcst]
  dsimp [vstar,V]
  have hcL : (cLower:ℝ)=449607/500000 := by norm_num [cLower]
  have hT : (Tzero:ℝ)=2380990934/1000000000 := by norm_num [Tzero]
  rw [hcL] at hd ⊢
  rw [hT] at hzero ⊢
  generalize slope*frameCap=sf
  linarith

/-- The squared comparison does not require a sign on the isolated
polynomial difference Q(P-H)-A². -/
theorem radical_gap_positive {A P H : ℝ} (hA : 0<A) (hP : 0≤P) (hH : 0<H)
    (hZ : 0<4*A^2*qCap*H-(qCap*(P-H)-A^2)^2) :
    0<A-R*Real.sqrt P+R*Real.sqrt H := by
  have hR : 0<R := by linarith [radius_bounds.1]
  have hX : 0≤R*Real.sqrt P := mul_nonneg hR.le (Real.sqrt_nonneg _)
  have hY : 0<R*Real.sqrt H := mul_pos hR (Real.sqrt_pos.mpr hH)
  have hX2 : (R*Real.sqrt P)^2=qCap*P := by rw [mul_pow,radius_sq,Real.sq_sqrt hP]
  have hY2 : (R*Real.sqrt H)^2=qCap*H := by rw [mul_pow,radius_sq,Real.sq_sqrt hH.le]
  have hright : 0≤2*A*(R*Real.sqrt H) := by positivity
  have hright2 : (2*A*(R*Real.sqrt H))^2=4*A^2*qCap*H := by
    rw [mul_pow,mul_pow,hY2]
    ring
  have hmiddle : qCap*(P-H)-A^2<2*A*(R*Real.sqrt H) := by
    by_contra hh
    have hs := pow_le_pow_left₀ hright (le_of_not_gt hh) 2
    nlinarith only [hs,hright2,hZ]
  have hsum : 0≤A+R*Real.sqrt H := by linarith
  have hcross : R*Real.sqrt P<A+R*Real.sqrt H := by
    by_contra hh
    have hs := pow_le_pow_left₀ hsum (le_of_not_gt hh) 2
    nlinarith only [hs,hX2,hY2,hmiddle]
  linarith

theorem axis_gap_positive {A H : ℝ} (hH : 0<H) (hY : 0<qCap*H-A^2) :
    0<A+R*Real.sqrt H := by
  have hR : 0<R := by linarith [radius_bounds.1]
  have hroot : 0<R*Real.sqrt H := mul_pos hR (Real.sqrt_pos.mpr hH)
  have hsquare : (R*Real.sqrt H)^2=qCap*H := by
    rw [mul_pow,radius_sq,Real.sq_sqrt hH.le]
  by_contra hh
  have hle : R*Real.sqrt H≤-A := by linarith
  have hpow := pow_le_pow_left₀ hroot.le hle 2
  nlinarith

theorem full_certificate_positive (e : End) {n : ℝ}
    (hn : n∈Icc 0 frameCap) (hZ : 0<aeval n (Z e)) :
    0<D (coefficient e:ℝ) frameCap (-n)+slope*frameCap-vstar n := by
  have hA : (0:ℝ)<(constant e:ℝ) := by
    have hh := (Rat.cast_lt (K:=ℝ)).mpr (positive_constants e)
    push_cast at hh
    linarith
  have hpoly := norm_polynomial_bounds e hn
  have hZ' : 0<4*(constant e:ℝ)^2*qCap*aeval n H-
      (qCap*(aeval n (P e)-aeval n H)-(constant e:ℝ)^2)^2 := by
    simpa [Z,Q,qCap] using hZ
  exact (radical_gap_positive hA hpoly.1 (by linarith [hpoly.2.1]) hZ').trans_le
    (full_lower e hn)

theorem axis_identity {n : ℝ} (hn : n∈Icc (3/8:ℝ) frameCap) :
    D 1 frameCap (-n)+slope*frameCap-vstar n=
      (Real.cos frameCap+Real.sin frameCap-1)/2-axial*Real.sin frameCap+
      2*GlobalGA.Secondary.diagonal+slope*frameCap+1/2-R*pairNorm K 1 0-
      (axial+1/2)*Real.cos n+(1/2)*Real.sin n+R*pairNorm K 1 (-n) := by
  have hn0 : n∈Icc 0 frameCap := ⟨by linarith [hn.1],hn.2⟩
  rw [D,axis_support hn,edgeWidth_positive_formula
    (show frameCap∈Icc 0 frameCap by norm_num [frameCap]),edgeWidth_negative_formula hn0]
  simp only [forceA,Real.cos_neg,one_mul]
  dsimp [vstar,V]
  ring

theorem axis_lower {n : ℝ} (hn : n∈Icc (3/8:ℝ) frameCap) :
    aeval n axisA+R*Real.sqrt (aeval n H)≤
      D 1 frameCap (-n)+slope*frameCap-vstar n := by
  have hn0 : n∈Icc 0 frameCap := ⟨by linarith [hn.1],hn.2⟩
  have hh := taylor_bounds (show frameCap∈Icc 0 frameCap by norm_num [frameCap])
  have hnT := taylor_bounds hn0
  have hR : 0≤R := Real.sqrt_nonneg qCap
  have hnorm := mul_le_mul_of_nonneg_left (norm_polynomial_bounds .one hn0).2.2.2 hR
  have hsinH := (transport_trig
    (show frameCap∈Icc 0 frameCap by norm_num [frameCap])).2.2.1
  have hcosN : 0≤Real.cos n := by linarith [(transport_trig hn0).1]
  have haSin := mul_le_mul_of_nonneg_right radical_bounds.2.1.le hsinH
  have hSin := mul_le_mul_of_nonneg_left hh.2.2.1
    (show 0≤(aUpper:ℝ) by norm_num [aUpper])
  have haCos := mul_le_mul_of_nonneg_right radical_bounds.2.1.le hcosN
  have hCos := mul_le_mul_of_nonneg_left hnT.2.2.2.2.2
    (show 0≤(aUpper:ℝ)+1/2 by norm_num [aUpper])
  have heval : aeval n axisA=(axisConstant:ℝ)-
      ((aUpper:ℝ)+1/2)*aeval n C12+(1/2)*aeval n S11 := by simp [axisA]
  have hconst : (axisConstant:ℝ)=((phiLower:ℝ)-1)/2-
      (aUpper:ℝ)*aeval frameCap S9+2*(cLower:ℝ)+slope*frameCap+1/2-(Tzero:ℝ) := by
    have hhh : ((h:ℚ):ℝ)=frameCap := by norm_num [h,frameCap]
    rw [axisConstant]
    push_cast
    rw [← rational_aeval,hhh]
  rw [heval,hconst,axis_identity hn]
  have h1 := phi_lower
  have h2 := radical_bounds.1
  have h3 := radical_bounds.2.2
  have hcL : (cLower:ℝ)=449607/500000 := by norm_num [cLower]
  have hT : (Tzero:ℝ)=2380990934/1000000000 := by norm_num [Tzero]
  have hU : (aUpper:ℝ)=1414575672/1000000000 := by norm_num [aUpper]
  rw [hcL] at h2 ⊢
  rw [hT] at h3 ⊢
  rw [hU] at haSin hSin haCos hCos ⊢
  generalize slope*frameCap=sf
  linarith [hnT.2.1]

theorem axis_certificate_positive {n : ℝ} (hn : n∈Icc (3/8:ℝ) frameCap) :
    0<D 1 frameCap (-n)+slope*frameCap-vstar n := by
  have hn0 : n∈Icc 0 frameCap := ⟨by linarith [hn.1],hn.2⟩
  have hpoly := axis_positive hn
  have hH := (norm_polynomial_bounds .one hn0).2.1
  have hY : 0<qCap*aeval n H-(aeval n axisA)^2 := by
    have hh : 0<aeval n Y := by linarith
    simpa [Y,Q,qCap] using hh
  exact (axis_gap_positive (by linarith) hY).trans_le (axis_lower hn)

/-- The two intrinsic endpoints of the c-concavity argument, including
the complete closed n interval and the tangent-zero transition. -/
theorem endpoint (e : End) {n : ℝ} (hn : n∈Icc 0 frameCap) :
    0<D (coefficient e:ℝ) frameCap (-n)+slope*frameCap-vstar n := by
  cases e
  · by_cases hcut : n≤3/8
    · exact full_certificate_positive .one hn (by linarith [one_positive ⟨hn.1,hcut⟩])
    · have h1 : (coefficient .one:ℝ)=1 := by norm_num [coefficient]
      rw [h1]
      exact axis_certificate_positive ⟨(le_of_not_ge hcut),hn.2⟩
  · exact full_certificate_positive .upper hn (by linarith [upper_positive hn])

end SquaresInCircles.Eight.GlobalGA.PositiveBT3.DEndpoint
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.PositiveBT3
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open PairNormCalculus OrdinaryNegativeSlope

theorem sortedSupport_attained {f g : ℝ} (hf : 0<f) (hg : 0<g) :
    ∃a b : ℝ,0<a ∧ 0≤b ∧ b≤a ∧
      (a+1/2)^2+(b+1/2)^2=qCap ∧ sortedSupport f g=f*a+g*b := by
  by_cases hfg : f≤g
  · have hd0 : (0:ℝ)<GlobalGA.Secondary.diagonal :=
      (by norm_num : (0:ℝ)<8992140/10000000).trans diagonal_bounds.1
    refine ⟨GlobalGA.Secondary.diagonal,GlobalGA.Secondary.diagonal,hd0,hd0.le,le_rfl,
      by rw [← diagonal_circle]; ring,?_⟩
    simp [sortedSupport,hfg,diagonalSupport]
    ring
  by_cases haxis : (axial+1/2)*g≤f/2
  · have ha0 : (0:ℝ)<axial := (by norm_num : (0:ℝ)<14145756/10000000).trans axial_bounds.1
    refine ⟨axial,0,ha0,le_rfl,ha0.le,by rw [zero_add]; exact axial_circle,?_⟩
    rw [sortedSupport_axis hg haxis]
    ring
  let N := Real.sqrt (f^2+g^2)
  have hN : 0<N := Real.sqrt_pos.mpr (by positivity)
  have hN2 : N^2=f^2+g^2 := Real.sq_sqrt (by positivity)
  let a := R*f/N-1/2
  let b := R*g/N-1/2
  have hR : 0<R := Real.sqrt_pos.mpr (by norm_num [qCap])
  have hA : 0<axial+1/2 := by linarith [axial_bounds.1]
  have hcross : N/2<R*g := by
    have hstrict : f/2<(axial+1/2)*g := lt_of_not_ge haxis
    have hsquare := pow_lt_pow_left₀ hstrict (by positivity : 0≤f/2) (by norm_num : (2:ℕ)≠0)
    have hmul : ((axial+1/2)^2+(1/2)^2)*g^2=qCap*g^2 := by rw [axial_circle]
    have he : (R*g)^2=qCap*g^2 := by rw [mul_pow,radius_sq]
    have hsq : (N/2)^2<(R*g)^2 := by
      rw [he]
      linarith [hN2,hsquare,hmul]
    exact lt_of_pow_lt_pow_left₀ 2 (mul_pos hR hg).le hsq
  have hb0 : 0≤b := by
    have hh := (lt_div_iff₀ hN).2 (show (1/2)*N<R*g by linarith)
    dsimp [b]
    linarith
  have hsort : b≤a := by
    have hh := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (lt_of_not_ge hfg).le hR.le) hN.le
    dsimp [a,b]
    linarith
  have hc : (a+1/2)^2+(b+1/2)^2=qCap := by
    have ha' : a+1/2=R*f/N := by dsimp [a]; ring
    have hb' : b+1/2=R*g/N := by dsimp [b]; ring
    rw [ha',hb',div_pow,div_pow,← add_div,mul_pow,mul_pow,← mul_add,← hN2,radius_sq,
      mul_div_assoc,div_self (pow_ne_zero 2 hN.ne'),mul_one]
  have ha0 : 0<a := by
    have hh : GlobalGA.Secondary.diagonal≤a := by
      by_contra hlt
      have hlt' : a<GlobalGA.Secondary.diagonal := lt_of_not_ge hlt
      have p1 := mul_pos (sub_pos.mpr hlt')
        (show 0<GlobalGA.Secondary.diagonal+a+1 by linarith [diagonal_bounds.1])
      have p2 := mul_nonneg (sub_nonneg.mpr hsort) (show 0≤a+b+1 by linarith)
      linarith [diagonal_circle]
    linarith [diagonal_bounds.1]
  refine ⟨a,b,ha0,hb0,hsort,hc,?_⟩
  simp only [sortedSupport,hfg,haxis,↓reduceIte]
  change R*N-(f+g)/2=f*a+g*b
  have hfg' : f*a+g*b=R*(f^2+g^2)/N-(f+g)/2 := by dsimp [a,b]; ring
  rw [hfg',← hN2]
  field_simp

/-- The sorted support, including its tangent-zero branch, is convex along the interpolation of
the coefficient `c` between `1` and `Cmax`. -/
theorem D_weight_concave {c x y : ℝ} (hc : c∈Icc 1 Cmax)
    (hx : |x|≤frameCap) (hy : |y|≤frameCap) :
    ((Cmax-c)/(Cmax-1))*D 1 x y+((c-1)/(Cmax-1))*D Cmax x y≤D c x y := by
  have hp := force_positive hc hx hy
  obtain ⟨a,b,ha,hb,hs,hcircle,he⟩ := sortedSupport_attained hp.1 hp.2
  have hp1 := force_positive (show (1:ℝ)∈Icc 1 Cmax by norm_num [Cmax]) hx hy
  have hpC := force_positive (show Cmax∈Icc 1 Cmax by norm_num [Cmax]) hx hy
  have h1 := raw_sorted_support ha hb hs hcircle.le hp1.1.le hp1.2.le
  have hC := raw_sorted_support ha hb hs hcircle.le hpC.1.le hpC.2.le
  have hden : 0<Cmax-1 := by norm_num [Cmax]
  obtain ⟨α,hαd⟩ : ∃α:ℝ,α=(Cmax-c)/(Cmax-1) := ⟨_,rfl⟩
  obtain ⟨β,hβd⟩ : ∃β:ℝ,β=(c-1)/(Cmax-1) := ⟨_,rfl⟩
  have hα : 0≤α := by rw [hαd]; exact div_nonneg (sub_nonneg.mpr hc.2) hden.le
  have hβ : 0≤β := by rw [hβd]; exact div_nonneg (sub_nonneg.mpr hc.1) hden.le
  have hbary : α+β=1 := by rw [hαd,hβd]; field_simp [hden.ne']; ring
  have hcoef : α+β*Cmax=c := by rw [hαd,hβd]; field_simp [hden.ne']; ring
  rw [← hαd,← hβd]
  have hA : forceA c x y=α*forceA 1 x y+β*forceA Cmax x y := by
    simp only [forceA]
    linear_combination (-Real.sin x)*hcoef+(-Real.cos y)*hbary
  have hB : forceB c x y=α*forceB 1 x y+β*forceB Cmax x y := by
    simp only [forceB]
    linear_combination (-Real.cos x)*hcoef+(-Real.sin y)*hbary
  have key : D c x y-(α*D 1 x y+β*D Cmax x y)=
      α*(sortedSupport (forceA 1 x y) (forceB 1 x y)-(forceA 1 x y*a+forceB 1 x y*b))+
      β*(sortedSupport (forceA Cmax x y) (forceB Cmax x y)-
        (forceA Cmax x y*a+forceB Cmax x y*b)) := by
    simp only [D]
    rw [he,hA,hB]
    linear_combination (-(edgeWidth x-1)-GlobalGA.Secondary.diagonal)*hcoef+
      (-(edgeWidth y-1)-GlobalGA.Secondary.diagonal)*hbary
  have k1 := mul_nonneg hα (sub_nonneg.mpr h1)
  have k2 := mul_nonneg hβ (sub_nonneg.mpr hC)
  linarith

theorem mixed_far_endpoint {c n : ℝ} (hc : c∈Icc 1 Cmax)
    (hn : n∈Icc 0 frameCap) :
    0<D c frameCap (-n)+slope*frameCap-vstar n := by
  have h1 := DEndpoint.endpoint .one hn
  have hC := DEndpoint.endpoint .upper hn
  have e1 : ((DEndpoint.coefficient .one:ℚ):ℝ)=1 := by norm_num [DEndpoint.coefficient]
  have eC : ((DEndpoint.coefficient .upper:ℚ):ℝ)=Cmax := by
    norm_num [DEndpoint.coefficient,Cmax]
  rw [e1] at h1
  rw [eC] at hC
  have hw := D_weight_concave (x:=frameCap) (y:=-n) hc (by norm_num [frameCap])
    (by rw [abs_neg,abs_of_nonneg hn.1]; exact hn.2)
  have hden : 0<Cmax-1 := by norm_num [Cmax]
  obtain ⟨α,hαd⟩ : ∃α:ℝ,α=(Cmax-c)/(Cmax-1) := ⟨_,rfl⟩
  obtain ⟨β,hβd⟩ : ∃β:ℝ,β=(c-1)/(Cmax-1) := ⟨_,rfl⟩
  have hα : 0≤α := by rw [hαd]; exact div_nonneg (sub_nonneg.mpr hc.2) hden.le
  have hβ : 0≤β := by rw [hβd]; exact div_nonneg (sub_nonneg.mpr hc.1) hden.le
  have hs : α+β=1 := by rw [hαd,hβd]; field_simp [hden.ne']; ring
  rw [← hαd,← hβd] at hw
  generalize D 1 frameCap (-n)=d1 at h1 hw
  generalize D Cmax frameCap (-n)=dC at hC hw
  generalize D c frameCap (-n)=dc at hw ⊢
  generalize slope*frameCap=sf at h1 hC ⊢
  generalize vstar n=v at h1 hC ⊢
  have hsv : α*(sf-v)+β*(sf-v)=sf-v := by rw [← add_mul,hs,one_mul]
  by_cases hα0 : α=0
  · have hβ1 : β=1 := by linarith
    rw [hα0,hβ1] at hw
    linarith
  · have k1 := mul_pos (lt_of_le_of_ne hα (Ne.symm hα0)) h1
    have k2 := mul_nonneg hβ hC.le
    linarith

theorem vstar_slope_zero : Vd R K 1 0<1101/1000 := by
  have hN := pairNorm_pos (p:=K) (q:=1) (t:=0) (by norm_num [K])
    (by norm_num) (by norm_num [frameCap])
  have hN2 := pairNorm_sq (p:=K) (q:=1) (t:=0) (by norm_num [K])
    (by norm_num) (by norm_num [frameCap])
  have hR2 : (R*K)^2=qCap*K^2 := by rw [mul_pow,radius_sq]
  have hs : (R*K)^2<((1101/1000)*pairNorm K 1 0)^2 := by
    norm_num [pairEnergy,pairProduct,K] at hN2
    norm_num [qCap,K] at hR2 ⊢
    nlinarith
  have hc : R*K<(1101/1000)*pairNorm K 1 0 := by
    nlinarith [Real.sqrt_nonneg qCap]
  have he : Vd R K 1 0=R*K/pairNorm K 1 0 := by
    simp [Vd,mixedNDerivative,normD1,pairProduct]
    ring
  rw [he]
  exact (div_lt_iff₀ hN).2 hc

theorem vstar_linear_upper {n : ℝ} (hn : n∈Icc 0 frameCap) :
    vstar n≤(1101/1000)*n := by
  have hh := V_tangent_zero (p:=K) (q:=1) (by norm_num [K])
    (by norm_num [K]) (by norm_num [K]) hn
  have hm := mul_le_mul_of_nonneg_right vstar_slope_zero.le hn.1
  exact hh.trans hm

def diagonalIncrement (w x : ℝ) : ℝ :=
  w*(edgeWidth x-1)-w*GlobalGA.Secondary.diagonal*(Real.sin x+Real.cos x-1)

theorem diagonal_negative_growth {n : ℝ} (hn : n∈Icc 0 frameCap) :
    (1327/1000)*n≤(GlobalGA.Secondary.diagonal+1/2)*Real.sin n+(GlobalGA.Secondary.diagonal-1/2)*(1-Real.cos n) := by
  have hh := derivative_reserve
    (f:=fun t => (GlobalGA.Secondary.diagonal+1/2)*Real.sin t+(GlobalGA.Secondary.diagonal-1/2)*(1-Real.cos t))
    (df:=fun t => (GlobalGA.Secondary.diagonal+1/2)*Real.cos t+(GlobalGA.Secondary.diagonal-1/2)*Real.sin t)
    (k:=1327/1000) (by fun_prop)
    (fun t ht => by
      convert ((Real.hasDerivAt_sin t).const_mul (GlobalGA.Secondary.diagonal+1/2)).add
        (((hasDerivAt_const t (1:ℝ)).sub (Real.hasDerivAt_cos t)).const_mul
          (GlobalGA.Secondary.diagonal-1/2)) using 1
      ring)
    (fun t ht => by
      have hh := PositiveTD.diagonal_slope_lower (Ioo_subset_Icc_self ht)
      linarith)
    (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hn hn.1
  simpa using hh

theorem diagonal_increment_lower {w x : ℝ} (hw : w∈Icc 1 Cmax)
    (hx : |x|≤frameCap) :
    -slope*positivePart x+(1327/1000)*negativePart x≤diagonalIncrement w x := by
  by_cases hx0 : 0≤x
  · have ht : x∈Icc 0 frameCap := ⟨hx0,by simpa [abs_of_nonneg hx0] using hx⟩
    have hphi : Real.sin x+Real.cos x-1≤x := by
      linarith [Real.sin_le hx0,Real.cos_le_one x]
    have hwd : w*(GlobalGA.Secondary.diagonal-1/2)≤ slope := by
      have hm := mul_le_mul_of_nonneg_right hw.2
        (by linarith [diagonal_bounds.1] : 0≤GlobalGA.Secondary.diagonal-1/2)
      have hd := mul_lt_mul_of_pos_left
        (show GlobalGA.Secondary.diagonal-1/2<(2/5:ℝ) by linarith [diagonal_bounds.2])
        (show 0<Cmax by norm_num [Cmax])
      norm_num [slope,Cmax] at *
      linarith
    have hmul := mul_le_mul_of_nonneg_left hphi
      (show 0≤w*(GlobalGA.Secondary.diagonal-1/2) from
        mul_nonneg (by linarith [hw.1]) (by linarith [diagonal_bounds.1]))
    have hsl := mul_le_mul_of_nonneg_right hwd hx0
    rw [diagonalIncrement,edgeWidth_positive_formula ht]
    simp only [positivePart,negativePart,max_eq_left hx0,
      max_eq_right (neg_nonpos.mpr hx0),mul_zero,add_zero]
    generalize slope=s at hsl ⊢
    linarith
  · have hn : -x∈Icc 0 frameCap := ⟨by linarith,(neg_le_abs x).trans hx⟩
    have hh := diagonal_negative_growth hn
    have hg : 0≤(GlobalGA.Secondary.diagonal+1/2)*Real.sin (-x)+(GlobalGA.Secondary.diagonal-1/2)*(1-Real.cos (-x)) := by
      linarith [hn.1]
    have hm := mul_le_mul_of_nonneg_right hw.1 hg
    have he : diagonalIncrement w x=
        w*((GlobalGA.Secondary.diagonal+1/2)*Real.sin (-x)+(GlobalGA.Secondary.diagonal-1/2)*(1-Real.cos (-x))) := by
      have hwidth := edgeWidth_negative_formula hn
      simp only [neg_neg] at hwidth
      rw [diagonalIncrement,hwidth,Real.sin_neg,Real.cos_neg]
      ring
    rw [he]
    simp only [positivePart,negativePart,max_eq_right (le_of_not_ge hx0),
      max_eq_left (show 0≤ -x by linarith),mul_zero,zero_add]
    linarith

/-- The diagonal expression is nonnegative on each whole orthant, so integrating it needs no
assumption that a path stays in one branch. -/
theorem diagonal_residual {c x y : ℝ} (hc : c∈Icc 1 Cmax)
    (hxy : SignedDomain x y) :
    0≤c*(edgeWidth x-1)+edgeWidth y-1+(1+c)*GlobalGA.Secondary.diagonal-
      diagonalSupport (forceA c x y) (forceB c x y)+
      slope*positiveTotal x y-vstar (negativeTotal x y) := by
  have hangle := signed_domain_angles hxy
  have hx := diagonal_increment_lower hc hangle.1
  have hy := diagonal_increment_lower
    (show (1:ℝ)∈Icc 1 Cmax by norm_num [Cmax]) hangle.2
  have hN : negativeTotal x y∈Icc 0 frameCap :=
    ⟨add_nonneg (negativePart_nonneg _) (negativePart_nonneg _),hxy.2⟩
  have hv := vstar_linear_upper hN
  have he : c*(edgeWidth x-1)+edgeWidth y-1+(1+c)*GlobalGA.Secondary.diagonal-
      diagonalSupport (forceA c x y) (forceB c x y)=
      diagonalIncrement c x+diagonalIncrement 1 y := by
    dsimp [diagonalSupport,forceA,forceB,diagonalIncrement]
    ring
  rw [he]
  have hh : 0≤diagonalIncrement c x+diagonalIncrement 1 y+
      slope*positiveTotal x y-vstar (negativeTotal x y) := by
    have hnx := negativePart_nonneg x
    have hny := negativePart_nonneg y
    dsimp only [positiveTotal,negativeTotal] at *
    generalize slope=s at hx hy ⊢
    linarith
  exact hh

/-- A continuous full-support branch is bounded by its intrinsic boundary
values.  Strict curvature excludes an interior minimum even if the set
of admissible branch parameters has several components. -/
theorem branch_lower {f df ddf e₁ e₂ : ℝ → ℝ} {l u x κ : ℝ}
    (hf : Continuous f) (he₁ : Continuous e₁) (he₂ : Continuous e₂)
    (hx : x∈Icc l u) (hx₁ : 0≤e₁ x) (hx₂ : 0≤e₂ x) (hκ : 0<κ)
    (hbound : ∀z∈Icc l u,0≤e₁ z → 0≤e₂ z →
      (z=l ∨ z=u ∨ e₁ z=0 ∨ e₂ z=0) → 0≤f z)
    (hd : ∀z∈Ioo l u,0<e₁ z → 0<e₂ z → HasDerivAt f (df z) z)
    (hdd : ∀z∈Ioo l u,0<e₁ z → 0<e₂ z → HasDerivAt df (ddf z) z)
    (hcurv : ∀z∈Ioo l u,0<e₁ z → 0<e₂ z → ddf z≤ -κ) : 0≤f x := by
  let S : Set ℝ := {z | z∈Icc l u ∧ 0≤e₁ z ∧ 0≤e₂ z}
  have hc : IsCompact S := by
    have hS : S=Icc l u∩{z | 0≤e₁ z}∩{z | 0≤e₂ z} := by
      ext z
      simp only [S,Set.mem_ofPred_eq,Set.mem_inter_iff,and_assoc]
    rw [hS]
    exact (isCompact_Icc.inter_right (isClosed_le continuous_const he₁)).inter_right
      (isClosed_le continuous_const he₂)
  have hxS : x∈S := ⟨hx,hx₁,hx₂⟩
  obtain ⟨z,hz,hmin⟩ := hc.exists_isMinOn ⟨x,hxS⟩ hf.continuousOn
  have hz' : z∈Icc l u ∧ 0≤e₁ z ∧ 0≤e₂ z := hz
  by_cases hb : z=l ∨ z=u ∨ e₁ z=0 ∨ e₂ z=0
  · exact (hbound z hz'.1 hz'.2.1 hz'.2.2 hb).trans (hmin hxS)
  have hzi : z∈Ioo l u := by
    simp only [not_or] at hb
    exact ⟨lt_of_le_of_ne hz'.1.1 (Ne.symm hb.1),lt_of_le_of_ne hz'.1.2 hb.2.1⟩
  have hp₁ : 0<e₁ z := by
    have hn : e₁ z≠0 := fun h => hb (Or.inr (Or.inr (Or.inl h)))
    exact lt_of_le_of_ne hz'.2.1 (Ne.symm hn)
  have hp₂ : 0<e₂ z := by
    have hn : e₂ z≠0 := fun h => hb (Or.inr (Or.inr (Or.inr h)))
    exact lt_of_le_of_ne hz'.2.2 (Ne.symm hn)
  let O : Set ℝ := {v | v∈Ioo l u ∧ 0<e₁ v ∧ 0<e₂ v}
  have hO : IsOpen O := by
    have hO' : O=Ioo l u∩{v | 0<e₁ v}∩{v | 0<e₂ v} := by
      ext v
      simp only [O,Set.mem_ofPred_eq,Set.mem_inter_iff,and_assoc]
    rw [hO']
    exact (isOpen_Ioo.inter (isOpen_lt continuous_const he₁)).inter
      (isOpen_lt continuous_const he₂)
  exact False.elim (not_minimum_on_strictly_concave_curve
    (s:=S) (cost:=f) (p:=z) (fun v hv => hmin hv)
    (curve:=id) (value:=f) (dvalue:=df) (ddvalue:=ddf)
    hO (show z∈O from ⟨hzi,hp₁,hp₂⟩) hκ rfl
    (fun v hv => ⟨Ioo_subset_Icc_self hv.1,hv.2.1.le,hv.2.2.le⟩)
    (fun _ _ => rfl)
    (fun v hv => hd v hv.1 hv.2.1 hv.2.2)
    (fun v hv => hdd v hv.1 hv.2.1 hv.2.2)
    (fun v hv => hcurv v hv.1 hv.2.1 hv.2.2))

theorem sortedSupport_full_of_between {f g : ℝ} (hf : 0<f) (hg : 0<g)
    (hfg : g≤f) (haxis : f/2≤(axial+1/2)*g) :
    sortedSupport f g=fullSupport f g := by
  by_cases hd : f≤g
  · have he : f=g := le_antisymm hd hfg
    rw [sortedSupport_diagonal hd]
    exact (full_at_diagonal he (add_nonneg hf.le hg.le)).symm
  by_cases ha : (axial+1/2)*g≤f/2
  · have he : (axial+1/2)*g=f/2 := le_antisymm ha haxis
    rw [sortedSupport_axis hg ha,full_at_axis hf.le hg.le he]
  · simp only [sortedSupport,hd,ha,↓reduceIte]


/-- The three support regions are joined using only their values at the equalities. The continuous
full-circle branch is minimized on its closed region; the other two regions have direct
estimates. -/
theorem support_path_lower {base f g df ddf : ℝ → ℝ} {l u x κ : ℝ}
    (hb : Continuous base) (hf : Continuous f) (hg : Continuous g)
    (hx : x∈Icc l u) (hκ : 0<κ)
    (hpos : ∀z∈Icc l u,0<f z ∧ 0<g z)
    (hdiag : ∀z∈Icc l u,0≤base z-diagonalSupport (f z) (g z))
    (haxis : ∀z∈Icc l u,(axial+1/2)*g z≤f z/2 → 0≤base z-f z*axial)
    (hl : 0≤base l-sortedSupport (f l) (g l))
    (hu : 0≤base u-sortedSupport (f u) (g u))
    (hd : ∀z∈Ioo l u,HasDerivAt (fun v => base v-fullSupport (f v) (g v)) (df z) z)
    (hdd : ∀z∈Ioo l u,HasDerivAt df (ddf z) z)
    (hcurv : ∀z∈Ioo l u,ddf z≤ -κ) :
    0≤base x-sortedSupport (f x) (g x) := by
  by_cases hdiagx : f x≤g x
  · simpa [sortedSupport_diagonal hdiagx] using hdiag x hx
  by_cases haxisx : (axial+1/2)*g x≤f x/2
  · rw [sortedSupport_axis (hpos x hx).2 haxisx]
    exact haxis x hx haxisx
  have hfcont : Continuous (fun v => base v-fullSupport (f v) (g v)) := by
    dsimp [fullSupport]
    fun_prop
  have hh := branch_lower
    (e₁:=fun z => f z-g z) (e₂:=fun z => (axial+1/2)*g z-f z/2)
    (df:=df) (ddf:=ddf) hfcont (by fun_prop) (by fun_prop) hx
    (by linarith [lt_of_not_ge hdiagx]) (by linarith [lt_of_not_ge haxisx]) hκ
    (fun z hz hz₁ hz₂ hedge => by
      have hp := hpos z hz
      rcases hedge with he|he|he|he
      · subst z
        rw [←sortedSupport_full_of_between hp.1 hp.2 (by linarith) (by linarith)]
        exact hl
      · subst z
        rw [←sortedSupport_full_of_between hp.1 hp.2 (by linarith) (by linarith)]
        exact hu
      · rw [full_at_diagonal (by linarith : f z=g z) (add_nonneg hp.1.le hp.2.le)]
        exact hdiag z hz
      · have heq : (axial+1/2)*g z=f z/2 := by linarith
        rw [full_at_axis hp.1.le hp.2.le heq]
        exact haxis z hz heq.le)
    (fun z hz _ _ => hd z hz) (fun z hz _ _ => hdd z hz)
    (fun z hz _ _ => hcurv z hz)
  rw [sortedSupport_full_of_between (hpos x hx).1 (hpos x hx).2
    (le_of_lt (lt_of_not_ge hdiagx)) (le_of_lt (lt_of_not_ge haxisx))]
  exact hh

end SquaresInCircles.Eight.GlobalGA.PositiveBT3
end
end
end

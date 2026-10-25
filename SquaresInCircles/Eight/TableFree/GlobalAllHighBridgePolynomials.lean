module

public import SquaresInCircles.Eight.TableFree.GlobalAllHighBridgeDualSupport
public import SquaresInCircles.Eight.TableFree.PolynomialCertificates

/-!
# Four fixed whole-interval outer-bridge polynomials

The endpoint-source polynomials have degree eight.  The two circle
envelopes have degree twelve.  Each is certified on the full interval
[0,.7] by one translated coefficient bound or one retained quadratic;
there is no subdivision of an angle or of a state arc.  Uncompiled draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalAllHigh.Bridge.DualPolynomial

open Polynomial PowerTailBounds DirectedPowerBounds

def S7 : ℚ[X] := X-C (1/6)*X^3+C (1/120)*X^5-C (1/5040)*X^7
def C8 : ℚ[X] := 1-C (1/2)*X^2+C (1/24)*X^4-C (1/720)*X^6+C (1/40320)*X^8
def C10 : ℚ[X] := C8-C (1/3628800)*X^10
def capQ : ℚ := 710/113-6*(8833/10000)
def piLow : ℚ := 314159/100000
def eta : ℚ := 957/1000
def radiusUpper : ℚ := 494697/250000
def a1Upper : ℚ := 3246869/2500000
def b1Lower : ℚ := 811717/2500000
def Am (mu : ℚ) : ℚ := -103/100+(11/10)*(8898/15625)+(11/10+mu)*(1489593/1000000)
def Bm (mu : ℚ) : ℚ := -(11/10)*(195443/500000)+(11/10+mu)*(1580219/1000000)
def endpointPoly (mu lambda K g bonus : ℚ) : ℚ[X] :=
  C ((1+mu)*piLow/2-mu*(capQ-bonus)+K+g+lambda/2-mu*(9/100))-
    C (1+mu)*X+C (lambda*(1/2-a1Upper)+mu*(9/100))*C8+
    C (lambda*(1/2+b1Lower)+mu*(9/100))*S7
def normSqPoly (mu lambda : ℚ) : ℚ[X] :=
  C (Am mu^2+Bm mu^2+lambda^2)+C (2*lambda)*(C (Am mu)*C8-C (Bm mu)*S7)
def distancePoly (mu lambda K g bonus : ℚ) : ℚ[X] :=
  C ((1+mu)*piLow/2-mu*(capQ-bonus)+K+g+lambda/2-mu*(9/100)-eta)-
    C (1+mu)*X+C (lambda+mu*(9/100))*C10+C (mu*(9/100))*S7
def pLow : ℚ[X] := C (1463/200)-C (129/100)*X-C (18/25)*X^2
def pNonlow : ℚ[X] := C (3241/200)-C (2643/1000)*X-C (731/500)*X^2
def lowLow : ℚ[X] := endpointPoly (17/10) (59/25) (2113/2500) (-4029/2500) 0-
  C eta-C (1/625)
def lowNonlow : ℚ[X] := endpointPoly 5 (93/20) (-1673/10000) (-1357/1000) (93/10000)-C eta
def midLow : ℚ[X] := C 2*pLow*
    distancePoly (17/10) (59/25) (109221/10000) (-4029/2500) (93/10000)-
  C radiusUpper*(pLow^2+normSqPoly (17/10) (59/25))
def midNonlow : ℚ[X] := C 2*pNonlow*
    distancePoly 5 (93/20) (115297/5000) (-1357/1000) (43/2500)-
  C radiusUpper*(pNonlow^2+normSqPoly 5 (93/20))
def lowShift : ℚ[X] := shift (11/20) lowLow
def lowQuotient : ℚ[X] := lowShift.divX.divX
def midNonlowSlope : ℚ[X] := shift (7/20) (-midNonlow.derivative)

@[simp] theorem S7_eval (z : ℝ) : aeval z S7=Arithmetic.sin7 z := by
  simp [S7,Arithmetic.sin7]
  ring
@[simp] theorem C8_eval (z : ℝ) : aeval z C8=Arithmetic.cos8 z := by
  simp [C8,Arithmetic.cos8]
  ring
@[simp] theorem C10_eval (z : ℝ) : aeval z C10=Arithmetic.cos10 z := by
  simp [C10,Arithmetic.cos10,Arithmetic.cos8]
  ring
@[simp] theorem pLow_eval (z : ℝ) : aeval z pLow=1463/200-(129/100)*z-(18/25)*z^2 := by
  simp [pLow]
@[simp] theorem pNonlow_eval (z : ℝ) : aeval z pNonlow=3241/200-(2643/1000)*z-(731/500)*z^2 := by
  simp [pNonlow]

/-! ### Kernel certificates (integer lists of `PolynomialCertificates`) -/

open WholeIntervalPolynomial.Certificate (Scaled toPoly)

private theorem r58_rep_C (n : ℤ) (d : ℕ) {q : ℚ} (h : q=n/d) (hd : (d:ℚ)≠0) :
    (⟨[n],d⟩ : Scaled).Rep (C q) := by
  unfold Scaled.Rep
  simp only [toPoly,mul_zero,add_zero]
  rw [h,← map_mul,mul_div_cancel₀ _ hd]

/-- The coefficient list of the derivative. -/
private def r58_dlist : List ℤ → List ℤ
  | [] => []
  | [_] => []
  | _ :: b :: l => WholeIntervalPolynomial.Certificate.add (b :: l) (0 :: r58_dlist (b :: l))

private theorem r58_toPoly_dlist : ∀ l : List ℤ,toPoly (r58_dlist l)=derivative (toPoly l)
  | [] => by simp [r58_dlist,toPoly]
  | [a] => by simp [r58_dlist,toPoly]
  | a :: b :: l => by
    rw [r58_dlist,WholeIntervalPolynomial.Certificate.toPoly_add,
      show toPoly (a :: b :: l)=C (a:ℚ)+X*toPoly (b :: l) from rfl,
      show toPoly (0 :: r58_dlist (b :: l))=C ((0:ℤ):ℚ)+X*toPoly (r58_dlist (b :: l)) from rfl,
      r58_toPoly_dlist (b :: l)]
    simp only [Int.cast_zero,map_zero,zero_add,derivative_add,derivative_C,derivative_mul,
      derivative_X,one_mul]

private def r58_deriv (a : Scaled) : Scaled := ⟨r58_dlist a.l,a.s⟩

private theorem r58_rep_deriv {a : Scaled} {p : ℚ[X]} (ha : a.Rep p) :
    (r58_deriv a).Rep (derivative p) := by
  unfold Scaled.Rep at *
  show toPoly (r58_dlist a.l)=C (a.s:ℚ)*derivative p
  rw [r58_toPoly_dlist,ha,derivative_C_mul]

private theorem r58_comp_rep {S : Scaled} {p : ℚ[X]} (hp : S.Rep p) (num den : ℕ) (s t : ℤ)
    {m : ℚ} (hden : den≠0) (hm : m=num*s/den) (h1 : (1:ℚ)=num*t/den) :
    (S.center num den s t).Rep (p.comp (C m+X)) := by
  have hc := hp.centered num den s t (a:=m-1) (b:=m+1) hden (by rw [← hm]; ring)
    (by rw [← h1]; ring)
  rwa [WholeIntervalPolynomial.centered,WholeIntervalPolynomial.affine,
    show (m-1+(m+1))/2=m by ring,show (m+1-(m-1))/2=1 by ring,map_one,one_mul] at hc

private theorem r58_series_split {p : ℚ[X]} {n : ℕ} (hp : p.natDegree≤n) :
    p=CenteredMonomialBounds.series n p := by
  conv_lhs => rw [p.as_sum_range_C_mul_X_pow' (n:=n+1) (Nat.lt_succ_of_le hp)]
  rw [Finset.sum_range_succ',CenteredMonomialBounds.series,
    ← Fin.sum_univ_eq_sum_range (fun i => C (p.coeff (i+1))*X^(i+1)) n,pow_zero,mul_one,add_comm]

private theorem r58_constant_split {p : ℚ[X]} {n : ℕ} (hp : p.natDegree≤n) :
    p=C (p.coeff 0)+PowerTailBounds.tail p 1 n := by
  conv_lhs => rw [p.as_sum_range_C_mul_X_pow' (n:=n+1) (Nat.lt_succ_of_le hp)]
  rw [Finset.sum_range_succ',PowerTailBounds.tail,
    ← Fin.sum_univ_eq_sum_range (fun i => C (p.coeff (i+1))*X^(i+1)) n,pow_zero,mul_one,add_comm]

private theorem r58_quadratic_split {p : ℚ[X]} (h : p.natDegree≤12) :
    p=C (p.coeff 0)+C (p.coeff 1)*X+C (p.coeff 2)*X^2+PowerTailBounds.tail p 3 10 := by
  conv_lhs => rw [as_sum_range_C_mul_X_pow' p (Nat.lt_succ_of_le h)]
  rw [show Nat.succ 12=3+10 from rfl,Finset.sum_range_add,PowerTailBounds.tail,
    Fin.sum_univ_eq_sum_range (fun j => C (p.coeff (j+3))*X^(j+3)) 10]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,Nat.reduceAdd,pow_zero,pow_one,
    mul_one,zero_add,add_comm 3]

/-- `CenteredMonomialBounds.lower` at the radius `num/den`, scaled to an integer. -/
private def r58_lowerZ (l : List ℤ) (n num den : ℕ) : ℤ :=
  l.getD 0 0*(den:ℤ)^n+∑ j : Fin n,
    (if (j.val+1)%2=0 then min (l.getD (j.val+1) 0) 0 else -|l.getD (j.val+1) 0|)*
      (num:ℤ)^(j.val+1)*(den:ℤ)^(n-(j.val+1))

private theorem r58_lower_eq {S : Scaled} {p : ℚ[X]} (hp : S.Rep p) (hs : S.s≠0)
    (n num den : ℕ) (hden : den≠0) :
    CenteredMonomialBounds.lower n ((num:ℚ)/den) p=
      (r58_lowerZ S.l n num den:ℚ)/((S.s:ℚ)*(den:ℚ)^n) := by
  have hs' : (0:ℚ)<S.s := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hd : (0:ℚ)<den := by exact_mod_cast Nat.pos_of_ne_zero hden
  unfold CenteredMonomialBounds.lower r58_lowerZ
  simp only [hp.coeff hs]
  push_cast
  rw [add_div,Finset.sum_div]
  congr 1
  · field_simp
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    have hj : j.val+1≤n := j.isLt
    have hpow : (den:ℚ)^n=(den:ℚ)^(j.val+1)*(den:ℚ)^(n-(j.val+1)) := by
      rw [← pow_add,Nat.add_sub_cancel' hj]
    set L : ℚ := ((S.l.getD (j.val+1) 0:ℤ):ℚ)
    by_cases hk : (j.val+1)%2=0
    · simp only [CenteredMonomialBounds.lowerTerm,hk,↓reduceIte]
      rw [hpow,div_pow]
      rcases le_total L 0 with hl | hl
      · rw [min_eq_left hl,min_eq_left (div_nonpos_of_nonpos_of_nonneg hl hs'.le)]
        field_simp
      · rw [min_eq_right hl,min_eq_right (div_nonneg hl hs'.le)]
        simp
    · simp only [CenteredMonomialBounds.lowerTerm,hk,↓reduceIte]
      rw [hpow,div_pow,abs_div,abs_of_pos hs']
      field_simp

private theorem r58_lower_gt {S : Scaled} {p : ℚ[X]} (hp : S.Rep p) (hs : S.s≠0)
    (n num den a b : ℕ) (hden : den≠0) (hb : 0<b) {r c : ℚ} (hr : r=num/den) (hc : c=a/b)
    (h : (a:ℤ)*S.s*(den:ℤ)^n<b*r58_lowerZ S.l n num den) :
    c<CenteredMonomialBounds.lower n r p := by
  rw [hr,hc,r58_lower_eq hp hs n num den hden]
  have hs' : (0:ℚ)<S.s := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hd : (0:ℚ)<den := by exact_mod_cast Nat.pos_of_ne_zero hden
  have hb' : (0:ℚ)<b := by exact_mod_cast hb
  rw [div_lt_div_iff₀ hb' (by positivity)]
  have hq : (((a:ℤ)*S.s*(den:ℤ)^n:ℤ):ℚ)<((b*r58_lowerZ S.l n num den:ℤ):ℚ) := by
    exact_mod_cast h
  push_cast at hq
  linarith

/-- `DirectedPowerBounds.negativeNorm` at the radius `num/den`, scaled to an integer. -/
private def r58_negNormZ (l : List ℤ) (start count num den : ℕ) : ℤ :=
  ∑ j : Fin count,max (-(l.getD (j.val+start) 0)) 0*(num:ℤ)^(j.val+1)*
    (den:ℤ)^(count-(j.val+1))

private theorem r58_negNorm_eq {S : Scaled} {p : ℚ[X]} (hp : S.Rep p) (hs : S.s≠0)
    (start count num den : ℕ) (hden : den≠0) :
    DirectedPowerBounds.negativeNorm p start count ((num:ℚ)/den)=
      (r58_negNormZ S.l start count num den:ℚ)/((S.s:ℚ)*(den:ℚ)^count) := by
  have hs' : (0:ℚ)<S.s := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hd : (0:ℚ)<den := by exact_mod_cast Nat.pos_of_ne_zero hden
  unfold DirectedPowerBounds.negativeNorm r58_negNormZ
  simp only [hp.coeff hs]
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hj : j.val+1≤count := j.isLt
  have hpow : (den:ℚ)^count=(den:ℚ)^(j.val+1)*(den:ℚ)^(count-(j.val+1)) := by
    rw [← pow_add,Nat.add_sub_cancel' hj]
  rw [hpow,div_pow]
  set L : ℚ := ((S.l.getD (j.val+start) 0:ℤ):ℚ)
  rcases le_total (-L) 0 with hl | hl
  · rw [max_eq_right hl,max_eq_right (by rw [← neg_div]; exact div_nonpos_of_nonpos_of_nonneg hl hs'.le)]
    simp
  · rw [max_eq_left hl,max_eq_left (by rw [← neg_div]; exact div_nonneg hl hs'.le)]
    field_simp

/-- `PowerTailBounds.norm` at the radius `num/den`, scaled to an integer. -/
private def r58_normZ (l : List ℤ) (start count num den : ℕ) : ℤ :=
  ∑ j : Fin count,|l.getD (j.val+start) 0| *(num:ℤ)^(j.val+1)*(den:ℤ)^(count-(j.val+1))

private theorem r58_norm_eq {S : Scaled} {p : ℚ[X]} (hp : S.Rep p) (hs : S.s≠0)
    (start count num den : ℕ) (hden : den≠0) :
    PowerTailBounds.norm p start count ((num:ℚ)/den)=
      (r58_normZ S.l start count num den:ℚ)/((S.s:ℚ)*(den:ℚ)^count) := by
  have hs' : (0:ℚ)<S.s := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hd : (0:ℚ)<den := by exact_mod_cast Nat.pos_of_ne_zero hden
  unfold PowerTailBounds.norm r58_normZ
  simp only [hp.coeff hs]
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hj : j.val+1≤count := j.isLt
  rw [abs_div,abs_of_pos hs',div_pow,
    show (den:ℚ)^count=(den:ℚ)^(j.val+1)*(den:ℚ)^(count-(j.val+1)) by
      rw [← pow_add,Nat.add_sub_cancel' hj]]
  field_simp

/-- Horner evaluation at `num/den`, scaled to an integer. -/
private def r58_hornerZ (num den : ℕ) : List ℤ → ℤ
  | [] => 0
  | a :: l => a*(den:ℤ)^(l.length+1)+num*r58_hornerZ num den l

private theorem r58_eval_toPoly (num den : ℕ) (hden : den≠0) : ∀ l : List ℤ,
    (toPoly l).eval ((num:ℚ)/den)*(den:ℚ)^l.length=(r58_hornerZ num den l:ℚ)
  | [] => by simp [toPoly,r58_hornerZ]
  | a :: l => by
    have ih := r58_eval_toPoly num den hden l
    have hd : (den:ℚ)≠0 := by exact_mod_cast hden
    rw [show toPoly (a :: l)=C (a:ℚ)+X*toPoly l from rfl,r58_hornerZ]
    simp only [eval_add,eval_C,eval_mul,eval_X,List.length_cons]
    push_cast
    rw [← ih]
    field_simp
    ring

private theorem r58_eval_pos {S : Scaled} {p : ℚ[X]} (hp : S.Rep p) (hs : S.s≠0)
    (num den : ℕ) (hden : den≠0) {x : ℚ} (hx : x=num/den) (h : 0<r58_hornerZ num den S.l) :
    0<p.eval x := by
  have he := congrArg (fun q => q.eval x) hp
  simp only [eval_mul,eval_C] at he
  have hh := r58_eval_toPoly num den hden S.l
  rw [← hx,he] at hh
  have hs' : (0:ℚ)<S.s := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hd : (0:ℚ)<(den:ℚ)^S.l.length := by
    have : (0:ℚ)<den := by exact_mod_cast Nat.pos_of_ne_zero hden
    positivity
  have hpos : (0:ℚ)<(r58_hornerZ num den S.l:ℚ) := by exact_mod_cast h
  by_contra hneg
  push Not at hneg
  have : (S.s:ℚ)*p.eval x*(den:ℚ)^S.l.length≤0 :=
    mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hs'.le hneg) hd.le
  linarith

/-! Integer representations of the polynomials. -/

private def r58S7 : Scaled :=
  ((Scaled.var.sub ((⟨[1],6⟩ : Scaled).mul (Scaled.var.pow 3))).add
    ((⟨[1],120⟩ : Scaled).mul (Scaled.var.pow 5))).sub
    ((⟨[1],5040⟩ : Scaled).mul (Scaled.var.pow 7))
private theorem r58S7_rep : r58S7.Rep S7 :=
  ((Scaled.rep_var.sub ((r58_rep_C 1 6 (by norm_num) (by norm_num)).mul
    (Scaled.rep_var.pow 3))).add
    ((r58_rep_C 1 120 (by norm_num) (by norm_num)).mul (Scaled.rep_var.pow 5))).sub
    ((r58_rep_C 1 5040 (by norm_num) (by norm_num)).mul (Scaled.rep_var.pow 7))

private def r58C8 : Scaled :=
  ((((Scaled.ofNat 1).sub ((⟨[1],2⟩ : Scaled).mul (Scaled.var.pow 2))).add
    ((⟨[1],24⟩ : Scaled).mul (Scaled.var.pow 4))).sub
    ((⟨[1],720⟩ : Scaled).mul (Scaled.var.pow 6))).add
    ((⟨[1],40320⟩ : Scaled).mul (Scaled.var.pow 8))
private theorem r58C8_rep : r58C8.Rep C8 :=
  (((Scaled.rep_one.sub ((r58_rep_C 1 2 (by norm_num) (by norm_num)).mul
    (Scaled.rep_var.pow 2))).add
    ((r58_rep_C 1 24 (by norm_num) (by norm_num)).mul (Scaled.rep_var.pow 4))).sub
    ((r58_rep_C 1 720 (by norm_num) (by norm_num)).mul (Scaled.rep_var.pow 6))).add
    ((r58_rep_C 1 40320 (by norm_num) (by norm_num)).mul (Scaled.rep_var.pow 8))

private def r58C10 : Scaled := r58C8.sub ((⟨[1],3628800⟩ : Scaled).mul (Scaled.var.pow 10))
private theorem r58C10_rep : r58C10.Rep C10 :=
  r58C8_rep.sub ((r58_rep_C 1 3628800 (by norm_num) (by norm_num)).mul (Scaled.rep_var.pow 10))

private def r58EP (e1 e1b e2 e3 : Scaled) : Scaled :=
  ((e1.sub (e1b.mul Scaled.var)).add (e2.mul r58C8)).add (e3.mul r58S7)
private def r58DP (d1 d1b d2 d3 : Scaled) : Scaled :=
  ((d1.sub (d1b.mul Scaled.var)).add (d2.mul r58C10)).add (d3.mul r58S7)
private def r58NS (n1 n2 n3 n4 : Scaled) : Scaled :=
  n1.add (n2.mul ((n3.mul r58C8).sub (n4.mul r58S7)))

private def r58pLow : Scaled :=
  ((⟨[1463],200⟩ : Scaled).sub ((⟨[129],100⟩ : Scaled).mul Scaled.var)).sub
    ((⟨[18],25⟩ : Scaled).mul (Scaled.var.pow 2))
private theorem r58pLow_rep : r58pLow.Rep pLow :=
  ((r58_rep_C 1463 200 (by norm_num) (by norm_num)).sub
    ((r58_rep_C 129 100 (by norm_num) (by norm_num)).mul Scaled.rep_var)).sub
    ((r58_rep_C 18 25 (by norm_num) (by norm_num)).mul (Scaled.rep_var.pow 2))

private def r58pNonlow : Scaled :=
  ((⟨[3241],200⟩ : Scaled).sub ((⟨[2643],1000⟩ : Scaled).mul Scaled.var)).sub
    ((⟨[731],500⟩ : Scaled).mul (Scaled.var.pow 2))
private theorem r58pNonlow_rep : r58pNonlow.Rep pNonlow :=
  ((r58_rep_C 3241 200 (by norm_num) (by norm_num)).sub
    ((r58_rep_C 2643 1000 (by norm_num) (by norm_num)).mul Scaled.rep_var)).sub
    ((r58_rep_C 731 500 (by norm_num) (by norm_num)).mul (Scaled.rep_var.pow 2))

private def r58LL : Scaled :=
  ((r58EP ⟨[639577869],226000000⟩ ⟨[27],10⟩ ⟨[-108252771],62500000⟩
    ⟨[131203803],62500000⟩).sub ⟨[957],1000⟩).sub ⟨[1],625⟩
private theorem r58LL_rep : r58LL.Rep lowLow :=
  (((((r58_rep_C 639577869 226000000 (by norm_num [piLow,capQ]) (by norm_num)).sub
    ((r58_rep_C 27 10 (by norm_num) (by norm_num)).mul Scaled.rep_var)).add
    ((r58_rep_C (-108252771) 62500000 (by norm_num [a1Upper]) (by norm_num)).mul r58C8_rep)).add
    ((r58_rep_C 131203803 62500000 (by norm_num [b1Lower]) (by norm_num)).mul r58S7_rep)).sub
    (r58_rep_C 957 1000 (by norm_num [eta]) (by norm_num))).sub
    (r58_rep_C 1 625 (by norm_num) (by norm_num))

private def r58LN : Scaled :=
  (r58EP ⟨[55426961],11300000⟩ ⟨[6],1⟩ ⟨[-163208817],50000000⟩
    ⟨[214239681],50000000⟩).sub ⟨[957],1000⟩
private theorem r58LN_rep : r58LN.Rep lowNonlow :=
  ((((r58_rep_C 55426961 11300000 (by norm_num [piLow,capQ]) (by norm_num)).sub
    ((r58_rep_C 6 1 (by norm_num) (by norm_num)).mul Scaled.rep_var)).add
    ((r58_rep_C (-163208817) 50000000 (by norm_num [a1Upper]) (by norm_num)).mul r58C8_rep)).add
    ((r58_rep_C 214239681 50000000 (by norm_num [b1Lower]) (by norm_num)).mul r58S7_rep)).sub
    (r58_rep_C 957 1000 (by norm_num [eta]) (by norm_num))

private def r58ML : Scaled :=
  (((⟨[2],1⟩ : Scaled).mul r58pLow).mul
    (r58DP ⟨[2704248329],226000000⟩ ⟨[27],10⟩ ⟨[2513],1000⟩ ⟨[153],1000⟩)).sub
    ((⟨[494697],250000⟩ : Scaled).mul ((r58pLow.pow 2).add
      (r58NS ⟨[892978328229653],25000000000000⟩ ⟨[118],25⟩ ⟨[9418199],2500000⟩
        ⟨[19973193],5000000⟩)))
private theorem r58ML_rep : r58ML.Rep midLow :=
  (((r58_rep_C 2 1 (by norm_num) (by norm_num)).mul r58pLow_rep).mul
    ((((r58_rep_C 2704248329 226000000 (by norm_num [piLow,capQ,eta]) (by norm_num)).sub
      ((r58_rep_C 27 10 (by norm_num) (by norm_num)).mul Scaled.rep_var)).add
      ((r58_rep_C 2513 1000 (by norm_num) (by norm_num)).mul r58C10_rep)).add
      ((r58_rep_C 153 1000 (by norm_num) (by norm_num)).mul r58S7_rep))).sub
    ((r58_rep_C 494697 250000 (by norm_num [radiusUpper]) (by norm_num)).mul
      ((r58pLow_rep.pow 2).add
        ((r58_rep_C 892978328229653 25000000000000 (by norm_num [Am,Bm]) (by norm_num)).add
          ((r58_rep_C 118 25 (by norm_num) (by norm_num)).mul
            (((r58_rep_C 9418199 2500000 (by norm_num [Am]) (by norm_num)).mul r58C8_rep).sub
              ((r58_rep_C 19973193 5000000 (by norm_num [Bm]) (by norm_num)).mul r58S7_rep))))))

private def r58MN : Scaled :=
  (((⟨[2],1⟩ : Scaled).mul r58pNonlow).mul
    (r58DP ⟨[307520921],11300000⟩ ⟨[6],1⟩ ⟨[51],10⟩ ⟨[9],20⟩)).sub
    ((⟨[494697],250000⟩ : Scaled).mul ((r58pNonlow.pow 2).add
      (r58NS ⟨[9091411090848497],50000000000000⟩ ⟨[93],10⟩ ⟨[17365873],2000000⟩
        ⟨[92093613],10000000⟩)))
private theorem r58MN_rep : r58MN.Rep midNonlow :=
  (((r58_rep_C 2 1 (by norm_num) (by norm_num)).mul r58pNonlow_rep).mul
    ((((r58_rep_C 307520921 11300000 (by norm_num [piLow,capQ,eta]) (by norm_num)).sub
      ((r58_rep_C 6 1 (by norm_num) (by norm_num)).mul Scaled.rep_var)).add
      ((r58_rep_C 51 10 (by norm_num) (by norm_num)).mul r58C10_rep)).add
      ((r58_rep_C 9 20 (by norm_num) (by norm_num)).mul r58S7_rep))).sub
    ((r58_rep_C 494697 250000 (by norm_num [radiusUpper]) (by norm_num)).mul
      ((r58pNonlow_rep.pow 2).add
        ((r58_rep_C 9091411090848497 50000000000000 (by norm_num [Am,Bm]) (by norm_num)).add
          ((r58_rep_C 93 10 (by norm_num) (by norm_num)).mul
            (((r58_rep_C 17365873 2000000 (by norm_num [Am]) (by norm_num)).mul r58C8_rep).sub
              ((r58_rep_C 92093613 10000000 (by norm_num [Bm]) (by norm_num)).mul r58S7_rep))))))

private def r58LS : Scaled := r58LL.center 1 20 11 20
private theorem r58LS_rep : r58LS.Rep lowShift :=
  r58_comp_rep r58LL_rep 1 20 11 20 (by norm_num) (by norm_num) (by norm_num)

private def r58LQT : Scaled := r58LS.divX.divX.center 1 5 (-1) 5
private theorem r58LQT_rep :
    r58LQT.Rep (CenteredMonomialBounds.translated (-1/5) lowQuotient) :=
  r58_comp_rep r58LS_rep.divX.divX 1 5 (-1) 5 (by norm_num) (by norm_num) (by norm_num)

private def r58LND : Scaled := (r58_deriv r58LN).neg.center 1 20 7 20
private theorem r58LND_rep :
    r58LND.Rep (CenteredMonomialBounds.translated (7/20) (-lowNonlow.derivative)) :=
  r58_comp_rep (r58_rep_deriv r58LN_rep).neg 1 20 7 20 (by norm_num) (by norm_num)
    (by norm_num)

private def r58MNS : Scaled := (r58_deriv r58MN).neg.center 1 20 7 20
private theorem r58MNS_rep : r58MNS.Rep midNonlowSlope :=
  r58_comp_rep (r58_rep_deriv r58MN_rep).neg 1 20 7 20 (by norm_num) (by norm_num)
    (by norm_num)

private theorem r58LQT_facts : r58LQT.s≠0 ∧ r58LQT.l.length-1≤6 ∧
    ((3:ℕ):ℤ)*r58LQT.s*((20:ℕ):ℤ)^6<((25:ℕ):ℤ)*r58_lowerZ r58LQT.l 6 7 20 := by
  decide +kernel

private theorem r58LS_facts : r58LS.s≠0 ∧
    25*(r58LS.l.getD 1 0)^2<12*r58LS.l.getD 0 0*r58LS.s := by
  decide +kernel

private theorem r58ML_facts : r58ML.s≠0 ∧ r58ML.l.length-1≤12 ∧ 0<r58ML.l.getD 0 0 ∧
    0≤r58ML.l.getD 1 0 ∧ 0≤r58ML.l.getD 2 0*(10:ℤ)^10-r58_negNormZ r58ML.l 3 10 7 10 := by
  decide +kernel

private theorem r58LND_facts : r58LND.s≠0 ∧ r58LND.l.length-1≤7 ∧
    ((1:ℕ):ℤ)*r58LND.s*((20:ℕ):ℤ)^7<((4:ℕ):ℤ)*r58_lowerZ r58LND.l 7 7 20 := by
  decide +kernel

private theorem r58MNS_facts : r58MNS.s≠0 ∧ r58MNS.l.length-1≤11 ∧
    2*(r58MNS.s:ℤ)*(20:ℤ)^11<r58MNS.l.getD 0 0*(20:ℤ)^11-r58_normZ r58MNS.l 1 11 7 20 := by
  decide +kernel

private theorem r58_last_facts : r58LN.s≠0 ∧ 0<r58_hornerZ 7 10 r58LN.l ∧
    r58MN.s≠0 ∧ 0<r58_hornerZ 7 10 r58MN.l := by
  decide +kernel

theorem low_factor : lowShift=C (lowShift.coeff 0)+C (lowShift.coeff 1)*X+X^2*lowQuotient := by
  have h1 := divX_mul_X_add lowShift
  have h2 := divX_mul_X_add lowShift.divX
  rw [coeff_divX,zero_add] at h2
  rw [lowQuotient]
  linear_combination -h1-X*h2

theorem low_quotient_identity : CenteredMonomialBounds.translated (-1/5) lowQuotient=
    CenteredMonomialBounds.series 6 (CenteredMonomialBounds.translated (-1/5) lowQuotient) := by
  exact r58_series_split ((r58LQT_rep.natDegree_le r58LQT_facts.1).trans r58LQT_facts.2.1)

theorem low_quotient_reserve : (3/25:ℚ)<
    CenteredMonomialBounds.lowerOn 6 (-1/5) (7/20) lowQuotient := by
  show (3/25:ℚ)<CenteredMonomialBounds.lower 6 (7/20)
    (CenteredMonomialBounds.translated (-1/5) lowQuotient)
  exact r58_lower_gt r58LQT_rep r58LQT_facts.1 6 7 20 3 25 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) r58LQT_facts.2.2

theorem low_discriminant : (lowShift.coeff 1)^2<4*(3/25)*(lowShift.coeff 0) := by
  have hs := r58LS_facts.1
  have hs' : (0:ℚ)<r58LS.s := by exact_mod_cast Nat.pos_of_ne_zero hs
  rw [r58LS_rep.coeff hs,r58LS_rep.coeff hs]
  have h : ((25*(r58LS.l.getD 1 0)^2:ℤ):ℚ)<((12*r58LS.l.getD 0 0*r58LS.s:ℤ):ℚ) := by
    exact_mod_cast r58LS_facts.2
  push_cast at h
  rw [div_pow,div_lt_iff₀ (by positivity)]
  have he : 4*(3/25)*(((r58LS.l.getD 0 0:ℤ):ℚ)/r58LS.s)*(r58LS.s:ℚ)^2=
      12*((r58LS.l.getD 0 0:ℤ):ℚ)*r58LS.s/25 := by
    field_simp
    ring
  rw [he]
  linarith

theorem midLow_identity : midLow=C (midLow.coeff 0)+C (midLow.coeff 1)*X+
    C (midLow.coeff 2)*X^2+tail midLow 3 10 := by
  exact r58_quadratic_split ((r58ML_rep.natDegree_le r58ML_facts.1).trans r58ML_facts.2.1)

theorem midLow_reserves : (0:ℚ)< midLow.coeff 0 ∧ 0≤ midLow.coeff 1 ∧
    0≤ midLow.coeff 2-negativeNorm midLow 3 10 (7/10) := by
  have hs := r58ML_facts.1
  have hs' : (0:ℚ)<r58ML.s := by exact_mod_cast Nat.pos_of_ne_zero hs
  refine ⟨?_,?_,?_⟩
  · rw [r58ML_rep.coeff hs]
    exact div_pos (by exact_mod_cast r58ML_facts.2.2.1) hs'
  · rw [r58ML_rep.coeff hs]
    exact div_nonneg (by exact_mod_cast r58ML_facts.2.2.2.1) hs'.le
  · have hr : (7/10:ℚ)=((7:ℕ):ℚ)/((10:ℕ):ℚ) := by norm_num
    rw [hr,r58_negNorm_eq r58ML_rep hs 3 10 7 10 (by norm_num),r58ML_rep.coeff hs]
    have h : (0:ℚ)≤((r58ML.l.getD 2 0*(10:ℤ)^10-r58_negNormZ r58ML.l 3 10 7 10:ℤ):ℚ) := by
      exact_mod_cast r58ML_facts.2.2.2.2
    have he : ((r58ML.l.getD 2 0:ℤ):ℚ)/r58ML.s-
        (r58_negNormZ r58ML.l 3 10 7 10:ℚ)/((r58ML.s:ℚ)*((10:ℕ):ℚ)^10)=
        ((r58ML.l.getD 2 0*(10:ℤ)^10-r58_negNormZ r58ML.l 3 10 7 10:ℤ):ℚ)/
          ((r58ML.s:ℚ)*((10:ℕ):ℚ)^10) := by
      push_cast
      field_simp
      ring
    rw [he]
    exact div_nonneg h (by positivity)

theorem lowNonlow_slope_identity : CenteredMonomialBounds.translated (7/20) (-lowNonlow.derivative)=
    CenteredMonomialBounds.series 7
      (CenteredMonomialBounds.translated (7/20) (-lowNonlow.derivative)) := by
  exact r58_series_split ((r58LND_rep.natDegree_le r58LND_facts.1).trans r58LND_facts.2.1)

theorem lowNonlow_slope_reserve : (1/4:ℚ)<
    CenteredMonomialBounds.lowerOn 7 (7/20) (7/20) (-lowNonlow.derivative) := by
  show (1/4:ℚ)<CenteredMonomialBounds.lower 7 (7/20)
    (CenteredMonomialBounds.translated (7/20) (-lowNonlow.derivative))
  exact r58_lower_gt r58LND_rep r58LND_facts.1 7 7 20 1 4 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) r58LND_facts.2.2

theorem midNonlow_slope_identity : midNonlowSlope=C (midNonlowSlope.coeff 0)+
    tail midNonlowSlope 1 11 := by
  exact r58_constant_split ((r58MNS_rep.natDegree_le r58MNS_facts.1).trans r58MNS_facts.2.1)

theorem midNonlow_slope_reserve : (2:ℚ)< midNonlowSlope.coeff 0-
    PowerTailBounds.norm midNonlowSlope 1 11 (7/20) := by
  have hs := r58MNS_facts.1
  have hs' : (0:ℚ)<r58MNS.s := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hr : (7/20:ℚ)=((7:ℕ):ℚ)/((20:ℕ):ℚ) := by norm_num
  rw [hr,r58_norm_eq r58MNS_rep hs 1 11 7 20 (by norm_num),r58MNS_rep.coeff hs]
  have h : ((2*(r58MNS.s:ℤ)*(20:ℤ)^11:ℤ):ℚ)<
      ((r58MNS.l.getD 0 0*(20:ℤ)^11-r58_normZ r58MNS.l 1 11 7 20:ℤ):ℚ) := by
    exact_mod_cast r58MNS_facts.2.2
  have he : ((r58MNS.l.getD 0 0:ℤ):ℚ)/r58MNS.s-
      (r58_normZ r58MNS.l 1 11 7 20:ℚ)/((r58MNS.s:ℚ)*((20:ℕ):ℚ)^11)=
      ((r58MNS.l.getD 0 0*(20:ℤ)^11-r58_normZ r58MNS.l 1 11 7 20:ℤ):ℚ)/
        ((r58MNS.s:ℚ)*((20:ℕ):ℚ)^11) := by
    push_cast
    field_simp
    ring
  rw [he,lt_div_iff₀ (by positivity)]
  push_cast at h ⊢
  linarith

theorem last_reserves : (0:ℚ)<lowNonlow.eval (7/10) ∧ (0:ℚ)< midNonlow.eval (7/10) := by
  exact ⟨r58_eval_pos r58LN_rep r58_last_facts.1 7 10 (by norm_num) (by norm_num)
      r58_last_facts.2.1,
    r58_eval_pos r58MN_rep r58_last_facts.2.2.1 7 10 (by norm_num) (by norm_num)
      r58_last_facts.2.2.2⟩

theorem centered_domain {z : ℝ} (hz : z∈Icc 0 frameCap) :
    |z-(7/20:ℝ)|≤7/20 := by
  apply abs_le.mpr
  dsimp [frameCap] at hz
  constructor <;> linarith [hz.1,hz.2]

theorem lowLow_positive {z : ℝ} (hz : z∈Icc 0 frameCap) : 0<aeval z lowLow := by
  have hdom : |(z-11/20)-((-1/5:ℚ):ℝ)|≤((7/20:ℚ):ℝ) := by
    have h := centered_domain hz
    rw [show z-11/20-((-1/5:ℚ):ℝ)=z-7/20 by push_cast; ring]
    push_cast
    exact h
  have hl := CenteredMonomialBounds.interval_lower low_quotient_identity
    (by norm_num : (0:ℚ)≤7/20) hdom
  have hr : (3/25:ℝ)<(CenteredMonomialBounds.lowerOn 6 (-1/5) (7/20) lowQuotient:ℝ) := by
    have h := Rat.cast_lt (K:=ℝ) |>.mpr low_quotient_reserve
    rwa [show ((3/25:ℚ):ℝ)=3/25 by norm_num] at h
  have hq : (3/25:ℝ)≤aeval (z-11/20) lowQuotient := by linarith
  have hdisc : (lowShift.coeff 1:ℝ)^2<4*(3/25)*(lowShift.coeff 0:ℝ) := by
    have h := Rat.cast_lt (K:=ℝ) |>.mpr low_discriminant
    push_cast at h
    exact h
  have hp := positive_quadratic (z := z-11/20) (by norm_num : (0:ℝ)<3/25) hdisc
  have hm := mul_le_mul_of_nonneg_left hq (sq_nonneg (z-11/20))
  have hi := congrArg (fun p : ℚ[X] => aeval (z-11/20) p) low_factor
  simp only [map_add,map_mul,map_pow,aeval_C,aeval_X,eq_ratCast] at hi
  have he : aeval (z-11/20) lowShift=aeval z lowLow := by
    simp [lowShift,shift_eval]
  rw [he] at hi
  nlinarith only [hp,hm,hi]

theorem midLow_positive {z : ℝ} (hz : z∈Icc 0 frameCap) : 0<aeval z midLow := by
  have hz' : z∈Icc 0 ((7/10:ℚ):ℝ) := by
    have h2 := hz.2
    simp only [frameCap] at h2
    exact ⟨hz.1,by push_cast; exact h2⟩
  have hl := DirectedPowerBounds.quadratic_lower midLow_identity hz'
  have hr0 : (0:ℝ)<(midLow.coeff 0:ℝ) := by exact_mod_cast midLow_reserves.1
  have hr1 : (0:ℝ)≤(midLow.coeff 1:ℝ) := by exact_mod_cast midLow_reserves.2.1
  have hr2 : (0:ℝ)≤(midLow.coeff 2:ℝ)-(negativeNorm midLow 3 10 (7/10):ℝ) := by
    have h := Rat.cast_le (K:=ℝ) |>.mpr midLow_reserves.2.2
    push_cast at h
    exact h
  nlinarith only [hl,hr0,mul_nonneg hr1 hz.1,mul_nonneg hr2 (sq_nonneg z)]

theorem lowNonlow_derivative_negative {z : ℝ} (hz : z∈Icc 0 frameCap) :
    aeval z lowNonlow.derivative<0 := by
  have hdom : |z-((7/20:ℚ):ℝ)|≤((7/20:ℚ):ℝ) := by
    push_cast
    exact centered_domain hz
  have hl := CenteredMonomialBounds.interval_lower lowNonlow_slope_identity
    (by norm_num : (0:ℚ)≤7/20) hdom
  have hr : (1/4:ℝ)<
      (CenteredMonomialBounds.lowerOn 7 (7/20) (7/20) (-lowNonlow.derivative):ℝ) := by
    have h := Rat.cast_lt (K:=ℝ) |>.mpr lowNonlow_slope_reserve
    rwa [show ((1/4:ℚ):ℝ)=1/4 by norm_num] at h
  simp only [map_neg] at hl
  linarith

theorem midNonlow_derivative_negative {z : ℝ} (hz : z∈Icc 0 frameCap) :
    aeval z midNonlow.derivative<0 := by
  have hdom : |z-7/20|≤((7/20:ℚ):ℝ) := by
    push_cast
    exact centered_domain hz
  have hl := constant_lower midNonlow_slope_identity hdom
  have hr : (2:ℝ)<(midNonlowSlope.coeff 0:ℝ)-
      (PowerTailBounds.norm midNonlowSlope 1 11 (7/20):ℝ) := by
    have h := Rat.cast_lt (K:=ℝ) |>.mpr midNonlow_slope_reserve
    push_cast at h
    exact h
  have he : aeval (z-7/20) midNonlowSlope= -aeval z midNonlow.derivative := by
    simp [midNonlowSlope,shift_eval]
  rw [he] at hl
  linarith

theorem lowNonlow_positive {z : ℝ} (hz : z∈Icc 0 frameCap) : 0<aeval z lowNonlow := by
  have hm : AntitoneOn (fun z : ℝ => aeval z lowNonlow) (Icc 0 frameCap) := by
    apply antiOn_of_hasDeriv_nonpos
    · exact fun z _ => (CenteredMonomialBounds.aeval_hasDerivAt lowNonlow z).continuousAt.continuousWithinAt
    · exact fun z _ => CenteredMonomialBounds.aeval_hasDerivAt lowNonlow z
    · exact fun z hz => (lowNonlow_derivative_negative (Ioo_subset_Icc_self hz)).le
  have he : 0<aeval (frameCap:ℝ) lowNonlow := by
    rw [show frameCap=((7/10:ℚ):ℝ) by norm_num [frameCap],ZeroPolynomial.rational_aeval]
    exact_mod_cast last_reserves.1
  exact he.trans_le (hm hz ⟨by norm_num [frameCap],le_rfl⟩ hz.2)

theorem midNonlow_positive {z : ℝ} (hz : z∈Icc 0 frameCap) : 0<aeval z midNonlow := by
  have hm : AntitoneOn (fun z : ℝ => aeval z midNonlow) (Icc 0 frameCap) := by
    apply antiOn_of_hasDeriv_nonpos
    · exact fun z _ => (CenteredMonomialBounds.aeval_hasDerivAt midNonlow z).continuousAt.continuousWithinAt
    · exact fun z _ => CenteredMonomialBounds.aeval_hasDerivAt midNonlow z
    · exact fun z hz => (midNonlow_derivative_negative (Ioo_subset_Icc_self hz)).le
  have he : 0<aeval (frameCap:ℝ) midNonlow := by
    rw [show frameCap=((7/10:ℚ):ℝ) by norm_num [frameCap],ZeroPolynomial.rational_aeval]
    exact_mod_cast last_reserves.2
  exact he.trans_le (hm hz ⟨by norm_num [frameCap],le_rfl⟩ hz.2)

theorem pLow_positive {z : ℝ} (hz : z∈Icc 0 frameCap) : 0<aeval z pLow := by
  rw [pLow_eval]
  have h2 := pow_le_pow_left₀ hz.1 hz.2 2
  dsimp [frameCap] at *
  nlinarith

theorem pNonlow_positive {z : ℝ} (hz : z∈Icc 0 frameCap) : 0<aeval z pNonlow := by
  rw [pNonlow_eval]
  have h2 := pow_le_pow_left₀ hz.1 hz.2 2
  dsimp [frameCap] at *
  nlinarith

end SquaresInCircles.Eight.TableFree.GlobalAllHigh.Bridge.DualPolynomial

module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star
public import Mathlib.Data.Rat.Star
public import SquaresInCircles.Eight.Arithmetic.PolynomialCertificates
public import SquaresInCircles.Eight.Owners.CenteredMonomialBounds
public import SquaresInCircles.Eight.Owners.ChebyshevLeadingBounds
public import SquaresInCircles.Eight.Owners.DirectedPowerBounds
public import SquaresInCircles.Eight.Owners.GA.Two.PositiveAEnvelope
public import SquaresInCircles.Eight.Owners.GA.Two.PositivePolynomialData

/-!
# Eight squares: all six high A/T endpoint scalar inequalities

The sorted D support is bounded by its full-circle
support, all six polynomial numerators are transferred through their
positive masses, and the B coefficient uses the stated common cap.
-/

section
/-!
## Six whole-interval positive split endpoint numerators

The H and G numerators retain their value at 1/6.  Their quotient
polynomials are bounded by a Chebyshev coefficient sum or an exact
completed square.  Each B numerator retains its endpoint chord; the
chord quotient decreases to a positive value.  The displayed rational
identities and reserves concern the complete interval [1/6,7/10].
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalGA.TwoPositive.Certificate

open Polynomial WholeIntervalPolynomial WholeIntervalPolynomial.Certificate
open PositiveTD.Certificate (L h)

def highHDegree : Endpoint→ℕ
  | .atT => 40
  | .atA => 26
def highTGCoefficients : ℕ→ℚ := coefficient 43 (centered L h (highQG .atT))
def highAGCoefficients : ℕ→ℚ := coefficient 29 (centered L h (highQG .atA))
def highBNegSlope (e : Endpoint) : ℚ[X] :=
  DirectedPowerBounds.shift (13/30) (-(highQB e).derivative)

/-! ## Certificate helpers -/

private def r46_synth (r : ℤ) : List ℤ → List ℤ × ℤ
  | [] => ([],0)
  | [a] => ([],a)
  | a :: b :: l => match r46_synth r (b :: l) with
    | (q,rem) => (rem :: q,a+r*rem)

private def r46_evalZ (r : ℤ) : List ℤ → ℤ
  | [] => 0
  | a :: l => a+r*r46_evalZ r l

private theorem r46_eval_toPoly (r : ℤ) : ∀ l : List ℤ,(toPoly l).eval (r:ℚ)=(r46_evalZ r l:ℚ)
  | [] => by simp [toPoly,r46_evalZ]
  | a :: l => by
    simp only [toPoly,r46_evalZ,eval_add,eval_C,eval_mul,eval_X,r46_eval_toPoly r l]
    push_cast
    ring

private theorem r46_rep_frac {q : ℚ} {n : ℤ} {d : ℕ} (hd : d≠0) (h : q=n/d) :
    (⟨[n],d⟩ : Scaled).Rep (C q) := by
  unfold Scaled.Rep
  simp only [toPoly,mul_zero,add_zero,← map_mul]
  congr 1
  rw [h]
  field_simp

private theorem r46_value {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) (hs : c.s≠0) (r : ℤ) :
    p.eval (r:ℚ)=(r46_evalZ r c.l:ℚ)/c.s := by
  have h := congrArg (fun q => q.eval (r:ℚ)) hc
  simp only [r46_eval_toPoly,eval_mul,eval_C] at h
  rw [h]
  field_simp

private theorem r46_rep_div {c : Scaled} {P Q : ℚ[X]} {v α : ℚ} {r k : ℤ} {m : ℕ}
    (hc : c.Rep P) (hid : P=C v+C α*(X-C (r:ℚ))*Q)
    (hG : WholeIntervalPolynomial.Certificate.mul [-r,1] (r46_synth r c.l).1=
      WholeIntervalPolynomial.Certificate.add c.l [-(r46_synth r c.l).2])
    (hk : (k:ℚ)*α=m) :
    (⟨smul k (r46_synth r c.l).1,c.s*m⟩ : Scaled).Rep Q := by
  have h1 := congrArg toPoly hG
  rw [toPoly_mul,toPoly_add,hc,hid] at h1
  simp only [toPoly,mul_zero,add_zero,Int.cast_neg,Int.cast_one,map_neg,map_one,mul_one] at h1
  have hX : X-C (r:ℚ)≠0 := X_sub_C_ne_zero _
  have h2 : (X-C (r:ℚ))*(toPoly (r46_synth r c.l).1-C ((c.s:ℚ)*α)*Q)=
      C ((c.s:ℚ)*v-((r46_synth r c.l).2:ℚ)) := by
    rw [map_sub,map_mul,map_mul]
    linear_combination h1
  have h3 := congrArg (fun q => q.eval (r:ℚ)) h2
  simp only [eval_mul,eval_sub,eval_X,eval_C,sub_self,zero_mul] at h3
  rw [← h3,map_zero] at h2
  have h4 := sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left hX)
  unfold Scaled.Rep
  rw [toPoly_smul,h4]
  push_cast
  rw [← hk]
  simp only [map_mul]
  ring

private theorem r46_series_quadratic (b : ℕ→ℚ) (n : ℕ) :
    series (n+2) b=C (b 0-b 2)+C (b 1)*X+C (2*b 2)*X^2+ChebyshevLeadingBounds.tail b 3 n := by
  simp only [series,ChebyshevLeadingBounds.tail]
  rw [Fin.sum_univ_succ,Fin.sum_univ_succ]
  have hT : ∀ j : Fin n,C (b (((j.succ).succ : Fin (n+2)).val+1))*
      Chebyshev.T ℚ ((((j.succ).succ : Fin (n+2)).val:ℤ)+1)=
      C (b (j.val+3))*Chebyshev.T ℚ ((j.val:ℤ)+(3:ℕ)) := by
    intro j
    simp only [Fin.val_succ]
    push_cast
    ring_nf
  rw [Finset.sum_congr rfl (fun j _ => hT j)]
  have h1 : Chebyshev.T ℚ (((0:Fin (n+2)).val:ℤ)+1)=X := by simp
  have h2 : Chebyshev.T ℚ ((((0:Fin (n+1)).succ : Fin (n+2)).val:ℤ)+1)=2*X^2-1 := by
    simp only [Fin.succ_zero_eq_one,Fin.val_one]
    push_cast
    exact Chebyshev.T_two ℚ
  have h3 : (((0:Fin (n+1)).succ : Fin (n+2)).val)+1=2 := by simp
  rw [h1,h2,h3]
  simp only [Fin.val_zero,zero_add,map_sub,map_mul]
  rw [show (C (2:ℚ))=2 from rfl]
  ring

private theorem r46_series_cubic (b : ℕ→ℚ) (n : ℕ) :
    series (n+3) b=C (b 0-b 2)+C (b 1-3*b 3)*X+C (2*b 2)*X^2+C (4*b 3)*X^3+
      ChebyshevLeadingBounds.tail b 4 n := by
  simp only [series,ChebyshevLeadingBounds.tail]
  rw [Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_succ]
  have hT : ∀ j : Fin n,C (b ((((j.succ).succ).succ : Fin (n+3)).val+1))*
      Chebyshev.T ℚ (((((j.succ).succ).succ : Fin (n+3)).val:ℤ)+1)=
      C (b (j.val+4))*Chebyshev.T ℚ ((j.val:ℤ)+(4:ℕ)) := by
    intro j
    simp only [Fin.val_succ]
    push_cast
    ring_nf
  rw [Finset.sum_congr rfl (fun j _ => hT j)]
  have h1 : Chebyshev.T ℚ (((0:Fin (n+3)).val:ℤ)+1)=X := by simp
  have h2 : Chebyshev.T ℚ ((((0:Fin (n+2)).succ : Fin (n+3)).val:ℤ)+1)=2*X^2-1 := by
    simp only [Fin.succ_zero_eq_one,Fin.val_one]
    push_cast
    exact Chebyshev.T_two ℚ
  have h3 : Chebyshev.T ℚ (((((0:Fin (n+1)).succ : Fin (n+2)).succ : Fin (n+3)).val:ℤ)+1)=
      4*X^3-3*X := by
    simp only [Fin.succ_zero_eq_one,Fin.succ_one_eq_two,Fin.val_two]
    have := Chebyshev.T_add_two ℚ 1
    push_cast at this ⊢
    rw [this,Chebyshev.T_two,Chebyshev.T_one]
    ring
  have h4 : (((0:Fin (n+2)).succ : Fin (n+3)).val)+1=2 := by simp
  have h5 : ((((0:Fin (n+1)).succ : Fin (n+2)).succ : Fin (n+3)).val)+1=3 := by simp
  rw [h1,h2,h3,h4,h5]
  simp only [Fin.val_zero,zero_add,map_sub,map_mul]
  rw [show (C (2:ℚ))=2 from rfl,show (C (3:ℚ))=3 from rfl,show (C (4:ℚ))=4 from rfl]
  ring

private theorem r46_eq_tail {p : ℚ[X]} {n : ℕ} (h : p.natDegree≤n) :
    p=C (p.coeff 0)+PowerTailBounds.tail p 1 n := by
  conv_lhs => rw [p.as_sum_range_C_mul_X_pow' (n:=n+1) (by omega)]
  rw [Finset.sum_range_succ',PowerTailBounds.tail,Fin.sum_univ_eq_sum_range
    (fun i => C (p.coeff (i+1))*X^(i+1)) n]
  simp only [pow_zero,mul_one]
  ring

private theorem r46_lt_div {ρ : ℚ} {num Z M : ℤ} {den : ℕ} (hρ : ρ=num/den) (hden : 0<den)
    (hM : 0<M) (h : num*M<2*den*Z) : ρ<(Z:ℚ)/((M:ℚ)/2) := by
  have hd : (0:ℚ)<den := by exact_mod_cast hden
  have hM' : (0:ℚ)<M := by exact_mod_cast hM
  have hq : ((num*M:ℤ):ℚ)<((2*den*Z:ℤ):ℚ) := by exact_mod_cast h
  push_cast at hq
  rw [lt_div_iff₀ (by positivity),hρ,div_mul_eq_mul_div,div_lt_iff₀ hd]
  linarith

private theorem r46_scale_cast (c : Scaled) :
    (c.s:ℚ)*2^c.l.length/2=(((c.s*2^c.l.length : ℕ):ℤ):ℚ)/2 := by
  push_cast
  ring

private theorem r46_lowerOn_lt {c : Scaled} {a b : ℚ} {p : ℚ[X]}
    (hc : c.Rep (WholeIntervalPolynomial.centered a b p)) (hs : c.s≠0) {D : ℕ}
    (hl : c.l.length≤D+1) {ρ : ℚ} {num : ℤ} {den : ℕ} (hρ : ρ=num/den) (hden : 0<den)
    (h : num*((c.s*2^c.l.length : ℕ):ℤ)<2*den*lowerZ D (fun j => (chebList c.l).getD j 0)) :
    ρ<lowerOn D a b p := by
  rw [lowerOn_eq_of_rep hc hs hl,r46_scale_cast]
  exact r46_lt_div hρ hden (by have := Nat.pos_of_ne_zero hs; positivity) h

private theorem r46_quadratic {c : Scaled} {q : ℚ[X]} (hc : c.Rep q) (hs : c.s≠0) {D : ℕ}
    (hl : c.l.length≤D+1) (n : ℕ) {ρ : ℚ} {num : ℤ} {den : ℕ} (hρ : ρ=num/den) (hden : 0<den)
    (h2 : 0<(chebList c.l).getD 2 0)
    (h : num*(8*(chebList c.l).getD 2 0*((c.s*2^c.l.length : ℕ):ℤ))<
      2*den*(8*(chebList c.l).getD 2 0*((chebList c.l).getD 0 0-(chebList c.l).getD 2 0-
        ∑ j : Fin n,|(chebList c.l).getD (j.val+3) 0|)-((chebList c.l).getD 1 0)^2)) :
    0<coefficient D q 2 ∧ ρ<ChebyshevLeadingBounds.quadraticReserve (coefficient D q) n := by
  have hN0 := scale_pos hs
  have hb : ∀ j,coefficient D q j=((chebList c.l).getD j 0:ℚ)/(c.s*2^c.l.length/2) :=
    fun j => hc.coefficient_eq hs hl j
  have hB2 : (0:ℚ)<(chebList c.l).getD 2 0 := by exact_mod_cast h2
  refine ⟨by rw [hb]; exact div_pos hB2 hN0,?_⟩
  have hT : ChebyshevLeadingBounds.tailNorm (coefficient D q) 3 n=
      ((∑ j : Fin n,|(chebList c.l).getD (j.val+3) 0| : ℤ):ℚ)/(c.s*2^c.l.length/2) := by
    unfold ChebyshevLeadingBounds.tailNorm
    push_cast
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hb,abs_div,abs_of_pos hN0]
  unfold ChebyshevLeadingBounds.quadraticReserve
  rw [hT,hb 0,hb 1,hb 2]
  have hs' : (0:ℚ)<c.s := by exact_mod_cast Nat.pos_of_ne_zero hs
  have key : ((chebList c.l).getD 0 0:ℚ)/(c.s*2^c.l.length/2)-
      ((chebList c.l).getD 2 0:ℚ)/(c.s*2^c.l.length/2)-
      (((chebList c.l).getD 1 0:ℚ)/(c.s*2^c.l.length/2))^2/
        (8*(((chebList c.l).getD 2 0:ℚ)/(c.s*2^c.l.length/2)))-
      ((∑ j : Fin n,|(chebList c.l).getD (j.val+3) 0| : ℤ):ℚ)/(c.s*2^c.l.length/2)=
      ((8*(chebList c.l).getD 2 0*((chebList c.l).getD 0 0-(chebList c.l).getD 2 0-
        ∑ j : Fin n,|(chebList c.l).getD (j.val+3) 0|)-((chebList c.l).getD 1 0)^2 : ℤ):ℚ)/
      (((8*(chebList c.l).getD 2 0*((c.s*2^c.l.length : ℕ):ℤ) : ℤ):ℚ)/2) := by
    push_cast
    field_simp
    ring
  rw [key]
  exact r46_lt_div hρ hden (by positivity) h

private theorem r46_cubic {c : Scaled} {q : ℚ[X]} (hc : c.Rep q) (hs : c.s≠0) {D : ℕ}
    (hl : c.l.length≤D+1) (n : ℕ) {ρ : ℚ} {num : ℤ} {den : ℕ} (hρ : ρ=num/den) (hden : 0<den)
    (h3 : 0<2*(chebList c.l).getD 2 0-4*|(chebList c.l).getD 3 0|)
    (h : num*(4*(2*(chebList c.l).getD 2 0-4*|(chebList c.l).getD 3 0|)*
        ((c.s*2^c.l.length : ℕ):ℤ))<
      2*den*(4*(2*(chebList c.l).getD 2 0-4*|(chebList c.l).getD 3 0|)*
        ((chebList c.l).getD 0 0-(chebList c.l).getD 2 0-
          ∑ j : Fin n,|(chebList c.l).getD (j.val+4) 0|)-
        ((chebList c.l).getD 1 0-3*(chebList c.l).getD 3 0)^2)) :
    0<2*coefficient D q 2-4*|coefficient D q 3| ∧
      ρ<ChebyshevLeadingBounds.cubicReserve (coefficient D q) n := by
  have hN0 := scale_pos hs
  have hb : ∀ j,coefficient D q j=((chebList c.l).getD j 0:ℚ)/(c.s*2^c.l.length/2) :=
    fun j => hc.coefficient_eq hs hl j
  have hE : 2*coefficient D q 2-4*|coefficient D q 3|=
      ((2*(chebList c.l).getD 2 0-4*|(chebList c.l).getD 3 0| : ℤ):ℚ)/(c.s*2^c.l.length/2) := by
    rw [hb,hb,abs_div,abs_of_pos hN0]
    push_cast
    ring
  have hE0 : (0:ℚ)<((2*(chebList c.l).getD 2 0-4*|(chebList c.l).getD 3 0| : ℤ):ℚ) := by
    exact_mod_cast h3
  refine ⟨by rw [hE]; exact div_pos hE0 hN0,?_⟩
  have hT : ChebyshevLeadingBounds.tailNorm (coefficient D q) 4 n=
      ((∑ j : Fin n,|(chebList c.l).getD (j.val+4) 0| : ℤ):ℚ)/(c.s*2^c.l.length/2) := by
    unfold ChebyshevLeadingBounds.tailNorm
    push_cast
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hb,abs_div,abs_of_pos hN0]
  unfold ChebyshevLeadingBounds.cubicReserve
  rw [hT,hE,hb 0,hb 1,hb 2,hb 3]
  have hs' : (0:ℚ)<c.s := by exact_mod_cast Nat.pos_of_ne_zero hs
  set E : ℤ := 2*(chebList c.l).getD 2 0-4*|(chebList c.l).getD 3 0| with hEdef
  have key : ((chebList c.l).getD 0 0:ℚ)/(c.s*2^c.l.length/2)-
      ((chebList c.l).getD 2 0:ℚ)/(c.s*2^c.l.length/2)-
      (((chebList c.l).getD 1 0:ℚ)/(c.s*2^c.l.length/2)-
        3*(((chebList c.l).getD 3 0:ℚ)/(c.s*2^c.l.length/2)))^2/
        (4*((E:ℚ)/(c.s*2^c.l.length/2)))-
      ((∑ j : Fin n,|(chebList c.l).getD (j.val+4) 0| : ℤ):ℚ)/(c.s*2^c.l.length/2)=
      ((4*E*((chebList c.l).getD 0 0-(chebList c.l).getD 2 0-
        ∑ j : Fin n,|(chebList c.l).getD (j.val+4) 0|)-
        ((chebList c.l).getD 1 0-3*(chebList c.l).getD 3 0)^2 : ℤ):ℚ)/
      (((4*E*((c.s*2^c.l.length : ℕ):ℤ) : ℤ):ℚ)/2) := by
    push_cast
    field_simp
    ring
  rw [key]
  exact r46_lt_div hρ hden (by positivity) h

private theorem r46_power {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) (hs : c.s≠0) (n : ℕ)
    {r : ℚ} {rn rd : ℕ} (hr : r=rn/rd) (hrd : 0<rd) {ρ : ℚ} {num : ℤ} {den : ℕ}
    (hρ : ρ=num/den) (hden : 0<den)
    (h : num*((c.s*rd^n : ℕ):ℤ)<den*(c.l.getD 0 0*(rd:ℤ)^n-
      ∑ j : Fin n,|c.l.getD (j.val+1) 0| *(rn:ℤ)^(j.val+1)*(rd:ℤ)^(n-1-j.val))) :
    ρ<p.coeff 0-PowerTailBounds.norm p 1 n r := by
  have hs' : (0:ℚ)<c.s := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hd' : (0:ℚ)<rd := by exact_mod_cast hrd
  have hco := hc.coeff hs
  have hterm : ∀ j : Fin n,|p.coeff (j.val+1)| *r^(j.val+1)=
      ((|c.l.getD (j.val+1) 0| *(rn:ℤ)^(j.val+1)*(rd:ℤ)^(n-1-j.val) : ℤ):ℚ)/(c.s*rd^n) := by
    intro j
    have hp : (rd:ℚ)^n=rd^(j.val+1)*rd^(n-1-j.val) := by
      rw [← pow_add]
      congr 1
      have := j.isLt
      omega
    rw [hco,hr,abs_div,abs_of_pos hs',div_pow,hp]
    push_cast
    field_simp
  have hnorm : PowerTailBounds.norm p 1 n r=
      ((∑ j : Fin n,|c.l.getD (j.val+1) 0| *(rn:ℤ)^(j.val+1)*(rd:ℤ)^(n-1-j.val) : ℤ):ℚ)/
        (c.s*rd^n) := by
    unfold PowerTailBounds.norm
    rw [Finset.sum_congr rfl (fun j _ => hterm j)]
    push_cast
    rw [Finset.sum_div]
  rw [hnorm,hco 0]
  have key : ((c.l.getD 0 0:ℤ):ℚ)/c.s-
      ((∑ j : Fin n,|c.l.getD (j.val+1) 0| * (rn:ℤ)^(j.val+1)*(rd:ℤ)^(n-1-j.val) : ℤ):ℚ)/
        (c.s*rd^n)=
      ((c.l.getD 0 0*(rd:ℤ)^n-
        ∑ j : Fin n,|c.l.getD (j.val+1) 0| * (rn:ℤ)^(j.val+1)*(rd:ℤ)^(n-1-j.val) : ℤ):ℚ)/
        (c.s*rd^n) := by
    rw [Int.cast_sub,sub_div]
    congr 1
    push_cast
    field_simp
  have hden' : (0:ℚ)<den := by exact_mod_cast hden
  rw [key]
  generalize (c.l.getD 0 0*(rd:ℤ)^n-
    ∑ j : Fin n,|c.l.getD (j.val+1) 0| * (rn:ℤ)^(j.val+1)*(rd:ℤ)^(n-1-j.val))=Z at h ⊢
  have hq : ((num*((c.s*rd^n : ℕ):ℤ) : ℤ):ℚ)<((den*Z : ℤ):ℚ) := by exact_mod_cast h
  push_cast at hq
  rw [lt_div_iff₀ (by positivity),hρ,div_mul_eq_mul_div,div_lt_iff₀ hden']
  linarith

private theorem r46_value_lt {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) (hs : c.s≠0) (r : ℤ)
    {ρ : ℚ} {num : ℤ} {den : ℕ} (hρ : ρ=num/den) (hden : 0<den)
    (h : num*(c.s:ℤ)<den*r46_evalZ r c.l) : ρ<p.eval (r:ℚ) := by
  rw [r46_value hc hs r]
  have hs' : (0:ℚ)<c.s := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hd : (0:ℚ)<den := by exact_mod_cast hden
  have hq : ((num*(c.s:ℤ):ℤ):ℚ)<((den*r46_evalZ r c.l:ℤ):ℚ) := by exact_mod_cast h
  push_cast at hq
  rw [lt_div_iff₀ hs',hρ,div_mul_eq_mul_div,div_lt_iff₀ hd]
  linarith

private theorem r46_centered_eval (a b : ℚ) (p : ℚ[X]) (x : ℚ) :
    (WholeIntervalPolynomial.centered a b p).eval x=p.eval ((a+b)/2+(b-a)/2*x) := by
  simp [WholeIntervalPolynomial.centered,WholeIntervalPolynomial.affine,eval_comp]

private def r46_deriv : List ℤ → List ℤ
  | [] => []
  | _ :: l => WholeIntervalPolynomial.Certificate.add l (0 :: r46_deriv l)

private theorem r46_toPoly_deriv : ∀ l : List ℤ,toPoly (r46_deriv l)=derivative (toPoly l)
  | [] => by simp [r46_deriv,toPoly]
  | a :: l => by
    rw [r46_deriv,toPoly_add]
    simp only [toPoly,r46_toPoly_deriv l,derivative_add,derivative_C,derivative_mul,
      derivative_X,Int.cast_zero,map_zero]
    ring

private theorem r46_rep_deriv {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) :
    (⟨r46_deriv c.l,c.s⟩ : Scaled).Rep (derivative p) := by
  unfold Scaled.Rep at *
  rw [r46_toPoly_deriv,hc,derivative_C_mul]

/-- The gcd of the scale `s` and all entries of `l`. -/
private def r46_gcd (s : ℕ) : List ℤ → ℕ
  | [] => s
  | a :: l => Nat.gcd a.natAbs (r46_gcd s l)

private theorem r46_gcd_dvd (s : ℕ) : ∀ l : List ℤ,
    r46_gcd s l ∣ s ∧ ∀ a ∈ l,((r46_gcd s l : ℕ):ℤ) ∣ a
  | [] => by simp [r46_gcd]
  | a :: l => by
    obtain ⟨h1,h2⟩ := r46_gcd_dvd s l
    refine ⟨(Nat.gcd_dvd_right _ _).trans h1,?_⟩
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact Int.natCast_dvd.mpr (Nat.gcd_dvd_left _ _)
    · exact (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right _ _)).trans (h2 b hb)

private theorem r46_smul_div (g : ℤ) : ∀ l : List ℤ,(∀ a ∈ l,g ∣ a) →
    smul g (l.map (fun a => a/g))=l
  | [],_ => rfl
  | a :: l,h => by
    simp only [List.map_cons,smul]
    rw [Int.mul_ediv_cancel' (h a List.mem_cons_self),
      r46_smul_div g l (fun b hb => h b (List.mem_cons_of_mem a hb))]

private theorem r46_toPoly_zero : ∀ l : List ℤ,toPoly (l.map (fun _ => (0:ℤ)))=0
  | [] => rfl
  | a :: l => by
    simp only [List.map_cons,toPoly,r46_toPoly_zero l,Int.cast_zero,map_zero,mul_zero,add_zero]

/-- Division of a scaled list by the gcd of its entries and its scale. -/
private def r46_red (c : Scaled) : Scaled :=
  ⟨c.l.map (fun a => a/((r46_gcd c.s c.l : ℕ):ℤ)),c.s/r46_gcd c.s c.l⟩

private theorem r46_rep_red {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) : (r46_red c).Rep p := by
  obtain ⟨h1,h2⟩ := r46_gcd_dvd c.s c.l
  set g := r46_gcd c.s c.l with hg
  have hl := r46_smul_div (g:ℤ) c.l h2
  unfold Scaled.Rep at *
  rw [← hl,toPoly_smul] at hc
  obtain ⟨k,hk⟩ := h1
  simp only [r46_red,← hg]
  rcases Nat.eq_zero_or_pos g with h0 | hpos
  · have hs : c.s=0 := by rw [hk,h0,zero_mul]
    have hz : ∀ a ∈ c.l,a=0 := fun a ha => by
      have := h2 a ha
      rw [h0,Nat.cast_zero] at this
      exact zero_dvd_iff.mp this
    rw [h0,hs]
    simp only [Nat.cast_zero,Int.ediv_zero,Nat.zero_div,map_zero,zero_mul]
    exact r46_toPoly_zero _
  · have hg0 : (g:ℚ)≠0 := by exact_mod_cast hpos.ne'
    rw [hk,Nat.mul_div_cancel_left k hpos]
    rw [hk] at hc
    push_cast at hc
    have := mul_left_cancel₀ (show C (g:ℚ)≠0 from C_ne_zero.mpr hg0)
      (hc.trans (by rw [map_mul,mul_assoc]))
    exact this

/-! ## Integer representations of the high polynomials -/

private def sS5 : Scaled := r46_red ((Scaled.var.sub ((Scaled.const (1/6)).mul (Scaled.var.pow 3))).add
  ((Scaled.const (1/120)).mul (Scaled.var.pow 5)))
private theorem rS5 : sS5.Rep PositiveTD.Certificate.S5 := r46_rep_red ((Scaled.rep_var.sub ((Scaled.rep_const _).mul (Scaled.rep_var.pow 3))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 5)))
private def sS9 : Scaled := r46_red ((sS5.sub ((Scaled.const (1/5040)).mul (Scaled.var.pow 7))).add
  ((Scaled.const (1/362880)).mul (Scaled.var.pow 9)))
private theorem rS9 : sS9.Rep PositiveTD.Certificate.S9 := r46_rep_red ((rS5.sub ((Scaled.rep_const _).mul (Scaled.rep_var.pow 7))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 9)))
private def sS11 : Scaled := r46_red (sS9.sub ((Scaled.const (1/39916800)).mul (Scaled.var.pow 11)))
private theorem rS11 : sS11.Rep PositiveTD.Certificate.S11 := r46_rep_red (rS9.sub ((Scaled.rep_const _).mul (Scaled.rep_var.pow 11)))
private def sC4 : Scaled := r46_red (((Scaled.ofNat 1).sub ((Scaled.const (1/2)).mul (Scaled.var.pow 2))).add
  ((Scaled.const (1/24)).mul (Scaled.var.pow 4)))
private theorem rC4 : sC4.Rep PositiveTD.Certificate.C4 := r46_rep_red ((Scaled.rep_one.sub ((Scaled.rep_const _).mul (Scaled.rep_var.pow 2))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 4)))
private def sC10 : Scaled := r46_red (((sC4.sub ((Scaled.const (1/720)).mul (Scaled.var.pow 6))).add
  ((Scaled.const (1/40320)).mul (Scaled.var.pow 8))).sub
  ((Scaled.const (1/3628800)).mul (Scaled.var.pow 10)))
private theorem rC10 : sC10.Rep PositiveTD.Certificate.C10 := r46_rep_red (((rC4.sub ((Scaled.rep_const _).mul (Scaled.rep_var.pow 6))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 8))).sub
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 10)))
private def sC12 : Scaled := r46_red (sC10.add ((Scaled.const (1/479001600)).mul (Scaled.var.pow 12)))
private theorem rC12 : sC12.Rep PositiveTD.Certificate.C12 := r46_rep_red (rC10.add ((Scaled.rep_const _).mul (Scaled.rep_var.pow 12)))

private def sNum4 (A P0 P1 P2 P3 r0 r1 r2 r3 : Scaled) : Scaled :=
  (r46_red (((((Scaled.const 2).mul A).mul r0).mul r1).mul r2 |>.mul r3)).sub
    ((Scaled.const PositiveTD.Certificate.Rbar).mul
      (r46_red ((r46_red ((r46_red ((r46_red ((((P0.add (r0.pow 2)).mul r1).mul r2).mul r3)).add
        (r46_red ((((P1.add (r1.pow 2)).mul r0).mul r2).mul r3)))).add
        (r46_red ((((P2.add (r2.pow 2)).mul r0).mul r1).mul r3)))).add
        (r46_red ((((P3.add (r3.pow 2)).mul r0).mul r1).mul r2)))))
private theorem rNum4 {A P0 P1 P2 P3 r0 r1 r2 r3 : Scaled} {a p0 p1 p2 p3 q0 q1 q2 q3 : ℚ[X]}
    (hA : A.Rep a) (h0 : P0.Rep p0) (h1 : P1.Rep p1) (h2 : P2.Rep p2) (h3 : P3.Rep p3)
    (g0 : r0.Rep q0) (g1 : r1.Rep q1) (g2 : r2.Rep q2) (g3 : r3.Rep q3) :
    (sNum4 A P0 P1 P2 P3 r0 r1 r2 r3).Rep
      (PositiveTD.Certificate.num4 a p0 p1 p2 p3 q0 q1 q2 q3) :=
  (r46_rep_red ((((((Scaled.rep_const _).mul hA).mul g0).mul g1).mul g2).mul g3)).sub
    ((Scaled.rep_const _).mul
      (r46_rep_red ((r46_rep_red ((r46_rep_red ((r46_rep_red ((((h0.add (g0.pow 2)).mul g1).mul g2).mul g3)).add
        (r46_rep_red ((((h1.add (g1.pow 2)).mul g0).mul g2).mul g3)))).add
        (r46_rep_red ((((h2.add (g2.pow 2)).mul g0).mul g1).mul g3)))).add
        (r46_rep_red ((((h3.add (g3.pow 2)).mul g0).mul g1).mul g2)))))

private def sT : Scaled := Scaled.var.sub (Scaled.const L)
private theorem rT : sT.Rep t := Scaled.rep_var.sub (Scaled.rep_const _)
private def sHK : Scaled := r46_red ((((Scaled.const (1673/2500)).add ((Scaled.const (2609/5000)).mul sT)).sub
  ((Scaled.const (1489/2500)).mul (sT.pow 2))).add ((Scaled.const (527/1250)).mul (sT.pow 3)))
private theorem rHK : sHK.Rep highK := r46_rep_red ((((Scaled.rep_const _).add ((Scaled.rep_const _).mul rT)).sub
    ((Scaled.rep_const _).mul (rT.pow 2))).add ((Scaled.rep_const _).mul (rT.pow 3)))
private def sHL : Scaled := r46_red ((((Scaled.ofNat 1).add ((Scaled.const (7/400)).mul sT)).sub
  ((Scaled.const (2733/2500)).mul (sT.pow 2))).add ((Scaled.const (639/500)).mul (sT.pow 3)))
private theorem rHL : sHL.Rep highL := r46_rep_red (((Scaled.rep_one.add ((Scaled.rep_const _).mul rT)).sub
    ((Scaled.rep_const _).mul (rT.pow 2))).add ((Scaled.rep_const _).mul (rT.pow 3)))
private def sHC : Scaled := r46_red ((((Scaled.const (10163/10000)).sub ((Scaled.const (209/10000)).mul sT)).sub
  ((Scaled.const (5743/5000)).mul (sT.pow 2))).add ((Scaled.const (14069/10000)).mul (sT.pow 3)))
private theorem rHC : sHC.Rep highC := r46_rep_red ((((Scaled.rep_const _).sub ((Scaled.rep_const _).mul rT)).sub
    ((Scaled.rep_const _).mul (rT.pow 2))).add ((Scaled.rep_const _).mul (rT.pow 3)))
private def sHJ : Scaled := r46_red ((((Scaled.const (1/2)).mul (sC10.sub (Scaled.ofNat 1))).add
  ((Scaled.const (1/2-abar)).mul sS9)).sub ((Scaled.const (43/500)).mul (sT.pow 4)))
private theorem rHJ : sHJ.Rep highJ := r46_rep_red ((((Scaled.rep_const _).mul (rC10.sub Scaled.rep_one)).add
    ((Scaled.rep_const _).mul rS9)).sub ((Scaled.rep_const _).mul (rT.pow 4)))

private def sMinus : Scaled := r46_red (sHC.mul (sC10.add ((Scaled.const PositiveTD.Certificate.etaQ).mul sS11)))
private theorem rMinus : sMinus.Rep (PositiveTD.Certificate.mMinus highC) := r46_rep_red (rHC.mul (rC10.add ((Scaled.rep_const _).mul rS11)))
private def sPlus : Scaled := r46_red (sHC.mul (sC12.add ((Scaled.const PositiveTD.Certificate.etaQ).mul sS9)))
private theorem rPlus : sPlus.Rep (PositiveTD.Certificate.mPlus highC) := r46_rep_red (rHC.mul (rC12.add ((Scaled.rep_const _).mul rS9)))
private def sMMinus : Endpoint → Scaled
  | .atT => r46_red (sMinus)
  | .atA => r46_red (sHC)
private theorem rMMinus (e : Endpoint) : (sMMinus e).Rep (highMMinus e) := by
  cases e
  · exact r46_rep_red (rMinus)
  · exact r46_rep_red (rHC)
private def sMPlus : Endpoint → Scaled
  | .atT => r46_red (sPlus)
  | .atA => r46_red (sHC)
private theorem rMPlus (e : Endpoint) : (sMPlus e).Rep (highMPlus e) := by
  cases e
  · exact r46_rep_red (rPlus)
  · exact r46_rep_red (rHC)
private def sMu : Endpoint → Scaled
  | .atT => r46_red (sHC.mul (sC4.add ((Scaled.const PositiveTD.Certificate.etaQ).mul sS5)))
  | .atA => r46_red (sHC)
private theorem rMu (e : Endpoint) : (sMu e).Rep (highMu e) := by
  cases e
  · exact r46_rep_red (rHC.mul (rC4.add ((Scaled.rep_const _).mul rS5)))
  · exact r46_rep_red (rHC)
private def sHA : Endpoint → Scaled
  | .atT => r46_red (((((((((Scaled.const 2).mul sHK).add ((Scaled.const 3).mul sHL)).add
      ((Scaled.const (3/2)).mul (sMMinus .atT))).add ((Scaled.const (1/2)).mul sHC)).add
      (Scaled.const 3)).add (((Scaled.const (1/2)).mul sHC).mul
        (((Scaled.ofNat 1).add sC10).add sS11))).sub
      ((sHC.mul (Scaled.const PositiveTD.Certificate.sigmabar)).mul sS9)))
  | .atA => r46_red ((((((Scaled.const 2).mul sHK).add ((Scaled.const 3).mul sHL)).add
      ((Scaled.const 3).mul sHC)).add (Scaled.const 3)).add (sHL.mul sHJ))
private theorem rHA (e : Endpoint) : (sHA e).Rep (highA e) := by
  cases e
  · exact r46_rep_red (((((((((Scaled.rep_const _).mul rHK).add ((Scaled.rep_const _).mul rHL)).add
      ((Scaled.rep_const _).mul (rMMinus .atT))).add ((Scaled.rep_const _).mul rHC)).add
      (Scaled.rep_const _)).add (((Scaled.rep_const _).mul rHC).mul
        ((Scaled.rep_one.add rC10).add rS11))).sub
      ((rHC.mul (Scaled.rep_const _)).mul rS9)))
  · exact r46_rep_red ((((((Scaled.rep_const _).mul rHK).add ((Scaled.rep_const _).mul rHL)).add
      ((Scaled.rep_const _).mul rHC)).add (Scaled.rep_const _)).add (rHL.mul rHJ))

private def sPH : Scaled := r46_red ((Scaled.ofNat 1).add (sHK.pow 2))
private theorem rPH : sPH.Rep highPH := r46_rep_red (Scaled.rep_one.add (rHK.pow 2))
private def sPG : Scaled := r46_red ((sHK.pow 2).add (sHL.pow 2))
private theorem rPG : sPG.Rep highPG := r46_rep_red ((rHK.pow 2).add (rHL.pow 2))
private def sPD : Scaled := r46_red ((Scaled.ofNat 1).add (sHC.pow 2))
private theorem rPD : sPD.Rep highPD := r46_rep_red (Scaled.rep_one.add (rHC.pow 2))
private def sPB (e : Endpoint) : Scaled := r46_red (((sMPlus e).pow 2).add (sHL.pow 2))
private theorem rPB (e : Endpoint) : (sPB e).Rep (highPB e) := r46_rep_red (((rMPlus e).pow 2).add (rHL.pow 2))
private def sPHm : Scaled := r46_red (sPH.sub (((Scaled.const 2).mul sHK).mul sS11))
private theorem rPHm : sPHm.Rep highPHminus := r46_rep_red (rPH.sub (((Scaled.rep_const _).mul rHK).mul rS11))
private def sPGm : Scaled := r46_red (sPG.sub ((((Scaled.const 2).mul sHK).mul sHL).mul sS11))
private theorem rPGm : sPGm.Rep highPGminus := r46_rep_red (rPG.sub ((((Scaled.rep_const _).mul rHK).mul rHL).mul rS11))
private def sPBm (e : Endpoint) : Scaled := r46_red (
  (sPB e).sub ((((Scaled.const 2).mul sHL).mul (sMMinus e)).mul sS11))
private theorem rPBm (e : Endpoint) : (sPBm e).Rep (highPBminus e) := r46_rep_red ((rPB e).sub ((((Scaled.rep_const _).mul rHL).mul (rMMinus e)).mul rS11))
private def sRH : Scaled := r46_red ((Scaled.const (4/5)).add ((Scaled.const (3/5)).mul sHK))
private theorem rRH : sRH.Rep highRH := r46_rep_red ((Scaled.rep_const _).add ((Scaled.rep_const _).mul rHK))
private def sRG : Scaled := r46_red (((Scaled.const (31/50)).mul sHK).add ((Scaled.const (3923/5000)).mul sHL))
private theorem rRG : sRG.Rep highRG := r46_rep_red (((Scaled.rep_const _).mul rHK).add ((Scaled.rep_const _).mul rHL))
private def sRD : Scaled := r46_red ((Scaled.const (18/25)).add ((Scaled.const (347/500)).mul sHC))
private theorem rRD : sRD.Rep highRD := r46_rep_red ((Scaled.rep_const _).add ((Scaled.rep_const _).mul rHC))
private def sRB (e : Endpoint) : Scaled := r46_red ((Scaled.const (7071/10000)).mul (sHL.add (sMu e)))
private theorem rRB (e : Endpoint) : (sRB e).Rep (highRB e) := r46_rep_red ((Scaled.rep_const _).mul (rHL.add (rMu e)))
private def sRHm : Scaled := r46_red (((Scaled.const (89/100)).mul sC4).add ((Scaled.const (57/125)).mul (sHK.sub sS5)))
private theorem rRHm : sRHm.Rep highRHminus := r46_rep_red (((Scaled.rep_const _).mul rC4).add ((Scaled.rep_const _).mul (rHK.sub rS5)))
private def sRGm : Scaled := r46_red ((((Scaled.const (89/100)).mul sHL).mul sC4).add
  ((Scaled.const (57/125)).mul (sHK.sub (sHL.mul sS5))))
private theorem rRGm : sRGm.Rep highRGminus := r46_rep_red ((((Scaled.rep_const _).mul rHL).mul rC4).add ((Scaled.rep_const _).mul (rHK.sub (rHL.mul rS5))))
private def sRBm (e : Endpoint) : Scaled := r46_red ((((Scaled.const (83/100)).mul sHL).mul sC4).add
  ((Scaled.const (14/25)).mul ((sMu e).sub (sHL.mul sS5))))
private theorem rRBm (e : Endpoint) : (sRBm e).Rep (highRBminus e) := r46_rep_red ((((Scaled.rep_const _).mul rHL).mul rC4).add ((Scaled.rep_const _).mul ((rMu e).sub (rHL.mul rS5))))
private def sQ : Scaled := r46_red (sHL.add ((Scaled.const (3/20)).mul ((Scaled.const h).sub Scaled.var)))
private theorem rQ : sQ.Rep highQ := r46_rep_red (rHL.add ((Scaled.rep_const _).mul ((Scaled.rep_const _).sub Scaled.rep_var)))

private def sNH (e : Endpoint) : Scaled := r46_red (sNum4 (((sHA e).add sC10).sub (Scaled.ofNat 1))
  sPG (sPB e) sPHm sPD sRG (sRB e) sRHm sRD)
private theorem rNH (e : Endpoint) : (sNH e).Rep (highNH e) := r46_rep_red (rNum4 (((rHA e).add rC10).sub Scaled.rep_one) rPG (rPB e) rPHm rPD rRG (rRB e) rRHm rRD)
private def sNG (e : Endpoint) : Scaled := r46_red (sNum4 ((sHA e).add (sHL.mul (sC10.sub (Scaled.ofNat 1))))
  sPH (sPB e) sPGm sPD sRH (sRB e) sRGm sRD)
private theorem rNG (e : Endpoint) : (sNG e).Rep (highNG e) := r46_rep_red (rNum4 ((rHA e).add (rHL.mul (rC10.sub Scaled.rep_one))) rPH (rPB e) rPGm rPD rRH (rRB e) rRGm rRD)
private def sNB (e : Endpoint) : Scaled := r46_red (sNum4 ((sHA e).add (sQ.mul (sC10.sub (Scaled.ofNat 1))))
  sPH sPG (sPBm e) sPD sRH sRG (sRBm e) sRD)
private theorem rNB (e : Endpoint) : (sNB e).Rep (highNB e) := r46_rep_red (rNum4 ((rHA e).add (rQ.mul (rC10.sub Scaled.rep_one))) rPH rPG (rPBm e) rPD rRH rRG (rRBm e) rRD)

/-- The numerators centered on `[1/6,7/10]`: `(1/6+7/10)/2 = 13/30`, `(7/10-1/6)/2 = 8/30`. -/
private def cNH (e : Endpoint) : Scaled := r46_red ((sNH e).center 1 30 13 8)
private theorem rcNH (e : Endpoint) : (cNH e).Rep (centered L h (highNH e)) :=
  r46_rep_red ((rNH e).centered 1 30 13 8 (by norm_num) (by norm_num [L,h]) (by norm_num [L,h]))
private def cNG (e : Endpoint) : Scaled := r46_red ((sNG e).center 1 30 13 8)
private theorem rcNG (e : Endpoint) : (cNG e).Rep (centered L h (highNG e)) :=
  r46_rep_red ((rNG e).centered 1 30 13 8 (by norm_num) (by norm_num [L,h]) (by norm_num [L,h]))
private def cNB (e : Endpoint) : Scaled := r46_red ((sNB e).center 1 30 13 8)
private theorem rcNB (e : Endpoint) : (cNB e).Rep (centered L h (highNB e)) :=
  r46_rep_red ((rNB e).centered 1 30 13 8 (by norm_num) (by norm_num [L,h]) (by norm_num [L,h]))

/-! ## Quotients by the endpoint factors -/

theorem high_HG_identities (e : Endpoint) :
    highNH e=C ((highNH e).eval L)+(X-C L)*highQH e ∧
    highNG e=C ((highNG e).eval L)+(X-C L)*highQG e := by
  have h1 := (mul_divByMonic_eq_iff_isRoot (p:=highNH e-C ((highNH e).eval L)) (a:=L)).2
    (by simp [IsRoot])
  have h2 := (mul_divByMonic_eq_iff_isRoot (p:=highNG e-C ((highNG e).eval L)) (a:=L)).2
    (by simp [IsRoot])
  rw [highQH,highQG]
  exact ⟨by linear_combination -h1,by linear_combination -h2⟩

/-- `X-C L` and `X-C h` on the centered variable of `[1/6,7/10]`. -/
private theorem r46_left_factor :
    (X-C L).comp (affine L h)=C (4/15)*(X-C ((-1:ℤ):ℚ)) := by
  simp only [affine,sub_comp,C_comp,X_comp,L,h,Int.cast_neg,Int.cast_one,map_neg,map_one]
  rw [show ((1:ℚ)/6+7/10)/2=4/15+1/6 by norm_num,show ((7:ℚ)/10-1/6)/2=4/15 by norm_num,map_add]
  ring

private theorem r46_right_factor :
    (X-C h).comp (affine L h)=C (4/15)*(X-C ((1:ℤ):ℚ)) := by
  simp only [affine,sub_comp,C_comp,X_comp,L,h,Int.cast_one,map_one]
  rw [show ((1:ℚ)/6+7/10)/2=7/10-4/15 by norm_num,show ((7:ℚ)/10-1/6)/2=4/15 by norm_num,
    map_sub]
  ring

private theorem r46_high_centered {p q : ℚ[X]} {a : ℚ} {r : ℤ}
    (hfac : (X-C a).comp (affine L h)=C (4/15)*(X-C (r:ℚ)))
    (hpq : p=C (p.eval a)+(X-C a)*q) :
    centered L h p=C (p.eval a)+C (4/15)*(X-C (r:ℚ))*centered L h q := by
  conv_lhs => rw [hpq]
  rw [centered,add_comp,mul_comp,C_comp,hfac]
  rfl

private theorem r46_div_identity (p : ℚ[X]) (a : ℚ) :
    p=C (p.eval a)+(X-C a)*(p.divByMonic (X-C a)) := by
  have h := modByMonic_add_div p (X-C a)
  rw [modByMonic_X_sub_C_eq_C_eval] at h
  exact h.symm

private def cQH (e : Endpoint) : Scaled :=
  r46_red ⟨smul 15 (r46_synth (-1) (cNH e).l).1,(cNH e).s*4⟩
private def cQG (e : Endpoint) : Scaled :=
  r46_red ⟨smul 15 (r46_synth (-1) (cNG e).l).1,(cNG e).s*4⟩

/-- All integer facts about the H numerators, checked in one kernel reduction per endpoint. -/
private theorem r46_NH_facts (e : Endpoint) :
    WholeIntervalPolynomial.Certificate.mul [-(-1),1] (r46_synth (-1) (cNH e).l).1=
      WholeIntervalPolynomial.Certificate.add (cNH e).l [-(r46_synth (-1) (cNH e).l).2] ∧
    (cNH e).s≠0 ∧ (1:ℤ)*((cNH e).s:ℤ)<((625:ℕ):ℤ)*r46_evalZ (-1) (cNH e).l ∧
    (cQH e).s≠0 ∧ (cQH e).l.length≤highHDegree e+1 ∧
    (1:ℤ)*(((cQH e).s*2^(cQH e).l.length : ℕ):ℤ)<
      2*((20:ℕ):ℤ)*lowerZ (highHDegree e) (fun j => (chebList (cQH e).l).getD j 0) := by
  cases e <;> decide +kernel

private theorem rcQH (e : Endpoint) : (cQH e).Rep (centered L h (highQH e)) :=
  r46_rep_red (r46_rep_div (rcNH e) (r46_high_centered r46_left_factor (high_HG_identities e).1)
    (r46_NH_facts e).1 (by norm_num))

private theorem r46_left_value {c : Scaled} {p : ℚ[X]} (hc : c.Rep (centered L h p))
    (hs : c.s≠0) {ρ : ℚ} {num : ℤ} {den : ℕ} (hρ : ρ=num/den) (hden : 0<den)
    (hh : num*(c.s:ℤ)<den*r46_evalZ (-1) c.l) : ρ<p.eval L := by
  have hv := r46_value_lt hc hs (-1) hρ hden hh
  rwa [r46_centered_eval,show (L+h)/2+(h-L)/2*((-1:ℤ):ℚ)=L by norm_num [L,h]] at hv

private theorem r46_right_value {c : Scaled} {p : ℚ[X]} (hc : c.Rep (centered L h p))
    (hs : c.s≠0) {ρ : ℚ} {num : ℤ} {den : ℕ} (hρ : ρ=num/den) (hden : 0<den)
    (hh : num*(c.s:ℤ)<den*r46_evalZ 1 c.l) : ρ<p.eval h := by
  have hv := r46_value_lt hc hs 1 hρ hden hh
  rwa [r46_centered_eval,show (L+h)/2+(h-L)/2*((1:ℤ):ℚ)=h by norm_num [L,h]] at hv

/-- All integer facts about the G numerators. -/
private theorem r46_NG_facts (e : Endpoint) :
    WholeIntervalPolynomial.Certificate.mul [-(-1),1] (r46_synth (-1) (cNG e).l).1=
      WholeIntervalPolynomial.Certificate.add (cNG e).l [-(r46_synth (-1) (cNG e).l).2] ∧
    (cNG e).s≠0 ∧ (17:ℤ)*((cNG e).s:ℤ)<((10000:ℕ):ℤ)*r46_evalZ (-1) (cNG e).l ∧
    (cQG e).s≠0 := by
  cases e <;> decide +kernel

private theorem rcQG (e : Endpoint) : (cQG e).Rep (centered L h (highQG e)) :=
  r46_rep_red (r46_rep_div (rcNG e) (r46_high_centered r46_left_factor (high_HG_identities e).2)
    (r46_NG_facts e).1 (by norm_num))

/-- The quadratic and cubic reserve facts of the two G quotients. -/
private theorem r46_TG_facts :
    (cQG .atT).l.length≤43+1 ∧ 0<(chebList (cQG .atT).l).getD 2 0 ∧
    (69:ℤ)*(8*(chebList (cQG .atT).l).getD 2 0*(((cQG .atT).s*2^(cQG .atT).l.length : ℕ):ℤ))<
      2*((10000:ℕ):ℤ)*(8*(chebList (cQG .atT).l).getD 2 0*((chebList (cQG .atT).l).getD 0 0-
        (chebList (cQG .atT).l).getD 2 0-
        ∑ j : Fin 41,|(chebList (cQG .atT).l).getD (j.val+3) 0|)-
        ((chebList (cQG .atT).l).getD 1 0)^2) := by
  decide +kernel

private theorem r46_AG_facts :
    (cQG .atA).l.length≤29+1 ∧
    0<2*(chebList (cQG .atA).l).getD 2 0-4*|(chebList (cQG .atA).l).getD 3 0| ∧
    (29:ℤ)*(4*(2*(chebList (cQG .atA).l).getD 2 0-4*|(chebList (cQG .atA).l).getD 3 0|)*
        (((cQG .atA).s*2^(cQG .atA).l.length : ℕ):ℤ))<
      2*((2500:ℕ):ℤ)*(4*(2*(chebList (cQG .atA).l).getD 2 0-
        4*|(chebList (cQG .atA).l).getD 3 0|)*
        ((chebList (cQG .atA).l).getD 0 0-(chebList (cQG .atA).l).getD 2 0-
          ∑ j : Fin 26,|(chebList (cQG .atA).l).getD (j.val+4) 0|)-
        ((chebList (cQG .atA).l).getD 1 0-3*(chebList (cQG .atA).l).getD 3 0)^2) := by
  decide +kernel

theorem high_HG_left_reserves (e : Endpoint) :
    (1/625:ℚ)<(highNH e).eval L ∧ (17/10000:ℚ)<(highNG e).eval L :=
  ⟨r46_left_value (rcNH e) (r46_NH_facts e).2.1 (by norm_num) (by norm_num) (r46_NH_facts e).2.2.1,
    r46_left_value (rcNG e) (r46_NG_facts e).2.1 (by norm_num) (by norm_num)
      (r46_NG_facts e).2.2.1⟩

theorem high_H_expansion (e : Endpoint) :
    centered L h (highQH e)=expansion (highHDegree e) (centered L h (highQH e)) :=
  (rcQH e).eq_expansion (r46_NH_facts e).2.2.2.1 (r46_NH_facts e).2.2.2.2.1

theorem high_H_quotient_reserve (e : Endpoint) :
    (1/20:ℚ)<lowerOn (highHDegree e) L h (highQH e) :=
  r46_lowerOn_lt (rcQH e) (r46_NH_facts e).2.2.2.1 (r46_NH_facts e).2.2.2.2.1 (by norm_num)
    (by norm_num) (r46_NH_facts e).2.2.2.2.2

private theorem r46_Icc_cast {z : ℝ} (hz : z∈Icc (1/6:ℝ) (7/10:ℝ)) :
    z∈Icc ((L:ℚ):ℝ) ((h:ℚ):ℝ) := by
  simp only [L,h,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat]
  exact hz

theorem highNH_positive (e : Endpoint) {z : ℝ} (hz : z∈Icc (1/6:ℝ) (7/10:ℝ)) :
    0<aeval z (highNH e) := by
  have hq := positive_on_interval (by norm_num [L,h] : L<h)
    (high_H_expansion e) (high_H_quotient_reserve e) (r46_Icc_cast hz)
  have hleft : ((1/625:ℚ):ℝ)<(((highNH e).eval L:ℚ):ℝ) :=
    Rat.cast_lt.mpr (high_HG_left_reserves e).1
  rw [show ((1/625:ℚ):ℝ)=1/625 by norm_num] at hleft
  have he := congrArg (fun f : ℚ[X] => aeval z f) (high_HG_identities e).1
  simp only [map_add,map_mul,map_sub,aeval_C,aeval_X,eq_ratCast] at he
  have hprod : 0≤(z-(L:ℝ))*aeval z (highQH e) :=
    mul_nonneg (by simp only [L]; push_cast; linarith [hz.1]) (by push_cast at hq; linarith)
  linarith

theorem high_TG_identity :
    centered L h (highQG .atT)=C (highTGCoefficients 0-highTGCoefficients 2)+
      C (highTGCoefficients 1)*X+C (2*highTGCoefficients 2)*X^2+
        ChebyshevLeadingBounds.tail highTGCoefficients 3 41 := by
  rw [(rcQG .atT).eq_expansion (D:=43) (r46_NG_facts .atT).2.2.2 r46_TG_facts.1]
  exact r46_series_quadratic highTGCoefficients 41

theorem high_TG_reserve : 0<highTGCoefficients 2 ∧
    (69/10000:ℚ)<ChebyshevLeadingBounds.quadraticReserve highTGCoefficients 41 :=
  r46_quadratic (rcQG .atT) (D:=43) (r46_NG_facts .atT).2.2.2 r46_TG_facts.1 41
    (by norm_num) (by norm_num) r46_TG_facts.2.1 r46_TG_facts.2.2

theorem high_AG_identity :
    centered L h (highQG .atA)=C (highAGCoefficients 0-highAGCoefficients 2)+
      C (highAGCoefficients 1-3*highAGCoefficients 3)*X+
      C (2*highAGCoefficients 2)*X^2+C (4*highAGCoefficients 3)*X^3+
        ChebyshevLeadingBounds.tail highAGCoefficients 4 26 := by
  rw [(rcQG .atA).eq_expansion (D:=29) (r46_NG_facts .atA).2.2.2 r46_AG_facts.1]
  exact r46_series_cubic highAGCoefficients 26

theorem high_AG_reserve : 0<2*highAGCoefficients 2-4*|highAGCoefficients 3| ∧
    (29/2500:ℚ)<ChebyshevLeadingBounds.cubicReserve highAGCoefficients 26 :=
  r46_cubic (rcQG .atA) (D:=29) (r46_NG_facts .atA).2.2.2 r46_AG_facts.1 26
    (by norm_num) (by norm_num) r46_AG_facts.2.1 r46_AG_facts.2.2

theorem highQG_positive (e : Endpoint) {z : ℝ} (hz : z∈Icc (1/6:ℝ) (7/10:ℝ)) :
    0<aeval z (highQG e) := by
  cases e
  · have hh := ChebyshevLeadingBounds.quadratic_on_interval
      (by norm_num [L,h] : L<h) high_TG_identity high_TG_reserve.1 (r46_Icc_cast hz)
    have hr : ((69/10000:ℚ):ℝ)<
        (ChebyshevLeadingBounds.quadraticReserve highTGCoefficients 41:ℝ) :=
      Rat.cast_lt.mpr high_TG_reserve.2
    rw [show ((69/10000:ℚ):ℝ)=69/10000 by norm_num] at hr
    linarith
  · have hh := ChebyshevLeadingBounds.cubic_on_interval
      (by norm_num [L,h] : L<h) high_AG_identity high_AG_reserve.1 (r46_Icc_cast hz)
    have hr : ((29/2500:ℚ):ℝ)<
        (ChebyshevLeadingBounds.cubicReserve highAGCoefficients 26:ℝ) :=
      Rat.cast_lt.mpr high_AG_reserve.2
    rw [show ((29/2500:ℚ):ℝ)=29/2500 by norm_num] at hr
    linarith

theorem highNG_positive (e : Endpoint) {z : ℝ} (hz : z∈Icc (1/6:ℝ) (7/10:ℝ)) :
    0<aeval z (highNG e) := by
  have hq := highQG_positive e hz
  have hleft : ((17/10000:ℚ):ℝ)<(((highNG e).eval L:ℚ):ℝ) :=
    Rat.cast_lt.mpr (high_HG_left_reserves e).2
  rw [show ((17/10000:ℚ):ℝ)=17/10000 by norm_num] at hleft
  have he := congrArg (fun f : ℚ[X] => aeval z f) (high_HG_identities e).2
  simp only [map_add,map_mul,map_sub,aeval_C,aeval_X,eq_ratCast] at he
  have hprod : 0≤(z-(L:ℝ))*aeval z (highQG e) :=
    mul_nonneg (by simp only [L]; push_cast; linarith [hz.1]) hq.le
  linarith

/-! ## The B numerators: chord, double quotient and its slope -/

private def sVL (e : Endpoint) : Scaled := ⟨[r46_evalZ (-1) (cNB e).l],(cNB e).s⟩
private def sVh (e : Endpoint) : Scaled := ⟨[r46_evalZ 1 (cNB e).l],(cNB e).s⟩
private def sChord (e : Endpoint) : Scaled :=
  (((Scaled.const (1/(h-L))).mul ((Scaled.const h).sub Scaled.var)).mul (sVL e)).add
    (((Scaled.const (1/(h-L))).mul (Scaled.var.sub (Scaled.const L))).mul (sVh e))
private def sDiff (e : Endpoint) : Scaled := r46_red ((sNB e).sub (sChord e))
private def cDiff (e : Endpoint) : Scaled := r46_red ((sDiff e).center 1 30 13 8)
private def cA1 (e : Endpoint) : Scaled :=
  r46_red ⟨smul 15 (r46_synth (-1) (cDiff e).l).1,(cDiff e).s*4⟩
private def cA2 (e : Endpoint) : Scaled :=
  r46_red ⟨smul 15 (r46_synth 1 (cA1 e).l).1,(cA1 e).s*4⟩
private def cQB (e : Endpoint) : Scaled := (cA2 e).neg
private def cSh (e : Endpoint) : Scaled := r46_red ((cA2 e).center 15 4 0 1)
private def cSl (e : Endpoint) : Scaled := ⟨r46_deriv (cSh e).l,(cSh e).s⟩

/-- All integer facts about the B numerators. -/
private theorem r46_NB_facts (e : Endpoint) :
    (cNB e).s≠0 ∧
    (3:ℤ)*((cNB e).s:ℤ)<((100:ℕ):ℤ)*r46_evalZ (-1) (cNB e).l ∧
    (3:ℤ)*((cNB e).s:ℤ)<((100:ℕ):ℤ)*r46_evalZ 1 (cNB e).l ∧
    WholeIntervalPolynomial.Certificate.mul [-(-1),1] (r46_synth (-1) (cDiff e).l).1=
      WholeIntervalPolynomial.Certificate.add (cDiff e).l [-(r46_synth (-1) (cDiff e).l).2] ∧
    WholeIntervalPolynomial.Certificate.mul [-1,1] (r46_synth 1 (cA1 e).l).1=
      WholeIntervalPolynomial.Certificate.add (cA1 e).l [-(r46_synth 1 (cA1 e).l).2] ∧
    (cQB e).s≠0 ∧ (3:ℤ)*((cQB e).s:ℤ)<((40:ℕ):ℤ)*r46_evalZ 1 (cQB e).l ∧
    (cSl e).s≠0 ∧ (cSl e).l.length-1≤40 ∧
    (2:ℤ)*(((cSl e).s*15^40 : ℕ):ℤ)<((5:ℕ):ℤ)*((cSl e).l.getD 0 0*((15:ℕ):ℤ)^40-
      ∑ j : Fin 40,|(cSl e).l.getD (j.val+1) 0| * ((4:ℕ):ℤ)^(j.val+1)*((15:ℕ):ℤ)^(40-1-j.val)) := by
  cases e <;> decide +kernel

private theorem r46_NB_value (e : Endpoint) (r : ℤ) :
    (centered L h (highNB e)).eval (r:ℚ)=(r46_evalZ r (cNB e).l:ℚ)/(cNB e).s :=
  r46_value (rcNB e) (r46_NB_facts e).1 r

private theorem rChord (e : Endpoint) : (sChord e).Rep (highChord e) := by
  have hL : (highNB e).eval L=(r46_evalZ (-1) (cNB e).l:ℚ)/(cNB e).s := by
    rw [← r46_NB_value,r46_centered_eval]
    congr 1
    norm_num [L,h]
  have hh : (highNB e).eval h=(r46_evalZ 1 (cNB e).l:ℚ)/(cNB e).s := by
    rw [← r46_NB_value,r46_centered_eval]
    congr 1
    norm_num [L,h]
  exact (((Scaled.rep_const _).mul ((Scaled.rep_const _).sub Scaled.rep_var)).mul
      (r46_rep_frac (r46_NB_facts e).1 hL)).add
    (((Scaled.rep_const _).mul (Scaled.rep_var.sub (Scaled.rep_const _))).mul
      (r46_rep_frac (r46_NB_facts e).1 hh))

private theorem rcDiff (e : Endpoint) : (cDiff e).Rep (centered L h (highNB e-highChord e)) :=
  r46_rep_red ((r46_rep_red ((rNB e).sub (rChord e))).centered 1 30 13 8 (by norm_num)
    (by norm_num [L,h]) (by norm_num [L,h]))

private theorem rcA1 (e : Endpoint) :
    (cA1 e).Rep (centered L h ((highNB e-highChord e).divByMonic (X-C L))) :=
  r46_rep_red (r46_rep_div (rcDiff e) (r46_high_centered r46_left_factor (r46_div_identity _ L))
    (r46_NB_facts e).2.2.2.1 (by norm_num))

private theorem rcA2 (e : Endpoint) :
    (cA2 e).Rep (centered L h (((highNB e-highChord e).divByMonic (X-C L)).divByMonic (X-C h))) :=
  r46_rep_red (r46_rep_div (rcA1 e) (r46_high_centered r46_right_factor (r46_div_identity _ h))
    (r46_NB_facts e).2.2.2.2.1 (by norm_num))

private theorem rcQB (e : Endpoint) : (cQB e).Rep (centered L h (highQB e)) := by
  have he : centered L h (highQB e)=
      -centered L h (((highNB e-highChord e).divByMonic (X-C L)).divByMonic (X-C h)) := by
    rw [highQB,centered,centered,neg_comp]
  rw [he]
  exact (rcA2 e).neg

private theorem r46_slope_eq (e : Endpoint) :
    highBNegSlope e=derivative (centered (-15/4) (15/4)
      (centered L h (((highNB e-highChord e).divByMonic (X-C L)).divByMonic (X-C h)))) := by
  have haff : (affine L h).comp (affine (-15/4) (15/4))=C (13/30)+X := by
    simp only [affine,add_comp,mul_comp,C_comp,X_comp,L,h]
    rw [show ((-15:ℚ)/4+15/4)/2=0 by norm_num,show ((15:ℚ)/4- -15/4)/2=15/4 by norm_num,
      show ((1:ℚ)/6+7/10)/2=13/30 by norm_num,show ((7:ℚ)/10-1/6)/2=4/15 by norm_num,
      map_zero,zero_add,← mul_assoc,← map_mul,show (4:ℚ)/15*(15/4)=1 by norm_num,map_one,one_mul]
  rw [highBNegSlope,DirectedPowerBounds.shift,highQB,centered,centered,comp_assoc,haff,
    derivative_comp,derivative_neg,neg_neg]
  simp only [derivative_add,derivative_C,derivative_X,zero_add,one_mul]

private theorem rcSl (e : Endpoint) : (cSl e).Rep (highBNegSlope e) := by
  rw [r46_slope_eq]
  exact r46_rep_deriv (r46_rep_red ((rcA2 e).centered 15 4 0 1 (by norm_num) (by norm_num)
    (by norm_num)))

theorem high_B_chord_identity (e : Endpoint) :
    highNB e=highChord e+(X-C L)*(C h-X)*highQB e := by
  have hhL : (h:ℚ)-L≠0 := by norm_num [h,L]
  have hL : (highNB e-highChord e).eval L=0 := by
    simp only [highChord,eval_sub,eval_add,eval_mul,eval_C,eval_X,sub_self,mul_zero]
    field_simp
    ring
  have h1 := r46_div_identity (highNB e-highChord e) L
  rw [hL,map_zero,zero_add] at h1
  have hA : ((highNB e-highChord e).divByMonic (X-C L)).eval h=0 := by
    have hev := congrArg (eval h) h1
    have hc : (highChord e).eval h=(highNB e).eval h := by
      simp only [highChord,eval_add,eval_mul,eval_C,eval_sub,eval_X,sub_self,mul_zero,zero_mul,
        zero_add]
      field_simp
    rw [eval_sub,hc,sub_self,eval_mul,eval_sub,eval_X,eval_C] at hev
    rcases mul_eq_zero.mp hev.symm with h0 | h0
    · exact absurd h0 hhL
    · exact h0
  have h2 := r46_div_identity ((highNB e-highChord e).divByMonic (X-C L)) h
  rw [hA,map_zero,zero_add] at h2
  rw [highQB]
  linear_combination h1+(X-C L)*h2

theorem high_B_slope_identity (e : Endpoint) :
    highBNegSlope e=C ((highBNegSlope e).coeff 0)+
      PowerTailBounds.tail (highBNegSlope e) 1 40 :=
  r46_eq_tail (((rcSl e).natDegree_le (r46_NB_facts e).2.2.2.2.2.2.2.1).trans
    (r46_NB_facts e).2.2.2.2.2.2.2.2.1)

theorem high_B_slope_reserve (e : Endpoint) :
    (2/5:ℚ)<(highBNegSlope e).coeff 0-
      PowerTailBounds.norm (highBNegSlope e) 1 40 (4/15) :=
  r46_power (rcSl e) (r46_NB_facts e).2.2.2.2.2.2.2.1 40 (rn:=4) (rd:=15) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (r46_NB_facts e).2.2.2.2.2.2.2.2.2

theorem high_B_endpoint_reserves (e : Endpoint) :
    (3/100:ℚ)<(highNB e).eval L ∧ (3/100:ℚ)<(highNB e).eval h ∧
      (3/40:ℚ)<(highQB e).eval h :=
  ⟨r46_left_value (rcNB e) (r46_NB_facts e).1 (by norm_num) (by norm_num) (r46_NB_facts e).2.1,
    r46_right_value (rcNB e) (r46_NB_facts e).1 (by norm_num) (by norm_num) (r46_NB_facts e).2.2.1,
    r46_right_value (rcQB e) (r46_NB_facts e).2.2.2.2.2.1 (by norm_num) (by norm_num)
      (r46_NB_facts e).2.2.2.2.2.2.1⟩

theorem highQB_derivative_negative (e : Endpoint) {z : ℝ}
    (hz : z∈Icc (1/6:ℝ) (7/10:ℝ)) : aeval z (highQB e).derivative<0 := by
  have hx : |z-13/30|≤((4/15:ℚ):ℝ) := by
    rw [abs_le]
    push_cast
    exact ⟨by linarith [hz.1],by linarith [hz.2]⟩
  have hh := DirectedPowerBounds.constant_lower (high_B_slope_identity e) hx
  have hr : ((2/5:ℚ):ℝ)<(((highBNegSlope e).coeff 0-
      PowerTailBounds.norm (highBNegSlope e) 1 40 (4/15):ℚ):ℝ) :=
    Rat.cast_lt.mpr (high_B_slope_reserve e)
  rw [show ((2/5:ℚ):ℝ)=2/5 by norm_num,Rat.cast_sub] at hr
  have he : aeval (z-13/30) (highBNegSlope e)= -aeval z (highQB e).derivative := by
    simp only [highBNegSlope,DirectedPowerBounds.shift_eval,map_neg]
    push_cast
    ring_nf
  rw [he] at hh
  linarith

private theorem r46_aeval_rat (p : ℚ[X]) (q : ℚ) : aeval (q:ℝ) p=((p.eval q:ℚ):ℝ) := by
  rw [← eq_ratCast (algebraMap ℚ ℝ),← eq_ratCast (algebraMap ℚ ℝ),
    aeval_algebraMap_apply_eq_algebraMap_eval]

theorem highQB_positive (e : Endpoint) {z : ℝ} (hz : z∈Icc (1/6:ℝ) (7/10:ℝ)) :
    0<aeval z (highQB e) := by
  have hm : AntitoneOn (fun z : ℝ => aeval z (highQB e)) (Icc (1/6) (7/10)) := by
    apply antiOn_of_hasDeriv_nonpos
    · intro z _
      exact (CenteredMonomialBounds.aeval_hasDerivAt (highQB e) z).continuousAt.continuousWithinAt
    · exact fun z _ => CenteredMonomialBounds.aeval_hasDerivAt (highQB e) z
    · exact fun z hz => (highQB_derivative_negative e (Ioo_subset_Icc_self hz)).le
  have hh := hm hz (by norm_num) hz.2
  have hr : ((3/40:ℚ):ℝ)<(((highQB e).eval h:ℚ):ℝ) :=
    Rat.cast_lt.mpr (high_B_endpoint_reserves e).2.2
  rw [← r46_aeval_rat,show ((3/40:ℚ):ℝ)=3/40 by norm_num,
    show ((h:ℚ):ℝ)=7/10 by norm_num [h]] at hr
  simp only at hh
  linarith

theorem highNB_positive (e : Endpoint) {z : ℝ} (hz : z∈Icc (1/6:ℝ) (7/10:ℝ)) :
    0<aeval z (highNB e) := by
  have hq := highQB_positive e hz
  have hleft : ((3/100:ℚ):ℝ)<(((highNB e).eval L:ℚ):ℝ) :=
    Rat.cast_lt.mpr (high_B_endpoint_reserves e).1
  have hright : ((3/100:ℚ):ℝ)<(((highNB e).eval h:ℚ):ℝ) :=
    Rat.cast_lt.mpr (high_B_endpoint_reserves e).2.1
  rw [show ((3/100:ℚ):ℝ)=3/100 by norm_num] at hleft hright
  have hchord : aeval z (highChord e)=(15/8)*(7/10-z)*(((highNB e).eval L:ℚ):ℝ)+
      (15/8)*(z-1/6)*(((highNB e).eval h:ℚ):ℝ) := by
    simp only [highChord,map_add,map_mul,map_sub,aeval_C,aeval_X,eq_ratCast]
    rw [show (((1/(h-L)):ℚ):ℝ)=15/8 by norm_num [h,L],show ((h:ℚ):ℝ)=7/10 by norm_num [h],
      show ((L:ℚ):ℝ)=1/6 by norm_num [L]]
  have h1 := mul_le_mul_of_nonneg_left hleft.le (show (0:ℝ)≤(15/8)*(7/10-z) by
    nlinarith [hz.2])
  have h2 := mul_le_mul_of_nonneg_left hright.le (show (0:ℝ)≤(15/8)*(z-1/6) by
    nlinarith [hz.1])
  have hp : 0≤(z-1/6)*(7/10-z)*aeval z (highQB e) :=
    mul_nonneg (mul_nonneg (by linarith [hz.1]) (by linarith [hz.2])) hq.le
  have he := congrArg (fun f : ℚ[X] => aeval z f) (high_B_chord_identity e)
  simp only [map_add,map_mul,map_sub,aeval_C,aeval_X,eq_ratCast] at he
  rw [show ((h:ℚ):ℝ)=7/10 by norm_num [h],show ((L:ℚ):ℝ)=1/6 by norm_num [L]] at he
  nlinarith [he,hchord,h1,h2,hp]

end SquaresInCircles.Eight.GlobalGA.TwoPositive.Certificate
end
end
end

section
/-!
## The explicit high split family stays in its analytic domain

Endpoint quotients retain the monotonic directions of the cubic
weights.  The A/T auxiliary masses have a common positive lower
bound.  The B coefficient cap is proved on the whole interval by
one completed square, including its interior minimum.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalGA.TwoPositive.Certificate

open Polynomial WholeIntervalPolynomial
open PositiveTD.Certificate (L h)

def kRight : ℚ[X] := (highK-C (highK.eval h)).divByMonic (X-C h)
def lRight : ℚ[X] := -((highL-C (highL.eval h)).divByMonic (X-C h))
def cLeft : ℚ[X] := -((highC-C (highC.eval L)).divByMonic (X-C L))
def cRight : ℚ[X] := -((highC-C (highC.eval h)).divByMonic (X-C h))
def rangePoly : Fin 7→ℚ[X] :=
  ![highK,kRight,lRight,cLeft,cRight,highC-C (9/10)*highL,C (11/10)*highL-highC]
def rangeReserve : Fin 7→ℚ := ![669/1000,1/10,1/100,1/100,1/100,2/25,2/25]
def mass (e : Endpoint) : Fin 7→ℚ[X] :=
  ![highRH,highRG,highRD,highRB e,highRHminus,highRGminus,highRBminus e]
def gapCentered : ℚ[X] := DirectedPowerBounds.shift (13/30) highQGap
def gapCurvature : ℚ := gapCentered.coeff 2-PowerTailBounds.norm gapCentered 3 6 (4/15)
def gapReserve : ℚ := gapCentered.coeff 0-(gapCentered.coeff 1)^2/(4*gapCurvature)


/-! ## Certificate helpers -/

section r47
open WholeIntervalPolynomial.Certificate
open PositiveTD.Certificate (C4 S5)

private def r47_k (n : ℤ) (d : ℕ) : Scaled := ⟨[n],d⟩

private theorem r47_rep_frac {q : ℚ} {n : ℤ} {d : ℕ} (hd : d≠0) (hq : q=n/d) :
    (r47_k n d).Rep (C q) := by
  unfold r47_k Scaled.Rep
  simp only [toPoly,mul_zero,add_zero,← map_mul]
  congr 1
  rw [hq]
  field_simp

private theorem r47_lt_div {ρ : ℚ} {num Z M : ℤ} {den : ℕ} (hρ : ρ=num/den) (hden : 0<den)
    (hM : 0<M) (hlt : num*M<2*den*Z) : ρ<(Z:ℚ)/((M:ℚ)/2) := by
  have hd : (0:ℚ)<den := by exact_mod_cast hden
  have hM' : (0:ℚ)<M := by exact_mod_cast hM
  have hq : ((num*M:ℤ):ℚ)<((2*den*Z:ℤ):ℚ) := by exact_mod_cast hlt
  push_cast at hq
  rw [lt_div_iff₀ (by positivity),hρ,div_mul_eq_mul_div,div_lt_iff₀ hd]
  linarith

/-- Centering on `[L,h]=[1/6,7/10]`: midpoint `13/30`, half-width `8/30`. -/
private theorem r47_center {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) :
    (c.center 1 30 13 8).Rep (centered L h p) :=
  hc.centered 1 30 13 8 (by norm_num) (by norm_num) (by norm_num)

private theorem r47_id {c : Scaled} {p : ℚ[X]} (hc : c.Rep p)
    (hs : (c.center 1 30 13 8).s≠0) {D : ℕ} (hl : (c.center 1 30 13 8).l.length≤D+1) :
    centered L h p=expansion D (centered L h p) :=
  (r47_center hc).eq_expansion hs hl

private theorem r47_low {c : Scaled} {p : ℚ[X]} (hc : c.Rep p)
    (hs : (c.center 1 30 13 8).s≠0) {D : ℕ} (hl : (c.center 1 30 13 8).l.length≤D+1)
    {ρ : ℚ} {num : ℤ} {den : ℕ} (hρ : ρ=num/den) (hden : 0<den)
    (hlt : num*(((c.center 1 30 13 8).s*2^(c.center 1 30 13 8).l.length : ℕ):ℤ)<
      2*den*lowerZ D (fun j => (chebList (c.center 1 30 13 8).l).getD j 0)) :
    ρ<lowerOn D L h p := by
  rw [lowerOn_eq_of_rep (r47_center hc) hs hl]
  have he : ((c.center 1 30 13 8).s:ℚ)*2^(c.center 1 30 13 8).l.length/2=
      ((((c.center 1 30 13 8).s*2^(c.center 1 30 13 8).l.length : ℕ):ℤ):ℚ)/2 := by
    push_cast
    ring
  rw [he]
  exact r47_lt_div hρ hden (by have := Nat.pos_of_ne_zero hs; positivity) hlt

/-- `p - p(a)` is divisible by `X - a`. -/
private theorem r47_root (p : ℚ[X]) (a : ℚ) :
    p=C (p.eval a)+(X-C a)*((p-C (p.eval a)) /ₘ (X-C a)) := by
  rw [(mul_divByMonic_eq_iff_isRoot (p := p-C (p.eval a)) (a := a)).2 (by simp [IsRoot])]
  ring

private def r47_pKR : ℚ[X] := C (149089/375000)-C (6391/12500)*X+C (527/1250)*X^2
private def r47_pLR : ℚ[X] := C (306/3125)+C (1047/1250)*X-C (639/500)*X^2
private def r47_pCL : ℚ[X] := C (48527/30000)*X-C (75461/360000)-C (14069/10000)*X^2
private def r47_pCR : ℚ[X] := C (383537/3000000)+C (43361/50000)*X-C (14069/10000)*X^2

private theorem r47_kRight : kRight=r47_pKR := by
  have hv : highK.eval h=7104683/8437500 := by norm_num [highK,t]
  have hid : highK-C (7104683/8437500)=(X-C h)*r47_pKR := by
    apply Polynomial.funext
    intro r
    simp only [highK,t,r47_pKR,eval_sub,eval_add,eval_mul,eval_C,eval_X,eval_pow,L,h]
    ring
  rw [kRight,hv,hid,mul_divByMonic_cancel_left _ (monic_X_sub_C h)]

private theorem r47_lRight : lRight=r47_pLR := by
  have hv : highL.eval h=27883/31250 := by norm_num [highL,t]
  have hid : highL-C (27883/31250)=(X-C h)*(-r47_pLR) := by
    apply Polynomial.funext
    intro r
    simp only [highL,t,r47_pLR,eval_sub,eval_add,eval_mul,eval_C,eval_X,eval_pow,eval_neg,
      eval_one,L,h]
    ring
  rw [lRight,hv,hid,mul_divByMonic_cancel_left _ (monic_X_sub_C h),neg_neg]

private theorem r47_cLeft : cLeft=r47_pCL := by
  have hv : highC.eval L=10163/10000 := by norm_num [highC,t]
  have hid : highC-C (10163/10000)=(X-C L)*(-r47_pCL) := by
    apply Polynomial.funext
    intro r
    simp only [highC,t,r47_pCL,eval_sub,eval_add,eval_mul,eval_C,eval_X,eval_pow,eval_neg,L]
    ring
  rw [cLeft,hv,hid,mul_divByMonic_cancel_left _ (monic_X_sub_C L),neg_neg]

private theorem r47_cRight : cRight=r47_pCR := by
  have hv : highC.eval h=30100693/33750000 := by norm_num [highC,t]
  have hid : highC-C (30100693/33750000)=(X-C h)*(-r47_pCR) := by
    apply Polynomial.funext
    intro r
    simp only [highC,t,r47_pCR,eval_sub,eval_add,eval_mul,eval_C,eval_X,eval_pow,eval_neg,L,h]
    ring
  rw [cRight,hv,hid,mul_divByMonic_cancel_left _ (monic_X_sub_C h),neg_neg]

private def r47_cT : Scaled :=
  (Scaled.var).sub (r47_k (1) 6)
private theorem r47_rT : r47_cT.Rep t :=
  (Scaled.rep_var).sub (r47_rep_frac (q := 1/6) (n := 1) (d := 6) (by norm_num) (by norm_num))

private def r47_cK : Scaled :=
  (((r47_k (1673) 2500).add ((r47_k (2609) 5000).mul (r47_cT))).sub ((r47_k (1489) 2500).mul ((r47_cT).pow 2))).add ((r47_k (527) 1250).mul ((r47_cT).pow 3))
private theorem r47_rK : r47_cK.Rep highK :=
  (((r47_rep_frac (q := 1673/2500) (n := 1673) (d := 2500) (by norm_num) (by norm_num)).add ((r47_rep_frac (q := 2609/5000) (n := 2609) (d := 5000) (by norm_num) (by norm_num)).mul (r47_rT))).sub ((r47_rep_frac (q := 1489/2500) (n := 1489) (d := 2500) (by norm_num) (by norm_num)).mul ((r47_rT).pow 2))).add ((r47_rep_frac (q := 527/1250) (n := 527) (d := 1250) (by norm_num) (by norm_num)).mul ((r47_rT).pow 3))

private def r47_cL : Scaled :=
  (((Scaled.ofNat 1).add ((r47_k (7) 400).mul (r47_cT))).sub ((r47_k (2733) 2500).mul ((r47_cT).pow 2))).add ((r47_k (639) 500).mul ((r47_cT).pow 3))
private theorem r47_rL : r47_cL.Rep highL :=
  (((Scaled.rep_one).add ((r47_rep_frac (q := 7/400) (n := 7) (d := 400) (by norm_num) (by norm_num)).mul (r47_rT))).sub ((r47_rep_frac (q := 2733/2500) (n := 2733) (d := 2500) (by norm_num) (by norm_num)).mul ((r47_rT).pow 2))).add ((r47_rep_frac (q := 639/500) (n := 639) (d := 500) (by norm_num) (by norm_num)).mul ((r47_rT).pow 3))

private def r47_cC : Scaled :=
  (((r47_k (10163) 10000).sub ((r47_k (209) 10000).mul (r47_cT))).sub ((r47_k (5743) 5000).mul ((r47_cT).pow 2))).add ((r47_k (14069) 10000).mul ((r47_cT).pow 3))
private theorem r47_rC : r47_cC.Rep highC :=
  (((r47_rep_frac (q := 10163/10000) (n := 10163) (d := 10000) (by norm_num) (by norm_num)).sub ((r47_rep_frac (q := 209/10000) (n := 209) (d := 10000) (by norm_num) (by norm_num)).mul (r47_rT))).sub ((r47_rep_frac (q := 5743/5000) (n := 5743) (d := 5000) (by norm_num) (by norm_num)).mul ((r47_rT).pow 2))).add ((r47_rep_frac (q := 14069/10000) (n := 14069) (d := 10000) (by norm_num) (by norm_num)).mul ((r47_rT).pow 3))

private def r47_cC4 : Scaled :=
  ((Scaled.ofNat 1).sub ((r47_k (1) 2).mul ((Scaled.var).pow 2))).add ((r47_k (1) 24).mul ((Scaled.var).pow 4))
private theorem r47_rC4 : r47_cC4.Rep C4 :=
  ((Scaled.rep_one).sub ((r47_rep_frac (q := 1/2) (n := 1) (d := 2) (by norm_num) (by norm_num)).mul ((Scaled.rep_var).pow 2))).add ((r47_rep_frac (q := 1/24) (n := 1) (d := 24) (by norm_num) (by norm_num)).mul ((Scaled.rep_var).pow 4))

private def r47_cS5 : Scaled :=
  ((Scaled.var).sub ((r47_k (1) 6).mul ((Scaled.var).pow 3))).add ((r47_k (1) 120).mul ((Scaled.var).pow 5))
private theorem r47_rS5 : r47_cS5.Rep S5 :=
  ((Scaled.rep_var).sub ((r47_rep_frac (q := 1/6) (n := 1) (d := 6) (by norm_num) (by norm_num)).mul ((Scaled.rep_var).pow 3))).add ((r47_rep_frac (q := 1/120) (n := 1) (d := 120) (by norm_num) (by norm_num)).mul ((Scaled.rep_var).pow 5))

private def r47_cMu : Scaled :=
  (r47_cC).mul ((r47_cC4).add ((r47_k (293) 1000).mul (r47_cS5)))
private theorem r47_rMu : r47_cMu.Rep (highMu .atT) :=
  (r47_rC).mul ((r47_rC4).add ((r47_rep_frac (q := 293/1000) (n := 293) (d := 1000) (by norm_num) (by norm_num)).mul (r47_rS5)))

private def r47_cQ : Scaled :=
  (r47_cL).add ((r47_k (3) 20).mul ((r47_k (7) 10).sub (Scaled.var)))
private theorem r47_rQ : r47_cQ.Rep highQ :=
  (r47_rL).add ((r47_rep_frac (q := 3/20) (n := 3) (d := 20) (by norm_num) (by norm_num)).mul ((r47_rep_frac (q := 7/10) (n := 7) (d := 10) (by norm_num) (by norm_num)).sub (Scaled.rep_var)))

private def r47_cKR : Scaled :=
  ((r47_k (149089) 375000).sub ((r47_k (6391) 12500).mul (Scaled.var))).add ((r47_k (527) 1250).mul ((Scaled.var).pow 2))
private theorem r47_rKR : r47_cKR.Rep r47_pKR :=
  ((r47_rep_frac (q := 149089/375000) (n := 149089) (d := 375000) (by norm_num) (by norm_num)).sub ((r47_rep_frac (q := 6391/12500) (n := 6391) (d := 12500) (by norm_num) (by norm_num)).mul (Scaled.rep_var))).add ((r47_rep_frac (q := 527/1250) (n := 527) (d := 1250) (by norm_num) (by norm_num)).mul ((Scaled.rep_var).pow 2))

private def r47_cLR : Scaled :=
  ((r47_k (306) 3125).add ((r47_k (1047) 1250).mul (Scaled.var))).sub ((r47_k (639) 500).mul ((Scaled.var).pow 2))
private theorem r47_rLR : r47_cLR.Rep r47_pLR :=
  ((r47_rep_frac (q := 306/3125) (n := 306) (d := 3125) (by norm_num) (by norm_num)).add ((r47_rep_frac (q := 1047/1250) (n := 1047) (d := 1250) (by norm_num) (by norm_num)).mul (Scaled.rep_var))).sub ((r47_rep_frac (q := 639/500) (n := 639) (d := 500) (by norm_num) (by norm_num)).mul ((Scaled.rep_var).pow 2))

private def r47_cCL : Scaled :=
  (((r47_k (48527) 30000).mul (Scaled.var)).sub (r47_k (75461) 360000)).sub ((r47_k (14069) 10000).mul ((Scaled.var).pow 2))
private theorem r47_rCL : r47_cCL.Rep r47_pCL :=
  (((r47_rep_frac (q := 48527/30000) (n := 48527) (d := 30000) (by norm_num) (by norm_num)).mul (Scaled.rep_var)).sub (r47_rep_frac (q := 75461/360000) (n := 75461) (d := 360000) (by norm_num) (by norm_num))).sub ((r47_rep_frac (q := 14069/10000) (n := 14069) (d := 10000) (by norm_num) (by norm_num)).mul ((Scaled.rep_var).pow 2))

private def r47_cCR : Scaled :=
  ((r47_k (383537) 3000000).add ((r47_k (43361) 50000).mul (Scaled.var))).sub ((r47_k (14069) 10000).mul ((Scaled.var).pow 2))
private theorem r47_rCR : r47_cCR.Rep r47_pCR :=
  ((r47_rep_frac (q := 383537/3000000) (n := 383537) (d := 3000000) (by norm_num) (by norm_num)).add ((r47_rep_frac (q := 43361/50000) (n := 43361) (d := 50000) (by norm_num) (by norm_num)).mul (Scaled.rep_var))).sub ((r47_rep_frac (q := 14069/10000) (n := 14069) (d := 10000) (by norm_num) (by norm_num)).mul ((Scaled.rep_var).pow 2))

private def r47_cR5 : Scaled :=
  (r47_cC).sub ((r47_k (9) 10).mul (r47_cL))
private theorem r47_rR5 : r47_cR5.Rep (highC-C (9/10)*highL) :=
  (r47_rC).sub ((r47_rep_frac (q := 9/10) (n := 9) (d := 10) (by norm_num) (by norm_num)).mul (r47_rL))

private def r47_cR6 : Scaled :=
  ((r47_k (11) 10).mul (r47_cL)).sub (r47_cC)
private theorem r47_rR6 : r47_cR6.Rep (C (11/10)*highL-highC) :=
  ((r47_rep_frac (q := 11/10) (n := 11) (d := 10) (by norm_num) (by norm_num)).mul (r47_rL)).sub (r47_rC)

private def r47_cRH : Scaled :=
  (r47_k (4) 5).add ((r47_k (3) 5).mul (r47_cK))
private theorem r47_rRH : r47_cRH.Rep highRH :=
  (r47_rep_frac (q := 4/5) (n := 4) (d := 5) (by norm_num) (by norm_num)).add ((r47_rep_frac (q := 3/5) (n := 3) (d := 5) (by norm_num) (by norm_num)).mul (r47_rK))

private def r47_cRG : Scaled :=
  ((r47_k (31) 50).mul (r47_cK)).add ((r47_k (3923) 5000).mul (r47_cL))
private theorem r47_rRG : r47_cRG.Rep highRG :=
  ((r47_rep_frac (q := 31/50) (n := 31) (d := 50) (by norm_num) (by norm_num)).mul (r47_rK)).add ((r47_rep_frac (q := 3923/5000) (n := 3923) (d := 5000) (by norm_num) (by norm_num)).mul (r47_rL))

private def r47_cRD : Scaled :=
  (r47_k (18) 25).add ((r47_k (347) 500).mul (r47_cC))
private theorem r47_rRD : r47_cRD.Rep highRD :=
  (r47_rep_frac (q := 18/25) (n := 18) (d := 25) (by norm_num) (by norm_num)).add ((r47_rep_frac (q := 347/500) (n := 347) (d := 500) (by norm_num) (by norm_num)).mul (r47_rC))

private def r47_cRBT : Scaled :=
  (r47_k (7071) 10000).mul ((r47_cL).add (r47_cMu))
private theorem r47_rRBT : r47_cRBT.Rep (highRB .atT) :=
  (r47_rep_frac (q := 7071/10000) (n := 7071) (d := 10000) (by norm_num) (by norm_num)).mul ((r47_rL).add (r47_rMu))

private def r47_cRBA : Scaled :=
  (r47_k (7071) 10000).mul ((r47_cL).add (r47_cC))
private theorem r47_rRBA : r47_cRBA.Rep (highRB .atA) :=
  (r47_rep_frac (q := 7071/10000) (n := 7071) (d := 10000) (by norm_num) (by norm_num)).mul ((r47_rL).add (r47_rC))

private def r47_cRHm : Scaled :=
  ((r47_k (89) 100).mul (r47_cC4)).add ((r47_k (57) 125).mul ((r47_cK).sub (r47_cS5)))
private theorem r47_rRHm : r47_cRHm.Rep highRHminus :=
  ((r47_rep_frac (q := 89/100) (n := 89) (d := 100) (by norm_num) (by norm_num)).mul (r47_rC4)).add ((r47_rep_frac (q := 57/125) (n := 57) (d := 125) (by norm_num) (by norm_num)).mul ((r47_rK).sub (r47_rS5)))

private def r47_cRGm : Scaled :=
  (((r47_k (89) 100).mul (r47_cL)).mul (r47_cC4)).add ((r47_k (57) 125).mul ((r47_cK).sub ((r47_cL).mul (r47_cS5))))
private theorem r47_rRGm : r47_cRGm.Rep highRGminus :=
  (((r47_rep_frac (q := 89/100) (n := 89) (d := 100) (by norm_num) (by norm_num)).mul (r47_rL)).mul (r47_rC4)).add ((r47_rep_frac (q := 57/125) (n := 57) (d := 125) (by norm_num) (by norm_num)).mul ((r47_rK).sub ((r47_rL).mul (r47_rS5))))

private def r47_cRBmT : Scaled :=
  (((r47_k (83) 100).mul (r47_cL)).mul (r47_cC4)).add ((r47_k (14) 25).mul ((r47_cMu).sub ((r47_cL).mul (r47_cS5))))
private theorem r47_rRBmT : r47_cRBmT.Rep (highRBminus .atT) :=
  (((r47_rep_frac (q := 83/100) (n := 83) (d := 100) (by norm_num) (by norm_num)).mul (r47_rL)).mul (r47_rC4)).add ((r47_rep_frac (q := 14/25) (n := 14) (d := 25) (by norm_num) (by norm_num)).mul ((r47_rMu).sub ((r47_rL).mul (r47_rS5))))

private def r47_cRBmA : Scaled :=
  (((r47_k (83) 100).mul (r47_cL)).mul (r47_cC4)).add ((r47_k (14) 25).mul ((r47_cC).sub ((r47_cL).mul (r47_cS5))))
private theorem r47_rRBmA : r47_cRBmA.Rep (highRBminus .atA) :=
  (((r47_rep_frac (q := 83/100) (n := 83) (d := 100) (by norm_num) (by norm_num)).mul (r47_rL)).mul (r47_rC4)).add ((r47_rep_frac (q := 14/25) (n := 14) (d := 25) (by norm_num) (by norm_num)).mul ((r47_rC).sub ((r47_rL).mul (r47_rS5))))

private def r47_cQC : Scaled :=
  (r47_cQ).sub (r47_cC)
private theorem r47_rQC : r47_cQC.Rep (highQ-highC) :=
  (r47_rQ).sub (r47_rC)

private def r47_cGap : Scaled :=
  (r47_cQ).sub ((r47_cC).mul ((r47_cC4).add ((r47_k (293) 1000).mul (r47_cS5))))
private theorem r47_rGap : r47_cGap.Rep highQGap :=
  (r47_rQ).sub ((r47_rC).mul ((r47_rC4).add ((r47_rep_frac (q := 293/1000) (n := 293) (d := 1000) (by norm_num) (by norm_num)).mul (r47_rS5))))


private theorem r47_rKRight : r47_cKR.Rep kRight := by rw [r47_kRight]; exact r47_rKR
private theorem r47_rLRight : r47_cLR.Rep lRight := by rw [r47_lRight]; exact r47_rLR
private theorem r47_rCLeft : r47_cCL.Rep cLeft := by rw [r47_cLeft]; exact r47_rCL
private theorem r47_rCRight : r47_cCR.Rep cRight := by rw [r47_cRight]; exact r47_rCR

private theorem r47_cast_lt {a b : ℚ} {c : ℝ} (hab : a<b) (hc : (b:ℝ)=c) : (a:ℝ)<c :=
  hc ▸ Rat.cast_lt.mpr hab

private theorem r47_lt_cast {a b : ℚ} {c : ℝ} (hab : a<b) (hc : (a:ℝ)=c) : c<(b:ℝ) :=
  hc ▸ Rat.cast_lt.mpr hab

private theorem r47_mem {z : ℝ} (hz : z∈Icc (1/6:ℝ) (7/10:ℝ)) : z∈Icc (L:ℝ) (h:ℝ) := by
  simp only [L,h]
  push_cast
  exact hz

/-- `gapCentered` is the recentring of `highQGap` at `13/30` with half-width one. -/
private theorem r47_gap_centered : gapCentered=centered (-17/30) (43/30) highQGap := by
  simp only [gapCentered,DirectedPowerBounds.shift,centered,affine]
  congr 1
  norm_num

private theorem r47_rGapC : (r47_cGap.center 1 30 13 30).Rep gapCentered := by
  rw [r47_gap_centered]
  exact r47_rGap.centered 1 30 13 30 (by norm_num) (by norm_num) (by norm_num)

private theorem r47_gap_list : (r47_cGap.center 1 30 13 30).l=
    [152510652260952065054842237747200000000000000000000000,1176975157352626588763634794496000000000000000000000000,9710529435340682462097372610560000000000000000000000000,-9224475516833305404484111564800000000000000000000000000,4171342304465857687566090240000000000000000000000000000,18210399438438800914816696320000000000000000000000000000,-924444453641786098148966400000000000000000000000000000,-1629000506123127339024384000000000000000000000000000000,-84777066429306079150080000000000000000000000000000000] := by
  decide +kernel

private theorem r47_gap_scale : (r47_cGap.center 1 30 13 30).s=
    24679069470425088000000000000000000000000000000000000000 := by
  decide +kernel

private theorem r47_gap_coeff (i : ℕ) :
    gapCentered.coeff i=(([152510652260952065054842237747200000000000000000000000,1176975157352626588763634794496000000000000000000000000,9710529435340682462097372610560000000000000000000000000,-9224475516833305404484111564800000000000000000000000000,4171342304465857687566090240000000000000000000000000000,18210399438438800914816696320000000000000000000000000000,-924444453641786098148966400000000000000000000000000000,-1629000506123127339024384000000000000000000000000000000,-84777066429306079150080000000000000000000000000000000] : List ℤ).getD i 0:ℚ)/(24679069470425088000000000000000000000000000000000000000:ℕ) := by
  rw [r47_rGapC.coeff (by rw [r47_gap_scale]; norm_num) i,r47_gap_list,r47_gap_scale]

private theorem r47_split8 {p : ℚ[X]} (hp : p.natDegree≤8) :
    p=C (p.coeff 0)+C (p.coeff 1)*X+C (p.coeff 2)*X^2+PowerTailBounds.tail p 3 6 := by
  conv_lhs => rw [p.as_sum_range_C_mul_X_pow' (n:=9) (by omega)]
  simp only [PowerTailBounds.tail,Finset.sum_range_succ,Finset.sum_range_zero,Fin.sum_univ_succ,
    Fin.sum_univ_zero,Fin.val_zero,Fin.val_succ]
  ring

private theorem r47_idRH :
    centered L h highRH=expansion 8 (centered L h highRH) :=
  r47_id r47_rRH (by decide +kernel) (by decide +kernel)

private theorem r47_idRG :
    centered L h highRG=expansion 8 (centered L h highRG) :=
  r47_id r47_rRG (by decide +kernel) (by decide +kernel)

private theorem r47_idRD :
    centered L h highRD=expansion 8 (centered L h highRD) :=
  r47_id r47_rRD (by decide +kernel) (by decide +kernel)

private theorem r47_idRHm :
    centered L h highRHminus=expansion 8 (centered L h highRHminus) :=
  r47_id r47_rRHm (by decide +kernel) (by decide +kernel)

private theorem r47_idRGm :
    centered L h highRGminus=expansion 8 (centered L h highRGminus) :=
  r47_id r47_rRGm (by decide +kernel) (by decide +kernel)

private theorem r47_idRBT :
    centered L h (highRB .atT)=expansion 8 (centered L h (highRB .atT)) :=
  r47_id r47_rRBT (by decide +kernel) (by decide +kernel)

private theorem r47_idRBA :
    centered L h (highRB .atA)=expansion 8 (centered L h (highRB .atA)) :=
  r47_id r47_rRBA (by decide +kernel) (by decide +kernel)

private theorem r47_idRBmT :
    centered L h (highRBminus .atT)=expansion 8 (centered L h (highRBminus .atT)) :=
  r47_id r47_rRBmT (by decide +kernel) (by decide +kernel)

private theorem r47_idRBmA :
    centered L h (highRBminus .atA)=expansion 8 (centered L h (highRBminus .atA)) :=
  r47_id r47_rRBmA (by decide +kernel) (by decide +kernel)

private theorem r47_lowRH : (7/10:ℚ)<lowerOn 8 L h highRH :=
  r47_low r47_rRH (by decide +kernel) (by decide +kernel) (ρ := 7/10) (num := 7) (den := 10)
      (by norm_num) (by norm_num) (by decide +kernel)

private theorem r47_lowRG : (7/10:ℚ)<lowerOn 8 L h highRG :=
  r47_low r47_rRG (by decide +kernel) (by decide +kernel) (ρ := 7/10) (num := 7) (den := 10)
      (by norm_num) (by norm_num) (by decide +kernel)

private theorem r47_lowRD : (7/10:ℚ)<lowerOn 8 L h highRD :=
  r47_low r47_rRD (by decide +kernel) (by decide +kernel) (ρ := 7/10) (num := 7) (den := 10)
      (by norm_num) (by norm_num) (by decide +kernel)

private theorem r47_lowRHm : (7/10:ℚ)<lowerOn 8 L h highRHminus :=
  r47_low r47_rRHm (by decide +kernel) (by decide +kernel) (ρ := 7/10) (num := 7) (den := 10)
      (by norm_num) (by norm_num) (by decide +kernel)

private theorem r47_lowRGm : (7/10:ℚ)<lowerOn 8 L h highRGminus :=
  r47_low r47_rRGm (by decide +kernel) (by decide +kernel) (ρ := 7/10) (num := 7) (den := 10)
      (by norm_num) (by norm_num) (by decide +kernel)

private theorem r47_lowRBT : (7/10:ℚ)<lowerOn 8 L h (highRB .atT) :=
  r47_low r47_rRBT (by decide +kernel) (by decide +kernel) (ρ := 7/10) (num := 7) (den := 10)
      (by norm_num) (by norm_num) (by decide +kernel)

private theorem r47_lowRBA : (7/10:ℚ)<lowerOn 8 L h (highRB .atA) :=
  r47_low r47_rRBA (by decide +kernel) (by decide +kernel) (ρ := 7/10) (num := 7) (den := 10)
      (by norm_num) (by norm_num) (by decide +kernel)

private theorem r47_lowRBmT : (7/10:ℚ)<lowerOn 8 L h (highRBminus .atT) :=
  r47_low r47_rRBmT (by decide +kernel) (by decide +kernel) (ρ := 7/10) (num := 7) (den := 10)
      (by norm_num) (by norm_num) (by decide +kernel)

private theorem r47_lowRBmA : (7/10:ℚ)<lowerOn 8 L h (highRBminus .atA) :=
  r47_low r47_rRBmA (by decide +kernel) (by decide +kernel) (ρ := 7/10) (num := 7) (den := 10)
      (by norm_num) (by norm_num) (by decide +kernel)

private theorem r47_id3K :
    centered L h highK=expansion 3 (centered L h highK) :=
  r47_id r47_rK (by decide +kernel) (by decide +kernel)

private theorem r47_low3K : (669/1000:ℚ)<lowerOn 3 L h highK :=
  r47_low r47_rK (by decide +kernel) (by decide +kernel) (num := 669) (den := 1000)
    (by norm_num) (by norm_num) (by decide +kernel)

private theorem r47_id3KRight :
    centered L h kRight=expansion 3 (centered L h kRight) :=
  r47_id r47_rKRight (by decide +kernel) (by decide +kernel)

private theorem r47_low3KRight : (1/10:ℚ)<lowerOn 3 L h kRight :=
  r47_low r47_rKRight (by decide +kernel) (by decide +kernel) (num := 1) (den := 10)
    (by norm_num) (by norm_num) (by decide +kernel)

private theorem r47_id3LRight :
    centered L h lRight=expansion 3 (centered L h lRight) :=
  r47_id r47_rLRight (by decide +kernel) (by decide +kernel)

private theorem r47_low3LRight : (1/100:ℚ)<lowerOn 3 L h lRight :=
  r47_low r47_rLRight (by decide +kernel) (by decide +kernel) (num := 1) (den := 100)
    (by norm_num) (by norm_num) (by decide +kernel)

private theorem r47_id3CLeft :
    centered L h cLeft=expansion 3 (centered L h cLeft) :=
  r47_id r47_rCLeft (by decide +kernel) (by decide +kernel)

private theorem r47_low3CLeft : (1/100:ℚ)<lowerOn 3 L h cLeft :=
  r47_low r47_rCLeft (by decide +kernel) (by decide +kernel) (num := 1) (den := 100)
    (by norm_num) (by norm_num) (by decide +kernel)

private theorem r47_id3CRight :
    centered L h cRight=expansion 3 (centered L h cRight) :=
  r47_id r47_rCRight (by decide +kernel) (by decide +kernel)

private theorem r47_low3CRight : (1/100:ℚ)<lowerOn 3 L h cRight :=
  r47_low r47_rCRight (by decide +kernel) (by decide +kernel) (num := 1) (den := 100)
    (by norm_num) (by norm_num) (by decide +kernel)

private theorem r47_id3R5 :
    centered L h (highC-C (9/10)*highL)=expansion 3 (centered L h (highC-C (9/10)*highL)) :=
  r47_id r47_rR5 (by decide +kernel) (by decide +kernel)

private theorem r47_low3R5 : (2/25:ℚ)<lowerOn 3 L h (highC-C (9/10)*highL) :=
  r47_low r47_rR5 (by decide +kernel) (by decide +kernel) (num := 2) (den := 25)
    (by norm_num) (by norm_num) (by decide +kernel)

private theorem r47_id3R6 :
    centered L h (C (11/10)*highL-highC)=expansion 3 (centered L h (C (11/10)*highL-highC)) :=
  r47_id r47_rR6 (by decide +kernel) (by decide +kernel)

private theorem r47_low3R6 : (2/25:ℚ)<lowerOn 3 L h (C (11/10)*highL-highC) :=
  r47_low r47_rR6 (by decide +kernel) (by decide +kernel) (num := 2) (den := 25)
    (by norm_num) (by norm_num) (by decide +kernel)

end r47
theorem range_identities (i : Fin 7) :
    centered L h (rangePoly i)=expansion 3 (centered L h (rangePoly i)) := by
  fin_cases i
  · exact r47_id3K
  · exact r47_id3KRight
  · exact r47_id3LRight
  · exact r47_id3CLeft
  · exact r47_id3CRight
  · exact r47_id3R5
  · exact r47_id3R6

theorem range_reserves (i : Fin 7) :
    rangeReserve i<lowerOn 3 L h (rangePoly i) := by
  fin_cases i
  · exact r47_low3K
  · exact r47_low3KRight
  · exact r47_low3LRight
  · exact r47_low3CLeft
  · exact r47_low3CRight
  · exact r47_low3R5
  · exact r47_low3R6

theorem range_lower (i : Fin 7) {z : ℝ} (hz : z∈Icc (1/6:ℝ) (7/10:ℝ)) :
    (rangeReserve i:ℝ)<aeval z (rangePoly i) :=
  positive_on_interval (by norm_num [L,h]) (range_identities i) (range_reserves i) (r47_mem hz)

theorem weight_endpoint_identities :
    highK=C (highK.eval h)+(X-C h)*kRight ∧
    highL=C (highL.eval h)+(C h-X)*lRight ∧
    highC=C (highC.eval L)-(X-C L)*cLeft ∧
    highC=C (highC.eval h)+(C h-X)*cRight := by
  refine ⟨r47_root highK h,?_,?_,?_⟩
  · have e := r47_root highL h
    rw [lRight]
    linear_combination e
  · have e := r47_root highC L
    rw [cLeft]
    linear_combination e
  · have e := r47_root highC h
    rw [cRight]
    linear_combination e

theorem weight_endpoint_reserves :
    highK.eval h<(843/1000:ℚ) ∧ (89/100:ℚ)<highL.eval h ∧
      (89/100:ℚ)<highC.eval h ∧ highC.eval L=10163/10000 := by
  refine ⟨?_,?_,?_,?_⟩ <;> norm_num [highK,highL,highC,t]

theorem highL_upper {z : ℝ} (hz : z∈Icc (1/6:ℝ) (7/10:ℝ)) :
    aeval z highL<(5001/5000:ℝ) := by
  let u : ℝ := z-1/6
  have hu : u∈Icc 0 (8/15:ℝ) := ⟨by dsimp [u]; linarith [hz.1],
    by dsimp [u]; linarith [hz.2]⟩
  have hcube : u^3≤(8/15)*u^2 := by
    nlinarith [mul_le_mul_of_nonneg_right hu.2 (sq_nonneg u)]
  have he : aeval z highL=1+(7/400)*u-(2733/2500)*u^2+(639/500)*u^3 := by
    simp [highL,t,u,L]
  rw [he]
  nlinarith [sq_nonneg (u-(7/400)/(2*(1029/2500)))]

/-- Every inequality holds throughout the one high interval. -/
theorem high_ranges {z : ℝ} (hz : z∈Icc (1/6:ℝ) (7/10:ℝ)) :
    (669/1000:ℝ)<aeval z highK ∧ aeval z highK<843/1000 ∧
      (89/100:ℝ)<aeval z highL ∧ aeval z highL<5001/5000 ∧
      (89/100:ℝ)<aeval z highC ∧ aeval z highC≤10163/10000 ∧
      (9/10)*aeval z highL<aeval z highC ∧
      aeval z highC<(11/10)*aeval z highL := by
  have h0 := range_lower 0 hz
  have h1 := range_lower 1 hz
  have h2 := range_lower 2 hz
  have h3 := range_lower 3 hz
  have h4 := range_lower 4 hz
  have h5 := range_lower 5 hz
  have h6 := range_lower 6 hz
  norm_num [rangePoly,rangeReserve] at h0 h1 h2 h3 h4 h5 h6
  have eK := congrArg (fun f : ℚ[X] => aeval z f) weight_endpoint_identities.1
  have eL := congrArg (fun f : ℚ[X] => aeval z f) weight_endpoint_identities.2.1
  have eC0 := congrArg (fun f : ℚ[X] => aeval z f) weight_endpoint_identities.2.2.1
  have eCh := congrArg (fun f : ℚ[X] => aeval z f) weight_endpoint_identities.2.2.2
  simp only [map_add,map_sub,map_mul,aeval_C,aeval_X,eq_ratCast] at eK eL eC0 eCh
  have hK : ((highK.eval h:ℚ):ℝ)<843/1000 :=
    r47_cast_lt weight_endpoint_reserves.1 (by norm_num)
  have hL : (89/100:ℝ)<((highL.eval h:ℚ):ℝ) :=
    r47_lt_cast weight_endpoint_reserves.2.1 (by norm_num)
  have hC : (89/100:ℝ)<((highC.eval h:ℚ):ℝ) :=
    r47_lt_cast weight_endpoint_reserves.2.2.1 (by norm_num)
  have hC0 : ((highC.eval L:ℚ):ℝ)=10163/10000 := by
    rw [weight_endpoint_reserves.2.2.2]
    norm_num
  have pK := mul_nonpos_of_nonpos_of_nonneg
    (show z-(h:ℝ)≤0 by norm_num [h]; linarith [hz.2]) (show 0≤aeval z kRight by linarith)
  have pL := mul_nonneg (show 0≤(h:ℝ)-z by norm_num [h]; linarith [hz.2])
    (show 0≤aeval z lRight by linarith)
  have pC0 := mul_nonneg (show 0≤z-(L:ℝ) by norm_num [L]; linarith [hz.1])
    (show 0≤aeval z cLeft by linarith)
  have pCh := mul_nonneg (show 0≤(h:ℝ)-z by norm_num [h]; linarith [hz.2])
    (show 0≤aeval z cRight by linarith)
  exact ⟨h0,by linarith,by linarith,highL_upper hz,by linarith,by linarith,
    by linarith,by linarith⟩

theorem mass_identities (e : Endpoint) (i : Fin 7) :
    centered L h (mass e i)=expansion 8 (centered L h (mass e i)) := by
  cases e <;> fin_cases i
  · exact r47_idRH
  · exact r47_idRG
  · exact r47_idRD
  · exact r47_idRBT
  · exact r47_idRHm
  · exact r47_idRGm
  · exact r47_idRBmT
  · exact r47_idRH
  · exact r47_idRG
  · exact r47_idRD
  · exact r47_idRBA
  · exact r47_idRHm
  · exact r47_idRGm
  · exact r47_idRBmA

theorem mass_reserves (e : Endpoint) (i : Fin 7) :
    (7/10:ℚ)<lowerOn 8 L h (mass e i) := by
  cases e <;> fin_cases i
  · exact r47_lowRH
  · exact r47_lowRG
  · exact r47_lowRD
  · exact r47_lowRBT
  · exact r47_lowRHm
  · exact r47_lowRGm
  · exact r47_lowRBmT
  · exact r47_lowRH
  · exact r47_lowRG
  · exact r47_lowRD
  · exact r47_lowRBA
  · exact r47_lowRHm
  · exact r47_lowRGm
  · exact r47_lowRBmA

theorem masses_positive (e : Endpoint) (i : Fin 7) {z : ℝ}
    (hz : z∈Icc (1/6:ℝ) (7/10:ℝ)) : 0<aeval z (mass e i) := by
  have hh := positive_on_interval (by norm_num [L,h] : L<h)
    (mass_identities e i) (mass_reserves e i) (r47_mem hz)
  push_cast at hh
  linarith

theorem gap_identity :
    gapCentered=C (gapCentered.coeff 0)+C (gapCentered.coeff 1)*X+
      C (gapCentered.coeff 2)*X^2+PowerTailBounds.tail gapCentered 3 6 :=
  r47_split8 ((r47_rGapC.natDegree_le (by rw [r47_gap_scale]; norm_num)).trans
    (by rw [r47_gap_list]; simp))

theorem gap_reserves : (107/400:ℚ)<gapCurvature ∧ (1/250:ℚ)<gapReserve := by
  simp only [gapReserve,gapCurvature,PowerTailBounds.norm,Fin.sum_univ_six,r47_gap_coeff]
  norm_num

theorem highQGap_positive {z : ℝ} (hz : z∈Icc (1/6:ℝ) (7/10:ℝ)) :
    0<aeval z highQGap := by
  have hx : |z-13/30|≤((4/15:ℚ):ℝ) := by
    push_cast
    exact abs_le.mpr ⟨by linarith [hz.1],by linarith [hz.2]⟩
  have hb := PowerTailBounds.quadratic_lower (r := 4/15) gap_identity (by norm_num) hx
  have hc : (0:ℝ)<(gapCurvature:ℝ) := by
    exact_mod_cast (lt_trans (by norm_num : (0:ℚ)<107/400) gap_reserves.1)
  have hm := ChebyshevLeadingBounds.quadratic_min
    (a:=(gapCentered.coeff 0:ℝ)) (b:=(gapCentered.coeff 1:ℝ)) (x:=z-13/30) hc
  have he : aeval (z-13/30) gapCentered=aeval z highQGap := by
    simp [gapCentered]
  rw [he] at hb
  have hr : (1/250:ℝ)<(gapReserve:ℝ) := r47_lt_cast gap_reserves.2 (by norm_num)
  dsimp [gapReserve,gapCurvature] at hr hm hc
  push_cast at hr hm hc
  linarith

theorem highQ_C_identity :
    centered L h (highQ-highC)=expansion 3 (centered L h (highQ-highC)) :=
  r47_id r47_rQC (by decide +kernel) (by decide +kernel)

theorem highQ_C_reserve : (1/3000:ℚ)<lowerOn 3 L h (highQ-highC) :=
  r47_low r47_rQC (by decide +kernel) (by decide +kernel) (ρ := 1/3000) (num := 1) (den := 3000)
      (by norm_num) (by norm_num) (by decide +kernel)

theorem highQ_C_positive {z : ℝ} (hz : z∈Icc (1/6:ℝ) (7/10:ℝ)) :
    aeval z highC<aeval z highQ := by
  have hh := positive_on_interval (by norm_num [L,h] : L<h)
    highQ_C_identity highQ_C_reserve (r47_mem hz)
  simp only [map_sub] at hh
  push_cast at hh
  linarith

end SquaresInCircles.Eight.GlobalGA.TwoPositive.Certificate
end
end
end

section
/-!
## Explicit weights are admissible for every split of the fixed total

The coefficients depend on the actual total A/T angle and stay fixed
while that angle is split.  Their ratio bounds hold over the entire
split interval.  The high family also satisfies the balanced envelope
conditions for every ordinary block, without assuming all large
coefficients are at least one.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalGA.TwoPositive

open Candidate Secondary PositiveTD

def highK (t : ℝ) : ℝ := Polynomial.aeval t Certificate.highK
def highL (t : ℝ) : ℝ := Polynomial.aeval t Certificate.highL
def highC (t : ℝ) : ℝ := Polynomial.aeval t Certificate.highC

theorem low_factor_monotone :
    MonotoneOn (fun z : ℝ => Real.cos z+eta*Real.sin z) (Icc 0 (1/6)) := by
  apply monoOn_of_hasDeriv_nonneg (d := fun z => -Real.sin z+eta*Real.cos z)
  · exact (Real.continuous_cos.add (continuous_const.mul Real.continuous_sin)).continuousOn
  · intro z _
    exact (Real.hasDerivAt_cos z).add ((Real.hasDerivAt_sin z).const_mul eta)
  · intro z hz
    have hz' : z∈Icc 0 frameCap := ⟨hz.1.le,by simp only [frameCap]; linarith [hz.2]⟩
    have hc := (transport_trig hz').1
    have hs := Real.sin_le hz.1.le
    simp only [eta]
    linarith [hz.2]

theorem low_split_domain {t z : ℝ} (ht : t∈Icc 0 (1/6:ℝ)) (hz : z∈Icc 0 t) :
    Explicit.lowK t∈Icc (1/2:ℝ) (17/20) ∧
      Explicit.lowL t∈Icc (Explicit.lowK t) (2*Explicit.lowK t) ∧
      Explicit.lowC t∈Icc (Explicit.lowK t) 2 ∧
      (Explicit.lowL t≤2*tilted (Explicit.lowC t) z ∧
        tilted (Explicit.lowC t) z≤2*Explicit.lowL t) ∧
      Explicit.lowC t≤(3/2)*Explicit.lowL t ∧
        tilted (Explicit.lowC t) z≤(3/2)*Explicit.lowL t := by
  have hd := Explicit.low_domain ht
  have hr := Explicit.low_ranges ht
  have hz' : z∈Icc 0 (1/6:ℝ) := ⟨hz.1,hz.2.trans ht.2⟩
  have hc : 0≤Explicit.lowC t := by linarith [hd.1.1,hd.2.2.1.1]
  have hmlo₀ := mul_le_mul_of_nonneg_left (Explicit.low_factor hz').1 hc
  have hmhi := mul_le_mul_of_nonneg_left (low_factor_monotone hz' ht hz.2) hc
  have htotal := (Explicit.low_tilted ht).2
  have hmlo : Explicit.lowC t≤tilted (Explicit.lowC t) z := by
    simpa [tilted] using hmlo₀
  change tilted (Explicit.lowC t) z≤tilted (Explicit.lowC t) t at hmhi
  exact ⟨hd.1,hd.2.1,hd.2.2.1,⟨by linarith [hr.2.2.1,hr.2.2.2.1],
    by linarith [hr.2.2.1]⟩,by linarith,by linarith⟩

theorem high_ranges {t : ℝ} (ht : t∈Icc (1/6:ℝ) frameCap) :
    (669/1000:ℝ)<highK t ∧ highK t<843/1000 ∧
      (89/100:ℝ)<highL t ∧ highL t<5001/5000 ∧
      (89/100:ℝ)<highC t ∧ highC t≤10163/10000 ∧
      (9/10)*highL t<highC t ∧ highC t<(11/10)*highL t :=
  Certificate.high_ranges ht

theorem high_tilted {t z : ℝ} (ht : t∈Icc (1/6:ℝ) frameCap) (hz : z∈Icc 0 t) :
    (2/3)*highL t<tilted (highC t) z ∧
      tilted (highC t) z<(3/2)*highL t ∧
      tilted (highC t) z<1061/1000 := by
  have hr := high_ranges ht
  have hc : 0<highC t := by linarith [hr.2.2.2.2.1]
  have hz' : z∈Icc 0 frameCap := ⟨hz.1,hz.2.trans ht.2⟩
  have hlow₀ := mul_lt_mul_of_pos_left (Explicit.factor_lower hz') hc
  have hhigh := mul_lt_mul_of_pos_left (Explicit.factor_upper z) hc
  have hlow : (19/20)*highC t<tilted (highC t) z := by
    simpa [tilted,mul_comm] using hlow₀
  change tilted (highC t) z<highC t*(1043/1000) at hhigh
  exact ⟨by linarith [hr.2.2.1,hr.2.2.2.2.2.2.1],
    by linarith [hr.2.2.1,hr.2.2.2.2.2.2.2],by linarith [hr.2.2.2.2.2.1]⟩

theorem high_split_domain {t z : ℝ} (ht : t∈Icc (1/6:ℝ) frameCap) (hz : z∈Icc 0 t) :
    highK t∈Icc (1/2:ℝ) (17/20) ∧
      highL t∈Icc (highK t) (2*highK t) ∧
      highC t∈Icc (highK t) 2 ∧
      (highL t≤2*tilted (highC t) z ∧ tilted (highC t) z≤2*highL t) ∧
      (9/10)*highL t≤highC t ∧ highC t≤(11/10)*highL t := by
  have hr := high_ranges ht
  have hm := high_tilted ht hz
  refine ⟨⟨by linarith [hr.1],by linarith [hr.2.1]⟩,
    ⟨by linarith [hr.2.1,hr.2.2.1],by linarith [hr.1,hr.2.2.2.1]⟩,
    ⟨by linarith [hr.2.1,hr.2.2.2.2.1],by linarith [hr.2.2.2.2.2.1]⟩,
    ⟨by linarith [hr.2.2.1,hm.1],by linarith [hr.2.2.1,hm.2.1]⟩,
    hr.2.2.2.2.2.2.1.le,hr.2.2.2.2.2.2.2.le⟩

theorem high_balanced {t z : ℝ} (ht : t∈Icc (1/6:ℝ) frameCap) (hz : z∈Icc 0 t) :
    (∀i : Fin 4,2*qWeights (highK t) (highL t) (tilted (highC t) z) i≤
      3*pWeights (highK t) (highL t) (tilted (highC t) z) i) ∧
    (∀i j : Fin 4,5*qWeights (highK t) (highL t) (tilted (highC t) z) i≤
      6*qWeights (highK t) (highL t) (tilted (highC t) z) j) := by
  have hr := high_ranges ht
  have hm := high_tilted ht hz
  have hq (i : Fin 4) :
      (89/100:ℝ)<qWeights (highK t) (highL t) (tilted (highC t) z) i ∧
        qWeights (highK t) (highL t) (tilted (highC t) z) i<1061/1000 := by
    fin_cases i
    · norm_num [qWeights]
    · exact ⟨hr.2.2.1,by simpa [qWeights] using
        (show highL t<1061/1000 by linarith [hr.2.2.2.1])⟩
    · change (89/100:ℝ) < max (highL t) (tilted (highC t) z) ∧
        max (highL t) (tilted (highC t) z)<1061/1000
      exact ⟨hr.2.2.1.trans_le (le_max_left _ _),
        max_lt (by linarith [hr.2.2.2.1]) hm.2.2⟩
    · norm_num [qWeights]
  constructor
  · intro i
    fin_cases i
    · simp [qWeights,pWeights]
      linarith [hr.1]
    · simp [qWeights,pWeights]
      linarith [hr.1,hr.2.2.2.1]
    · change 2*max (highL t) (tilted (highC t) z)≤
        3*min (highL t) (tilted (highC t) z)
      rcases le_total (highL t) (tilted (highC t) z) with hh | hh
      · rw [max_eq_right hh,min_eq_left hh]
        linarith [hm.2.1]
      · rw [max_eq_left hh,min_eq_right hh]
        linarith [hm.1]
    · simp [qWeights,pWeights]
      linarith [hr.1]
  · intro i j
    linarith [(hq i).2,(hq j).1]

end SquaresInCircles.Eight.GlobalGA.TwoPositive
end
end
end

section
@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalGA.TwoPositive.Certificate
open Polynomial Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PositiveTD
open PositiveTD.Certificate

abbrev kAt (t : ℝ) : ℝ := aeval t highK
abbrev lAt (t : ℝ) : ℝ := aeval t highL
abbrev cAt (t : ℝ) : ℝ := aeval t highC

def aAt : Endpoint→ℝ→ℝ | .atT,_ => 0 | .atA,t => t
def zAt : Endpoint→ℝ→ℝ | .atT,t => t | .atA,_ => 0
def mAt (e : Endpoint) (t : ℝ) : ℝ := tilted (cAt t) (zAt e t)

def endpointBase (e : Endpoint) (t : ℝ) : ℝ :=
  baseline (kAt t) (lAt t) (cAt t) (zAt e t)+lAt t*ASupport.charge (aAt e t)

def endpointNonradical (e : Endpoint) (t : ℝ) : ℝ :=
  2*kAt t+3*lAt t+(3/2)*mAt e t+cAt t/2+3+
    cAt t*edgeWidth (zAt e t)-cAt t*sigma*Real.sin (zAt e t)+
      lAt t*ASupport.charge (aAt e t)

theorem high_frame_domain {t : ℝ} (ht : t∈Icc (1/6:ℝ) frameCap) :
    t∈Icc 0 frameCap := ⟨by linarith [ht.1],ht.2⟩

theorem high_m_bounds (e : Endpoint) {t : ℝ} (ht : t∈Icc (1/6:ℝ) frameCap) :
    0<aeval t (highMMinus e) ∧ aeval t (highMMinus e)≤ mAt e t ∧
      mAt e t≤aeval t (highMPlus e) ∧ mAt e t≤aeval t (highMu e) := by
  have hr := high_ranges ht
  have hc : 0<cAt t := by linarith [hr.2.2.2.2.1]
  cases e
  · have hm := tilted_polynomial_bounds (c:=highC) (high_frame_domain ht) hc
    have hcos := cos_upper_four (high_frame_domain ht).1
    have hsin := sin_upper_five (high_frame_domain ht).1
    have htilt : Real.cos t+PositiveTD.eta*Real.sin t≤aeval t (C4+C etaQ*S5) := by
      have he : aeval t (C4+C etaQ*S5)=(1-t^2/2+t^4/24)+293/1000*(t-t^3/6+t^5/120) := by
        simp only [C4,S5,map_add,map_sub,map_mul,map_pow,map_one,aeval_C,aeval_X,eq_ratCast]
        push_cast
        ring
      rw [he,show PositiveTD.eta=293/1000 from rfl]
      linarith
    have hmu := mul_le_mul_of_nonneg_left htilt hc.le
    refine ⟨hm.1,hm.2.1,hm.2.2,?_⟩
    simpa [highMu,mAt,zAt,tilted] using hmu
  · simpa [highMMinus,highMPlus,highMu,mAt,zAt,tilted] using
      (show 0<cAt t ∧ cAt t≤cAt t ∧ cAt t≤cAt t ∧ cAt t≤cAt t from
        ⟨hc,le_rfl,le_rfl,le_rfl⟩)

theorem high_Q_bound (e : Endpoint) {t : ℝ} (ht : t∈Icc (1/6:ℝ) frameCap) :
    max (lAt t) (mAt e t)≤aeval t highQ := by
  have hL : lAt t≤aeval t highQ := by
    have he : aeval t highQ=lAt t+3/20*(7/10-t) := by
      simp only [highQ,map_add,map_mul,map_sub,aeval_C,aeval_X,eq_ratCast,h]
      push_cast
      ring
    have h2 := ht.2
    simp only [frameCap] at h2
    rw [he]
    linarith
  apply max_le hL
  cases e
  · have hg := highQGap_positive ht
    have hm := (high_m_bounds .atT ht).2.2.2
    simp only [highQGap,map_sub] at hg
    simpa only [highMu] using hm.trans (show
      aeval t (highC*(C4+C etaQ*S5))≤aeval t highQ by linarith)
  · simpa [mAt,zAt,tilted] using (highQ_C_positive ht).le

theorem high_nonradical_lower (e : Endpoint) {t : ℝ} (ht : t∈Icc (1/6:ℝ) frameCap) :
    aeval t (highA e)≤endpointNonradical e t := by
  have hr := high_ranges ht
  have hl : 0≤lAt t := by linarith [hr.2.2.1]
  have hc : 0≤cAt t := by linarith [hr.2.2.2.2.1]
  cases e
  · have hm := (high_m_bounds .atT ht).2.1
    have htrig := taylor_bounds (high_frame_domain ht)
    have hs := sigma_sine_upper (high_frame_domain ht) hc
    have hw₀ := mul_le_mul_of_nonneg_left
      (add_le_add htrig.2.2.2.2.1 htrig.2.1) hc
    have hw : cAt t/2*(1+aeval t C10+aeval t S11)≤cAt t*edgeWidth t := by
      rw [edgeWidth_positive_formula (high_frame_domain ht)]
      nlinarith only [hw₀]
    have hE : aeval t (highA .atT)=2*kAt t+3*lAt t+(3/2)*aeval t (highMMinus .atT)+
        (1/2)*cAt t+3+(1/2)*cAt t*(1+aeval t C10+aeval t S11)-
          cAt t*(sigmabar:ℝ)*aeval t S9 := by
      simp only [highA,map_add,map_sub,map_mul,map_one,aeval_C,eq_ratCast]
      push_cast
      ring
    rw [hE]
    simp only [endpointNonradical,aAt,zAt,ASupport.charge_zero,mul_zero,add_zero]
    generalize (sigmabar:ℝ)=S at hs ⊢
    linarith only [hm,hs,hw]
  · have hA := mul_le_mul_of_nonneg_left (ASupport.high_polynomial_charge ht) hl
    have hw : edgeWidth 0=1 := by norm_num [edgeWidth,pairWidth]
    have hE : aeval t (highA .atA)=2*kAt t+3*lAt t+3*cAt t+3+lAt t*aeval t highJ := by
      simp only [highA,map_add,map_mul,aeval_C,eq_ratCast]
      push_cast
      ring
    rw [hE]
    simp only [endpointNonradical,mAt,aAt,zAt,tilted,Real.cos_zero,Real.sin_zero,
      mul_zero,mul_one,add_zero,sub_zero,hw]
    linarith only [hA]

theorem high_norm_bounds (e : Endpoint) {t : ℝ} (ht : t∈Icc (1/6:ℝ) frameCap) :
    (pairNorm (kAt t) 1 0)^2≤aeval t highPH ∧
    (pairNorm (kAt t) (lAt t) 0)^2≤aeval t highPG ∧
    (pairNorm (cAt t) 1 0)^2≤aeval t highPD ∧
    (pairNorm (lAt t) (mAt e t) 0)^2≤aeval t (highPB e) ∧
    (pairNorm (kAt t) 1 (-t))^2≤aeval t highPHminus ∧
    (pairNorm (kAt t) (lAt t) (-t))^2≤aeval t highPGminus ∧
    (pairNorm (lAt t) (mAt e t) (-t))^2≤aeval t (highPBminus e) := by
  have hr := high_ranges ht
  have hk : 0<kAt t := by linarith [hr.1]
  have hl : 0<lAt t := by linarith [hr.2.2.1]
  have hm := high_m_bounds e ht
  have hm0 : 0< mAt e t := hm.1.trans_le hm.2.1
  have hm2 : (mAt e t)^2≤(aeval t (highMPlus e))^2 :=
    pow_le_pow_left₀ hm0.le hm.2.2.1 2
  have hs := taylor_bounds (high_frame_domain ht)
  have h2 : (algebraMap ℚ ℝ) 2=2 := by rw [eq_ratCast]; norm_num
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · rw [zero_norm_sq]
    exact le_of_eq (by simp only [highPH,map_add,map_pow,map_one]; ring)
  · rw [zero_norm_sq]
    exact le_of_eq (by simp only [highPG,map_add,map_pow])
  · rw [zero_norm_sq]
    exact le_of_eq (by simp only [highPD,map_add,map_pow,map_one]; ring)
  · rw [zero_norm_sq]
    simp only [highPB,map_add,map_pow]
    linarith
  · have hh := negative_norm_sq_le (q:=1) hk (by norm_num) (high_frame_domain ht) hs.2.1
    simp only [highPHminus,highPH,map_add,map_sub,map_mul,map_pow,map_one,aeval_C,h2]
    linarith only [hh]
  · have hh := negative_norm_sq_le hk hl (high_frame_domain ht) hs.2.1
    simp only [highPGminus,highPG,map_add,map_sub,map_mul,map_pow,aeval_C,h2]
    linarith only [hh]
  · have hh := negative_norm_sq_le hl hm0 (high_frame_domain ht) hs.2.1
    have hp := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hm.2.1 hs.1) hl.le
    simp only [highPBminus,highPB,map_add,map_sub,map_mul,map_pow,aeval_C,h2]
    linarith only [hh,hp,hm2]

theorem baseline_full_lower (k l c z a : ℝ) :
    2*k+3*l+(3/2)*tilted c z+c/2+3+c*edgeWidth z-c*sigma*Real.sin z+l*ASupport.charge a-
      R*(pairNorm k 1 0+pairNorm k l 0+pairNorm l (tilted c z) 0+pairNorm c 1 0)≤
        baseline k l c z+l*ASupport.charge a := by
  have hD := clippedSupport_le_fullSupport 1 c
  simp only [baseline,fullSupport_pair] at hD ⊢
  nlinarith only [hD]

theorem high_H_lower (e : Endpoint) (t : ℝ) :
    endpointNonradical e t+Real.cos t-1-
      R*(pairNorm (kAt t) (lAt t) 0+pairNorm (lAt t) (mAt e t) 0+
        pairNorm (kAt t) 1 (-t)+pairNorm (cAt t) 1 0)≤
      endpointBase e t+V R (kAt t) 1 t := by
  have hh := baseline_full_lower (kAt t) (lAt t) (cAt t) (zAt e t) (aAt e t)
  dsimp [endpointNonradical,endpointBase,mAt,V]
  nlinarith only [hh]

theorem high_G_lower (e : Endpoint) (t : ℝ) :
    endpointNonradical e t+lAt t*(Real.cos t-1)-
      R*(pairNorm (kAt t) 1 0+pairNorm (lAt t) (mAt e t) 0+
        pairNorm (kAt t) (lAt t) (-t)+pairNorm (cAt t) 1 0)≤
      endpointBase e t+V R (kAt t) (lAt t) t := by
  have hh := baseline_full_lower (kAt t) (lAt t) (cAt t) (zAt e t) (aAt e t)
  dsimp [endpointNonradical,endpointBase,mAt,V]
  nlinarith only [hh]

theorem sorted_pair_norm (l m s : ℝ) :
    pairNorm (min l m) (max l m) s=pairNorm l m s := by
  rcases le_total l m with h | h
  · rw [min_eq_left h,max_eq_right h]
  · rw [min_eq_right h,max_eq_left h,pairNorm_symm]

theorem high_B_lower (e : Endpoint) (t : ℝ) :
    endpointNonradical e t+max (lAt t) (mAt e t)*(Real.cos t-1)-
      R*(pairNorm (kAt t) 1 0+pairNorm (kAt t) (lAt t) 0+
        pairNorm (lAt t) (mAt e t) (-t)+pairNorm (cAt t) 1 0)≤
      endpointBase e t+V R (min (lAt t) (mAt e t)) (max (lAt t) (mAt e t)) t := by
  have hh := baseline_full_lower (kAt t) (lAt t) (cAt t) (zAt e t) (aAt e t)
  simp only [V,sorted_pair_norm]
  dsimp [endpointNonradical,endpointBase,mAt]
  nlinarith only [hh]

theorem high_H_positive (e : Endpoint) {t : ℝ} (ht : t∈Icc (1/6:ℝ) frameCap) :
    0<endpointBase e t+V R (kAt t) 1 t := by
  have hn := high_norm_bounds e ht
  have htrig := taylor_bounds (high_frame_domain ht)
  have hA : aeval t (highA e+C10-1)≤endpointNonradical e t+Real.cos t-1 := by
    simp only [map_add,map_sub,map_one]
    linarith [high_nonradical_lower e ht,htrig.2.2.2.2.1]
  have hrG : 0<aeval t highRG := by simpa [mass] using masses_positive e 1 ht
  have hrB : 0<aeval t (highRB e) := by simpa [mass] using masses_positive e 3 ht
  have hrH : 0<aeval t highRHminus := by simpa [mass] using masses_positive e 4 ht
  have hrD : 0<aeval t highRD := by simpa [mass] using masses_positive e 2 ht
  have hp := num4_transfer hrG hrB hrH hrD
    (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _)
    (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _)
    hn.2.1 hn.2.2.2.1 hn.2.2.2.2.1 hn.2.2.1 hA (highNH_positive e ht)
  exact hp.trans_le (high_H_lower e t)

theorem high_G_positive (e : Endpoint) {t : ℝ} (ht : t∈Icc (1/6:ℝ) frameCap) :
    0<endpointBase e t+V R (kAt t) (lAt t) t := by
  have hn := high_norm_bounds e ht
  have hr := high_ranges ht
  have htrig := taylor_bounds (high_frame_domain ht)
  have hcos := mul_le_mul_of_nonneg_left (sub_le_sub_right htrig.2.2.2.2.1 1)
    (show 0≤lAt t by linarith [hr.2.2.1])
  have hA : aeval t (highA e+highL*(C10-1))≤
      endpointNonradical e t+lAt t*(Real.cos t-1) := by
    simp only [map_add,map_mul,map_sub,map_one]
    linarith [high_nonradical_lower e ht]
  have hrH : 0<aeval t highRH := by simpa [mass] using masses_positive e 0 ht
  have hrB : 0<aeval t (highRB e) := by simpa [mass] using masses_positive e 3 ht
  have hrG : 0<aeval t highRGminus := by simpa [mass] using masses_positive e 5 ht
  have hrD : 0<aeval t highRD := by simpa [mass] using masses_positive e 2 ht
  have hp := num4_transfer hrH hrB hrG hrD
    (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _)
    (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _)
    hn.1 hn.2.2.2.1 hn.2.2.2.2.2.1 hn.2.2.1 hA (highNG_positive e ht)
  exact hp.trans_le (high_G_lower e t)

theorem high_B_positive (e : Endpoint) {t : ℝ} (ht : t∈Icc (1/6:ℝ) frameCap) :
    0<endpointBase e t+
      V R (min (lAt t) (mAt e t)) (max (lAt t) (mAt e t)) t := by
  have hn := high_norm_bounds e ht
  have hr := high_ranges ht
  have htrig := taylor_bounds (high_frame_domain ht)
  have hQ := high_Q_bound e ht
  have hQ0 : 0≤aeval t highQ := by
    have hlq := (le_max_left (lAt t) (mAt e t)).trans hQ
    linarith [hr.2.2.1]
  have h₁ := mul_le_mul_of_nonneg_left (sub_le_sub_right htrig.2.2.2.2.1 1) hQ0
  have h₂ := mul_le_mul_of_nonpos_right hQ (sub_nonpos.mpr (Real.cos_le_one t))
  have hA : aeval t (highA e+highQ*(C10-1))≤endpointNonradical e t+
      max (lAt t) (mAt e t)*(Real.cos t-1) := by
    simp only [map_add,map_mul,map_sub,map_one]
    linarith [high_nonradical_lower e ht]
  have hrH : 0<aeval t highRH := by simpa [mass] using masses_positive e 0 ht
  have hrG : 0<aeval t highRG := by simpa [mass] using masses_positive e 1 ht
  have hrB : 0<aeval t (highRBminus e) := by simpa [mass] using masses_positive e 6 ht
  have hrD : 0<aeval t highRD := by simpa [mass] using masses_positive e 2 ht
  have hp := num4_transfer hrH hrG hrB hrD
    (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _)
    (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _)
    hn.1 hn.2.1 hn.2.2.2.2.2.2 hn.2.2.1 hA (highNB_positive e ht)
  exact hp.trans_le (high_B_lower e t)

/-- Both all-A and all-T endpoints satisfy all three high alternatives. -/
theorem high_six_scalars_positive (e : Endpoint) {t : ℝ} (ht : t∈Icc (1/6:ℝ) frameCap) :
    0<endpointBase e t+V R (kAt t) 1 t ∧
    0<endpointBase e t+V R (kAt t) (lAt t) t ∧
    0<endpointBase e t+
      V R (min (lAt t) (mAt e t)) (max (lAt t) (mAt e t)) t :=
  ⟨high_H_positive e ht,high_G_positive e ht,high_B_positive e ht⟩

end SquaresInCircles.Eight.GlobalGA.TwoPositive.Certificate
end
end
end

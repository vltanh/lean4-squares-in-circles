module

public import SquaresInCircles.Eight.TableFree.GlobalGATwoPositivePolynomialData
public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveTDLowPolynomial
public import SquaresInCircles.Eight.TableFree.PolynomialCertificates

/-!
# Four complete low-angle A-endpoint polynomial bounds

The single-negative numerator retains its right-endpoint value.
The mixed numerator uses one completed Chebyshev square; the two
separated alternatives use centered coefficient norms.  These are
exact rational statements on the whole interval [0,1/6].
Uncompiled source draft; the kernel reductions have not been run.
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.TableFree.GlobalGA.TwoPositive.Certificate

open Polynomial WholeIntervalPolynomial WholeIntervalPolynomial.Certificate
open PositiveTD.Certificate (L)

def lowMixedCoefficients : ℕ→ℚ := coefficient 24 (centered 0 L lowPM)
def lowSHCentered : ℚ[X] := DirectedPowerBounds.shift (1/12) lowPSH
def lowSGCentered : ℚ[X] := DirectedPowerBounds.shift (1/12) lowPSG

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

/-! ## Integer representations of the low polynomials

Each polynomial of the low numerators is mirrored by a scaled integer list
(`PolynomialCertificates`); the kernel evaluates the lists. -/

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

private def sNum3 (A P0 P1 P2 r0 r1 r2 : Scaled) : Scaled :=
  (r46_red ((((Scaled.const 2).mul A).mul r0).mul r1 |>.mul r2)).sub
    ((Scaled.const PositiveTD.Certificate.Rbar).mul
      (r46_red ((r46_red ((r46_red (((P0.add (r0.pow 2)).mul r1).mul r2)).add
        (r46_red (((P1.add (r1.pow 2)).mul r0).mul r2)))).add
        (r46_red (((P2.add (r2.pow 2)).mul r0).mul r1)))))
private theorem rNum3 {A P0 P1 P2 r0 r1 r2 : Scaled} {a p0 p1 p2 q0 q1 q2 : ℚ[X]}
    (hA : A.Rep a) (h0 : P0.Rep p0) (h1 : P1.Rep p1) (h2 : P2.Rep p2)
    (g0 : r0.Rep q0) (g1 : r1.Rep q1) (g2 : r2.Rep q2) :
    (sNum3 A P0 P1 P2 r0 r1 r2).Rep (PositiveTD.Certificate.num3 a p0 p1 p2 q0 q1 q2) :=
  (r46_rep_red (((((Scaled.rep_const _).mul hA).mul g0).mul g1).mul g2)).sub
    ((Scaled.rep_const _).mul
      (r46_rep_red ((r46_rep_red ((r46_rep_red (((h0.add (g0.pow 2)).mul g1).mul g2)).add
        (r46_rep_red (((h1.add (g1.pow 2)).mul g0).mul g2)))).add
        (r46_rep_red (((h2.add (g2.pow 2)).mul g0).mul g1)))))

private def sD : Scaled := Scaled.var.sub (Scaled.const (83/500))
private theorem rD : sD.Rep (X-C (83/500)) := Scaled.rep_var.sub (Scaled.rep_const _)
private def sLK : Scaled := r46_red (((Scaled.const (84/125)).sub ((Scaled.const (1/5)).mul sD)).add
  ((Scaled.const (5/2)).mul (sD.pow 2)))
private theorem rLK : sLK.Rep PositiveTD.Certificate.lowK := r46_rep_red (((Scaled.rep_const _).sub ((Scaled.rep_const _).mul rD)).add ((Scaled.rep_const _).mul (rD.pow 2)))
private def sLL : Scaled := r46_red ((((Scaled.const (101/100)).sub ((Scaled.const (5/2)).mul sD)).add
  ((Scaled.const 6).mul (sD.pow 2))).add ((Scaled.const 48).mul (sD.pow 3)))
private theorem rLL : sLL.Rep PositiveTD.Certificate.lowL := r46_rep_red ((((Scaled.rep_const _).sub ((Scaled.rep_const _).mul rD)).add
    ((Scaled.rep_const _).mul (rD.pow 2))).add ((Scaled.rep_const _).mul (rD.pow 3)))
private def sLC : Scaled := r46_red (((Scaled.const (1043/1000)).sub ((Scaled.const (21/5)).mul sD)).add
  ((Scaled.const 8).mul (sD.pow 2)))
private theorem rLC : sLC.Rep PositiveTD.Certificate.lowC := r46_rep_red (((Scaled.rep_const _).sub ((Scaled.rep_const _).mul rD)).add ((Scaled.rep_const _).mul (rD.pow 2)))

private theorem r46_ch : PositiveTD.Certificate.ch=3964941898733393/5184000000000000 := by
  simp only [PositiveTD.Certificate.ch,PositiveTD.Certificate.C10,PositiveTD.Certificate.C4,
    PositiveTD.Certificate.h,eval_sub,eval_add,eval_mul,eval_pow,eval_C,eval_X,eval_one]
  norm_num
private theorem r46_Ch : PositiveTD.Certificate.Ch=52337233065258114343/68428800000000000000 := by
  simp only [PositiveTD.Certificate.Ch,PositiveTD.Certificate.C12,PositiveTD.Certificate.C10,
    PositiveTD.Certificate.C4,PositiveTD.Certificate.h,eval_sub,eval_add,eval_mul,eval_pow,eval_C,
    eval_X,eval_one]
  norm_num
private theorem r46_sh : PositiveTD.Certificate.sh=367358693969535751/570240000000000000 := by
  simp only [PositiveTD.Certificate.sh,PositiveTD.Certificate.S11,PositiveTD.Certificate.S9,
    PositiveTD.Certificate.S5,PositiveTD.Certificate.h,eval_sub,eval_add,eval_mul,eval_pow,eval_C,
    eval_X]
  norm_num

private def sLJ : Scaled := r46_red (((Scaled.const (1/2)).mul (sC10.sub (Scaled.ofNat 1))).add
  ((Scaled.const (1/2-abar)).mul sS9))
private theorem rLJ : sLJ.Rep lowJ := r46_rep_red (((Scaled.rep_const _).mul (rC10.sub Scaled.rep_one)).add ((Scaled.rep_const _).mul rS9))
private def sLA : Scaled := r46_red (((((((Scaled.const 2).mul sLK).add ((Scaled.const 3).mul sLL)).add
  ((Scaled.const (5/2)).mul sLC)).add (Scaled.const (5/2))).sub
  (((Scaled.ofNat 1).add sLC).mul (Scaled.const PositiveTD.Certificate.cbar))).add (sLL.mul sLJ))
private theorem rLA : sLA.Rep lowA := r46_rep_red (((((((Scaled.rep_const _).mul rLK).add ((Scaled.rep_const _).mul rLL)).add
    ((Scaled.rep_const _).mul rLC)).add (Scaled.rep_const _)).sub
    ((Scaled.rep_one.add rLC).mul (Scaled.rep_const _))).add (rLL.mul rLJ))
private def sLPH : Scaled := r46_red (
  ((Scaled.ofNat 1).add (sLK.pow 2)).sub (((Scaled.const 2).mul sLK).mul sS11))
private theorem rLPH : sLPH.Rep lowPH := r46_rep_red ((Scaled.rep_one.add (rLK.pow 2)).sub (((Scaled.rep_const _).mul rLK).mul rS11))
private def sLPG : Scaled := r46_red ((sLK.pow 2).add (sLL.pow 2))
private theorem rLPG : sLPG.Rep lowPG := r46_rep_red ((rLK.pow 2).add (rLL.pow 2))
private def sLPB : Scaled := r46_red ((sLC.pow 2).add (sLL.pow 2))
private theorem rLPB : sLPB.Rep lowPB := r46_rep_red ((rLC.pow 2).add (rLL.pow 2))
private def sLRH : Scaled := r46_red (((Scaled.const (89/100)).mul ((Scaled.ofNat 1).sub
    ((Scaled.const (1/2)).mul (Scaled.var.pow 2)))).add
  ((Scaled.const (57/125)).mul ((sLK.sub Scaled.var).add
    ((Scaled.const (1/6)).mul (Scaled.var.pow 3)))))
private theorem rLRH : sLRH.Rep lowRH := r46_rep_red (((Scaled.rep_const _).mul (Scaled.rep_one.sub
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 2)))).add
    ((Scaled.rep_const _).mul ((rLK.sub Scaled.rep_var).add
      ((Scaled.rep_const _).mul (Scaled.rep_var.pow 3)))))
private def sLRG : Scaled := r46_red (((Scaled.const (11/20)).mul sLK).add ((Scaled.const (167/200)).mul sLL))
private theorem rLRG : sLRG.Rep lowRG := r46_rep_red (((Scaled.rep_const _).mul rLK).add ((Scaled.rep_const _).mul rLL))
private def sLRB : Scaled := r46_red (
  ((Scaled.const (729/1000)).mul sLC).add ((Scaled.const (1369/2000)).mul sLL))
private theorem rLRB : sLRB.Rep lowRB := r46_rep_red (((Scaled.rep_const _).mul rLC).add ((Scaled.rep_const _).mul rLL))
private def sLP : Scaled := r46_red (
  sNum3 ((sLA.add sC10).sub (Scaled.ofNat 1)) sLPH sLPG sLPB sLRH sLRG sLRB)
private theorem rLP : sLP.Rep lowP := r46_rep_red (rNum3 ((rLA.add rC10).sub Scaled.rep_one) rLPH rLPG rLPB rLRH rLRG rLRB)

private def sChSh : Scaled := ⟨[803502302830208981],570240000000000000⟩
private theorem rChSh : sChSh.Rep (C (PositiveTD.Certificate.ch+PositiveTD.Certificate.sh)) :=
  r46_rep_frac (by norm_num) (by rw [r46_ch,r46_sh]; norm_num)
private def sCh_sh : Scaled := ⟨[8254189788913824223],68428800000000000000⟩
private theorem rCh_sh : sCh_sh.Rep (C (PositiveTD.Certificate.Ch-PositiveTD.Certificate.sh)) :=
  r46_rep_frac (by norm_num) (by rw [r46_Ch,r46_sh]; norm_num)
private def sCh : Scaled := ⟨[3964941898733393],5184000000000000⟩
private theorem rCh : sCh.Rep (C PositiveTD.Certificate.ch) :=
  r46_rep_frac (by norm_num) (by rw [r46_ch]; norm_num)
private def sTwoSh : Scaled := ⟨[367358693969535751],285120000000000000⟩
private theorem rTwoSh : sTwoSh.Rep (C (2*PositiveTD.Certificate.sh)) :=
  r46_rep_frac (by norm_num) (by rw [r46_sh]; norm_num)
private def sChM1 : Scaled := ⟨[-1219058101266607],5184000000000000⟩
private theorem rChM1 : sChM1.Rep (C (PositiveTD.Certificate.ch-1)) :=
  r46_rep_frac (by norm_num) (by rw [r46_ch]; norm_num)

private def sLMC : Scaled := r46_red ((sLK.mul (((sChSh.mul sC10).sub (sCh_sh.mul sS9)).sub (Scaled.ofNat 1))).add
  (sLL.mul (sCh.sub sC12)))
private theorem rLMC : sLMC.Rep lowMixedCharge := r46_rep_red ((rLK.mul (((rChSh.mul rC10).sub (rCh_sh.mul rS9)).sub Scaled.rep_one)).add (rLL.mul (rCh.sub rC12)))
private def sLDen : Scaled := r46_red ((((Scaled.const 2).mul sLRH).mul sLRG).mul sLRB)
private theorem rLDen : sLDen.Rep lowDen := r46_rep_red ((((Scaled.rep_const _).mul rLRH).mul rLRG).mul rLRB)
private def sLPM : Scaled := r46_red (sLP.add (sLDen.mul sLMC))
private theorem rLPM : sLPM.Rep lowPM := r46_rep_red (rLP.add (rLDen.mul rLMC))
private def sLAstar : Scaled := r46_red (
  sLA.sub (((Scaled.const (109/200)).mul sLC).mul ((Scaled.const PositiveTD.Certificate.h).sub Scaled.var)))
private theorem rLAstar : sLAstar.Rep lowAstar := r46_rep_red (rLA.sub (((Scaled.rep_const _).mul rLC).mul ((Scaled.rep_const _).sub Scaled.rep_var)))
private def sLPHh : Scaled := r46_red (((Scaled.ofNat 1).add (sLK.pow 2)).sub (sTwoSh.mul sLK))
private theorem rLPHh : sLPHh.Rep lowPHh := r46_rep_red ((Scaled.rep_one.add (rLK.pow 2)).sub (rTwoSh.mul rLK))
private def sLPH0 : Scaled := r46_red ((Scaled.ofNat 1).add (sLK.pow 2))
private theorem rLPH0 : sLPH0.Rep lowPH0 := r46_rep_red (Scaled.rep_one.add (rLK.pow 2))
private def sLPGh : Scaled := r46_red (((sLK.pow 2).add (sLL.pow 2)).sub ((sTwoSh.mul sLK).mul sLL))
private theorem rLPGh : sLPGh.Rep lowPGh := r46_rep_red (((rLK.pow 2).add (rLL.pow 2)).sub ((rTwoSh.mul rLK).mul rLL))
private def sLPSH : Scaled := r46_red (
  sNum3 (sLAstar.add sChM1) sLPHh sLPG sLPB (Scaled.const (77/100)) sLRG sLRB)
private theorem rLPSH : sLPSH.Rep lowPSH := r46_rep_red (rNum3 (rLAstar.add rChM1) rLPHh rLPG rLPB (Scaled.rep_const _) rLRG rLRB)
private def sLPSG : Scaled := r46_red (
  sNum3 (sLAstar.add (sLL.mul sChM1)) sLPH0 sLPGh sLPB
    ((Scaled.const (41/50)).add ((Scaled.const (143/250)).mul sLK))
    ((Scaled.const (153/200)).mul sLL) sLRB)
private theorem rLPSG : sLPSG.Rep lowPSG := r46_rep_red (rNum3 (rLAstar.add (rLL.mul rChM1)) rLPH0 rLPGh rLPB
    ((Scaled.rep_const _).add ((Scaled.rep_const _).mul rLK))
    ((Scaled.rep_const _).mul rLL) rLRB)

/-- The centered numerator on `[0,1/6]`, its quotient by `1-X`, and the remainder. -/
private def cLP : Scaled := r46_red (sLP.center 1 12 1 1)
private theorem rcLP : cLP.Rep (centered 0 L lowP) :=
  r46_rep_red (rLP.centered 1 12 1 1 (by norm_num) (by norm_num [L]) (by norm_num [L]))
private def cLQ : Scaled := r46_red ⟨smul (-12) (r46_synth 1 cLP.l).1,cLP.s*1⟩
private def cLPM : Scaled := r46_red (sLPM.center 1 12 1 1)
private theorem rcLPM : cLPM.Rep (centered 0 L lowPM) :=
  r46_rep_red (rLPM.centered 1 12 1 1 (by norm_num) (by norm_num [L]) (by norm_num [L]))

private theorem r46_shift_eq (a : ℚ) (p : ℚ[X]) :
    DirectedPowerBounds.shift a p=centered (a-1) (a+1) p := by
  simp only [DirectedPowerBounds.shift,centered,affine]
  congr 1
  rw [show (a-1+(a+1))/2=a by ring,show (a+1-(a-1))/2=1 by ring,map_one,one_mul]

private def cLSH : Scaled := r46_red (sLPSH.center 1 12 1 12)
private theorem rcLSH : cLSH.Rep lowSHCentered := by
  rw [lowSHCentered,r46_shift_eq]
  exact r46_rep_red (rLPSH.centered 1 12 1 12 (by norm_num) (by norm_num) (by norm_num))
private def cLSG : Scaled := r46_red (sLPSG.center 1 12 1 12)
private theorem rcLSG : cLSG.Rep lowSGCentered := by
  rw [lowSGCentered,r46_shift_eq]
  exact r46_rep_red (rLPSG.centered 1 12 1 12 (by norm_num) (by norm_num) (by norm_num))

theorem low_quotient_identity :
    lowP=C (lowP.eval L)+(C L-X)*lowQuotient := by
  have h := (mul_divByMonic_eq_iff_isRoot (p:=lowP-C (lowP.eval L)) (a:=L)).2
    (by simp [IsRoot])
  rw [lowQuotient]
  linear_combination -h

private theorem r46_low_centered :
    centered 0 L lowP=C (lowP.eval L)+C (-1/12)*(X-C ((1:ℤ):ℚ))*centered 0 L lowQuotient := by
  have hlin : (C L-X).comp (affine 0 L)=C (-1/12)*(X-C ((1:ℤ):ℚ)) := by
    simp only [affine,sub_comp,C_comp,X_comp,L,Int.cast_one,map_one]
    rw [show ((0:ℚ)+1/6)/2=1/12 by norm_num,show ((1:ℚ)/6-0)/2=1/12 by norm_num,
      show (1/6:ℚ)=1/12+1/12 by norm_num,show (-1/12:ℚ)=-(1/12) by norm_num,map_add,map_neg]
    ring
  conv_lhs => rw [low_quotient_identity]
  rw [centered,add_comp,mul_comp,C_comp,hlin]
  rfl

/-- All integer facts about the single-negative numerator, in one kernel reduction. -/
private theorem r46_LP_facts :
    WholeIntervalPolynomial.Certificate.mul [-1,1] (r46_synth 1 cLP.l).1=
      WholeIntervalPolynomial.Certificate.add cLP.l [-(r46_synth 1 cLP.l).2] ∧
    cLP.s≠0 ∧ (127:ℤ)*(cLP.s:ℤ)<((10000:ℕ):ℤ)*r46_evalZ 1 cLP.l ∧
    cLQ.s≠0 ∧ cLQ.l.length≤21+1 ∧
    (21:ℤ)*((cLQ.s*2^cLQ.l.length : ℕ):ℤ)<
      2*((25:ℕ):ℤ)*lowerZ 21 (fun j => (chebList cLQ.l).getD j 0) := by
  decide +kernel

private theorem rcLQ : cLQ.Rep (centered 0 L lowQuotient) :=
  r46_rep_red (r46_rep_div rcLP r46_low_centered r46_LP_facts.1 (by norm_num))

theorem low_quotient_expansion :
    centered 0 L lowQuotient=expansion 21 (centered 0 L lowQuotient) :=
  rcLQ.eq_expansion r46_LP_facts.2.2.2.1 r46_LP_facts.2.2.2.2.1

theorem low_quotient_reserve :
    (127/10000:ℚ)<lowP.eval L ∧ (21/25:ℚ)<lowerOn 21 0 L lowQuotient := by
  constructor
  · have hv := r46_value_lt rcLP r46_LP_facts.2.1 1 (ρ:=127/10000) (num:=127) (den:=10000)
      (by norm_num) (by norm_num) r46_LP_facts.2.2.1
    rwa [r46_centered_eval,Int.cast_one,show ((0:ℚ)+L)/2+(L-0)/2*1=L by ring] at hv
  · exact r46_lowerOn_lt rcLQ r46_LP_facts.2.2.2.1 r46_LP_facts.2.2.2.2.1 (num:=21) (den:=25)
      (by norm_num) (by norm_num) r46_LP_facts.2.2.2.2.2

theorem lowP_positive {z : ℝ} (hz : z∈Set.Icc 0 (1/6:ℝ)) :
    0<aeval z lowP := by
  have hz' : z∈Set.Icc ((0:ℚ):ℝ) ((L:ℚ):ℝ) := by
    simp only [L,Rat.cast_zero,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat]
    exact hz
  have hq := positive_on_interval (by norm_num [L] : (0:ℚ)<L)
    low_quotient_expansion low_quotient_reserve.2 hz'
  have hc : ((127/10000:ℚ):ℝ)<((lowP.eval L:ℚ):ℝ) := Rat.cast_lt.mpr low_quotient_reserve.1
  rw [show ((127/10000:ℚ):ℝ)=127/10000 by norm_num] at hc
  have he := congrArg (fun f : ℚ[X] => aeval z f) low_quotient_identity
  simp only [map_add,map_mul,map_sub,aeval_C,aeval_X,eq_ratCast] at he
  have hp : 0≤((L:ℝ)-z)*aeval z lowQuotient :=
    mul_nonneg (by simp only [L]; push_cast; linarith [hz.2]) (by push_cast at hq; linarith)
  linarith

/-- All integer facts about the mixed numerator. -/
private theorem r46_LPM_facts :
    cLPM.s≠0 ∧ cLPM.l.length≤24+1 ∧ 0<(chebList cLPM.l).getD 2 0 ∧
    (93:ℤ)*(8*(chebList cLPM.l).getD 2 0*((cLPM.s*2^cLPM.l.length : ℕ):ℤ))<
      2*((1000:ℕ):ℤ)*(8*(chebList cLPM.l).getD 2 0*((chebList cLPM.l).getD 0 0-
        (chebList cLPM.l).getD 2 0-∑ j : Fin 22,|(chebList cLPM.l).getD (j.val+3) 0|)-
        ((chebList cLPM.l).getD 1 0)^2) := by
  decide +kernel

theorem low_mixed_identity :
    centered 0 L lowPM=C (lowMixedCoefficients 0-lowMixedCoefficients 2)+
      C (lowMixedCoefficients 1)*X+C (2*lowMixedCoefficients 2)*X^2+
        ChebyshevLeadingBounds.tail lowMixedCoefficients 3 22 := by
  rw [rcLPM.eq_expansion (D:=24) r46_LPM_facts.1 r46_LPM_facts.2.1]
  exact r46_series_quadratic lowMixedCoefficients 22

theorem low_mixed_reserve :
    0<lowMixedCoefficients 2 ∧
      (93/1000:ℚ)<ChebyshevLeadingBounds.quadraticReserve lowMixedCoefficients 22 :=
  r46_quadratic rcLPM (D:=24) r46_LPM_facts.1 r46_LPM_facts.2.1 22 (num:=93) (den:=1000)
    (by norm_num) (by norm_num) r46_LPM_facts.2.2.1 r46_LPM_facts.2.2.2

theorem lowPM_positive {z : ℝ} (hz : z∈Set.Icc 0 (1/6:ℝ)) :
    0<aeval z lowPM := by
  have hz' : z∈Set.Icc ((0:ℚ):ℝ) ((L:ℚ):ℝ) := by
    simp only [L,Rat.cast_zero,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat]
    exact hz
  have hh := ChebyshevLeadingBounds.quadratic_on_interval
    (by norm_num [L] : (0:ℚ)<L) low_mixed_identity low_mixed_reserve.1 hz'
  have hr : ((93/1000:ℚ):ℝ)<
      (ChebyshevLeadingBounds.quadraticReserve lowMixedCoefficients 22:ℝ) :=
    Rat.cast_lt.mpr low_mixed_reserve.2
  rw [show ((93/1000:ℚ):ℝ)=93/1000 by norm_num] at hr
  linarith

/-- All integer facts about the two separated numerators. -/
private theorem r46_LS_facts :
    cLSH.s≠0 ∧ cLSH.l.length-1≤19 ∧
    (9:ℤ)*((cLSH.s*12^19 : ℕ):ℤ)<((50:ℕ):ℤ)*(cLSH.l.getD 0 0*((12:ℕ):ℤ)^19-
      ∑ j : Fin 19,|cLSH.l.getD (j.val+1) 0| * ((1:ℕ):ℤ)^(j.val+1)*((12:ℕ):ℤ)^(19-1-j.val)) ∧
    cLSG.s≠0 ∧ cLSG.l.length-1≤21 ∧
    (43:ℤ)*((cLSG.s*12^21 : ℕ):ℤ)<((1000:ℕ):ℤ)*(cLSG.l.getD 0 0*((12:ℕ):ℤ)^21-
      ∑ j : Fin 21,|cLSG.l.getD (j.val+1) 0| * ((1:ℕ):ℤ)^(j.val+1)*((12:ℕ):ℤ)^(21-1-j.val)) := by
  decide +kernel

theorem low_separated_identities :
    lowSHCentered=C (lowSHCentered.coeff 0)+PowerTailBounds.tail lowSHCentered 1 19 ∧
    lowSGCentered=C (lowSGCentered.coeff 0)+PowerTailBounds.tail lowSGCentered 1 21 :=
  ⟨r46_eq_tail ((rcLSH.natDegree_le r46_LS_facts.1).trans r46_LS_facts.2.1),
    r46_eq_tail ((rcLSG.natDegree_le r46_LS_facts.2.2.2.1).trans r46_LS_facts.2.2.2.2.1)⟩

theorem low_separated_reserves :
    (9/50:ℚ)<lowSHCentered.coeff 0-PowerTailBounds.norm lowSHCentered 1 19 (1/12) ∧
    (43/1000:ℚ)<lowSGCentered.coeff 0-PowerTailBounds.norm lowSGCentered 1 21 (1/12) :=
  ⟨r46_power rcLSH r46_LS_facts.1 19 (rn:=1) (rd:=12) (by norm_num) (by norm_num)
      (num:=9) (den:=50) (by norm_num) (by norm_num) r46_LS_facts.2.2.1,
    r46_power rcLSG r46_LS_facts.2.2.2.1 21 (rn:=1) (rd:=12) (by norm_num) (by norm_num)
      (num:=43) (den:=1000) (by norm_num) (by norm_num) r46_LS_facts.2.2.2.2.2⟩

theorem lowPSH_positive {z : ℝ} (hz : z∈Set.Icc 0 (1/6:ℝ)) :
    0<aeval z lowPSH := by
  have hx : |z-1/12|≤((1/12:ℚ):ℝ) := by
    rw [abs_le]
    push_cast
    exact ⟨by linarith [hz.1],by linarith [hz.2]⟩
  have hh := DirectedPowerBounds.constant_lower low_separated_identities.1 hx
  have hr : ((9/50:ℚ):ℝ)<((lowSHCentered.coeff 0-
      PowerTailBounds.norm lowSHCentered 1 19 (1/12):ℚ):ℝ) :=
    Rat.cast_lt.mpr low_separated_reserves.1
  rw [show ((9/50:ℚ):ℝ)=9/50 by norm_num,Rat.cast_sub] at hr
  have he : aeval (z-1/12) lowSHCentered=aeval z lowPSH := by
    simp only [lowSHCentered,DirectedPowerBounds.shift_eval]
    push_cast
    ring_nf
  rw [he] at hh
  linarith

theorem lowPSG_positive {z : ℝ} (hz : z∈Set.Icc 0 (1/6:ℝ)) :
    0<aeval z lowPSG := by
  have hx : |z-1/12|≤((1/12:ℚ):ℝ) := by
    rw [abs_le]
    push_cast
    exact ⟨by linarith [hz.1],by linarith [hz.2]⟩
  have hh := DirectedPowerBounds.constant_lower low_separated_identities.2 hx
  have hr : ((43/1000:ℚ):ℝ)<((lowSGCentered.coeff 0-
      PowerTailBounds.norm lowSGCentered 1 21 (1/12):ℚ):ℝ) :=
    Rat.cast_lt.mpr low_separated_reserves.2
  rw [show ((43/1000:ℚ):ℝ)=43/1000 by norm_num,Rat.cast_sub] at hr
  have he : aeval (z-1/12) lowSGCentered=aeval z lowPSG := by
    simp only [lowSGCentered,DirectedPowerBounds.shift_eval]
    push_cast
    ring_nf
  rw [he] at hh
  linarith

theorem low_masses_positive {z : ℝ} (hz : z∈Set.Icc 0 (1/6:ℝ)) :
    0<aeval z lowRH ∧ 0<aeval z lowRG ∧ 0<aeval z lowRB := by
  have hh := PositiveTD.Certificate.low_masses_positive hz
  have hd := PositiveTD.Explicit.low_domain hz
  have hC : 0<aeval z PositiveTD.Certificate.lowC := by
    rw [PositiveTD.Certificate.lowC_eval]
    linarith [hd.1.1,hd.2.2.1.1]
  have hL : 0<aeval z PositiveTD.Certificate.lowL := by
    rw [PositiveTD.Certificate.lowL_eval]
    linarith [hd.1.1,hd.2.1.1]
  refine ⟨?_,?_,?_⟩
  · simpa only [lowRH,PositiveTD.Certificate.lowRH] using hh.1
  · simpa only [lowRG,PositiveTD.Certificate.lowRG] using hh.2.1
  · simp only [lowRB,map_add,map_mul,aeval_C,eq_ratCast]
    push_cast
    linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.TwoPositive.Certificate

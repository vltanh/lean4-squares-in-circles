module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Rat.Star
public import SquaresInCircles.Eight.Owners.ChebyshevLeadingBounds
public import SquaresInCircles.Eight.Owners.GA.Joint.NegativeAETD2PolynomialData

/-!
# Eight squares: the six exact whole-interval endpoint certificates

The low and middle rows retain a quadratic leading part.
The full-D rows retain the prescribed fifth and third powers, charging
only adverse higher coefficients on their nonnegative interval.

The kernel evaluates integer coefficient lists that mirror the polynomials. The numerator
and the shift are one integer product or evaluation read back in a large base (Kronecker
substitution).
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.JointNegativeAETD2.Certificate
open Polynomial PowerTailBounds DirectedPowerBounds
open WholeIntervalPolynomial.Certificate (Scaled toPoly)


/-! ### Kernel certificates: gcd normalization of scaled lists -/

private def r67_gcd (s : ℕ) : List ℤ → ℕ
  | [] => s
  | a :: l => Nat.gcd a.natAbs (r67_gcd s l)

private theorem r67_gcd_dvd (s : ℕ) : ∀ l : List ℤ,
    r67_gcd s l ∣ s ∧ ∀ a ∈ l,((r67_gcd s l : ℕ):ℤ) ∣ a
  | [] => by simp [r67_gcd]
  | a :: l => by
    obtain ⟨h1,h2⟩ := r67_gcd_dvd s l
    refine ⟨(Nat.gcd_dvd_right _ _).trans h1,?_⟩
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact Int.natCast_dvd.mpr (Nat.gcd_dvd_left _ _)
    · exact (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right _ _)).trans (h2 b hb)

private theorem r67_smul_div (g : ℤ) : ∀ l : List ℤ,(∀ a ∈ l,g ∣ a) →
    WholeIntervalPolynomial.Certificate.smul g (l.map (fun a => a/g))=l
  | [],_ => rfl
  | a :: l,h => by
    simp only [List.map_cons,WholeIntervalPolynomial.Certificate.smul]
    rw [Int.mul_ediv_cancel' (h a List.mem_cons_self),
      r67_smul_div g l (fun b hb => h b (List.mem_cons_of_mem a hb))]

private theorem r67_toPoly_zero : ∀ l : List ℤ,toPoly (l.map (fun _ => (0:ℤ)))=0
  | [] => rfl
  | a :: l => by
    simp only [List.map_cons,toPoly,r67_toPoly_zero l,Int.cast_zero,map_zero,mul_zero,add_zero]

/-- Division of a scaled list by the gcd of its entries and its scale. -/
private def r67_red (c : Scaled) : Scaled :=
  ⟨c.l.map (fun a => a/((r67_gcd c.s c.l : ℕ):ℤ)),c.s/r67_gcd c.s c.l⟩

private theorem r67_rep_red {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) : (r67_red c).Rep p := by
  obtain ⟨h1,h2⟩ := r67_gcd_dvd c.s c.l
  set g := r67_gcd c.s c.l with hg
  have hl := r67_smul_div (g:ℤ) c.l h2
  unfold Scaled.Rep at *
  rw [← hl,WholeIntervalPolynomial.Certificate.toPoly_smul] at hc
  obtain ⟨k,hk⟩ := h1
  simp only [r67_red,← hg]
  rcases Nat.eq_zero_or_pos g with h0 | hpos
  · have hs : c.s=0 := by rw [hk,h0,zero_mul]
    rw [h0,hs]
    simp only [Nat.cast_zero,Int.ediv_zero,Nat.zero_div,map_zero,zero_mul]
    exact r67_toPoly_zero _
  · have hg0 : (g:ℚ)≠0 := by exact_mod_cast hpos.ne'
    rw [hk,Nat.mul_div_cancel_left k hpos]
    rw [hk] at hc
    push_cast at hc
    exact mul_left_cancel₀ (show C (g:ℚ)≠0 from C_ne_zero.mpr hg0)
      (hc.trans (by rw [map_mul,mul_assoc]))

/-! ### Shifts, splittings and coefficient sums -/

/-- A polynomial of degree below `start+count` is its head plus its power tail. -/
private theorem r67_split (p : ℚ[X]) (start count : ℕ) (h : p.natDegree<start+count) :
    p=(∑ i ∈ Finset.range start,C (p.coeff i)*X^i)+PowerTailBounds.tail p start count := by
  conv_lhs => rw [p.as_sum_range_C_mul_X_pow' h,Finset.sum_range_add]
  congr 1
  rw [PowerTailBounds.tail,Fin.sum_univ_eq_sum_range (fun j => C (p.coeff (j+start))*X^(j+start))]
  exact Finset.sum_congr rfl fun j _ => by rw [add_comm start j]

private theorem r67_natDegree_lt {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) (hs : c.s≠0) {n : ℕ}
    (hl : c.l.length≤n) (hn : 0<n) : p.natDegree<n :=
  lt_of_le_of_lt (hc.natDegree_le hs) (by omega)

/-- Horner form of `∑ j<k, |a_j| num^j den^(k-j)`. -/
private def r67_hsum (num den : ℕ) : List ℤ → ℕ → ℤ
  | [],_ => 0
  | _ :: _,0 => 0
  | a :: l,k+1 => |a| *((den^(k+1):ℕ):ℤ)+(num:ℤ)*r67_hsum num den l k

private theorem r67_hsum_eq (num den : ℕ) : ∀ (l : List ℤ) (k : ℕ),
    (r67_hsum num den l k:ℚ)=∑ j : Fin k,|(l.getD j.val 0:ℚ)| *(num:ℚ)^j.val*(den:ℚ)^(k-j.val)
  | [],k => by simp [r67_hsum]
  | a :: l,0 => by simp [r67_hsum]
  | a :: l,k+1 => by
    rw [Fin.sum_univ_succ]
    simp only [r67_hsum,Fin.val_zero,Fin.val_succ,List.getD_cons_zero,List.getD_cons_succ,
      pow_zero,mul_one,Nat.sub_zero]
    push_cast
    rw [r67_hsum_eq num den l k,Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

private theorem r67_getD_drop (l : List ℤ) (s j : ℕ) : (l.drop s).getD j 0=l.getD (j+s) 0 := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_drop,add_comm s j]

private theorem r67_wsum_eq {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) (hs : c.s≠0)
    (start e count num den : ℕ) (hden : den≠0) :
    ∑ j : Fin count,|p.coeff (j.val+start)| *((num:ℚ)/den)^(j.val+e)=
      ((num:ℚ)^e*(r67_hsum num den (c.l.drop start) count:ℚ))/(c.s*(den:ℚ)^(count+e)) := by
  rw [r67_hsum_eq,Finset.mul_sum,Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hs' : (0:ℚ)<c.s := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hd : (den:ℚ)≠0 := by exact_mod_cast hden
  rw [hc.coeff hs,r67_getD_drop,abs_div,abs_of_pos hs',div_pow,
    show (den:ℚ)^(count+e)=den^(j.val+e)*den^(count-j.val) by
      rw [← pow_add]; congr 1; omega,pow_add]
  field_simp

private theorem r67_norm_eq {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) (hs : c.s≠0)
    (start count num den : ℕ) (hden : den≠0) :
    PowerTailBounds.norm p start count ((num:ℚ)/den)=
      (((num*r67_hsum num den (c.l.drop start) count:ℤ)):ℚ)/(c.s*(den:ℚ)^(count+1)) := by
  rw [PowerTailBounds.norm,r67_wsum_eq hc hs start 1 count num den hden]
  push_cast
  ring

/-! ### Rational comparisons from integer ones -/

private theorem r67_gt {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) (hs : c.s≠0) (i : ℕ)
    {Z : ℤ} {D : ℕ} (hD : 0<D) {a : ℤ} {b : ℕ} (hb : 0<b)
    (h : a*((c.s:ℤ)*D)<(c.l.getD i 0*D-Z)*b) :
    (a:ℚ)/b<p.coeff i-(Z:ℚ)/(c.s*D) := by
  have hs' : (0:ℚ)<c.s := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hD' : (0:ℚ)<D := by exact_mod_cast hD
  have hb' : (0:ℚ)<b := by exact_mod_cast hb
  have e : p.coeff i-(Z:ℚ)/(c.s*D)=(((c.l.getD i 0*D-Z:ℤ)):ℚ)/((c.s:ℚ)*D) := by
    rw [hc.coeff hs]; push_cast; field_simp
  rw [e,div_lt_div_iff₀ hb' (by positivity)]
  exact_mod_cast h

private theorem r67_coeff_gt {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) (hs : c.s≠0) (i : ℕ)
    {a : ℤ} {b : ℕ} (hb : 0<b) (h : a*c.s<c.l.getD i 0*b) : (a:ℚ)/b<p.coeff i := by
  have hh := r67_gt hc hs i (Z:=0) (D:=1) one_pos hb (by simpa using h)
  simpa using hh

private theorem r67_coeff_lt {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) (hs : c.s≠0) (i : ℕ)
    {a : ℤ} {b : ℕ} (hb : 0<b) (h : c.l.getD i 0*b<a*c.s) : p.coeff i<(a:ℚ)/b := by
  have hs' : (0:ℚ)<c.s := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hb' : (0:ℚ)<b := by exact_mod_cast hb
  rw [hc.coeff hs,div_lt_div_iff₀ hs' hb']
  exact_mod_cast h

private theorem r67_coeff_abs_lt {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) (hs : c.s≠0) (i : ℕ)
    {a : ℤ} {b : ℕ} (hb : 0<b) (h : |c.l.getD i 0| *b<a*c.s) : |p.coeff i|<(a:ℚ)/b := by
  have hs' : (0:ℚ)<c.s := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hb' : (0:ℚ)<b := by exact_mod_cast hb
  rw [hc.coeff hs,abs_div,abs_of_pos hs',div_lt_div_iff₀ hs' hb']
  exact_mod_cast h

/-- Composition with `(num/den) X`: the coefficient `a_i` becomes `a_i num^i den^(n-i)`. -/
private def r67_scale (c : Scaled) (num den : ℕ) : Scaled :=
  ⟨WholeIntervalPolynomial.Certificate.prescale num den (c.l.length-1) 0 c.l,
    c.s*den^(c.l.length-1)⟩

private theorem r67_scale_rep {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) (num den : ℕ)
    (hden : den≠0) : (r67_scale c num den).Rep (p.comp (C ((num:ℚ)/den)*X)) := by
  have h := WholeIntervalPolynomial.Certificate.toPoly_prescale (num:=num) hden
    (c.l.length-1) c.l 0 (by omega)
  simp only [pow_zero,one_mul,map_one] at h
  unfold Scaled.Rep at *
  simp only [r67_scale]
  rw [← h,hc,mul_comp,C_comp]
  push_cast
  rw [map_mul]
  ring

/-- The monomial `X^k`, as the list it would get by `Scaled.var.pow k`. -/
private def r67_mono (k : ℕ) : Scaled := ⟨List.replicate k 0++[1],1⟩
private theorem r67_mono_rep (k : ℕ) : (r67_mono k).Rep (X^k) := by
  unfold Scaled.Rep r67_mono
  simp only [Nat.cast_one,map_one,one_mul]
  induction k with
  | zero => simp [toPoly]
  | succ k ih =>
    rw [List.replicate_succ,List.cons_append,toPoly,ih,pow_succ]
    simp only [Int.cast_zero,map_zero,zero_add]
    ring

private def r67_S : Scaled := r67_red
  ((((((((Scaled.var.sub ((Scaled.const (1/6)).mul (r67_mono 3))).add
    ((Scaled.const (1/120)).mul (r67_mono 5))).sub
    ((Scaled.const (1/5040)).mul (r67_mono 7))).add
    ((Scaled.const (1/362880)).mul (r67_mono 9))).sub
    ((Scaled.const (1/39916800)).mul (r67_mono 11))).add
    ((Scaled.const (1/6227020800)).mul (r67_mono 13))).sub
    ((Scaled.const (1/1307674368000)).mul (r67_mono 15))))
private theorem r67_S_rep : r67_S.Rep PositiveScalarPolynomials.sine := r67_rep_red
  ((((((((Scaled.rep_var.sub ((Scaled.rep_const _).mul (r67_mono_rep 3))).add
    ((Scaled.rep_const _).mul (r67_mono_rep 5))).sub
    ((Scaled.rep_const _).mul (r67_mono_rep 7))).add
    ((Scaled.rep_const _).mul (r67_mono_rep 9))).sub
    ((Scaled.rep_const _).mul (r67_mono_rep 11))).add
    ((Scaled.rep_const _).mul (r67_mono_rep 13))).sub
    ((Scaled.rep_const _).mul (r67_mono_rep 15))))

private def r67_C : Scaled := r67_red
  (((((((((Scaled.ofNat 1).sub ((Scaled.const (1/2)).mul (r67_mono 2))).add
    ((Scaled.const (1/24)).mul (r67_mono 4))).sub
    ((Scaled.const (1/720)).mul (r67_mono 6))).add
    ((Scaled.const (1/40320)).mul (r67_mono 8))).sub
    ((Scaled.const (1/3628800)).mul (r67_mono 10))).add
    ((Scaled.const (1/479001600)).mul (r67_mono 12))).sub
    ((Scaled.const (1/87178291200)).mul (r67_mono 14))).add
    ((Scaled.const (1/20922789888000)).mul (r67_mono 16)))
private theorem r67_C_rep : r67_C.Rep PositiveScalarPolynomials.cosine := r67_rep_red
  ((((((((Scaled.rep_one.sub ((Scaled.rep_const _).mul (r67_mono_rep 2))).add
    ((Scaled.rep_const _).mul (r67_mono_rep 4))).sub
    ((Scaled.rep_const _).mul (r67_mono_rep 6))).add
    ((Scaled.rep_const _).mul (r67_mono_rep 8))).sub
    ((Scaled.rep_const _).mul (r67_mono_rep 10))).add
    ((Scaled.rep_const _).mul (r67_mono_rep 12))).sub
    ((Scaled.rep_const _).mul (r67_mono_rep 14))).add
    ((Scaled.rep_const _).mul (r67_mono_rep 16)))

/-- Horner form of `∑ j<k, max(-a_j,0) num^j den^(k-j)`. -/
private def r67_nhsum (num den : ℕ) : List ℤ → ℕ → ℤ
  | [],_ => 0
  | _ :: _,0 => 0
  | a :: l,k+1 => max (-a) 0*((den^(k+1):ℕ):ℤ)+(num:ℤ)*r67_nhsum num den l k

private theorem r67_nhsum_eq (num den : ℕ) : ∀ (l : List ℤ) (k : ℕ),
    (r67_nhsum num den l k:ℚ)=
      ∑ j : Fin k,max (-(l.getD j.val 0:ℚ)) 0*(num:ℚ)^j.val*(den:ℚ)^(k-j.val)
  | [],k => by simp [r67_nhsum]
  | a :: l,0 => by simp [r67_nhsum]
  | a :: l,k+1 => by
    rw [Fin.sum_univ_succ]
    simp only [r67_nhsum,Fin.val_zero,Fin.val_succ,List.getD_cons_zero,List.getD_cons_succ,
      pow_zero,mul_one,Nat.sub_zero]
    push_cast
    rw [r67_nhsum_eq num den l k,Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

private theorem r67_negNorm_eq {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) (hs : c.s≠0)
    (start count num den : ℕ) (hden : den≠0) :
    DirectedPowerBounds.negativeNorm p start count ((num:ℚ)/den)=
      (((num*r67_nhsum num den (c.l.drop start) count:ℤ)):ℚ)/(c.s*(den:ℚ)^(count+1)) := by
  unfold DirectedPowerBounds.negativeNorm
  push_cast
  rw [r67_nhsum_eq,Finset.mul_sum,Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hs' : (0:ℚ)<c.s := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hd : (den:ℚ)≠0 := by exact_mod_cast hden
  have hm : max (-((c.l.getD (j.val+start) 0:ℚ)/c.s)) 0=max (-(c.l.getD (j.val+start) 0:ℚ)) 0/c.s := by
    rw [← max_div_div_right hs'.le,zero_div,neg_div]
  rw [hc.coeff hs,r67_getD_drop,hm,div_pow,
    show (den:ℚ)^(count+1)=den^(j.val+1)*den^(count-j.val) by
      rw [← pow_add]; congr 1; omega,pow_succ]
  field_simp

/-! ### The numerators as scaled integer lists -/

private theorem r67_erase_prod (f : Fin 4 → ℚ[X]) :
    (∏ j ∈ Finset.univ.erase (0:Fin 4),f j)=f 1*f 2*f 3 ∧
    (∏ j ∈ Finset.univ.erase (1:Fin 4),f j)=f 0*f 2*f 3 ∧
    (∏ j ∈ Finset.univ.erase (2:Fin 4),f j)=f 0*f 1*f 3 ∧
    (∏ j ∈ Finset.univ.erase (3:Fin 4),f j)=f 0*f 1*f 2 := by
  have h0 : Finset.univ.erase (0:Fin 4)={1,2,3} := by decide
  have h1 : Finset.univ.erase (1:Fin 4)={0,2,3} := by decide
  have h2 : Finset.univ.erase (2:Fin 4)={0,1,3} := by decide
  have h3 : Finset.univ.erase (3:Fin 4)={0,1,2} := by decide
  refine ⟨?_,?_,?_,?_⟩
  · rw [h0,Finset.prod_insert (by decide),Finset.prod_insert (by decide),Finset.prod_singleton,
      mul_assoc]
  · rw [h1,Finset.prod_insert (by decide),Finset.prod_insert (by decide),Finset.prod_singleton,
      mul_assoc]
  · rw [h2,Finset.prod_insert (by decide),Finset.prod_insert (by decide),Finset.prod_singleton,
      mul_assoc]
  · rw [h3,Finset.prod_insert (by decide),Finset.prod_insert (by decide),Finset.prod_singleton,
      mul_assoc]

private theorem r67_numerator_eq (r : Row) (e : Endpoint) : numerator r e=
    C 2*H r e*(alpha r e 0*alpha r e 1*alpha r e 2*alpha r e 3)-C Rplus*
      (weight r e 0*(v r e 0+(alpha r e 0)^2)*(alpha r e 1*alpha r e 2*alpha r e 3)+
        weight r e 1*(v r e 1+(alpha r e 1)^2)*(alpha r e 0*alpha r e 2*alpha r e 3)+
        weight r e 2*(v r e 2+(alpha r e 2)^2)*(alpha r e 0*alpha r e 1*alpha r e 3)+
        weight r e 3*(v r e 3+(alpha r e 3)^2)*(alpha r e 0*alpha r e 1*alpha r e 2)) := by
  obtain ⟨e0,e1,e2,e3⟩ := r67_erase_prod (alpha r e)
  rw [numerator,Fin.prod_univ_four,Fin.sum_univ_four,e0,e1,e2,e3]

/-! ### Kronecker substitution

An integer list is evaluated at an integer `B`; when every entry lies in `[-B/2,B/2)`, the list
is read back from the value as its balanced base-`B` digits (`r67k_dec_enc`). -/

/-- The list evaluated at `B`. -/
private def r67kenc (B : ℤ) : List ℤ → ℤ
  | [] => 0
  | a :: l => a+B*r67kenc B l

/-- The residue of `N` modulo `B` in `[-B/2,B/2)`. -/
private def r67kbal (B N : ℤ) : ℤ := if 2*(N % B)<B then N % B else N % B-B

/-- The first `n` balanced base-`B` digits of `N`. -/
private def r67kdec (B : ℤ) : ℕ → ℤ → List ℤ
  | 0,_ => []
  | n+1,N => r67kbal B N :: r67kdec B n ((N-r67kbal B N) / B)

/-- The sum of the absolute values of the entries. -/
private def r67kasum : List ℤ → ℕ
  | [] => 0
  | a :: l => a.natAbs+r67kasum l

/-- The largest absolute value of an entry. -/
private def r67kamax : List ℤ → ℕ
  | [] => 0
  | a :: l => max a.natAbs (r67kamax l)

private theorem r67k_enc_eq (B : ℤ) : ∀ l : List ℤ,(r67kenc B l : ℚ)=(toPoly l).eval (B:ℚ)
  | [] => by simp [r67kenc,toPoly]
  | a :: l => by simp [r67kenc,toPoly,r67k_enc_eq B l]

private theorem r67k_bal_eq {B c M : ℤ} (hc : -B≤2*c ∧ 2*c<B) : r67kbal B (c+B*M)=c := by
  have hB : 0<B := by omega
  unfold r67kbal
  rw [Int.add_mul_emod_self_left]
  rcases le_or_gt 0 c with h0|h0
  · rw [Int.emod_eq_of_lt h0 (by omega),ite_eq_left hc.2]
  · have e : c % B=c+B := by
      rw [show c=(c+B)+B*(-1) by ring,Int.add_mul_emod_self_left,Int.emod_eq_of_lt (by omega) (by omega)]
      ring
    rw [e,ite_eq_right (by omega)]
    ring

private theorem r67k_dec_enc {B : ℤ} (hB : 0<B) : ∀ (n : ℕ) (c : List ℤ),c.length≤n →
    (∀ j,-B≤2*c.getD j 0 ∧ 2*c.getD j 0<B) → toPoly (r67kdec B n (r67kenc B c))=toPoly c
  | 0,c,hl,_ => by
    rw [List.length_eq_zero_iff.1 (by omega : c.length=0)]
    rfl
  | n+1,[],_,_ => by
    have h0 : r67kbal B 0=0 := by
      simpa using r67k_bal_eq (c:=0) (M:=0) (B:=B) (by omega)
    have ih : toPoly (r67kdec B n 0)=0 := r67k_dec_enc hB n [] (by simp) (fun j => by simp; omega)
    show toPoly (r67kdec B (n+1) 0)=0
    rw [r67kdec,h0,sub_zero,Int.zero_ediv]
    simp [toPoly,ih]
  | n+1,x :: c,hl,hb => by
    have hx := hb 0
    simp only [List.getD_cons_zero] at hx
    have h1 := r67k_bal_eq (M:=r67kenc B c) hx
    have h2 : (x+B*r67kenc B c-x) / B=r67kenc B c := by
      rw [add_sub_cancel_left,Int.mul_ediv_cancel_left _ hB.ne']
    have ih := r67k_dec_enc hB n c (by simpa using hl) (fun j => by simpa using hb (j+1))
    simp only [r67kenc,r67kdec,h1,h2]
    rw [toPoly,toPoly,ih]

private theorem r67k_getD_smul (c : ℤ) : ∀ (l : List ℤ) (j : ℕ),
    (WholeIntervalPolynomial.Certificate.smul c l).getD j 0=c*l.getD j 0
  | [],j => by simp [WholeIntervalPolynomial.Certificate.smul]
  | a :: l,0 => by simp [WholeIntervalPolynomial.Certificate.smul]
  | a :: l,j+1 => by
    simp only [WholeIntervalPolynomial.Certificate.smul,List.getD_cons_succ,r67k_getD_smul c l j]

private theorem r67k_getD_le_amax : ∀ (l : List ℤ) (j : ℕ),|l.getD j 0|≤r67kamax l
  | [],j => by simp
  | a :: l,0 => by simp only [List.getD_cons_zero,r67kamax]; push_cast; exact le_max_left _ _
  | a :: l,j+1 => by
    simp only [List.getD_cons_succ,r67kamax]
    push_cast
    exact (r67k_getD_le_amax l j).trans (le_max_right _ _)

private theorem r67k_mul_bound : ∀ (a m : List ℤ) (j : ℕ),
    |(WholeIntervalPolynomial.Certificate.mul a m).getD j 0|≤r67kasum a*r67kamax m
  | [],m,j => by simp [WholeIntervalPolynomial.Certificate.mul]; positivity
  | a :: l,[],j => by simp [WholeIntervalPolynomial.Certificate.mul]; positivity
  | a :: l,b :: m,j => by
    rw [WholeIntervalPolynomial.Certificate.mul,WholeIntervalPolynomial.Certificate.getD_add,
      r67k_getD_smul]
    have h1 : |a*(b :: m).getD j 0|≤|a| * r67kamax (b :: m) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (r67k_getD_le_amax _ j) (abs_nonneg a)
    have h2 : |(0 :: WholeIntervalPolynomial.Certificate.mul l (b :: m)).getD j 0|≤
        r67kasum l*r67kamax (b :: m) := by
      rcases j with _|j
      · simp only [List.getD_cons_zero,abs_zero]; positivity
      · simpa only [List.getD_cons_succ] using r67k_mul_bound l (b :: m) j
    simp only [r67kasum]
    push_cast
    calc _≤_ := abs_add_le _ _
      _≤_ := add_le_add h1 h2
      _=_ := by ring

private theorem r67k_length_add : ∀ l m : List ℤ,
    (WholeIntervalPolynomial.Certificate.add l m).length=max l.length m.length
  | [],m => by simp [WholeIntervalPolynomial.Certificate.add]
  | a :: l,[] => by simp [WholeIntervalPolynomial.Certificate.add]
  | a :: l,b :: m => by
    simp [WholeIntervalPolynomial.Certificate.add,r67k_length_add l m,Nat.succ_max_succ]

private theorem r67k_length_smul (c : ℤ) : ∀ l : List ℤ,
    (WholeIntervalPolynomial.Certificate.smul c l).length=l.length
  | [] => rfl
  | a :: l => by simp [WholeIntervalPolynomial.Certificate.smul,r67k_length_smul c l]

private theorem r67k_length_mul : ∀ a m : List ℤ,
    (WholeIntervalPolynomial.Certificate.mul a m).length≤a.length+m.length-1
  | [],m => by simp [WholeIntervalPolynomial.Certificate.mul]
  | a :: l,[] => by simp [WholeIntervalPolynomial.Certificate.mul]
  | a :: l,b :: m => by
    have ih := r67k_length_mul l (b :: m)
    rw [WholeIntervalPolynomial.Certificate.mul,r67k_length_add,r67k_length_smul]
    rcases l with _|⟨c,l⟩
    · simp [WholeIntervalPolynomial.Certificate.mul]
    · simp only [List.length_cons] at ih ⊢
      omega

/-! ### Encoded sums and products

`r67kK` holds the value `N` at a base `B` of an integer list of at most `n` entries, each of
absolute value at most `β`, that represents `s` times a polynomial.  Sums and products act on
`N` alone, so a whole expression costs a few integer operations; `toScaled` reads the list
back as balanced base-`B` digits once `B` exceeds `2β`. -/

private structure r67kK where
  N : ℤ
  s : ℕ
  n : ℕ
  β : ℕ

private def r67kK.Rep (B : ℤ) (k : r67kK) (p : ℚ[X]) : Prop :=
  ∃ l : List ℤ,l.length≤k.n ∧ (∀ j,|l.getD j 0|≤k.β) ∧ k.N=r67kenc B l ∧ toPoly l=C (k.s:ℚ)*p

private def r67kK.add (a b : r67kK) : r67kK := ⟨a.N*b.s+b.N*a.s,a.s*b.s,max a.n b.n,a.β*b.s+b.β*a.s⟩
private def r67kK.sub (a b : r67kK) : r67kK := ⟨a.N*b.s-b.N*a.s,a.s*b.s,max a.n b.n,a.β*b.s+b.β*a.s⟩
private def r67kK.mul (a b : r67kK) : r67kK := ⟨a.N*b.N,a.s*b.s,a.n+b.n-1,a.n*a.β*b.β⟩
private def r67kK.const (q : ℚ) : r67kK := ⟨q.num,q.den,1,q.num.natAbs⟩
private def r67kK.ofScaled (B : ℤ) (S : Scaled) : r67kK := ⟨r67kenc B S.l,S.s,S.l.length,r67kamax S.l⟩
private def r67kK.toScaled (B : ℤ) (k : r67kK) : Scaled :=
  if 2*(k.β:ℤ)<B then ⟨r67kdec B k.n k.N,k.s⟩ else ⟨[],0⟩

private theorem r67k_enc_add (B : ℤ) (l m : List ℤ) :
    r67kenc B (WholeIntervalPolynomial.Certificate.add l m)=r67kenc B l+r67kenc B m := by
  have e : (r67kenc B (WholeIntervalPolynomial.Certificate.add l m) : ℚ)=r67kenc B l+r67kenc B m := by
    rw [r67k_enc_eq,r67k_enc_eq,r67k_enc_eq,WholeIntervalPolynomial.Certificate.toPoly_add,eval_add]
  exact_mod_cast e

private theorem r67k_enc_smul (B c : ℤ) (l : List ℤ) :
    r67kenc B (WholeIntervalPolynomial.Certificate.smul c l)=c*r67kenc B l := by
  have e : (r67kenc B (WholeIntervalPolynomial.Certificate.smul c l) : ℚ)=c*r67kenc B l := by
    rw [r67k_enc_eq,r67k_enc_eq,WholeIntervalPolynomial.Certificate.toPoly_smul,eval_mul,eval_C]
  exact_mod_cast e

private theorem r67k_enc_mul (B : ℤ) (l m : List ℤ) :
    r67kenc B (WholeIntervalPolynomial.Certificate.mul l m)=r67kenc B l*r67kenc B m := by
  have e : (r67kenc B (WholeIntervalPolynomial.Certificate.mul l m) : ℚ)=r67kenc B l*r67kenc B m := by
    rw [r67k_enc_eq,r67k_enc_eq,r67k_enc_eq,WholeIntervalPolynomial.Certificate.toPoly_mul,eval_mul]
  exact_mod_cast e

private theorem r67k_amax_le {l : List ℤ} {β : ℕ} (h : ∀ j,|l.getD j 0|≤β) : r67kamax l≤β := by
  induction l generalizing β with
  | nil => simp [r67kamax]
  | cons a l ih =>
    have h0 := h 0
    simp only [List.getD_cons_zero,Int.abs_eq_natAbs,Nat.cast_le] at h0
    have h1 := ih (fun j => by simpa using h (j+1))
    exact max_le h0 h1

private theorem r67k_asum_le {l : List ℤ} {β : ℕ} (h : ∀ j,|l.getD j 0|≤β) :
    r67kasum l≤l.length*β := by
  induction l generalizing β with
  | nil => simp [r67kasum]
  | cons a l ih =>
    have h0 := h 0
    simp only [List.getD_cons_zero,Int.abs_eq_natAbs,Nat.cast_le] at h0
    have h1 := ih (fun j => by simpa using h (j+1))
    simp only [r67kasum,List.length_cons]
    nlinarith

private theorem r67kK.Rep.add {B : ℤ} {a b : r67kK} {p q : ℚ[X]} (ha : a.Rep B p) (hb : b.Rep B q) :
    (a.add b).Rep B (p+q) := by
  obtain ⟨la,hla,hba,hNa,hpa⟩ := ha
  obtain ⟨lb,hlb,hbb,hNb,hpb⟩ := hb
  refine ⟨WholeIntervalPolynomial.Certificate.add (WholeIntervalPolynomial.Certificate.smul b.s la) (WholeIntervalPolynomial.Certificate.smul a.s lb),?_,?_,?_,?_⟩
  · rw [r67k_length_add,r67k_length_smul,r67k_length_smul]
    exact max_le_max hla hlb
  · intro j
    rw [WholeIntervalPolynomial.Certificate.getD_add,r67k_getD_smul,r67k_getD_smul]
    calc _≤|(b.s:ℤ)*la.getD j 0|+|(a.s:ℤ)*lb.getD j 0| := abs_add_le _ _
      _≤(b.s:ℤ)*a.β+(a.s:ℤ)*b.β := by
        rw [abs_mul,abs_mul,Nat.abs_cast,Nat.abs_cast]
        exact add_le_add (mul_le_mul_of_nonneg_left (hba j) (by positivity))
          (mul_le_mul_of_nonneg_left (hbb j) (by positivity))
      _=_ := by simp only [r67kK.add]; push_cast; ring
  · simp only [r67kK.add,r67k_enc_add,r67k_enc_smul,hNa,hNb]
    ring
  · simp only [r67kK.add,WholeIntervalPolynomial.Certificate.toPoly_add,WholeIntervalPolynomial.Certificate.toPoly_smul,hpa,hpb,Int.cast_natCast,
      Nat.cast_mul,map_mul]
    ring

private theorem r67kK.Rep.sub {B : ℤ} {a b : r67kK} {p q : ℚ[X]} (ha : a.Rep B p) (hb : b.Rep B q) :
    (a.sub b).Rep B (p-q) := by
  obtain ⟨la,hla,hba,hNa,hpa⟩ := ha
  obtain ⟨lb,hlb,hbb,hNb,hpb⟩ := hb
  refine ⟨WholeIntervalPolynomial.Certificate.add (WholeIntervalPolynomial.Certificate.smul b.s la) (WholeIntervalPolynomial.Certificate.smul (-(a.s:ℤ)) lb),?_,?_,?_,?_⟩
  · rw [r67k_length_add,r67k_length_smul,r67k_length_smul]
    exact max_le_max hla hlb
  · intro j
    rw [WholeIntervalPolynomial.Certificate.getD_add,r67k_getD_smul,r67k_getD_smul]
    calc _≤|(b.s:ℤ)*la.getD j 0|+|(-(a.s:ℤ))*lb.getD j 0| := abs_add_le _ _
      _≤(b.s:ℤ)*a.β+(a.s:ℤ)*b.β := by
        rw [abs_mul,abs_mul,abs_neg,Nat.abs_cast,Nat.abs_cast]
        exact add_le_add (mul_le_mul_of_nonneg_left (hba j) (by positivity))
          (mul_le_mul_of_nonneg_left (hbb j) (by positivity))
      _=_ := by simp only [r67kK.sub]; push_cast; ring
  · simp only [r67kK.sub,r67k_enc_add,r67k_enc_smul,hNa,hNb]
    ring
  · simp only [r67kK.sub,WholeIntervalPolynomial.Certificate.toPoly_add,WholeIntervalPolynomial.Certificate.toPoly_smul,hpa,hpb,Int.cast_natCast,
      Int.cast_neg,Nat.cast_mul,map_mul,map_neg]
    ring

private theorem r67kK.Rep.mul {B : ℤ} {a b : r67kK} {p q : ℚ[X]} (ha : a.Rep B p) (hb : b.Rep B q) :
    (a.mul b).Rep B (p*q) := by
  obtain ⟨la,hla,hba,hNa,hpa⟩ := ha
  obtain ⟨lb,hlb,hbb,hNb,hpb⟩ := hb
  refine ⟨WholeIntervalPolynomial.Certificate.mul la lb,?_,?_,?_,?_⟩
  · have := r67k_length_mul la lb
    simp only [r67kK.mul]
    omega
  · intro j
    have h1 := r67k_mul_bound la lb j
    have h2 : r67kasum la*r67kamax lb≤a.n*a.β*b.β :=
      Nat.mul_le_mul ((r67k_asum_le hba).trans (Nat.mul_le_mul_right _ hla)) (r67k_amax_le hbb)
    simp only [r67kK.mul]
    calc _≤((r67kasum la*r67kamax lb:ℕ):ℤ) := by exact_mod_cast h1
      _≤_ := by exact_mod_cast h2
  · simp only [r67kK.mul,r67k_enc_mul,hNa,hNb]
  · simp only [r67kK.mul,WholeIntervalPolynomial.Certificate.toPoly_mul,hpa,hpb,Nat.cast_mul,map_mul]
    ring

private theorem r67kK.rep_const (B : ℤ) (q : ℚ) : (r67kK.const q).Rep B (C q) := by
  refine ⟨[q.num],by simp [r67kK.const],fun j => ?_,by simp [r67kK.const,r67kenc],?_⟩
  · rcases j with _|j
    · simp only [List.getD_cons_zero,r67kK.const]
      exact (Int.abs_eq_natAbs _).le
    · simp
  · simp only [r67kK.const,toPoly,mul_zero,add_zero,← map_mul,Rat.den_mul_eq_num]

private theorem r67kK.rep_ofScaled (B : ℤ) {S : Scaled} {p : ℚ[X]} (hS : S.Rep p) :
    (r67kK.ofScaled B S).Rep B p :=
  ⟨S.l,le_rfl,r67k_getD_le_amax S.l,rfl,hS⟩

private theorem r67kK.Rep.toScaled {B : ℤ} {k : r67kK} {p : ℚ[X]} (hk : k.Rep B p) :
    (k.toScaled B).Rep p := by
  unfold r67kK.toScaled
  split_ifs with h
  · obtain ⟨l,hl,hb,hN,hp⟩ := hk
    have hB : 0<B := lt_of_le_of_lt (by positivity) h
    show toPoly (r67kdec B k.n k.N)=_
    rw [hN,r67k_dec_enc hB _ _ hl (fun j => by obtain ⟨h1,h2⟩ := abs_le.1 (hb j); constructor <;> linarith)]
    exact hp
  · show toPoly []=C ((0:ℕ):ℚ)*p
    simp [toPoly]


/-! ### Composition with `s+tX` by Kronecker substitution

The entries of the composition of `L` with `s+tX` are at most `Σ|Lᵢ| (|s|+|t|+1)^(n-1)`, so they
are the balanced base-`B` digits of the value of `L` at `s+tB` for `B` above twice that bound. -/

private theorem r67k_asum_add : ∀ l m : List ℤ,
    r67kasum (WholeIntervalPolynomial.Certificate.add l m)≤r67kasum l+r67kasum m
  | [],m => by simp [WholeIntervalPolynomial.Certificate.add,r67kasum]
  | a :: l,[] => by simp [WholeIntervalPolynomial.Certificate.add,r67kasum]
  | a :: l,b :: m => by
    have ih := r67k_asum_add l m
    have := Int.natAbs_add_le a b
    simp only [WholeIntervalPolynomial.Certificate.add,r67kasum]
    omega

private theorem r67k_asum_affMulAux (s t : ℤ) : ∀ (c : ℤ) (z : List ℤ),
    r67kasum (WholeIntervalPolynomial.Certificate.affMulAux s t c z)≤
      s.natAbs*r67kasum z+t.natAbs*c.natAbs+t.natAbs*r67kasum z
  | c,[] => by simp [WholeIntervalPolynomial.Certificate.affMulAux,r67kasum,Int.natAbs_mul]
  | c,x :: z => by
    have ih := r67k_asum_affMulAux s t x z
    have h1 := Int.natAbs_add_le (s*x) (t*c)
    simp only [WholeIntervalPolynomial.Certificate.affMulAux,r67kasum,Int.natAbs_mul] at h1 ⊢
    nlinarith

private theorem r67k_asum_affMul (s t : ℤ) (z : List ℤ) :
    r67kasum (WholeIntervalPolynomial.Certificate.affMul s t z)≤(s.natAbs+t.natAbs)*r67kasum z := by
  unfold WholeIntervalPolynomial.Certificate.affMul
  split_ifs with h
  · obtain ⟨rfl,rfl⟩ := h
    cases z with
    | nil => simp [WholeIntervalPolynomial.Certificate.shiftMul,r67kasum]
    | cons x z =>
      have := r67k_asum_add (x :: z) (0 :: x :: z)
      simp only [WholeIntervalPolynomial.Certificate.shiftMul]
      simp only [r67kasum] at this ⊢
      simp
      omega
  · cases z with
    | nil => simp [WholeIntervalPolynomial.Certificate.affMulGen,r67kasum]
    | cons x z =>
      have := r67k_asum_affMulAux s t x z
      simp only [WholeIntervalPolynomial.Certificate.affMulGen,r67kasum,Int.natAbs_mul]
      nlinarith

private theorem r67k_asum_compAff (s t : ℤ) : ∀ l : List ℤ,
    r67kasum (WholeIntervalPolynomial.Certificate.compAff s t l)≤
      r67kasum l*(s.natAbs+t.natAbs+1)^(l.length-1)
  | [] => by simp [WholeIntervalPolynomial.Certificate.compAff,r67kasum]
  | b :: l => by
    have h1 := r67k_asum_add [b] (WholeIntervalPolynomial.Certificate.affMul s t
      (WholeIntervalPolynomial.Certificate.compAff s t l))
    have h2 := r67k_asum_affMul s t (WholeIntervalPolynomial.Certificate.compAff s t l)
    have hb : r67kasum [b]=b.natAbs := by simp [r67kasum]
    rw [WholeIntervalPolynomial.Certificate.compAff]
    simp only [r67kasum,List.length_cons,Nat.add_sub_cancel]
    rcases l with _|⟨c,l⟩
    · simp [WholeIntervalPolynomial.Certificate.compAff,WholeIntervalPolynomial.Certificate.affMul,
        WholeIntervalPolynomial.Certificate.shiftMul,WholeIntervalPolynomial.Certificate.affMulGen,
        WholeIntervalPolynomial.Certificate.add,r67kasum]
    · have ih := r67k_asum_compAff s t (c :: l)
      generalize r67kasum (WholeIntervalPolynomial.Certificate.compAff s t (c :: l))=A at h1 h2 ih
      simp only [List.length_cons,Nat.add_sub_cancel] at ih ⊢
      have key : (s.natAbs+t.natAbs)*A≤r67kasum (c :: l)*(s.natAbs+t.natAbs+1)^(l.length+1) :=
        calc (s.natAbs+t.natAbs)*A≤(s.natAbs+t.natAbs+1)*A := Nat.mul_le_mul_right _ (Nat.le_succ _)
          _≤(s.natAbs+t.natAbs+1)*(r67kasum (c :: l)*(s.natAbs+t.natAbs+1)^l.length) :=
            Nat.mul_le_mul_left _ ih
          _=_ := by ring
      have hM : 1≤(s.natAbs+t.natAbs+1)^(l.length+1) := Nat.one_le_pow _ _ (by omega)
      have hb' : b.natAbs≤b.natAbs*(s.natAbs+t.natAbs+1)^(l.length+1) := Nat.le_mul_of_pos_right _ hM
      rw [hb] at h1
      rw [add_mul]
      omega

private theorem r67k_getD_le_asum : ∀ (l : List ℤ) (j : ℕ),(l.getD j 0).natAbs≤r67kasum l
  | [],j => by simp [r67kasum]
  | a :: l,0 => by simp [r67kasum]
  | a :: l,j+1 => by
    have := r67k_getD_le_asum l j
    simp only [List.getD_cons_succ,r67kasum]
    omega

private theorem r67k_length_affMulAux (s t : ℤ) : ∀ (c : ℤ) (z : List ℤ),
    (WholeIntervalPolynomial.Certificate.affMulAux s t c z).length=z.length+1
  | c,[] => rfl
  | c,x :: z => by
    simp [WholeIntervalPolynomial.Certificate.affMulAux,r67k_length_affMulAux s t x z]

private theorem r67k_length_affMul (s t : ℤ) (z : List ℤ) :
    (WholeIntervalPolynomial.Certificate.affMul s t z).length≤z.length+1 := by
  unfold WholeIntervalPolynomial.Certificate.affMul
  split_ifs
  · cases z with
    | nil => simp [WholeIntervalPolynomial.Certificate.shiftMul]
    | cons x z =>
      rw [WholeIntervalPolynomial.Certificate.shiftMul,r67k_length_add]
      simp
  · cases z with
    | nil => simp [WholeIntervalPolynomial.Certificate.affMulGen]
    | cons x z =>
      simp [WholeIntervalPolynomial.Certificate.affMulGen,r67k_length_affMulAux]

private theorem r67k_length_compAff (s t : ℤ) : ∀ l : List ℤ,
    (WholeIntervalPolynomial.Certificate.compAff s t l).length≤l.length
  | [] => by simp [WholeIntervalPolynomial.Certificate.compAff]
  | b :: l => by
    have ih := r67k_length_compAff s t l
    have h := r67k_length_affMul s t (WholeIntervalPolynomial.Certificate.compAff s t l)
    rw [WholeIntervalPolynomial.Certificate.compAff,r67k_length_add]
    simp only [List.length_cons,List.length_nil]
    omega

private def r67kkcenterWith (B s t : ℤ) (L : List ℤ) : List ℤ :=
  r67kdec B L.length (r67kenc (s+t*B) L)
/-- The composition of `L` with `s+tX`, by one evaluation at `s+tB`, read back in base
`B = 2 Σ|Lᵢ| (|s|+|t|+1)^(n-1) + 1`. -/
private def r67kkcenterAux (s t : ℤ) (L : List ℤ) : List ℤ :=
  r67kkcenterWith (2*(r67kasum L*(s.natAbs+t.natAbs+1)^(L.length-1))+1) s t L

private theorem r67k_toPoly_kcenterAux (s t : ℤ) (L : List ℤ) :
    toPoly (r67kkcenterAux s t L)=toPoly (WholeIntervalPolynomial.Certificate.compAff s t L) := by
  rw [r67kkcenterAux,r67kkcenterWith]
  generalize hB : (2*(r67kasum L*(s.natAbs+t.natAbs+1)^(L.length-1))+1 : ℤ)=B
  have hB0 : 0<B := by rw [← hB]; positivity
  have he : r67kenc (s+t*B) L=r67kenc B (WholeIntervalPolynomial.Certificate.compAff s t L) := by
    have e : (r67kenc (s+t*B) L : ℚ)=(r67kenc B (WholeIntervalPolynomial.Certificate.compAff s t L) : ℚ) := by
      rw [r67k_enc_eq,r67k_enc_eq,WholeIntervalPolynomial.Certificate.toPoly_compAff,eval_comp]
      simp
    exact_mod_cast e
  rw [he]
  apply r67k_dec_enc hB0 _ _ (r67k_length_compAff s t L)
  intro j
  have h1 := r67k_getD_le_asum (WholeIntervalPolynomial.Certificate.compAff s t L) j
  have h2 := r67k_asum_compAff s t L
  have h3 : ((WholeIntervalPolynomial.Certificate.compAff s t L).getD j 0).natAbs≤
      r67kasum L*(s.natAbs+t.natAbs+1)^(L.length-1) := h1.trans h2
  have h4 : |(WholeIntervalPolynomial.Certificate.compAff s t L).getD j 0|≤
      ((r67kasum L*(s.natAbs+t.natAbs+1)^(L.length-1) : ℕ) : ℤ) := by
    rw [Int.abs_eq_natAbs]; exact_mod_cast h3
  obtain ⟨h5,h6⟩ := abs_le.1 h4
  push_cast at h5 h6 hB
  constructor <;> linarith

/-- `Scaled.center`, with the composition by `r67kkcenterAux`. -/
private def _root_.SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate.Scaled.kcenter
    (c : Scaled) (num den : ℕ) (s t : ℤ) : Scaled :=
  ⟨r67kkcenterAux s t (WholeIntervalPolynomial.Certificate.prescale num den (c.l.length-1) 0 c.l),
    c.s*den^(c.l.length-1)⟩

private theorem _root_.SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate.Scaled.Rep.kcentered
    {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) (num den : ℕ) (s t : ℤ)
    {a b : ℚ} (hden : den≠0) (hm : (a+b)/2=num*s/den) (hh : (b-a)/2=num*t/den) :
    (c.kcenter num den s t).Rep (WholeIntervalPolynomial.centered a b p) := by
  have h := hc.centered num den s t hden hm hh
  unfold Scaled.Rep at h ⊢
  show toPoly (r67kkcenterAux s t _)=_
  rw [r67k_toPoly_kcenterAux]
  exact h

/-- The shift by `a=num/den`, through the fast centering on `[0,2a]`. -/
private theorem r67_fast_shift {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) (num den : ℕ) {a : ℚ}
    (hden : den≠0) (hnum : num≠0) (ha : a=num/den) :
    (r67_scale (c.kcenter num den 1 1) den num).Rep (DirectedPowerBounds.shift a p) := by
  have h1 := hc.kcentered num den 1 1 (a:=0) (b:=2*a) hden (by rw [ha]; push_cast; ring)
    (by rw [ha]; push_cast; ring)
  have h2 := r67_scale_rep h1 den num hnum
  have hq : (WholeIntervalPolynomial.affine 0 (2*a)).comp (C ((den:ℚ)/num)*X)=C a+X := by
    have e1 : (0+2*a)/2=a := by ring
    have e2 : (2*a-0)/2*((den:ℚ)/num)=1 := by
      have : (num:ℚ)≠0 := by exact_mod_cast hnum
      have : (den:ℚ)≠0 := by exact_mod_cast hden
      rw [ha]; field_simp; ring
    rw [WholeIntervalPolynomial.affine,add_comp,mul_comp,C_comp,C_comp,X_comp,← mul_assoc,
      ← map_mul,e1,e2,map_one,one_mul]
  rwa [WholeIntervalPolynomial.centered,comp_assoc,hq] at h2

private theorem r67_rep_eq {S : Scaled} {p q : ℚ[X]} (e : q=p) (h : S.Rep q) : S.Rep p := e ▸ h

/-- The numerator on encoded lists, sharing the partial products `a0a1` and `a2a3`. -/
private def r67_numKT (h a0 a1 a2 a3 w0 w1 w2 w3 v0 v1 v2 v3 p01 p23 : r67kK) : r67kK :=
  (((r67kK.const 2).mul h).mul (p01.mul p23)).sub ((r67kK.const Rplus).mul
    (((w0.mul (v0.add (a0.mul a0))).mul (a1.mul p23)
        |>.add ((w1.mul (v1.add (a1.mul a1))).mul (a0.mul p23))).add
      ((w2.mul (v2.add (a2.mul a2))).mul (p01.mul a3)
        |>.add ((w3.mul (v3.add (a3.mul a3))).mul (p01.mul a2)))))
private def r67_numKE (h a0 a1 a2 a3 w0 w1 w2 w3 v0 v1 v2 v3 : r67kK) : r67kK :=
  r67_numKT h a0 a1 a2 a3 w0 w1 w2 w3 v0 v1 v2 v3 (a0.mul a1) (a2.mul a3)
private def r67_numKB (B : ℤ) (h a0 a1 a2 a3 w0 w1 w2 w3 v0 v1 v2 v3 : Scaled) : r67kK :=
  r67_numKE (.ofScaled B h) (.ofScaled B a0) (.ofScaled B a1) (.ofScaled B a2) (.ofScaled B a3)
    (.ofScaled B w0) (.ofScaled B w1) (.ofScaled B w2) (.ofScaled B w3) (.ofScaled B v0)
    (.ofScaled B v1) (.ofScaled B v2) (.ofScaled B v3)
private def r67_numWith (B : ℤ) (h a0 a1 a2 a3 w0 w1 w2 w3 v0 v1 v2 v3 : Scaled) : Scaled :=
  (r67_numKB B h a0 a1 a2 a3 w0 w1 w2 w3 v0 v1 v2 v3).toScaled B
/-- The numerator from its pieces, read back in a base above twice its coefficient bound. -/
private def r67_num (h a0 a1 a2 a3 w0 w1 w2 w3 v0 v1 v2 v3 : Scaled) : Scaled :=
  r67_numWith (2*(r67_numKB 0 h a0 a1 a2 a3 w0 w1 w2 w3 v0 v1 v2 v3).β+1)
    h a0 a1 a2 a3 w0 w1 w2 w3 v0 v1 v2 v3

private theorem r67_numWith_rep (B : ℤ) {h a0 a1 a2 a3 w0 w1 w2 w3 v0 v1 v2 v3 : Scaled}
    {ph p0 p1 p2 p3 q0 q1 q2 q3 u0 u1 u2 u3 : ℚ[X]} (hh : h.Rep ph)
    (h0 : a0.Rep p0) (h1 : a1.Rep p1) (h2 : a2.Rep p2) (h3 : a3.Rep p3)
    (g0 : w0.Rep q0) (g1 : w1.Rep q1) (g2 : w2.Rep q2) (g3 : w3.Rep q3)
    (k0 : v0.Rep u0) (k1 : v1.Rep u1) (k2 : v2.Rep u2) (k3 : v3.Rep u3) :
    (r67_numWith B h a0 a1 a2 a3 w0 w1 w2 w3 v0 v1 v2 v3).Rep
      (C 2*ph*(p0*p1*p2*p3)-C Rplus*
        (q0*(u0+p0^2)*(p1*p2*p3)+q1*(u1+p1^2)*(p0*p2*p3)+q2*(u2+p2^2)*(p0*p1*p3)+
          q3*(u3+p3^2)*(p0*p1*p2))) := by
  have jh := r67kK.rep_ofScaled B hh
  have j0 := r67kK.rep_ofScaled B h0
  have j1 := r67kK.rep_ofScaled B h1
  have j2 := r67kK.rep_ofScaled B h2
  have j3 := r67kK.rep_ofScaled B h3
  have m0 := r67kK.rep_ofScaled B g0
  have m1 := r67kK.rep_ofScaled B g1
  have m2 := r67kK.rep_ofScaled B g2
  have m3 := r67kK.rep_ofScaled B g3
  have n0 := r67kK.rep_ofScaled B k0
  have n1 := r67kK.rep_ofScaled B k1
  have n2 := r67kK.rep_ofScaled B k2
  have n3 := r67kK.rep_ofScaled B k3
  have P01 := j0.mul j1
  have P23 := j2.mul j3
  exact r67_rep_eq (by ring) (r67kK.Rep.toScaled
    ((((r67kK.rep_const B 2).mul jh).mul (P01.mul P23)).sub ((r67kK.rep_const B Rplus).mul
      (((m0.mul (n0.add (j0.mul j0))).mul (j1.mul P23)
          |>.add ((m1.mul (n1.add (j1.mul j1))).mul (j0.mul P23))).add
        ((m2.mul (n2.add (j2.mul j2))).mul (P01.mul j3)
          |>.add ((m3.mul (n3.add (j3.mul j3))).mul (P01.mul j2)))))))
private theorem r67_num_rep {h a0 a1 a2 a3 w0 w1 w2 w3 v0 v1 v2 v3 : Scaled}
    {ph p0 p1 p2 p3 q0 q1 q2 q3 u0 u1 u2 u3 : ℚ[X]} (hh : h.Rep ph)
    (h0 : a0.Rep p0) (h1 : a1.Rep p1) (h2 : a2.Rep p2) (h3 : a3.Rep p3)
    (g0 : w0.Rep q0) (g1 : w1.Rep q1) (g2 : w2.Rep q2) (g3 : w3.Rep q3)
    (k0 : v0.Rep u0) (k1 : v1.Rep u1) (k2 : v2.Rep u2) (k3 : v3.Rep u3) :
    (r67_num h a0 a1 a2 a3 w0 w1 w2 w3 v0 v1 v2 v3).Rep
      (C 2*ph*(p0*p1*p2*p3)-C Rplus*
        (q0*(u0+p0^2)*(p1*p2*p3)+q1*(u1+p1^2)*(p0*p2*p3)+q2*(u2+p2^2)*(p0*p1*p3)+
          q3*(u3+p3^2)*(p0*p1*p2))) :=
  r67_numWith_rep _ hh h0 h1 h2 h3 g0 g1 g2 g3 k0 k1 k2 k3

private def r67_k : Row → Scaled
  | .low => Scaled.const (13/20)
  | _ => r67_red <| ((((((Scaled.const (65433234/100000000)).sub
      ((Scaled.const (6770392/100000000)).mul Scaled.var)).add
      ((Scaled.const (39062724/100000000)).mul (r67_mono 2))).sub
      ((Scaled.const (29937498/100000000)).mul (r67_mono 3))).add
      ((Scaled.const (35999242/100000000)).mul (r67_mono 4))).sub
      ((Scaled.const (29068717/100000000)).mul (r67_mono 5))).add
      ((Scaled.const (14649232/100000000)).mul (r67_mono 6))
private theorem r67_kd_rep : (((((((Scaled.const (65433234/100000000)).sub
      ((Scaled.const (6770392/100000000)).mul Scaled.var)).add
      ((Scaled.const (39062724/100000000)).mul (r67_mono 2))).sub
      ((Scaled.const (29937498/100000000)).mul (r67_mono 3))).add
      ((Scaled.const (35999242/100000000)).mul (r67_mono 4))).sub
      ((Scaled.const (29068717/100000000)).mul (r67_mono 5))).add
      ((Scaled.const (14649232/100000000)).mul (r67_mono 6))).Rep (k .transition) :=
  ((((((Scaled.rep_const _).sub ((Scaled.rep_const _).mul Scaled.rep_var)).add
    ((Scaled.rep_const _).mul (r67_mono_rep 2))).sub
    ((Scaled.rep_const _).mul (r67_mono_rep 3))).add
    ((Scaled.rep_const _).mul (r67_mono_rep 4))).sub
    ((Scaled.rep_const _).mul (r67_mono_rep 5))).add
    ((Scaled.rep_const _).mul (r67_mono_rep 6))
private theorem r67_k_rep : ∀ r : Row,(r67_k r).Rep (k r)
  | .low => Scaled.rep_const _
  | .transition => r67_rep_red r67_kd_rep
  | .full => r67_rep_red r67_kd_rep

private def r67_c : Row → Scaled
  | .low => ((Scaled.const (69/50)).sub ((Scaled.const (13/5)).mul Scaled.var)).add
      ((Scaled.const (14/5)).mul (r67_mono 2))
  | _ => ((Scaled.const (230229/200000)).sub ((Scaled.const (9/10)).mul Scaled.var)).add
      ((Scaled.const (11/20)).mul (r67_mono 2))
private theorem r67_c_rep : ∀ r : Row,(r67_c r).Rep (c r)
  | .low => ((Scaled.rep_const _).sub ((Scaled.rep_const _).mul Scaled.rep_var)).add
      ((Scaled.rep_const _).mul (r67_mono_rep 2))
  | .transition => ((Scaled.rep_const _).sub ((Scaled.rep_const _).mul Scaled.rep_var)).add
      ((Scaled.rep_const _).mul (r67_mono_rep 2))
  | .full => ((Scaled.rep_const _).sub ((Scaled.rep_const _).mul Scaled.rep_var)).add
      ((Scaled.rep_const _).mul (r67_mono_rep 2))

private def r67_M (r : Row) : Scaled :=
  r67_red ((r67_c r).mul (r67_C.add ((Scaled.const eta).mul r67_S)))
private theorem r67_M_rep (r : Row) : (r67_M r).Rep (M r) :=
  r67_rep_red ((r67_c_rep r).mul (r67_C_rep.add ((Scaled.rep_const _).mul r67_S_rep)))
private def r67_Jp : Scaled :=
  ((Scaled.ofNat 1).add ((Scaled.const 2).mul r67_C)).add
    ((Scaled.const (1/2+(3/2)*eta-sigmaPlus)).mul r67_S)
private theorem r67_Jp_rep : r67_Jp.Rep J :=
  (Scaled.rep_one.add ((Scaled.rep_const _).mul r67_C_rep)).add ((Scaled.rep_const _).mul r67_S_rep)

private def r67_zero : Scaled := ⟨[],1⟩

private def r67_v0 (r : Row) : Scaled := (Scaled.ofNat 1).add ((r67_k r).pow 2)
private def r67_v1 (r : Row) : Scaled := (Scaled.ofNat 1).add ((r67_M r).pow 2)
private def r67_v2 (r : Row) : Endpoint → Scaled
  | .V => ((Scaled.ofNat 1).add ((r67_k r).pow 2)).sub (((Scaled.const 2).mul (r67_k r)).mul r67_S)
  | .F => (Scaled.ofNat 1).add (((r67_k r).pow 2).mul (r67_C.pow 2))
private def r67_v3 : Row → Scaled
  | .full => (Scaled.ofNat 1).add ((r67_c .full).pow 2)
  | _ => r67_zero
private def r67_a0 (r : Row) : Scaled :=
  (Scaled.const (1/109)).mul ((Scaled.const 91).add ((Scaled.const 60).mul (r67_k r)))
private def r67_a1 (r : Row) : Scaled :=
  (Scaled.const (1/29)).mul ((Scaled.const 20).add ((Scaled.const 21).mul (r67_M r)))
private def r67_a2 (r : Row) : Endpoint → Scaled
  | .V => (Scaled.const (1/85)).mul (((Scaled.const 36).mul ((r67_k r).sub r67_S)).add
      ((Scaled.const 77).mul r67_C))
  | .F => (Scaled.const (1/109)).mul ((Scaled.const 91).add (((Scaled.const 60).mul (r67_k r)).mul r67_C))
private def r67_a3 : Row → Scaled
  | .full => (Scaled.const (1/29)).mul ((Scaled.const 21).add ((Scaled.const 20).mul (r67_c .full)))
  | _ => Scaled.ofNat 1
private def r67_w : Endpoint → Scaled
  | .V => Scaled.ofNat 1
  | .F => r67_C
private def r67_w3 : Row → Endpoint → Scaled
  | .full,e => r67_w e
  | _,_ => r67_zero
private def r67_Hb (r : Row) : Endpoint → Scaled
  | .V => ((((Scaled.const 2).mul (r67_k r)).add (Scaled.ofNat 5)).add r67_C).add
      ((r67_c r).mul r67_Jp)
  | .F => (((((Scaled.const 2).mul (r67_k r)).add (Scaled.ofNat 5)).add
      ((r67_c r).mul r67_Jp)).mul r67_C).add (Scaled.ofNat 1) |>.add
      ((Scaled.const (13/12)).mul r67_S)
private def r67_Hd : Row → Endpoint → Scaled
  | .full,_ => r67_zero
  | r,e => ((Scaled.const (Rplus*dPlus)).mul ((Scaled.ofNat 1).add (r67_c r))).mul (r67_w e)
private def r67_H (r : Row) (e : Endpoint) : Scaled := (r67_Hb r e).sub (r67_Hd r e)

private theorem r67_Hb_rep (r : Row) : ∀ e,(r67_Hb r e).Rep
    (if e=.V then C 2*k r+5+Cstar+c r*J else (C 2*k r+5+c r*J)*Cstar+1+C (13/12)*S)
  | .V => ((((Scaled.rep_const _).mul (r67_k_rep r)).add (Scaled.rep_ofNat 5)).add r67_C_rep).add
      ((r67_c_rep r).mul r67_Jp_rep)
  | .F => (((((Scaled.rep_const _).mul (r67_k_rep r)).add (Scaled.rep_ofNat 5)).add
      ((r67_c_rep r).mul r67_Jp_rep)).mul r67_C_rep).add Scaled.rep_one |>.add
      ((Scaled.rep_const _).mul r67_S_rep)
private theorem r67_w_rep : ∀ e : Endpoint,(r67_w e).Rep (if e=.V then 1 else Cstar)
  | .V => Scaled.rep_one
  | .F => r67_C_rep
private theorem r67_Hd_rep : ∀ r e,(r67_Hd r e).Rep
    (if diagonalD r then C (Rplus*dPlus)*(1+c r)*(if e=.V then 1 else Cstar) else 0)
  | .low,e => ((Scaled.rep_const _).mul (Scaled.rep_one.add (r67_c_rep .low))).mul (r67_w_rep e)
  | .transition,e => ((Scaled.rep_const _).mul (Scaled.rep_one.add (r67_c_rep .transition))).mul
      (r67_w_rep e)
  | .full,_ => Scaled.rep_zero
private theorem r67_H_rep (r : Row) (e : Endpoint) : (r67_H r e).Rep (H r e) :=
  (r67_Hb_rep r e).sub (r67_Hd_rep r e)

private theorem r67_a0_rep (r : Row) (e : Endpoint) : (r67_a0 r).Rep (alpha r e 0) :=
  (Scaled.rep_const _).mul ((Scaled.rep_const _).add ((Scaled.rep_const _).mul (r67_k_rep r)))
private theorem r67_a1_rep (r : Row) (e : Endpoint) : (r67_a1 r).Rep (alpha r e 1) :=
  (Scaled.rep_const _).mul ((Scaled.rep_const _).add ((Scaled.rep_const _).mul (r67_M_rep r)))
private theorem r67_a2_rep (r : Row) : ∀ e,(r67_a2 r e).Rep (alpha r e 2)
  | .V => (Scaled.rep_const _).mul (((Scaled.rep_const _).mul ((r67_k_rep r).sub r67_S_rep)).add
      ((Scaled.rep_const _).mul r67_C_rep))
  | .F => (Scaled.rep_const _).mul ((Scaled.rep_const _).add
      (((Scaled.rep_const _).mul (r67_k_rep r)).mul r67_C_rep))
private theorem r67_a3_rep : ∀ (r : Row) (e : Endpoint),(r67_a3 r).Rep (alpha r e 3)
  | .low,_ => Scaled.rep_one
  | .transition,_ => Scaled.rep_one
  | .full,_ => (Scaled.rep_const _).mul ((Scaled.rep_const _).add
      ((Scaled.rep_const _).mul (r67_c_rep .full)))
private theorem r67_w0_rep (r : Row) : ∀ e,(r67_w e).Rep (weight r e 0)
  | .V => Scaled.rep_one
  | .F => r67_C_rep
private theorem r67_w1_rep (r : Row) : ∀ e,(r67_w e).Rep (weight r e 1)
  | .V => Scaled.rep_one
  | .F => r67_C_rep
private theorem r67_w2_rep (r : Row) (e : Endpoint) : (Scaled.ofNat 1).Rep (weight r e 2) :=
  Scaled.rep_one
private theorem r67_w3_rep : ∀ (r : Row) (e : Endpoint),(r67_w3 r e).Rep (weight r e 3)
  | .low,_ => Scaled.rep_zero
  | .transition,_ => Scaled.rep_zero
  | .full,.V => Scaled.rep_one
  | .full,.F => r67_C_rep
private theorem r67_v0_rep (r : Row) (e : Endpoint) : (r67_v0 r).Rep (v r e 0) :=
  Scaled.rep_one.add ((r67_k_rep r).pow 2)
private theorem r67_v1_rep (r : Row) (e : Endpoint) : (r67_v1 r).Rep (v r e 1) :=
  Scaled.rep_one.add ((r67_M_rep r).pow 2)
private theorem r67_v2_rep (r : Row) : ∀ e,(r67_v2 r e).Rep (v r e 2)
  | .V => (Scaled.rep_one.add ((r67_k_rep r).pow 2)).sub
      (((Scaled.rep_const _).mul (r67_k_rep r)).mul r67_S_rep)
  | .F => Scaled.rep_one.add (((r67_k_rep r).pow 2).mul (r67_C_rep.pow 2))
private theorem r67_v3_rep : ∀ (r : Row) (e : Endpoint),(r67_v3 r).Rep (v r e 3)
  | .low,_ => Scaled.rep_zero
  | .transition,_ => Scaled.rep_zero
  | .full,_ => Scaled.rep_one.add ((r67_c_rep .full).pow 2)

private def r67_N (r : Row) (e : Endpoint) : Scaled :=
  r67_red (r67_num (r67_H r e) (r67_a0 r) (r67_a1 r) (r67_a2 r e) (r67_a3 r)
    (r67_w e) (r67_w e) (Scaled.ofNat 1) (r67_w3 r e)
    (r67_v0 r) (r67_v1 r) (r67_v2 r e) (r67_v3 r))

private theorem r67_N_rep (r : Row) (e : Endpoint) : (r67_N r e).Rep (numerator r e) := by
  rw [r67_numerator_eq]
  exact r67_rep_red (r67_num_rep (r67_H_rep r e) (r67_a0_rep r e) (r67_a1_rep r e) (r67_a2_rep r e)
    (r67_a3_rep r e) (r67_w0_rep r e) (r67_w1_rep r e) (r67_w2_rep r e) (r67_w3_rep r e)
    (r67_v0_rep r e) (r67_v1_rep r e) (r67_v2_rep r e) (r67_v3_rep r e))

private def r67_cnum : Row → ℕ | .low => 3 | .transition => 37 | .full => 19
private def r67_cden : Row → ℕ | .low => 20 | .transition => 200 | .full => 100

private def r67_cN (r : Row) (e : Endpoint) : Scaled :=
  r67_red (r67_scale ((r67_N r e).kcenter (r67_cnum r) (r67_cden r) 1 1) (r67_cden r) (r67_cnum r))
private theorem r67_cN_rep (r : Row) (e : Endpoint) : (r67_cN r e).Rep (centered r e) :=
  r67_rep_red (r67_fast_shift (r67_N_rep r e) (r67_cnum r) (r67_cden r)
    (by cases r <;> norm_num [r67_cden]) (by cases r <;> norm_num [r67_cnum])
    (by cases r <;> norm_num [r67_cnum,r67_cden,center]))

/-! ### Identities and coefficient comparisons from the integer facts -/

private theorem r67_id3 {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) (hs : c.s≠0) {n : ℕ}
    (hl : c.l.length≤3+n) :
    p=C (p.coeff 0)+C (p.coeff 1)*X+C (p.coeff 2)*X^2+PowerTailBounds.tail p 3 n := by
  have hd : p.natDegree<3+n := lt_of_le_of_lt (hc.natDegree_le hs) (by omega)
  conv_lhs => rw [r67_split p 3 n hd]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,mul_one,pow_one]

private theorem r67_quad_gt {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) (hs : c.s≠0)
    (count num den : ℕ) (hden : 0<den) {a : ℤ} {b : ℕ} (hb : 0<b)
    (h : a*((c.s:ℤ)*((den^(count+1):ℕ):ℤ))<
      (c.l.getD 2 0*((den^(count+1):ℕ):ℤ)-num*r67_hsum num den (c.l.drop 3) count)*b) :
    (a:ℚ)/b<p.coeff 2-PowerTailBounds.norm p 3 count ((num:ℚ)/den) := by
  rw [r67_norm_eq hc hs 3 count num den hden.ne']
  have hh := r67_gt hc hs 2 (Z:=num*r67_hsum num den (c.l.drop 3) count) (D:=den^(count+1))
    (by positivity) hb h
  push_cast at hh ⊢
  exact hh

private theorem r67_negtail_gt {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) (hs : c.s≠0)
    (i count num den : ℕ) (hden : 0<den) {a : ℤ} {b : ℕ} (hb : 0<b)
    (h : a*((c.s:ℤ)*((den^(count+1):ℕ):ℤ))<
      (c.l.getD i 0*((den^(count+1):ℕ):ℤ)-num*r67_nhsum num den (c.l.drop (i+1)) count)*b) :
    (a:ℚ)/b<p.coeff i-DirectedPowerBounds.negativeNorm p (i+1) count ((num:ℚ)/den) := by
  rw [r67_negNorm_eq hc hs (i+1) count num den hden.ne']
  have hh := r67_gt hc hs i (Z:=num*r67_nhsum num den (c.l.drop (i+1)) count)
    (D:=den^(count+1)) (by positivity) hb h
  push_cast at hh ⊢
  exact hh

/-! ### The integer facts, one kernel computation per numerator -/

private theorem r67_lowV_facts : (r67_cN .low .V).s≠0 ∧ (r67_cN .low .V).l.length≤3+50 ∧
    329*((r67_cN .low .V).s:ℤ)<(r67_cN .low .V).l.getD 0 0*200000 ∧
    (r67_cN .low .V).l.getD 1 0*500< -63*((r67_cN .low .V).s:ℤ) ∧
    73*(((r67_cN .low .V).s:ℤ)*((20^(50+1):ℕ):ℤ))<((r67_cN .low .V).l.getD 2 0*((20^(50+1):ℕ):ℤ)-
      3*r67_hsum 3 20 ((r67_cN .low .V).l.drop 3) 50)*125 := by
  decide +kernel

private theorem r67_lowF_facts : (r67_cN .low .F).s≠0 ∧ (r67_cN .low .F).l.length≤3+66 ∧
    3289*((r67_cN .low .F).s:ℤ)<(r67_cN .low .F).l.getD 0 0*1000000 ∧
    (r67_cN .low .F).l.getD 1 0*10< -1*((r67_cN .low .F).s:ℤ) ∧
    617*(((r67_cN .low .F).s:ℤ)*((20^(66+1):ℕ):ℤ))<((r67_cN .low .F).l.getD 2 0*((20^(66+1):ℕ):ℤ)-
      3*r67_hsum 3 20 ((r67_cN .low .F).l.drop 3) 66)*500 := by
  decide +kernel

private theorem r67_midV_facts : (r67_cN .transition .V).s≠0 ∧
    (r67_cN .transition .V).l.length≤3+56 ∧
    4709*((r67_cN .transition .V).s:ℤ)<(r67_cN .transition .V).l.getD 0 0*100000000 ∧
    |(r67_cN .transition .V).l.getD 1 0| *1000000<799*((r67_cN .transition .V).s:ℤ) ∧
    3001*(((r67_cN .transition .V).s:ℤ)*((200^(56+1):ℕ):ℤ))<
      ((r67_cN .transition .V).l.getD 2 0*((200^(56+1):ℕ):ℤ)-
        7*r67_hsum 7 200 ((r67_cN .transition .V).l.drop 3) 56)*5000 := by
  decide +kernel

private theorem r67_midF_facts : (r67_cN .transition .F).s≠0 ∧
    (r67_cN .transition .F).l.length≤3+78 ∧
    1267*((r67_cN .transition .F).s:ℤ)<(r67_cN .transition .F).l.getD 0 0*25000000 ∧
    |(r67_cN .transition .F).l.getD 1 0| *500000<421*((r67_cN .transition .F).s:ℤ) ∧
    13*(((r67_cN .transition .F).s:ℤ)*((200^(78+1):ℕ):ℤ))<
      ((r67_cN .transition .F).l.getD 2 0*((200^(78+1):ℕ):ℤ)-
        7*r67_hsum 7 200 ((r67_cN .transition .F).l.drop 3) 78)*20 := by
  decide +kernel

private theorem r67_fullV_facts : (r67_cN .full .V).s≠0 ∧ (r67_cN .full .V).l.length≤6+55 ∧
    41*((r67_cN .full .V).s:ℤ)<(r67_cN .full .V).l.getD 0 0*500000 ∧
    3777*((r67_cN .full .V).s:ℤ)<(r67_cN .full .V).l.getD 1 0*500000 ∧
    -2507*((r67_cN .full .V).s:ℤ)<(r67_cN .full .V).l.getD 2 0*100000 ∧
    58973*((r67_cN .full .V).s:ℤ)<(r67_cN .full .V).l.getD 3 0*50000 ∧
    -24597*((r67_cN .full .V).s:ℤ)<(r67_cN .full .V).l.getD 4 0*10000 ∧
    91789*(((r67_cN .full .V).s:ℤ)*((100^(55+1):ℕ):ℤ))<
      ((r67_cN .full .V).l.getD 5 0*((100^(55+1):ℕ):ℤ)-
        51*r67_nhsum 51 100 ((r67_cN .full .V).l.drop (5+1)) 55)*100000 := by
  decide +kernel

private theorem r67_fullF_facts : (r67_cN .full .F).s≠0 ∧ (r67_cN .full .F).l.length≤4+79 ∧
    883*((r67_cN .full .F).s:ℤ)<(r67_cN .full .F).l.getD 0 0*10000000 ∧
    8137*((r67_cN .full .F).s:ℤ)<(r67_cN .full .F).l.getD 1 0*1000000 ∧
    -2479*((r67_cN .full .F).s:ℤ)<(r67_cN .full .F).l.getD 2 0*100000 ∧
    367*(((r67_cN .full .F).s:ℤ)*((100^(79+1):ℕ):ℤ))<
      ((r67_cN .full .F).l.getD 3 0*((100^(79+1):ℕ):ℤ)-
        51*r67_nhsum 51 100 ((r67_cN .full .F).l.drop (3+1)) 79)*10000 := by
  decide +kernel

/-! ### The six certificates -/

theorem low_identity (e : Endpoint) :
    centered .low e=C ((centered .low e).coeff 0)+C ((centered .low e).coeff 1)*X+
      C ((centered .low e).coeff 2)*X^2+tail (centered .low e) 3 (degree .low e-2) := by
  cases e
  · exact r67_id3 (r67_cN_rep .low .V) r67_lowV_facts.1 r67_lowV_facts.2.1
  · exact r67_id3 (r67_cN_rep .low .F) r67_lowF_facts.1 r67_lowF_facts.2.1

theorem low_coefficients (e : Endpoint) :
    lowConstant e<(centered .low e).coeff 0 ∧
    (centered .low e).coeff 1<lowLinear e ∧
    lowQuadratic e<(centered .low e).coeff 2-
      PowerTailBounds.norm (centered .low e) 3 (degree .low e-2) (3/20) := by
  rw [show (3/20:ℚ)=((3:ℕ):ℚ)/((20:ℕ):ℚ) by norm_num]
  cases e
  · obtain ⟨hs,-,h0,h1,h2⟩ := r67_lowV_facts
    have c0 := r67_coeff_gt (r67_cN_rep .low .V) hs 0 (a:=329) (b:=200000) (by norm_num) h0
    have c1 := r67_coeff_lt (r67_cN_rep .low .V) hs 1 (a:=-63) (b:=500) (by norm_num) h1
    have c2 := r67_quad_gt (r67_cN_rep .low .V) hs 50 3 20 (by norm_num) (a:=73) (b:=125)
      (by norm_num) h2
    refine ⟨?_,?_,?_⟩
    · norm_num [lowConstant] at c0 ⊢; exact c0
    · norm_num [lowLinear] at c1 ⊢; linarith
    · norm_num [lowQuadratic] at c2 ⊢; exact c2
  · obtain ⟨hs,-,h0,h1,h2⟩ := r67_lowF_facts
    have c0 := r67_coeff_gt (r67_cN_rep .low .F) hs 0 (a:=3289) (b:=1000000) (by norm_num) h0
    have c1 := r67_coeff_lt (r67_cN_rep .low .F) hs 1 (a:=-1) (b:=10) (by norm_num) h1
    have c2 := r67_quad_gt (r67_cN_rep .low .F) hs 66 3 20 (by norm_num) (a:=617) (b:=500)
      (by norm_num) h2
    refine ⟨?_,?_,?_⟩
    · norm_num [lowConstant] at c0 ⊢; exact c0
    · norm_num [lowLinear] at c1 ⊢; linarith
    · norm_num [lowQuadratic] at c2 ⊢; exact c2

theorem low_positive (e : Endpoint) {z : ℝ} (hz : z∈Icc 0 (3/20:ℝ)) :
    (lowConstant e:ℝ)<aeval z (numerator .low e) := by
  let u : ℝ := z-3/20
  have hu : u≤0 := by dsimp [u]; linarith [hz.2]
  have habs : |u|≤(3/20:ℝ) := by
    apply abs_le.mpr
    dsimp [u]
    exact ⟨by linarith [hz.1],hu.trans (by norm_num)⟩
  have hp := PowerTailBounds.quadratic_lower (r:=3/20) (low_identity e) (by norm_num)
    (show |u|≤((3/20:ℚ):ℝ) by rw [show ((3/20:ℚ):ℝ)=3/20 by norm_num]; exact habs)
  have h0 : (lowConstant e:ℝ)<((centered .low e).coeff 0:ℝ) := by
    exact_mod_cast (low_coefficients e).1
  have h1 : ((centered .low e).coeff 1:ℝ)<(lowLinear e:ℝ) := by
    exact_mod_cast (low_coefficients e).2.1
  have h2 : (lowQuadratic e:ℝ)<((centered .low e).coeff 2:ℝ)-
      (PowerTailBounds.norm (centered .low e) 3 (degree .low e-2) (3/20):ℝ) := by
    exact_mod_cast (low_coefficients e).2.2
  have hc1 : (lowLinear e:ℝ)≤0 := by cases e <;> norm_num [lowLinear]
  have hc2 : 0<(lowQuadratic e:ℝ) := by cases e <;> norm_num [lowQuadratic]
  have hlin := mul_nonneg_of_nonpos_of_nonpos (h1.le.trans hc1) hu
  have hquad := mul_nonneg (hc2.le.trans h2.le) (sq_nonneg u)
  have hid : aeval u (centered .low e)=aeval z (numerator .low e) := by
    simp [centered,center,u]
  rw [hid] at hp
  linarith

theorem middle_identity (e : Endpoint) :
    centered .transition e=C ((centered .transition e).coeff 0)+
      C ((centered .transition e).coeff 1)*X+C ((centered .transition e).coeff 2)*X^2+
      tail (centered .transition e) 3 (degree .transition e-2) := by
  cases e
  · exact r67_id3 (r67_cN_rep .transition .V) r67_midV_facts.1 r67_midV_facts.2.1
  · exact r67_id3 (r67_cN_rep .transition .F) r67_midF_facts.1 r67_midF_facts.2.1

theorem middle_coefficients (e : Endpoint) :
    middleConstant e<(centered .transition e).coeff 0 ∧
    |(centered .transition e).coeff 1|< middleLinear e ∧
    middleQuadratic e<(centered .transition e).coeff 2-
      PowerTailBounds.norm (centered .transition e) 3 (degree .transition e-2) (7/200) := by
  rw [show (7/200:ℚ)=((7:ℕ):ℚ)/((200:ℕ):ℚ) by norm_num]
  cases e
  · obtain ⟨hs,-,h0,h1,h2⟩ := r67_midV_facts
    have c0 := r67_coeff_gt (r67_cN_rep .transition .V) hs 0 (a:=4709) (b:=100000000)
      (by norm_num) h0
    have c1 := r67_coeff_abs_lt (r67_cN_rep .transition .V) hs 1 (a:=799) (b:=1000000)
      (by norm_num) h1
    have c2 := r67_quad_gt (r67_cN_rep .transition .V) hs 56 7 200 (by norm_num) (a:=3001)
      (b:=5000) (by norm_num) h2
    refine ⟨?_,?_,?_⟩
    · norm_num [middleConstant] at c0 ⊢; exact c0
    · norm_num [middleLinear] at c1 ⊢; exact c1
    · norm_num [middleQuadratic] at c2 ⊢; exact c2
  · obtain ⟨hs,-,h0,h1,h2⟩ := r67_midF_facts
    have c0 := r67_coeff_gt (r67_cN_rep .transition .F) hs 0 (a:=1267) (b:=25000000)
      (by norm_num) h0
    have c1 := r67_coeff_abs_lt (r67_cN_rep .transition .F) hs 1 (a:=421) (b:=500000)
      (by norm_num) h1
    have c2 := r67_quad_gt (r67_cN_rep .transition .F) hs 78 7 200 (by norm_num) (a:=13)
      (b:=20) (by norm_num) h2
    refine ⟨?_,?_,?_⟩
    · norm_num [middleConstant] at c0 ⊢; exact c0
    · norm_num [middleLinear] at c1 ⊢; exact c1
    · norm_num [middleQuadratic] at c2 ⊢; exact c2

theorem middle_positive (e : Endpoint) {z : ℝ} (hz : z∈Icc (3/20:ℝ) (19/100)) :
    (middleReserve e:ℝ)<aeval z (numerator .transition e) := by
  let u : ℝ := z-37/200
  have hu : |u|≤(7/200:ℝ) := by
    apply abs_le.mpr
    dsimp [u]
    exact ⟨by linarith [hz.1],by linarith [hz.2]⟩
  have hp := PowerTailBounds.quadratic_lower (r:=7/200) (middle_identity e) (by norm_num)
    (show |u|≤((7/200:ℚ):ℝ) by rw [show ((7/200:ℚ):ℝ)=7/200 by norm_num]; exact hu)
  have h0 : (middleConstant e:ℝ)<((centered .transition e).coeff 0:ℝ) := by
    exact_mod_cast (middle_coefficients e).1
  have h1 : |((centered .transition e).coeff 1:ℝ)|<(middleLinear e:ℝ) := by
    exact_mod_cast (middle_coefficients e).2.1
  have h2 : (middleQuadratic e:ℝ)<((centered .transition e).coeff 2:ℝ)-
      (PowerTailBounds.norm (centered .transition e) 3 (degree .transition e-2) (7/200):ℝ) := by
    exact_mod_cast (middle_coefficients e).2.2
  have hc2 : 0<(middleQuadratic e:ℝ) := by cases e <;> norm_num [middleQuadratic]
  have hlin : -(middleLinear e:ℝ)*|u|≤((centered .transition e).coeff 1:ℝ)*u := by
    have hh := mul_le_mul_of_nonneg_right h1.le (abs_nonneg u)
    rw [←abs_mul] at hh
    rw [neg_mul]
    exact (abs_le.mp hh).1
  have hquad := mul_le_mul_of_nonneg_right h2.le (sq_nonneg u)
  have hm := ChebyshevLeadingBounds.quadratic_min (a:=(middleConstant e:ℝ))
    (b:=-(middleLinear e:ℝ)) (x:=|u|) hc2
  have hr : (middleReserve e:ℝ)<(middleConstant e:ℝ)-
      (middleLinear e:ℝ)^2/(4*(middleQuadratic e:ℝ)) := by
    cases e <;> norm_num [middleReserve,middleConstant,middleLinear,middleQuadratic]
  have hid : aeval u (centered .transition e)=aeval z (numerator .transition e) := by
    simp [centered,center,u]
  rw [hid] at hp
  rw [sq_abs,neg_sq] at hm
  linarith

theorem full_V_identity :
    centered .full .V=C ((centered .full .V).coeff 0)+C ((centered .full .V).coeff 1)*X+
      C ((centered .full .V).coeff 2)*X^2+C ((centered .full .V).coeff 3)*X^3+
      C ((centered .full .V).coeff 4)*X^4+C ((centered .full .V).coeff 5)*X^5+
      tail (centered .full .V) 6 55 := by
  obtain ⟨hs,hl,-⟩ := r67_fullV_facts
  have hd := r67_natDegree_lt (r67_cN_rep .full .V) hs hl (by norm_num)
  conv_lhs => rw [r67_split _ 6 55 hd]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,mul_one,pow_one]

theorem full_V_coefficients :
    (41/500000:ℚ)<(centered .full .V).coeff 0 ∧
    (3777/500000:ℚ)<(centered .full .V).coeff 1 ∧
    (-2507/100000:ℚ)<(centered .full .V).coeff 2 ∧
    (58973/50000:ℚ)<(centered .full .V).coeff 3 ∧
    (-24597/10000:ℚ)<(centered .full .V).coeff 4 ∧
    (91789/100000:ℚ)<(centered .full .V).coeff 5-
      negativeNorm (centered .full .V) 6 55 (51/100) := by
  obtain ⟨hs,-,h0,h1,h2,h3,h4,h5⟩ := r67_fullV_facts
  have c0 := r67_coeff_gt (r67_cN_rep .full .V) hs 0 (a:=41) (b:=500000) (by norm_num) h0
  have c1 := r67_coeff_gt (r67_cN_rep .full .V) hs 1 (a:=3777) (b:=500000) (by norm_num) h1
  have c2 := r67_coeff_gt (r67_cN_rep .full .V) hs 2 (a:=-2507) (b:=100000) (by norm_num) h2
  have c3 := r67_coeff_gt (r67_cN_rep .full .V) hs 3 (a:=58973) (b:=50000) (by norm_num) h3
  have c4 := r67_coeff_gt (r67_cN_rep .full .V) hs 4 (a:=-24597) (b:=10000) (by norm_num) h4
  have c5 := r67_negtail_gt (r67_cN_rep .full .V) hs 5 55 51 100 (by norm_num) (a:=91789)
    (b:=100000) (by norm_num) h5
  rw [show (51/100:ℚ)=((51:ℕ):ℚ)/((100:ℕ):ℚ) by norm_num]
  norm_num at c0 c1 c2 c3 c4 c5 ⊢
  exact ⟨c0,c1,by linarith,c3,by linarith,c5⟩

theorem full_V_positive {z : ℝ} (hz : z∈Icc (19/100:ℝ) (7/10)) :
    (41/500000:ℝ)<aeval z (numerator .full .V) := by
  let u : ℝ := z-19/100
  have hu : u∈Icc (0:ℝ) (51/100:ℝ) := by
    dsimp [u]
    exact ⟨by linarith [hz.1],by linarith [hz.2]⟩
  have hu' : u∈Icc 0 ((51/100:ℚ):ℝ) := by rw [show ((51/100:ℚ):ℝ)=51/100 by norm_num]; exact hu
  have ht := DirectedPowerBounds.tail_lower (p:=centered .full .V) (k:=5) (n:=55) hu'
  have hi := congrArg (fun p : ℚ[X] => aeval u p) full_V_identity
  simp only [map_add,map_mul,map_pow,aeval_C,aeval_X,eq_ratCast] at hi
  rw [show (5:ℕ)+1=6 from rfl] at ht
  have hc :
      (41/500000:ℝ)<((centered .full .V).coeff 0:ℝ) ∧
      (3777/500000:ℝ)<((centered .full .V).coeff 1:ℝ) ∧
      (-2507/100000:ℝ)<((centered .full .V).coeff 2:ℝ) ∧
      (58973/50000:ℝ)<((centered .full .V).coeff 3:ℝ) ∧
      (-24597/10000:ℝ)<((centered .full .V).coeff 4:ℝ) ∧
      (91789/100000:ℝ)<((centered .full .V).coeff 5:ℝ)-
        (negativeNorm (centered .full .V) 6 55 (51/100):ℝ) := by
    obtain ⟨p0,p1,p2,p3,p4,p5⟩ := full_V_coefficients
    have q0 := (Rat.cast_lt (K:=ℝ)).mpr p0
    have q1 := (Rat.cast_lt (K:=ℝ)).mpr p1
    have q2 := (Rat.cast_lt (K:=ℝ)).mpr p2
    have q3 := (Rat.cast_lt (K:=ℝ)).mpr p3
    have q4 := (Rat.cast_lt (K:=ℝ)).mpr p4
    have q5 := (Rat.cast_lt (K:=ℝ)).mpr p5
    push_cast at q0 q1 q2 q3 q4 q5
    exact ⟨q0,q1,q2,q3,q4,q5⟩
  have h1 := mul_le_mul_of_nonneg_right hc.2.1.le hu.1
  have h2 := mul_le_mul_of_nonneg_right hc.2.2.1.le (sq_nonneg u)
  have h3 := mul_le_mul_of_nonneg_right hc.2.2.2.1.le (pow_nonneg hu.1 3)
  have h4 := mul_le_mul_of_nonneg_right hc.2.2.2.2.1.le (pow_nonneg hu.1 4)
  have h5 := mul_le_mul_of_nonneg_right hc.2.2.2.2.2.le (pow_nonneg hu.1 5)
  have hfactor := mul_nonneg (show 0≤51/100-u by linarith [hu.2])
    (show 0≤24597/10000-(91789/100000)*(u+51/100) by linarith [hu.2])
  have hq : (1637/10000:ℝ)≤58973/50000-(24597/10000)*u+(91789/100000)*u^2 := by
    linarith
  have hq3 := mul_le_mul_of_nonneg_right hq (pow_nonneg hu.1 3)
  have hinner : 0≤3777/500000-(2507/100000)*u+(1637/10000)*u^2 := by
    linarith [sq_nonneg (2*(1637/10000:ℝ)*u-2507/100000)]
  have hnonneg := mul_nonneg hu.1 hinner
  have hid : aeval u (centered .full .V)=aeval z (numerator .full .V) := by
    simp [centered,center,u]
  rw [hid] at hi
  linarith

theorem full_F_identity :
    centered .full .F=C ((centered .full .F).coeff 0)+C ((centered .full .F).coeff 1)*X+
      C ((centered .full .F).coeff 2)*X^2+C ((centered .full .F).coeff 3)*X^3+
      tail (centered .full .F) 4 79 := by
  obtain ⟨hs,hl,-⟩ := r67_fullF_facts
  have hd := r67_natDegree_lt (r67_cN_rep .full .F) hs hl (by norm_num)
  conv_lhs => rw [r67_split _ 4 79 hd]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,mul_one,pow_one]

theorem full_F_coefficients :
    (883/10000000:ℚ)<(centered .full .F).coeff 0 ∧
    (8137/1000000:ℚ)<(centered .full .F).coeff 1 ∧
    (-2479/100000:ℚ)<(centered .full .F).coeff 2 ∧
    (367/10000:ℚ)<(centered .full .F).coeff 3-
      negativeNorm (centered .full .F) 4 79 (51/100) := by
  obtain ⟨hs,-,h0,h1,h2,h3⟩ := r67_fullF_facts
  have c0 := r67_coeff_gt (r67_cN_rep .full .F) hs 0 (a:=883) (b:=10000000) (by norm_num) h0
  have c1 := r67_coeff_gt (r67_cN_rep .full .F) hs 1 (a:=8137) (b:=1000000) (by norm_num) h1
  have c2 := r67_coeff_gt (r67_cN_rep .full .F) hs 2 (a:=-2479) (b:=100000) (by norm_num) h2
  have c3 := r67_negtail_gt (r67_cN_rep .full .F) hs 3 79 51 100 (by norm_num) (a:=367)
    (b:=10000) (by norm_num) h3
  rw [show (51/100:ℚ)=((51:ℕ):ℚ)/((100:ℕ):ℚ) by norm_num]
  norm_num at c0 c1 c2 c3 ⊢
  exact ⟨c0,c1,by linarith,c3⟩

theorem full_F_positive {z : ℝ} (hz : z∈Icc (19/100:ℝ) (7/10)) :
    (883/10000000:ℝ)<aeval z (numerator .full .F) := by
  let u : ℝ := z-19/100
  have hu : u∈Icc (0:ℝ) (51/100:ℝ) := by
    dsimp [u]
    exact ⟨by linarith [hz.1],by linarith [hz.2]⟩
  have hu' : u∈Icc 0 ((51/100:ℚ):ℝ) := by rw [show ((51/100:ℚ):ℝ)=51/100 by norm_num]; exact hu
  have hp := DirectedPowerBounds.cubic_lower full_F_identity hu'
  have hc : (883/10000000:ℝ)<((centered .full .F).coeff 0:ℝ) ∧
      (8137/1000000:ℝ)<((centered .full .F).coeff 1:ℝ) ∧
      (-2479/100000:ℝ)<((centered .full .F).coeff 2:ℝ) ∧
      (367/10000:ℝ)<((centered .full .F).coeff 3:ℝ)-
        (negativeNorm (centered .full .F) 4 79 (51/100):ℝ) := by
    obtain ⟨p0,p1,p2,p3⟩ := full_F_coefficients
    have q0 := (Rat.cast_lt (K:=ℝ)).mpr p0
    have q1 := (Rat.cast_lt (K:=ℝ)).mpr p1
    have q2 := (Rat.cast_lt (K:=ℝ)).mpr p2
    have q3 := (Rat.cast_lt (K:=ℝ)).mpr p3
    push_cast at q0 q1 q2 q3
    exact ⟨q0,q1,q2,q3⟩
  have h1 := mul_le_mul_of_nonneg_right hc.2.1.le hu.1
  have h2 := mul_le_mul_of_nonneg_right hc.2.2.1.le (sq_nonneg u)
  have h3 := mul_le_mul_of_nonneg_right hc.2.2.2.le (pow_nonneg hu.1 3)
  have hinner : 0≤8137/1000000-(2479/100000)*u+(367/10000)*u^2 := by
    linarith [sq_nonneg (2*(367/10000:ℝ)*u-2479/100000)]
  have hnonneg := mul_nonneg hu.1 hinner
  have hid : aeval u (centered .full .F)=aeval z (numerator .full .F) := by
    simp [centered,center,u]
  rw [hid] at hp
  linarith

/-- A uniform reserve, strictly larger than the stated Taylor allowance. -/
theorem numerator_positive (r : Row) (e : Endpoint) {z : ℝ}
    (hz : z∈Icc (left r:ℝ) (right r:ℝ)) :
    (1/25000:ℝ)<aeval z (numerator r e) := by
  cases r
  · have hz' : z∈Icc (0:ℝ) (3/20) := by
      have h := hz
      norm_num [left,right] at h
      exact h
    have hh := low_positive e hz'
    cases e <;> norm_num [lowConstant] at hh <;> linarith
  · have hz' : z∈Icc (3/20:ℝ) (19/100) := by
      have h := hz
      norm_num [left,right] at h
      exact h
    have hh := middle_positive e hz'
    cases e <;> norm_num [middleReserve] at hh <;> linarith
  · have hz' : z∈Icc (19/100:ℝ) (7/10) := by
      have h := hz
      norm_num [left,right] at h
      exact h
    cases e
    · linarith [full_V_positive hz']
    · linarith [full_F_positive hz']

end SquaresInCircles.Eight.GlobalGA.JointNegativeAETD2.Certificate

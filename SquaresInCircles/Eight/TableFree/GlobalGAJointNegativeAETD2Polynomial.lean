module

public import SquaresInCircles.Eight.TableFree.GlobalGAJointNegativeAETD2PolynomialData

/-!
# The six exact whole-interval endpoint certificates

Uncompiled transcription of (19)--(26) in the joint-negative scalar
companion. The low and middle rows retain a quadratic leading part.
The full-D rows retain the prescribed fifth and third powers, charging
only adverse higher coefficients on their nonnegative interval.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.JointNegativeAETD2.Certificate
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

private theorem r67_shift_rep {S : Scaled} {p : ℚ[X]} (hp : S.Rep p) (num den : ℕ) (s t : ℤ)
    {a : ℚ} (hden : den≠0) (ha : a=num*s/den) (h1 : (1:ℚ)=num*t/den) :
    (S.center num den s t).Rep (DirectedPowerBounds.shift a p) := by
  have hc := hp.centered num den s t (a:=a-1) (b:=a+1) hden (by rw [← ha]; ring)
    (by rw [← h1]; ring)
  have he : WholeIntervalPolynomial.centered (a-1) (a+1) p=DirectedPowerBounds.shift a p := by
    rw [WholeIntervalPolynomial.centered,WholeIntervalPolynomial.affine,DirectedPowerBounds.shift,
      show (a-1+(a+1))/2=a by ring,show (a+1-(a-1))/2=1 by ring,map_one,one_mul]
  rwa [he] at hc

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

/-- The shift by `a=num/den`, through the fast centering on `[0,2a]`. -/
private theorem r67_fast_shift {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) (num den : ℕ) {a : ℚ}
    (hden : den≠0) (hnum : num≠0) (ha : a=num/den) :
    (r67_scale (c.center num den 1 1) den num).Rep (DirectedPowerBounds.shift a p) := by
  have h1 := hc.centered num den 1 1 (a:=0) (b:=2*a) hden (by rw [ha]; push_cast; ring)
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

private def r67_S : Scaled := r67_red
  ((((((((Scaled.var.sub ((Scaled.const (1/6)).mul (Scaled.var.pow 3))).add
    ((Scaled.const (1/120)).mul (Scaled.var.pow 5))).sub
    ((Scaled.const (1/5040)).mul (Scaled.var.pow 7))).add
    ((Scaled.const (1/362880)).mul (Scaled.var.pow 9))).sub
    ((Scaled.const (1/39916800)).mul (Scaled.var.pow 11))).add
    ((Scaled.const (1/6227020800)).mul (Scaled.var.pow 13))).sub
    ((Scaled.const (1/1307674368000)).mul (Scaled.var.pow 15))))
private theorem r67_S_rep : r67_S.Rep PositiveScalarPolynomials.sine := r67_rep_red
  ((((((((Scaled.rep_var.sub ((Scaled.rep_const _).mul (Scaled.rep_var.pow 3))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 5))).sub
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 7))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 9))).sub
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 11))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 13))).sub
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 15))))

private def r67_C : Scaled := r67_red
  (((((((((Scaled.ofNat 1).sub ((Scaled.const (1/2)).mul (Scaled.var.pow 2))).add
    ((Scaled.const (1/24)).mul (Scaled.var.pow 4))).sub
    ((Scaled.const (1/720)).mul (Scaled.var.pow 6))).add
    ((Scaled.const (1/40320)).mul (Scaled.var.pow 8))).sub
    ((Scaled.const (1/3628800)).mul (Scaled.var.pow 10))).add
    ((Scaled.const (1/479001600)).mul (Scaled.var.pow 12))).sub
    ((Scaled.const (1/87178291200)).mul (Scaled.var.pow 14))).add
    ((Scaled.const (1/20922789888000)).mul (Scaled.var.pow 16)))
private theorem r67_C_rep : r67_C.Rep PositiveScalarPolynomials.cosine := r67_rep_red
  ((((((((Scaled.rep_one.sub ((Scaled.rep_const _).mul (Scaled.rep_var.pow 2))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 4))).sub
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 6))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 8))).sub
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 10))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 12))).sub
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 14))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 16)))

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

/-- The numerator from its pieces, sharing the partial products and reducing as it goes. -/
private def r67_num (h a0 a1 a2 a3 w0 w1 w2 w3 v0 v1 v2 v3 : Scaled) : Scaled :=
  let p01 := r67_red (a0.mul a1)
  let p23 := r67_red (a2.mul a3)
  let t0 := r67_red ((w0.mul (v0.add (a0.pow 2))).mul (r67_red (a1.mul p23)))
  let t1 := r67_red ((w1.mul (v1.add (a1.pow 2))).mul (r67_red (a0.mul p23)))
  let t2 := r67_red ((w2.mul (v2.add (a2.pow 2))).mul (r67_red (p01.mul a3)))
  let t3 := r67_red ((w3.mul (v3.add (a3.pow 2))).mul (r67_red (p01.mul a2)))
  (r67_red (((Scaled.const 2).mul h).mul (r67_red (p01.mul p23)))).sub
    ((Scaled.const Rplus).mul (r67_red ((t0.add t1).add (t2.add t3))))

private theorem r67_num_rep {h a0 a1 a2 a3 w0 w1 w2 w3 v0 v1 v2 v3 : Scaled}
    {ph p0 p1 p2 p3 q0 q1 q2 q3 u0 u1 u2 u3 : ℚ[X]} (hh : h.Rep ph)
    (h0 : a0.Rep p0) (h1 : a1.Rep p1) (h2 : a2.Rep p2) (h3 : a3.Rep p3)
    (g0 : w0.Rep q0) (g1 : w1.Rep q1) (g2 : w2.Rep q2) (g3 : w3.Rep q3)
    (k0 : v0.Rep u0) (k1 : v1.Rep u1) (k2 : v2.Rep u2) (k3 : v3.Rep u3) :
    (r67_num h a0 a1 a2 a3 w0 w1 w2 w3 v0 v1 v2 v3).Rep
      (C 2*ph*(p0*p1*p2*p3)-C Rplus*
        (q0*(u0+p0^2)*(p1*p2*p3)+q1*(u1+p1^2)*(p0*p2*p3)+q2*(u2+p2^2)*(p0*p1*p3)+
          q3*(u3+p3^2)*(p0*p1*p2))) := by
  have p01 := r67_rep_red (h0.mul h1)
  have p23 := r67_rep_red (h2.mul h3)
  have t0 := r67_rep_red ((g0.mul (k0.add (h0.pow 2))).mul (r67_rep_red (h1.mul p23)))
  have t1 := r67_rep_red ((g1.mul (k1.add (h1.pow 2))).mul (r67_rep_red (h0.mul p23)))
  have t2 := r67_rep_red ((g2.mul (k2.add (h2.pow 2))).mul (r67_rep_red (p01.mul h3)))
  have t3 := r67_rep_red ((g3.mul (k3.add (h3.pow 2))).mul (r67_rep_red (p01.mul h2)))
  have hN := (r67_rep_red (((Scaled.rep_const 2).mul hh).mul (r67_rep_red (p01.mul p23)))).sub
    ((Scaled.rep_const Rplus).mul (r67_rep_red ((t0.add t1).add (t2.add t3))))
  have e : C 2*ph*(p0*p1*p2*p3)-C Rplus*
      (q0*(u0+p0^2)*(p1*p2*p3)+q1*(u1+p1^2)*(p0*p2*p3)+q2*(u2+p2^2)*(p0*p1*p3)+
        q3*(u3+p3^2)*(p0*p1*p2))=C 2*ph*(p0*p1*(p2*p3))-C Rplus*
      (q0*(u0+p0^2)*(p1*(p2*p3))+q1*(u1+p1^2)*(p0*(p2*p3))+
        (q2*(u2+p2^2)*(p0*p1*p3)+q3*(u3+p3^2)*(p0*p1*p2))) := by ring
  rw [e]
  exact hN

private def r67_k : Row → Scaled
  | .low => Scaled.const (13/20)
  | _ => r67_red <| ((((((Scaled.const (65433234/100000000)).sub
      ((Scaled.const (6770392/100000000)).mul Scaled.var)).add
      ((Scaled.const (39062724/100000000)).mul (Scaled.var.pow 2))).sub
      ((Scaled.const (29937498/100000000)).mul (Scaled.var.pow 3))).add
      ((Scaled.const (35999242/100000000)).mul (Scaled.var.pow 4))).sub
      ((Scaled.const (29068717/100000000)).mul (Scaled.var.pow 5))).add
      ((Scaled.const (14649232/100000000)).mul (Scaled.var.pow 6))
private theorem r67_kd_rep : (((((((Scaled.const (65433234/100000000)).sub
      ((Scaled.const (6770392/100000000)).mul Scaled.var)).add
      ((Scaled.const (39062724/100000000)).mul (Scaled.var.pow 2))).sub
      ((Scaled.const (29937498/100000000)).mul (Scaled.var.pow 3))).add
      ((Scaled.const (35999242/100000000)).mul (Scaled.var.pow 4))).sub
      ((Scaled.const (29068717/100000000)).mul (Scaled.var.pow 5))).add
      ((Scaled.const (14649232/100000000)).mul (Scaled.var.pow 6))).Rep (k .transition) :=
  ((((((Scaled.rep_const _).sub ((Scaled.rep_const _).mul Scaled.rep_var)).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 2))).sub
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 3))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 4))).sub
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 5))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 6))
private theorem r67_k_rep : ∀ r : Row,(r67_k r).Rep (k r)
  | .low => Scaled.rep_const _
  | .transition => r67_rep_red r67_kd_rep
  | .full => r67_rep_red r67_kd_rep

private def r67_c : Row → Scaled
  | .low => ((Scaled.const (69/50)).sub ((Scaled.const (13/5)).mul Scaled.var)).add
      ((Scaled.const (14/5)).mul (Scaled.var.pow 2))
  | _ => ((Scaled.const (230229/200000)).sub ((Scaled.const (9/10)).mul Scaled.var)).add
      ((Scaled.const (11/20)).mul (Scaled.var.pow 2))
private theorem r67_c_rep : ∀ r : Row,(r67_c r).Rep (c r)
  | .low => ((Scaled.rep_const _).sub ((Scaled.rep_const _).mul Scaled.rep_var)).add
      ((Scaled.rep_const _).mul (Scaled.rep_var.pow 2))
  | .transition => ((Scaled.rep_const _).sub ((Scaled.rep_const _).mul Scaled.rep_var)).add
      ((Scaled.rep_const _).mul (Scaled.rep_var.pow 2))
  | .full => ((Scaled.rep_const _).sub ((Scaled.rep_const _).mul Scaled.rep_var)).add
      ((Scaled.rep_const _).mul (Scaled.rep_var.pow 2))

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
  r67_red (r67_scale ((r67_N r e).center (r67_cnum r) (r67_cden r) 1 1) (r67_cden r) (r67_cnum r))
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

end SquaresInCircles.Eight.TableFree.GlobalGA.JointNegativeAETD2.Certificate

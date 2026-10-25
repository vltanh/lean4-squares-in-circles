module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeABT3ScalarData
public import SquaresInCircles.Eight.TableFree.PolynomialCertificates

/-!
# Nonradical lower bounds for the reference endpoints

Uncompiled Section 7. The low diagonal term uses its rational upper
constant. Every cosine-scaled positive baseline factor is proved
positive first, and the negative angular cost is multiplied by the
upper cosine polynomial, as required by its sign.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeABT3
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

namespace Certificate
open WholeIntervalPolynomial

/-! ### Kernel certificate of the baseline factor (scaled integer lists, as in
`GlobalGANegativeABT3Polynomial`) -/

section Certificates
open WholeIntervalPolynomial.Certificate
open PositiveTD.Certificate (S5 S9 S11 C4 C10 C12 etaQ cbar sigmabar)

private def gcdAcc : List ℤ → ℕ → ℕ
  | [],g => g
  | x :: l,g => gcdAcc l (Nat.gcd x.natAbs g)

private theorem gcdAcc_dvd_acc : ∀ (l : List ℤ) (g : ℕ),gcdAcc l g∣g
  | [],_ => dvd_rfl
  | _ :: l,_ => (gcdAcc_dvd_acc l _).trans (Nat.gcd_dvd_right _ _)

private theorem gcdAcc_dvd_mem : ∀ (l : List ℤ) (g : ℕ),∀ x∈l,((gcdAcc l g:ℕ):ℤ)∣x
  | [],_,_,hx => by simp at hx
  | _ :: l,_,x,hx => by
    rcases List.mem_cons.1 hx with rfl | hx
    · exact Int.natCast_dvd.2 ((gcdAcc_dvd_acc l _).trans (Nat.gcd_dvd_left _ _))
    · exact gcdAcc_dvd_mem l _ x hx

private theorem toPoly_map_div (g : ℤ) : ∀ l : List ℤ,(∀ x∈l,g∣x) →
    toPoly l=C (g:ℚ)*toPoly (l.map (fun x => x/g))
  | [],_ => by simp [toPoly]
  | x :: l,h => by
    have hx : (x:ℚ)=(g:ℚ)*((x/g:ℤ):ℚ) := by
      rw [← Int.cast_mul,Int.mul_ediv_cancel' (h x List.mem_cons_self)]
    rw [List.map_cons,toPoly,toPoly,
      toPoly_map_div g l (fun y hy => h y (List.mem_cons_of_mem _ hy)),hx,C_mul]
    ring

private theorem toPoly_map_div_zero : ∀ l : List ℤ,toPoly (l.map (fun x => x/(0:ℤ)))=0
  | [] => by simp [toPoly]
  | x :: l => by rw [List.map_cons,toPoly,toPoly_map_div_zero l,Int.ediv_zero]; simp

private def trim : List ℤ → List ℤ
  | [] => []
  | x :: l => match trim l with
    | [] => if x=0 then [] else [x]
    | y :: t => x :: y :: t

private theorem toPoly_trim : ∀ l : List ℤ,toPoly (trim l)=toPoly l
  | [] => rfl
  | x :: l => by
    have ih := toPoly_trim l
    simp only [trim]
    split
    · rename_i h
      rw [h] at ih
      change (0:ℚ[X])=toPoly l at ih
      change _=C (x:ℚ)+X*toPoly l
      rw [← ih]
      split_ifs with hx
      · rw [hx]; simp [toPoly]
      · change C (x:ℚ)+X*0=_
        rfl
    · rename_i y t h
      rw [h] at ih
      change C (x:ℚ)+X*toPoly (y :: t)=C (x:ℚ)+X*toPoly l
      rw [ih]

/-- The list divided by the gcd of its entries and its scale, without trailing zeros. -/
private def nrm (a : Scaled) : Scaled :=
  ⟨trim (a.l.map (fun x => x/((gcdAcc a.l a.s:ℕ):ℤ))),a.s/gcdAcc a.l a.s⟩

private theorem rep_nrm {a : Scaled} {p : ℚ[X]} (ha : a.Rep p) : (nrm a).Rep p := by
  unfold Scaled.Rep at *
  rw [nrm,toPoly_trim]
  have h1 := toPoly_map_div ((gcdAcc a.l a.s:ℕ):ℤ) a.l (gcdAcc_dvd_mem a.l a.s)
  have h2 : gcdAcc a.l a.s∣a.s := gcdAcc_dvd_acc a.l a.s
  generalize gcdAcc a.l a.s=g at h1 h2
  rcases Nat.eq_zero_or_pos g with rfl | hg
  · have hs : a.s=0 := Nat.eq_zero_of_zero_dvd h2
    simp only [Nat.cast_zero,Nat.div_zero,map_zero,zero_mul] at h1 ⊢
    exact toPoly_map_div_zero a.l
  · have hgq : (g:ℚ)≠0 := by exact_mod_cast hg.ne'
    have hdiv : ((a.s/g:ℕ):ℚ)=(a.s:ℚ)/g := Nat.cast_div h2 hgq
    apply mul_left_cancel₀ (show (C (g:ℚ):ℚ[X])≠0 from C_ne_zero.2 hgq)
    push_cast at h1
    rw [← h1,ha,hdiv,← mul_assoc,← C_mul,mul_div_cancel₀ _ hgq]

/-! #### Normalized operations -/

private def nadd (a b : Scaled) : Scaled := nrm (a.add b)
private def nsub (a b : Scaled) : Scaled := nrm (a.sub b)
private def nmul (a b : Scaled) : Scaled := nrm (a.mul b)
private def npow (a : Scaled) : ℕ → Scaled
  | 0 => Scaled.ofNat 1
  | n+1 => nmul (npow a n) a
private def ncst (q : ℚ) : Scaled := Scaled.const q
private def none' : Scaled := ⟨[],1⟩

private theorem rep_nadd {a b : Scaled} {p q : ℚ[X]} (ha : a.Rep p) (hb : b.Rep q) :
    (nadd a b).Rep (p+q) := rep_nrm (ha.add hb)
private theorem rep_nsub {a b : Scaled} {p q : ℚ[X]} (ha : a.Rep p) (hb : b.Rep q) :
    (nsub a b).Rep (p-q) := rep_nrm (ha.sub hb)
private theorem rep_nmul {a b : Scaled} {p q : ℚ[X]} (ha : a.Rep p) (hb : b.Rep q) :
    (nmul a b).Rep (p*q) := rep_nrm (ha.mul hb)
private theorem rep_npow {a : Scaled} {p : ℚ[X]} (ha : a.Rep p) : ∀ n : ℕ,(npow a n).Rep (p^n)
  | 0 => by rw [pow_zero]; exact Scaled.rep_one
  | n+1 => by rw [pow_succ]; exact rep_nmul (rep_npow ha n) ha
private theorem rep_ncst (q : ℚ) : (ncst q).Rep (C q) := Scaled.rep_const q

/-! #### Polynomials in a represented argument -/

private def bS5 (v : Scaled) : Scaled :=
  nadd (nsub v (nmul (ncst (1/6)) (npow v 3))) (nmul (ncst (1/120)) (npow v 5))
private theorem rep_bS5 {v : Scaled} {q : ℚ[X]} (hv : v.Rep q) : (bS5 v).Rep (S5.comp q) := by
  have e : S5.comp q=q-C (1/6)*q^3+C (1/120)*q^5 := by
    simp only [S5,add_comp,sub_comp,mul_comp,C_comp,X_comp,pow_comp]
  rw [e]
  exact rep_nadd (rep_nsub hv (rep_nmul (rep_ncst _) (rep_npow hv 3)))
    (rep_nmul (rep_ncst _) (rep_npow hv 5))
private def bS9 (v : Scaled) : Scaled :=
  nadd (nsub (bS5 v) (nmul (ncst (1/5040)) (npow v 7))) (nmul (ncst (1/362880)) (npow v 9))
private theorem rep_bS9 {v : Scaled} {q : ℚ[X]} (hv : v.Rep q) : (bS9 v).Rep (S9.comp q) := by
  have e : S9.comp q=S5.comp q-C (1/5040)*q^7+C (1/362880)*q^9 := by
    simp only [S9,add_comp,sub_comp,mul_comp,C_comp,X_comp,pow_comp]
  rw [e]
  exact rep_nadd (rep_nsub (rep_bS5 hv) (rep_nmul (rep_ncst _) (rep_npow hv 7)))
    (rep_nmul (rep_ncst _) (rep_npow hv 9))
private def bS11 (v : Scaled) : Scaled := nsub (bS9 v) (nmul (ncst (1/39916800)) (npow v 11))
private theorem rep_bS11 {v : Scaled} {q : ℚ[X]} (hv : v.Rep q) : (bS11 v).Rep (S11.comp q) := by
  have e : S11.comp q=S9.comp q-C (1/39916800)*q^11 := by
    simp only [S11,sub_comp,mul_comp,C_comp,X_comp,pow_comp]
  rw [e]
  exact rep_nsub (rep_bS9 hv) (rep_nmul (rep_ncst _) (rep_npow hv 11))
private def bC4 (v : Scaled) : Scaled :=
  nadd (nsub (Scaled.ofNat 1) (nmul (ncst (1/2)) (npow v 2))) (nmul (ncst (1/24)) (npow v 4))
private theorem rep_bC4 {v : Scaled} {q : ℚ[X]} (hv : v.Rep q) : (bC4 v).Rep (C4.comp q) := by
  have e : C4.comp q=1-C (1/2)*q^2+C (1/24)*q^4 := by
    simp only [C4,add_comp,sub_comp,mul_comp,C_comp,X_comp,pow_comp,one_comp]
  rw [e]
  exact rep_nadd (rep_nsub Scaled.rep_one (rep_nmul (rep_ncst _) (rep_npow hv 2)))
    (rep_nmul (rep_ncst _) (rep_npow hv 4))
private def bC10 (v : Scaled) : Scaled :=
  nsub (nadd (nsub (bC4 v) (nmul (ncst (1/720)) (npow v 6))) (nmul (ncst (1/40320)) (npow v 8)))
    (nmul (ncst (1/3628800)) (npow v 10))
private theorem rep_bC10 {v : Scaled} {q : ℚ[X]} (hv : v.Rep q) : (bC10 v).Rep (C10.comp q) := by
  have e : C10.comp q=C4.comp q-C (1/720)*q^6+C (1/40320)*q^8-C (1/3628800)*q^10 := by
    simp only [C10,add_comp,sub_comp,mul_comp,C_comp,X_comp,pow_comp]
  rw [e]
  exact rep_nsub (rep_nadd (rep_nsub (rep_bC4 hv) (rep_nmul (rep_ncst _) (rep_npow hv 6)))
    (rep_nmul (rep_ncst _) (rep_npow hv 8))) (rep_nmul (rep_ncst _) (rep_npow hv 10))
private def bC12 (v : Scaled) : Scaled := nadd (bC10 v) (nmul (ncst (1/479001600)) (npow v 12))
private theorem rep_bC12 {v : Scaled} {q : ℚ[X]} (hv : v.Rep q) : (bC12 v).Rep (C12.comp q) := by
  have e : C12.comp q=C10.comp q+C (1/479001600)*q^12 := by
    simp only [C12,add_comp,mul_comp,C_comp,X_comp,pow_comp]
  rw [e]
  exact rep_nadd (rep_bC10 hv) (rep_nmul (rep_ncst _) (rep_npow hv 12))

/-! #### The two families -/

private def bk : Family → Scaled → Scaled
  | .low,v => nadd (ncst (2/3)) (nmul (ncst (1/20)) v)
  | .high,v =>
    let t := nsub v (ncst (1/5))
    nsub (nadd (nadd (ncst (169/250)) (nmul (ncst (1/5)) t)) (nmul (ncst (9/10)) (npow t 2)))
      (nmul (ncst (13/10)) (npow t 3))
private theorem rep_bk (f : Family) {v : Scaled} {q : ℚ[X]} (hv : v.Rep q) :
    (bk f v).Rep ((k f).comp q) := by
  cases f
  · have e : (k .low).comp q=C (2/3)+C (1/20)*q := by
      simp only [k,add_comp,mul_comp,C_comp,X_comp]
    rw [e]
    exact rep_nadd (rep_ncst _) (rep_nmul (rep_ncst _) hv)
  · have e : (k .high).comp q=C (169/250)+C (1/5)*(q-C (1/5))+C (9/10)*(q-C (1/5))^2-
        C (13/10)*(q-C (1/5))^3 := by
      simp only [k,add_comp,sub_comp,mul_comp,C_comp,X_comp,pow_comp]
    rw [e]
    have ht := rep_nsub hv (rep_ncst (1/5))
    exact rep_nsub (rep_nadd (rep_nadd (rep_ncst _) (rep_nmul (rep_ncst _) ht))
      (rep_nmul (rep_ncst _) (rep_npow ht 2))) (rep_nmul (rep_ncst _) (rep_npow ht 3))
private def bl : Family → Scaled → Scaled
  | .low,v => nsub (ncst (533/500)) (nmul (ncst (4/25)) v)
  | .high,v =>
    let t := nsub v (ncst (1/5))
    nsub (nadd (ncst (41/40)) (nmul (ncst (11/50)) t)) (nmul (ncst (3/10)) (npow t 2))
private theorem rep_bl (f : Family) {v : Scaled} {q : ℚ[X]} (hv : v.Rep q) :
    (bl f v).Rep ((l f).comp q) := by
  cases f
  · have e : (l .low).comp q=C (533/500)-C (4/25)*q := by
      simp only [l,sub_comp,mul_comp,C_comp,X_comp]
    rw [e]
    exact rep_nsub (rep_ncst _) (rep_nmul (rep_ncst _) hv)
  · have e : (l .high).comp q=C (41/40)+C (11/50)*(q-C (1/5))-C (3/10)*(q-C (1/5))^2 := by
      simp only [l,add_comp,sub_comp,mul_comp,C_comp,X_comp,pow_comp]
    rw [e]
    have ht := rep_nsub hv (rep_ncst (1/5))
    exact rep_nsub (rep_nadd (rep_ncst _) (rep_nmul (rep_ncst _) ht))
      (rep_nmul (rep_ncst _) (rep_npow ht 2))
private def bm : Family → Scaled → Scaled
  | .low,v => nsub (nadd (ncst (59/50)) (nmul (ncst (1/10)) v)) (nmul (ncst (769/200)) (npow v 2))
  | .high,v =>
    let t := nsub v (ncst (1/4))
    nadd (nsub (ncst (24/25)) (nmul (ncst (7/10)) t)) (nmul (ncst (6/5)) (npow t 2))
private theorem rep_bm (f : Family) {v : Scaled} {q : ℚ[X]} (hv : v.Rep q) :
    (bm f v).Rep ((m f).comp q) := by
  cases f
  · have e : (m .low).comp q=C (59/50)+C (1/10)*q-C (769/200)*q^2 := by
      simp only [m,add_comp,sub_comp,mul_comp,C_comp,X_comp,pow_comp]
    rw [e]
    exact rep_nsub (rep_nadd (rep_ncst _) (rep_nmul (rep_ncst _) hv))
      (rep_nmul (rep_ncst _) (rep_npow hv 2))
  · have e : (m .high).comp q=C (24/25)-C (7/10)*(q-C (1/4))+C (6/5)*(q-C (1/4))^2 := by
      simp only [m,add_comp,sub_comp,mul_comp,C_comp,X_comp,pow_comp]
    rw [e]
    have ht := rep_nsub hv (rep_ncst (1/4))
    exact rep_nadd (rep_nsub (rep_ncst _) (rep_nmul (rep_ncst _) ht))
      (rep_nmul (rep_ncst _) (rep_npow ht 2))
private def belem : Family → Scaled → Scaled
  | .low,v => nadd (nadd (nadd (nmul (ncst 2) (bk .low v)) (nmul (ncst 3) (bl .low v)))
      (ncst (5/2-cbar))) (nmul (bm .low v) (nadd (nadd (Scaled.ofNat 1)
        (nmul (ncst (3/2-cbar)) (bC10 v))) (nmul (ncst (1/2+etaQ*(1-cbar)-sigmabar)) (bS9 v))))
  | .high,v => nadd (nadd (nadd (nmul (ncst 2) (bk .high v)) (nmul (ncst 3) (bl .high v)))
      (ncst 3)) (nmul (bm .high v) (nadd (nadd (Scaled.ofNat 1)
        (nmul (ncst 2) (bC10 v))) (nmul (ncst (1/2+3*etaQ/2-sigmabar)) (bS9 v))))
private theorem rep_belem (f : Family) {v : Scaled} {q : ℚ[X]} (hv : v.Rep q) :
    (belem f v).Rep ((elementary f).comp q) := by
  cases f
  · rw [elementary,if_pos rfl]
    simp only [add_comp,sub_comp,mul_comp,C_comp,one_comp]
    exact rep_nadd (rep_nadd (rep_nadd (rep_nmul (rep_ncst _) (rep_bk .low hv))
      (rep_nmul (rep_ncst _) (rep_bl .low hv))) (rep_ncst _)) (rep_nmul (rep_bm .low hv)
        (rep_nadd (rep_nadd Scaled.rep_one (rep_nmul (rep_ncst _) (rep_bC10 hv)))
          (rep_nmul (rep_ncst _) (rep_bS9 hv))))
  · rw [elementary,if_neg (by decide)]
    simp only [add_comp,sub_comp,mul_comp,C_comp,one_comp]
    exact rep_nadd (rep_nadd (rep_nadd (rep_nmul (rep_ncst _) (rep_bk .high hv))
      (rep_nmul (rep_ncst _) (rep_bl .high hv))) (rep_ncst _)) (rep_nmul (rep_bm .high hv)
        (rep_nadd (rep_nadd Scaled.rep_one (rep_nmul (rep_ncst _) (rep_bC10 hv)))
          (rep_nmul (rep_ncst _) (rep_bS9 hv))))

/-! #### The fourteen curves -/

private def bz (e : Curve) : Scaled := nadd Scaled.var (ncst (start e))
private theorem rep_bz (e : Curve) : (bz e).Rep (z e) := rep_nadd Scaled.rep_var (rep_ncst _)
private def blAt (e : Curve) : Scaled := bl (family e) (bz e)
private theorem rep_blAt (e : Curve) : (blAt e).Rep (lAt e) := rep_bl (family e) (rep_bz e)
private def bbaseA (e : Curve) : Scaled := belem (family e) (bz e)
private theorem rep_bbaseA (e : Curve) : (bbaseA e).Rep (baseA e) := rep_belem (family e) (rep_bz e)
private def cnum : Curve → ℕ
  | .lowH | .lowM | .lowSH | .lowSG | .lowGA => 1
  | .abG | .abH => 4
  | _ => 9
private def cden : Curve → ℕ
  | .lowH | .lowM | .lowSH | .lowSG | .lowGA => 8
  | .abG | .abH => 25
  | _ => 40
private theorem center_data (e : Curve) :
    cden e≠0 ∧ ((0:ℚ)+length e)/2=(cnum e:ℚ)*((1:ℤ):ℚ)/(cden e:ℚ) ∧
      (length e-(0:ℚ))/2=(cnum e:ℚ)*((1:ℤ):ℚ)/(cden e:ℚ) := by
  cases e <;> norm_num [cnum,cden,length,right,family,start,split]
private theorem rep_center {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) (e : Curve) :
    (c.center (cnum e) (cden e) 1 1).Rep (WholeIntervalPolynomial.centered 0 (length e) p) :=
  hc.centered (cnum e) (cden e) 1 1 (center_data e).1 (center_data e).2.1 (center_data e).2.2

/-- The kernel-checked facts of a whole-interval bound `r < lowerOn D` for the centered list `c`. -/
private abbrev certOK (r : ℚ) (D : ℕ) (c : Scaled) : Prop :=
  c.s≠0 ∧ c.l.length≤D+1 ∧
    r.num*((c.s*2^c.l.length:ℕ):ℤ)<lowerZ D (fun i => (chebList c.l).getD i 0)*((2*r.den:ℕ):ℤ)
private theorem of_certOK {r : ℚ} {D : ℕ} {c : Scaled} {a b : ℚ} {p : ℚ[X]}
    (hc : c.Rep (WholeIntervalPolynomial.centered a b p)) (h : certOK r D c) :
    WholeIntervalPolynomial.centered a b p=expansion D (WholeIntervalPolynomial.centered a b p) ∧
      r<lowerOn D a b p := by
  obtain ⟨hs,hl,hz⟩ := h
  refine ⟨hc.eq_expansion hs hl,?_⟩
  rw [lowerOn_eq_of_rep hc hs hl]
  have hb : (0:ℚ)<r.den := by exact_mod_cast r.pos
  have hs' : (0:ℚ)<c.s := by exact_mod_cast Nat.pos_of_ne_zero hs
  have h' : (r.num:ℚ)*((c.s*2^c.l.length:ℕ):ℚ)<
      (lowerZ D (fun i => (chebList c.l).getD i 0):ℚ)*((2*r.den:ℕ):ℚ) := by exact_mod_cast hz
  push_cast at h'
  rw [← Rat.num_div_den r,div_lt_div_iff₀ hb (by positivity)]
  linarith
private theorem baseline_check_lowH :
    certOK 0 14 ((nsub (bbaseA .lowH) (blAt .lowH)).center (cnum .lowH) (cden .lowH) 1 1) := by
  decide +kernel
private theorem baseline_check_lowM :
    certOK 0 14 ((nsub (bbaseA .lowM) (blAt .lowM)).center (cnum .lowM) (cden .lowM) 1 1) := by
  decide +kernel
private theorem baseline_check_lowSH :
    certOK 0 14 ((nsub (bbaseA .lowSH) (blAt .lowSH)).center (cnum .lowSH) (cden .lowSH) 1 1) := by
  decide +kernel
private theorem baseline_check_lowSG :
    certOK 0 14 ((nsub (bbaseA .lowSG) (blAt .lowSG)).center (cnum .lowSG) (cden .lowSG) 1 1) := by
  decide +kernel
private theorem baseline_check_lowGA :
    certOK 0 14 ((nsub (bbaseA .lowGA) (blAt .lowGA)).center (cnum .lowGA) (cden .lowGA) 1 1) := by
  decide +kernel
private theorem baseline_check_highH :
    certOK 0 14 ((nsub (bbaseA .highH) (blAt .highH)).center (cnum .highH) (cden .highH) 1 1) := by
  decide +kernel
private theorem baseline_check_highG :
    certOK 0 14 ((nsub (bbaseA .highG) (blAt .highG)).center (cnum .highG) (cden .highG) 1 1) := by
  decide +kernel
private theorem baseline_check_highB :
    certOK 0 14 ((nsub (bbaseA .highB) (blAt .highB)).center (cnum .highB) (cden .highB) 1 1) := by
  decide +kernel
private theorem baseline_check_highGA :
    certOK 0 14 ((nsub (bbaseA .highGA) (blAt .highGA)).center (cnum .highGA) (cden .highGA) 1 1) := by
  decide +kernel
private theorem baseline_check_highAB :
    certOK 0 14 ((nsub (bbaseA .highAB) (blAt .highAB)).center (cnum .highAB) (cden .highAB) 1 1) := by
  decide +kernel
private theorem baseline_check_gaH :
    certOK 0 14 ((nsub (bbaseA .gaH) (blAt .gaH)).center (cnum .gaH) (cden .gaH) 1 1) := by
  decide +kernel
private theorem baseline_check_gaB :
    certOK 0 14 ((nsub (bbaseA .gaB) (blAt .gaB)).center (cnum .gaB) (cden .gaB) 1 1) := by
  decide +kernel
private theorem baseline_check_abG :
    certOK 0 14 ((nsub (bbaseA .abG) (blAt .abG)).center (cnum .abG) (cden .abG) 1 1) := by
  decide +kernel
private theorem baseline_check_abH :
    certOK 0 14 ((nsub (bbaseA .abH) (blAt .abH)).center (cnum .abH) (cden .abH) 1 1) := by
  decide +kernel
end Certificates
open WholeIntervalPolynomial.Certificate (lowerZ chebList)

theorem baseline_factor_certificate (e : Curve) :
    WholeIntervalPolynomial.centered 0 (length e) (baseA e-lAt e)=
      WholeIntervalPolynomial.expansion 14
        (WholeIntervalPolynomial.centered 0 (length e) (baseA e-lAt e)) ∧
    0<WholeIntervalPolynomial.lowerOn 14 0 (length e) (baseA e-lAt e) := by
  have h : certOK 0 14 ((nsub (bbaseA e) (blAt e)).center (cnum e) (cden e) 1 1) := by
    cases e
    · exact baseline_check_lowH
    · exact baseline_check_lowM
    · exact baseline_check_lowSH
    · exact baseline_check_lowSG
    · exact baseline_check_lowGA
    · exact baseline_check_highH
    · exact baseline_check_highG
    · exact baseline_check_highB
    · exact baseline_check_highGA
    · exact baseline_check_highAB
    · exact baseline_check_gaH
    · exact baseline_check_gaB
    · exact baseline_check_abG
    · exact baseline_check_abH
  exact of_certOK (rep_center (rep_nsub (rep_bbaseA e) (rep_blAt e)) e) h

theorem elementary_lower (f : Family) {z : ℝ}
    (hz : z∈Icc (left f:ℝ) (right f:ℝ)) : aeval z (elementary f)≤NegativeABT3.nonradical f z := by
  have hzf := Explicit.frame_domain f hz
  have hm := (Explicit.positive f hz).2.2
  have ht := PositiveTD.Certificate.taylor_bounds hzf
  have hs := (transport_trig hzf).2.2.1
  have hc0 : 0≤Real.cos z := by linarith [(transport_trig hzf).1]
  have hD : Secondary.diagonal≤(899214066/1000000000:ℝ) := by
    have h := PositiveTD.Certificate.diagonal_le_cbar
    simp only [PositiveTD.Certificate.cbar] at h
    push_cast at h
    exact h
  have hS : PositiveTD.sigma≤(1415477291/1000000000:ℝ) := by
    have h := PositiveTD.Certificate.sigma_le_sigmabar
    simp only [PositiveTD.Certificate.sigmabar] at h
    push_cast at h
    exact h
  cases f
  · have hcos := mul_le_mul_of_nonneg_left ht.2.2.2.2.1
      (show (0:ℝ)≤3/2-899214066/1000000000 by norm_num)
    have hsin := mul_le_mul_of_nonpos_left ht.2.2.1
      (show (1/2:ℝ)+(293/1000)*(1-899214066/1000000000)-1415477291/1000000000≤0 by norm_num)
    have hdc := mul_le_mul_of_nonneg_right hD hc0
    have hds := mul_le_mul_of_nonneg_right hD hs
    have hss := mul_le_mul_of_nonneg_right hS hs
    have hinner : 1+(3/2-899214066/1000000000)*aeval z PositiveTD.Certificate.C10+
        (1/2+(293/1000)*(1-899214066/1000000000)-1415477291/1000000000)*
          aeval z PositiveTD.Certificate.S9≤
      1+(3/2-Secondary.diagonal)*Real.cos z+
        (1/2+PositiveTD.eta*(1-Secondary.diagonal)-PositiveTD.sigma)*Real.sin z := by
      simp only [PositiveTD.eta]
      linarith
    have hprod := mul_le_mul_of_nonneg_left hinner hm.le
    simp only [elementary,NegativeABT3.nonradical,↓reduceIte,map_add,map_sub,map_mul,
      map_one,aeval_C,eq_ratCast,Explicit.k_eval,Explicit.l_eval,Explicit.m_eval]
    push_cast
    norm_num only [PositiveTD.Certificate.cbar,PositiveTD.Certificate.sigmabar,
      PositiveTD.Certificate.etaQ] at hprod ⊢
    linarith
  · have hsin := mul_le_mul_of_nonpos_left ht.2.2.1
      (show (1/2:ℝ)+3*(293/1000)/2-1415477291/1000000000≤0 by norm_num)
    have hss := mul_le_mul_of_nonneg_right hS hs
    have hinner : 1+2*aeval z PositiveTD.Certificate.C10+
        (1/2+3*(293/1000)/2-1415477291/1000000000)*aeval z PositiveTD.Certificate.S9≤
      1+2*Real.cos z+(1/2+3*PositiveTD.eta/2-PositiveTD.sigma)*Real.sin z := by
      simp only [PositiveTD.eta]
      linarith [ht.2.2.2.2.1]
    have hprod := mul_le_mul_of_nonneg_left hinner hm.le
    simp only [elementary,NegativeABT3.nonradical,↓reduceIte,reduceCtorEq,map_add,map_sub,map_mul,
      map_one,aeval_C,eq_ratCast,Explicit.k_eval,Explicit.l_eval,Explicit.m_eval]
    push_cast
    norm_num only [PositiveTD.Certificate.cbar,PositiveTD.Certificate.sigmabar,
      PositiveTD.Certificate.etaQ] at hprod ⊢
    linarith
end Certificate

namespace Analytic
open Certificate (Curve)

theorem cost_nonnegative (e : Curve) {z : ℝ} (hz : Domain e z) : 0≤cost e z := by
  have hl := (Explicit.positive (Certificate.family e) (domains e hz).1).2.1
  cases e <;> simp [cost,Certificate.selected] <;> linarith

theorem base_lower (e : Curve) {z : ℝ} (hz : Domain e z) :
    aeval (z-(Certificate.start e:ℝ)) (Certificate.baseA e)≤
      NegativeABT3.nonradical (Certificate.family e) z := by
  simpa [Certificate.baseA,aeval_comp] using Certificate.elementary_lower (Certificate.family e) (domains e hz).1

theorem base_factor_positive (e : Curve) {z : ℝ} (hz : Domain e z) :
    0<aeval (z-(Certificate.start e:ℝ)) (Certificate.baseA e)-Explicit.l (Certificate.family e) z := by
  have hh := WholeIntervalPolynomial.positive_on_interval (Certificate.length_positive e)
    (Certificate.baseline_factor_certificate e).1 (Certificate.baseline_factor_certificate e).2
    (by rw [Rat.cast_zero]; exact native_domain e hz)
  simpa using hh

theorem extra_lower (e : Curve) {z : ℝ} (hz : Domain e z) :
    aeval (z-(Certificate.start e:ℝ)) (Certificate.extraA e)≤extra e z := by
  have hd := domains e hz
  have hn := PositiveTD.Certificate.taylor_bounds hd.2.2.1
  have hcoeff := cost_nonnegative e hz
  have hcost := mul_le_mul_of_nonneg_left (sub_le_sub_right hn.2.2.2.2.1 1) hcoeff
  by_cases he : e=.lowM
  · subst e
    have hrest := PositiveTD.Certificate.taylor_bounds hd.2.2.2
    have hcap := PositiveTD.Certificate.taylor_bounds (show frameCap∈Icc 0 frameCap by norm_num [frameCap])
    have hb := Explicit.positive .low hd.1
    have h₁ := mul_le_mul_of_nonneg_left
      (show aeval (frameCap-z) PositiveTD.Certificate.C10+aeval (frameCap-z) PositiveTD.Certificate.S11-1≤
        PositiveAngularEnvelope.phi (frameCap-z)-1 by
          dsimp [PositiveAngularEnvelope.phi]; linarith [hrest.2.1,hrest.2.2.2.2.1]) hb.1.le
    have h₂ := mul_le_mul_of_nonneg_left (sub_le_sub_right hcap.2.2.2.2.1 1)
      (show 0≤Explicit.l .low z by linarith [hb.2.1])
    have hev : algebraMap ℚ ℝ (PositiveTD.Certificate.C10.eval PositiveTD.Certificate.h)=
        aeval frameCap PositiveTD.Certificate.C10 := by
      rw [← Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]
      norm_num [PositiveTD.Certificate.h,frameCap]
    have hh : algebraMap ℚ ℝ PositiveTD.Certificate.h=frameCap := by
      norm_num [PositiveTD.Certificate.h,frameCap]
    simp only [Certificate.extraA,extra,↓reduceIte,map_add,map_sub,map_mul,map_one,aeval_comp,
      aeval_C,hev,hh,native_z,native_k,native_l,Certificate.family]
    linarith
  · simp only [Certificate.extraA,if_neg he,extra,if_neg he,map_sub,map_mul,aeval_comp,
      native_cost,native_negativeAngle,aeval_C,map_one,native_z]
    split_ifs <;> norm_num [PositiveTD.Certificate.h,frameCap] at hcost ⊢ <;> linarith

theorem scaled_extra_nonpositive (e : Curve) {z : ℝ} (he : Certificate.scaled e=true)
    (hz : Domain e z) : extra e z≤0 := by
  have hcost := mul_nonpos_of_nonneg_of_nonpos (cost_nonnegative e hz)
    (sub_nonpos.mpr (Real.cos_le_one (negativeAngle e z)))
  cases e <;> simp only [Certificate.scaled] at he <;> first | contradiction |
    simpa [extra,Certificate.separated] using hcost

theorem nonradical_lower (e : Curve) {z : ℝ} (hz : Domain e z) :
    aeval (z-(Certificate.start e:ℝ)) (Certificate.A e)≤nonradical e z := by
  have hd := domains e hz
  have ht := PositiveTD.Certificate.taylor_bounds hd.2.1
  have hc0 : 0≤Real.cos (angle e z) := by linarith [(transport_trig hd.2.1).1]
  have hbase := base_lower e hz
  have hextra := extra_lower e hz
  by_cases he : Certificate.scaled e=true
  · have hl : 0≤Explicit.l (Certificate.family e) z :=
      by linarith [(Explicit.positive (Certificate.family e) hd.1).2.1]
    have hpos := base_factor_positive e hz
    have h₁ := mul_le_mul ht.2.2.2.2.1 (sub_le_sub_right hbase (Explicit.l (Certificate.family e) z))
      hpos.le hc0
    have h₂ := mul_le_mul_of_nonneg_left ht.2.1 (show 0≤(13/12)*Explicit.l (Certificate.family e) z by positivity)
    have he0 := scaled_extra_nonpositive e he hz
    have h₃ := mul_le_mul_of_nonpos_right ht.2.2.2.2.2 (hextra.trans he0)
    have h₄ := mul_le_mul_of_nonneg_left hextra hc0
    simp only [Certificate.A,if_pos he,nonradical,if_pos he,map_add,map_mul,map_sub,
      aeval_comp,native_angle,native_l,aeval_C,eq_ratCast]
    push_cast
    linarith
  · simp only [Certificate.A,if_neg he,nonradical,if_neg he,map_add]
    exact add_le_add hbase hextra

end Analytic
end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeABT3

module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeABT3PolynomialData
public import SquaresInCircles.Eight.TableFree.PolynomialCertificates

/-!
# Positivity of all fourteen BT3 reference numerators

Uncompiled Section 8. Seven curves have direct coefficient bounds,
five use their positive constant and exact polynomial quotient, and
the two tight low curves use the displayed reversed power tails.
The two low estimates retain their full quadratic reserves.
-/

@[expose] public section
noncomputable section
open Set Polynomial
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeABT3.Certificate
open WholeIntervalPolynomial

/-! ### Kernel certificates

Every polynomial of `GlobalGANegativeABT3PolynomialData` is mirrored by a scaled integer
coefficient list (`PolynomialCertificates`), built with the same operations; the lists are
divided by the gcd of their entries after every composite step. -/

section Certificates
open WholeIntervalPolynomial.Certificate
open PositiveTD.Certificate (S5 S9 S11 C4 C10 C12 num3 num4 etaQ Rbar cbar sigmabar)

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
private def bkAt (e : Curve) : Scaled := bk (family e) (bz e)
private theorem rep_bkAt (e : Curve) : (bkAt e).Rep (kAt e) := rep_bk (family e) (rep_bz e)
private def blAt (e : Curve) : Scaled := bl (family e) (bz e)
private theorem rep_blAt (e : Curve) : (blAt e).Rep (lAt e) := rep_bl (family e) (rep_bz e)
private def bmAt (e : Curve) : Scaled := bm (family e) (bz e)
private theorem rep_bmAt (e : Curve) : (bmAt e).Rep (mAt e) := rep_bm (family e) (rep_bz e)
private def brot (e : Curve) : Scaled :=
  nmul (bmAt e) (nadd (bC12 (bz e)) (nmul (ncst etaQ) (bS9 (bz e))))
private theorem rep_brot (e : Curve) : (brot e).Rep (rotation e) :=
  rep_nmul (rep_bmAt e) (rep_nadd (rep_bC12 (rep_bz e)) (rep_nmul (rep_ncst _) (rep_bS9 (rep_bz e))))
private def bangle (e : Curve) : Scaled :=
  match e with
  | .lowGA | .highGA | .highAB => bz e
  | .gaH | .gaB => ncst (1/4)
  | .abG | .abH => ncst (19/50)
  | _ => none'
private theorem rep_bangle : ∀ e : Curve,(bangle e).Rep (angle e)
  | .lowGA => rep_bz _ | .highGA => rep_bz _ | .highAB => rep_bz _
  | .gaH => rep_ncst _ | .gaB => rep_ncst _ | .abG => rep_ncst _ | .abH => rep_ncst _
  | .lowH => Scaled.rep_zero | .lowM => Scaled.rep_zero | .lowSH => Scaled.rep_zero
  | .lowSG => Scaled.rep_zero | .highH => Scaled.rep_zero | .highG => Scaled.rep_zero
  | .highB => Scaled.rep_zero
private def bneg (e : Curve) : Scaled :=
  match e with
  | .lowSH | .lowSG => ncst PositiveTD.Certificate.h
  | .gaH | .gaB | .abG | .abH => nsub (bz e) (bangle e)
  | _ => bz e
private theorem rep_bneg : ∀ e : Curve,(bneg e).Rep (negativeAngle e)
  | .lowSH => rep_ncst _ | .lowSG => rep_ncst _
  | .gaH => rep_nsub (rep_bz _) (rep_bangle _) | .gaB => rep_nsub (rep_bz _) (rep_bangle _)
  | .abG => rep_nsub (rep_bz _) (rep_bangle _) | .abH => rep_nsub (rep_bz _) (rep_bangle _)
  | .lowH => rep_bz _ | .lowM => rep_bz _ | .lowGA => rep_bz _ | .highH => rep_bz _
  | .highG => rep_bz _ | .highB => rep_bz _ | .highGA => rep_bz _ | .highAB => rep_bz _
private def bcost (e : Curve) : Scaled :=
  match selected e with
  | some j => if j=0 then Scaled.ofNat 1 else blAt e
  | none => none'
private theorem r69_cost_l (e : Curve) {j : Fin 4} (hj : selected e=some j) (hj0 : j≠0 := by decide) :
    (bcost e).Rep (cost e) := by
  unfold bcost cost
  rw [hj]
  simp only [hj0,↓reduceIte]
  exact rep_blAt e
private theorem rep_bcost : ∀ e : Curve,(bcost e).Rep (cost e)
  | .lowH => Scaled.rep_one | .lowSH => Scaled.rep_one | .highH => Scaled.rep_one
  | .gaH => Scaled.rep_one | .abH => Scaled.rep_one
  | .lowM => r69_cost_l .lowM rfl | .lowSG => r69_cost_l .lowSG rfl
  | .highG => r69_cost_l .highG rfl | .abG => r69_cost_l .abG rfl
  | .highB => r69_cost_l .highB rfl | .gaB => r69_cost_l .gaB rfl
  | .lowGA => Scaled.rep_zero | .highGA => Scaled.rep_zero | .highAB => Scaled.rep_zero
private def bbaseA (e : Curve) : Scaled := belem (family e) (bz e)
private theorem rep_bbaseA (e : Curve) : (bbaseA e).Rep (baseA e) := rep_belem (family e) (rep_bz e)
private def bextraA (e : Curve) : Scaled :=
  if e=.lowM then
    nadd (nmul (bkAt e) (nsub (nadd (bC10 (nsub (ncst PositiveTD.Certificate.h) (bz e)))
        (bS11 (nsub (ncst PositiveTD.Certificate.h) (bz e)))) (Scaled.ofNat 1)))
      (nmul (blAt e) (nsub (bC10 (ncst PositiveTD.Certificate.h)) (Scaled.ofNat 1)))
  else nsub (nmul (bcost e) (nsub (bC10 (bneg e)) (Scaled.ofNat 1)))
    (if separated e then nmul (ncst (109/160)) (nsub (ncst PositiveTD.Certificate.h) (bz e))
      else none')
private theorem rep_bextraA (e : Curve) : (bextraA e).Rep (extraA e) := by
  unfold bextraA extraA
  split_ifs
  · have e1 : (C10+S11).comp (C PositiveTD.Certificate.h-z e)=
        C10.comp (C PositiveTD.Certificate.h-z e)+S11.comp (C PositiveTD.Certificate.h-z e) :=
      add_comp
    have e2 : (C (C10.eval PositiveTD.Certificate.h-1):ℚ[X])=C10.comp (C PositiveTD.Certificate.h)-1 := by
      rw [comp_C,map_sub,map_one]
    rw [e1,e2]
    have hz := rep_nsub (rep_ncst PositiveTD.Certificate.h) (rep_bz e)
    exact rep_nadd (rep_nmul (rep_bkAt e) (rep_nsub (rep_nadd (rep_bC10 hz) (rep_bS11 hz))
      Scaled.rep_one)) (rep_nmul (rep_blAt e) (rep_nsub (rep_bC10 (rep_ncst _)) Scaled.rep_one))
  · exact rep_nsub (rep_nmul (rep_bcost e) (rep_nsub (rep_bC10 (rep_bneg e)) Scaled.rep_one))
      (rep_nmul (rep_ncst _) (rep_nsub (rep_ncst _) (rep_bz e)))
  · exact rep_nsub (rep_nmul (rep_bcost e) (rep_nsub (rep_bC10 (rep_bneg e)) Scaled.rep_one))
      Scaled.rep_zero
private def bA (e : Curve) : Scaled :=
  if scaled e then
    nadd (nadd (nadd (nmul (bC10 (bangle e)) (nsub (bbaseA e) (blAt e))) (blAt e))
      (nmul (nmul (ncst (13/12)) (blAt e)) (bS11 (bangle e)))) (nmul (bC12 (bangle e)) (bextraA e))
  else nadd (bbaseA e) (bextraA e)
private theorem rep_bA (e : Curve) : (bA e).Rep (A e) := by
  unfold bA A
  split_ifs
  · exact rep_nadd (rep_nadd (rep_nadd (rep_nmul (rep_bC10 (rep_bangle e))
      (rep_nsub (rep_bbaseA e) (rep_blAt e))) (rep_blAt e))
      (rep_nmul (rep_nmul (rep_ncst _) (rep_blAt e)) (rep_bS11 (rep_bangle e))))
      (rep_nmul (rep_bC12 (rep_bangle e)) (rep_bextraA e))
  · exact rep_nadd (rep_bbaseA e) (rep_bextraA e)
private def bbaseP (e : Curve) : Fin 4 → Scaled :=
  ![nadd (Scaled.ofNat 1) (npow (bkAt e) 2),nadd (npow (bkAt e) 2) (npow (blAt e) 2),
    nadd (npow (blAt e) 2) (npow (bmAt e) 2),nadd (Scaled.ofNat 1) (npow (brot e) 2)]
private theorem rep_bbaseP (e : Curve) (j : Fin 4) : (bbaseP e j).Rep (baseP e j) := by
  fin_cases j
  · exact rep_nadd Scaled.rep_one (rep_npow (rep_bkAt e) 2)
  · exact rep_nadd (rep_npow (rep_bkAt e) 2) (rep_npow (rep_blAt e) 2)
  · exact rep_nadd (rep_npow (rep_blAt e) 2) (rep_npow (rep_bmAt e) 2)
  · exact rep_nadd Scaled.rep_one (rep_npow (rep_brot e) 2)
private def bpair (e : Curve) : Fin 4 → Scaled :=
  ![bkAt e,nmul (bkAt e) (blAt e),nmul (blAt e) (bmAt e),brot e]
private theorem rep_bpair (e : Curve) (j : Fin 4) : (bpair e j).Rep (pairProduct e j) := by
  fin_cases j
  · exact rep_bkAt e
  · exact rep_nmul (rep_bkAt e) (rep_blAt e)
  · exact rep_nmul (rep_blAt e) (rep_bmAt e)
  · exact rep_brot e
private def bscaledP (e : Curve) (j : Fin 4) : Scaled :=
  if atG e=true ∧ j=1 then nadd (npow (blAt e) 2) (nmul (npow (bkAt e) 2) (npow (bC12 (bangle e)) 2))
  else if atG e=false ∧ j=2 then
    nadd (npow (blAt e) 2) (nmul (npow (bmAt e) 2) (npow (bC12 (bangle e)) 2))
  else nmul (npow (bC12 (bangle e)) 2) (bbaseP e j)
private theorem rep_bscaledP (e : Curve) (j : Fin 4) : (bscaledP e j).Rep (scaledP e j) := by
  unfold bscaledP scaledP
  split_ifs
  · exact rep_nadd (rep_npow (rep_blAt e) 2) (rep_nmul (rep_npow (rep_bkAt e) 2)
      (rep_npow (rep_bC12 (rep_bangle e)) 2))
  · exact rep_nadd (rep_npow (rep_blAt e) 2) (rep_nmul (rep_npow (rep_bmAt e) 2)
      (rep_npow (rep_bC12 (rep_bangle e)) 2))
  · exact rep_nmul (rep_npow (rep_bC12 (rep_bangle e)) 2) (rep_bbaseP e j)
private def bP (e : Curve) (j : Fin 4) : Scaled :=
  nsub (if scaled e then bscaledP e j else bbaseP e j)
    (if selected e=some j then
      nmul (nmul (nmul (ncst 2) (if scaled e then npow (bC10 (bangle e)) 2 else Scaled.ofNat 1))
        (bpair e j)) (bS11 (bneg e))
    else none')
private theorem rep_bP (e : Curve) (j : Fin 4) : (bP e j).Rep (P e j) := by
  unfold bP P
  have h1 : (if scaled e then bscaledP e j else bbaseP e j).Rep
      (if scaled e then scaledP e j else baseP e j) := by
    split_ifs
    · exact rep_bscaledP e j
    · exact rep_bbaseP e j
  refine rep_nsub h1 ?_
  split_ifs
  · exact rep_nmul (rep_nmul (rep_nmul (rep_ncst _) (rep_npow (rep_bC10 (rep_bangle e)) 2))
      (rep_bpair e j)) (rep_bS11 (rep_bneg e))
  · exact rep_nmul (rep_nmul (rep_nmul (rep_ncst _) Scaled.rep_one) (rep_bpair e j))
      (rep_bS11 (rep_bneg e))
  · exact Scaled.rep_zero

/-! #### The masses -/

private def btrunc (a : Scaled) : Scaled :=
  ⟨[a.l.getD 0 0,a.l.getD 1 0,a.l.getD 2 0,a.l.getD 3 0],a.s⟩
private theorem trunc3_eq (p : ℚ[X]) : PositiveBT3.LowCertificate.truncate3 p=
    C (p.coeff 0)+C (p.coeff 1)*X+C (p.coeff 2)*X^2+C (p.coeff 3)*X^3 := by
  simp [PositiveBT3.LowCertificate.truncate3,Fin.sum_univ_four]
private theorem rep_btrunc {a : Scaled} {p : ℚ[X]} (ha : a.Rep p) (hs : a.s≠0) :
    (btrunc a).Rep (PositiveBT3.LowCertificate.truncate3 p) := by
  have hs' : (a.s:ℚ)≠0 := by exact_mod_cast hs
  have hC : C (a.s:ℚ)*C ((a.s:ℚ)⁻¹)=1 := by rw [← map_mul,mul_inv_cancel₀ hs',map_one]
  have hd (x : ℚ) : x/(a.s:ℚ)=(a.s:ℚ)⁻¹*x := by ring
  unfold Scaled.Rep
  rw [trunc3_eq,ha.coeff hs 0,ha.coeff hs 1,ha.coeff hs 2,ha.coeff hs 3]
  simp only [btrunc,toPoly,hd,map_mul,mul_zero,add_zero]
  linear_combination (-(C ((a.l.getD 0 0:ℤ):ℚ)+C ((a.l.getD 1 0:ℤ):ℚ)*X+
    C ((a.l.getD 2 0:ℤ):ℚ)*X^2+C ((a.l.getD 3 0:ℤ):ℚ)*X^3))*hC
private def bhead (a : Scaled) : Scaled := ⟨[a.l.getD 0 0],a.s⟩
private theorem rep_bhead {a : Scaled} {p : ℚ[X]} (ha : a.Rep p) (hs : a.s≠0) :
    (bhead a).Rep (C (p.eval 0)) := by
  have hs' : (a.s:ℚ)≠0 := by exact_mod_cast hs
  unfold Scaled.Rep
  rw [← coeff_zero_eq_eval_zero,ha.coeff hs]
  simp only [bhead,toPoly,mul_zero,add_zero]
  rw [← map_mul]
  congr 1
  field_simp
private def binv (a : Scaled) : Scaled := ⟨[(a.s:ℤ)],(a.l.getD 0 0).toNat⟩
private theorem rep_binv {a : Scaled} {p : ℚ[X]} (ha : a.Rep p) (hs : a.s≠0)
    (h0 : 0<a.l.getD 0 0) : (binv a).Rep (C (1/p.eval 0)) := by
  have hs' : (a.s:ℚ)≠0 := by exact_mod_cast hs
  have h0' : ((a.l.getD 0 0:ℤ):ℚ)≠0 := by exact_mod_cast h0.ne'
  unfold Scaled.Rep
  rw [← coeff_zero_eq_eval_zero,ha.coeff hs]
  simp only [binv,toPoly,mul_zero,add_zero,Int.cast_natCast]
  rw [← map_mul]
  congr 1
  have ht : (((a.l.getD 0 0).toNat:ℕ):ℚ)=((a.l.getD 0 0:ℤ):ℚ) := by
    rw [← Int.cast_natCast,Int.toNat_of_nonneg h0.le]
  rw [ht]
  field_simp
private def bmassInner (p : Scaled) : Scaled :=
  let w := nmul (binv p) (nsub (btrunc p) (bhead p))
  nadd (nsub (nadd (Scaled.ofNat 1) (nmul (ncst (1/2)) w))
    (nmul (ncst (1/8)) (npow w 2))) (nmul (ncst (1/16)) (npow w 3))
private def bmass (e : Curve) (j : Fin 4) (p : Scaled) : Scaled :=
  if family e=.low ∧ j=3 then Scaled.ofNat 1 else nmul (ncst (rho e j)) (btrunc (bmassInner p))
/-- The facts the kernel checks for the mass built on `p`. -/
private abbrev massSide (p : Scaled) : Prop := p.s≠0 ∧ 0<p.l.getD 0 0 ∧ (bmassInner p).s≠0
private theorem rep_bmass (e : Curve) (j : Fin 4) {p : Scaled} (hp : p.Rep (P e j))
    (h : massSide p) : (bmass e j p).Rep (mass e j) := by
  obtain ⟨hs,h0,hi⟩ := h
  unfold bmass mass
  split_ifs
  · exact Scaled.rep_one
  · dsimp only
    have hw := rep_nmul (rep_binv hp hs h0) (rep_nsub (rep_btrunc hp hs) (rep_bhead hp hs))
    have hin : (bmassInner p).Rep _ :=
      rep_nadd (rep_nsub (rep_nadd Scaled.rep_one (rep_nmul (rep_ncst (1/2)) hw))
        (rep_nmul (rep_ncst (1/8)) (rep_npow hw 2))) (rep_nmul (rep_ncst (1/16)) (rep_npow hw 3))
    exact rep_nmul (rep_ncst _) (rep_btrunc hin hi)

/-! #### The numerators -/

private def bnum3 (A P0 P1 P2 r0 r1 r2 : Scaled) : Scaled :=
  nsub (nmul (nmul (nmul (nmul (ncst 2) A) r0) r1) r2) (nmul (ncst Rbar)
    (nadd (nadd (nmul (nmul (nadd P0 (npow r0 2)) r1) r2) (nmul (nmul (nadd P1 (npow r1 2)) r0) r2))
      (nmul (nmul (nadd P2 (npow r2 2)) r0) r1)))
private theorem rep_bnum3 {A P0 P1 P2 r0 r1 r2 : Scaled} {a p0 p1 p2 s0 s1 s2 : ℚ[X]}
    (hA : A.Rep a) (h0 : P0.Rep p0) (h1 : P1.Rep p1) (h2 : P2.Rep p2)
    (g0 : r0.Rep s0) (g1 : r1.Rep s1) (g2 : r2.Rep s2) :
    (bnum3 A P0 P1 P2 r0 r1 r2).Rep (num3 a p0 p1 p2 s0 s1 s2) :=
  rep_nsub (rep_nmul (rep_nmul (rep_nmul (rep_nmul (rep_ncst 2) hA) g0) g1) g2) (rep_nmul (rep_ncst _)
    (rep_nadd (rep_nadd (rep_nmul (rep_nmul (rep_nadd h0 (rep_npow g0 2)) g1) g2)
      (rep_nmul (rep_nmul (rep_nadd h1 (rep_npow g1 2)) g0) g2))
      (rep_nmul (rep_nmul (rep_nadd h2 (rep_npow g2 2)) g0) g1)))
private def bnum4 (A P0 P1 P2 P3 r0 r1 r2 r3 : Scaled) : Scaled :=
  nsub (nmul (nmul (nmul (nmul (nmul (ncst 2) A) r0) r1) r2) r3) (nmul (ncst Rbar)
    (nadd (nadd (nadd (nmul (nmul (nmul (nadd P0 (npow r0 2)) r1) r2) r3)
      (nmul (nmul (nmul (nadd P1 (npow r1 2)) r0) r2) r3))
      (nmul (nmul (nmul (nadd P2 (npow r2 2)) r0) r1) r3))
      (nmul (nmul (nmul (nadd P3 (npow r3 2)) r0) r1) r2)))
private theorem rep_bnum4 {A P0 P1 P2 P3 r0 r1 r2 r3 : Scaled}
    {a p0 p1 p2 p3 s0 s1 s2 s3 : ℚ[X]}
    (hA : A.Rep a) (h0 : P0.Rep p0) (h1 : P1.Rep p1) (h2 : P2.Rep p2) (h3 : P3.Rep p3)
    (g0 : r0.Rep s0) (g1 : r1.Rep s1) (g2 : r2.Rep s2) (g3 : r3.Rep s3) :
    (bnum4 A P0 P1 P2 P3 r0 r1 r2 r3).Rep (num4 a p0 p1 p2 p3 s0 s1 s2 s3) :=
  rep_nsub (rep_nmul (rep_nmul (rep_nmul (rep_nmul (rep_nmul (rep_ncst 2) hA) g0) g1) g2) g3)
    (rep_nmul (rep_ncst _)
    (rep_nadd (rep_nadd (rep_nadd (rep_nmul (rep_nmul (rep_nmul (rep_nadd h0 (rep_npow g0 2)) g1) g2) g3)
      (rep_nmul (rep_nmul (rep_nmul (rep_nadd h1 (rep_npow g1 2)) g0) g2) g3))
      (rep_nmul (rep_nmul (rep_nmul (rep_nadd h2 (rep_npow g2 2)) g0) g1) g3))
      (rep_nmul (rep_nmul (rep_nmul (rep_nadd h3 (rep_npow g3 2)) g0) g1) g2)))
private def bnumer (e : Curve) : Scaled :=
  let p0 := bP e 0
  let p1 := bP e 1
  let p2 := bP e 2
  let p3 := bP e 3
  if family e=.low then bnum3 (bA e) p0 p1 p2 (bmass e 0 p0) (bmass e 1 p1) (bmass e 2 p2)
  else bnum4 (bA e) p0 p1 p2 p3 (bmass e 0 p0) (bmass e 1 p1) (bmass e 2 p2) (bmass e 3 p3)
private abbrev numSide (e : Curve) : Prop :=
  massSide (bP e 0) ∧ massSide (bP e 1) ∧ massSide (bP e 2) ∧ massSide (bP e 3)
private theorem rep_bnumer (e : Curve) (h : numSide e) : (bnumer e).Rep (numerator e) := by
  unfold bnumer numerator
  dsimp only
  split_ifs
  · exact rep_bnum3 (rep_bA e) (rep_bP e 0) (rep_bP e 1) (rep_bP e 2)
      (rep_bmass e 0 (rep_bP e 0) h.1) (rep_bmass e 1 (rep_bP e 1) h.2.1)
      (rep_bmass e 2 (rep_bP e 2) h.2.2.1)
  · exact rep_bnum4 (rep_bA e) (rep_bP e 0) (rep_bP e 1) (rep_bP e 2) (rep_bP e 3)
      (rep_bmass e 0 (rep_bP e 0) h.1) (rep_bmass e 1 (rep_bP e 1) h.2.1)
      (rep_bmass e 2 (rep_bP e 2) h.2.2.1) (rep_bmass e 3 (rep_bP e 3) h.2.2.2)

/-! #### Centering on the native interval -/

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

/-! #### Integer comparisons -/

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
private theorem lt_coeff {a : ℤ} {b : ℕ} {x : ℤ} {s : ℕ} (hb : 0<b) (hs : 0<s)
    (h : a*(s:ℤ)<x*(b:ℤ)) : (a:ℚ)/b<(x:ℚ)/s := by
  have h' : (a:ℚ)*(s:ℚ)<(x:ℚ)*(b:ℚ) := by exact_mod_cast h
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  linarith

end Certificates
open WholeIntervalPolynomial.Certificate (lowerZ chebList lowerOn_eq_of_rep)


private theorem mass_check_lowH (j : Fin 4) : massSide (bP .lowH j) ∧
    certOK (19/25) 3 ((bmass .lowH j (bP .lowH j)).center (cnum .lowH) (cden .lowH) 1 1) := by
  fin_cases j <;> decide +kernel
private theorem mass_check_lowM (j : Fin 4) : massSide (bP .lowM j) ∧
    certOK (19/25) 3 ((bmass .lowM j (bP .lowM j)).center (cnum .lowM) (cden .lowM) 1 1) := by
  fin_cases j <;> decide +kernel
private theorem mass_check_lowSH (j : Fin 4) : massSide (bP .lowSH j) ∧
    certOK (19/25) 3 ((bmass .lowSH j (bP .lowSH j)).center (cnum .lowSH) (cden .lowSH) 1 1) := by
  fin_cases j <;> decide +kernel
private theorem mass_check_lowSG (j : Fin 4) : massSide (bP .lowSG j) ∧
    certOK (19/25) 3 ((bmass .lowSG j (bP .lowSG j)).center (cnum .lowSG) (cden .lowSG) 1 1) := by
  fin_cases j <;> decide +kernel
private theorem mass_check_lowGA (j : Fin 4) : massSide (bP .lowGA j) ∧
    certOK (19/25) 3 ((bmass .lowGA j (bP .lowGA j)).center (cnum .lowGA) (cden .lowGA) 1 1) := by
  fin_cases j <;> decide +kernel
private theorem mass_check_highH (j : Fin 4) : massSide (bP .highH j) ∧
    certOK (19/25) 3 ((bmass .highH j (bP .highH j)).center (cnum .highH) (cden .highH) 1 1) := by
  fin_cases j <;> decide +kernel
private theorem mass_check_highG (j : Fin 4) : massSide (bP .highG j) ∧
    certOK (19/25) 3 ((bmass .highG j (bP .highG j)).center (cnum .highG) (cden .highG) 1 1) := by
  fin_cases j <;> decide +kernel
private theorem mass_check_highB (j : Fin 4) : massSide (bP .highB j) ∧
    certOK (19/25) 3 ((bmass .highB j (bP .highB j)).center (cnum .highB) (cden .highB) 1 1) := by
  fin_cases j <;> decide +kernel
private theorem mass_check_highGA (j : Fin 4) : massSide (bP .highGA j) ∧
    certOK (19/25) 3 ((bmass .highGA j (bP .highGA j)).center (cnum .highGA) (cden .highGA) 1 1) := by
  fin_cases j <;> decide +kernel
private theorem mass_check_highAB (j : Fin 4) : massSide (bP .highAB j) ∧
    certOK (19/25) 3 ((bmass .highAB j (bP .highAB j)).center (cnum .highAB) (cden .highAB) 1 1) := by
  fin_cases j <;> decide +kernel
private theorem mass_check_gaH (j : Fin 4) : massSide (bP .gaH j) ∧
    certOK (19/25) 3 ((bmass .gaH j (bP .gaH j)).center (cnum .gaH) (cden .gaH) 1 1) := by
  fin_cases j <;> decide +kernel
private theorem mass_check_gaB (j : Fin 4) : massSide (bP .gaB j) ∧
    certOK (19/25) 3 ((bmass .gaB j (bP .gaB j)).center (cnum .gaB) (cden .gaB) 1 1) := by
  fin_cases j <;> decide +kernel
private theorem mass_check_abG (j : Fin 4) : massSide (bP .abG j) ∧
    certOK (19/25) 3 ((bmass .abG j (bP .abG j)).center (cnum .abG) (cden .abG) 1 1) := by
  fin_cases j <;> decide +kernel
private theorem mass_check_abH (j : Fin 4) : massSide (bP .abH j) ∧
    certOK (19/25) 3 ((bmass .abH j (bP .abH j)).center (cnum .abH) (cden .abH) 1 1) := by
  fin_cases j <;> decide +kernel

theorem mass_certificate (e : Curve) (j : Fin 4) :
    centered 0 (length e) (mass e j)=expansion 3 (centered 0 (length e) (mass e j)) ∧
    (19/25:ℚ)<lowerOn 3 0 (length e) (mass e j) := by
  have h : massSide (bP e j) ∧
      certOK (19/25) 3 ((bmass e j (bP e j)).center (cnum e) (cden e) 1 1) := by
    cases e
    · exact mass_check_lowH j
    · exact mass_check_lowM j
    · exact mass_check_lowSH j
    · exact mass_check_lowSG j
    · exact mass_check_lowGA j
    · exact mass_check_highH j
    · exact mass_check_highG j
    · exact mass_check_highB j
    · exact mass_check_highGA j
    · exact mass_check_highAB j
    · exact mass_check_gaH j
    · exact mass_check_gaB j
    · exact mass_check_abG j
    · exact mass_check_abH j
  exact of_certOK (rep_center (rep_bmass e j (rep_bP e j) h.1) e) h.2

theorem length_positive (e : Curve) : 0<length e := by
  cases e <;> norm_num [length,start,family,right,split]

theorem mass_positive (e : Curve) (j : Fin 4) {x : ℝ}
    (hx : x∈Icc 0 (length e:ℝ)) : 0<aeval x (mass e j) := by
  have hh := positive_on_interval (length_positive e) (mass_certificate e j).1
    (mass_certificate e j).2 (by rw [Rat.cast_zero]; exact hx)
  have h19 : (0:ℝ)<((19/25:ℚ):ℝ) := by norm_num
  linarith

def direct : Curve→Prop
  | .lowM | .lowSH | .lowSG | .highB | .highAB | .abG | .abH => True
  | _ => False
def directReserve : Curve→ℚ
  | .lowM => 63/1000 | .lowSH => 89/500 | .lowSG => 7/40
  | .highB => 259/1000 | .highAB => 287/10000
  | .abG => 337/10000 | .abH => 349/10000 | _ => 0

private theorem direct_check_lowM : numSide .lowM ∧
    certOK (directReserve .lowM) (degree .lowM) ((bnumer .lowM).center (cnum .lowM) (cden .lowM) 1 1) := by
  decide +kernel
private theorem direct_check_lowSH : numSide .lowSH ∧
    certOK (directReserve .lowSH) (degree .lowSH) ((bnumer .lowSH).center (cnum .lowSH) (cden .lowSH) 1 1) := by
  decide +kernel
private theorem direct_check_lowSG : numSide .lowSG ∧
    certOK (directReserve .lowSG) (degree .lowSG) ((bnumer .lowSG).center (cnum .lowSG) (cden .lowSG) 1 1) := by
  decide +kernel
private theorem direct_check_highB : numSide .highB ∧
    certOK (directReserve .highB) (degree .highB) ((bnumer .highB).center (cnum .highB) (cden .highB) 1 1) := by
  decide +kernel
private theorem direct_check_highAB : numSide .highAB ∧
    certOK (directReserve .highAB) (degree .highAB) ((bnumer .highAB).center (cnum .highAB) (cden .highAB) 1 1) := by
  decide +kernel
private theorem direct_check_abG : numSide .abG ∧
    certOK (directReserve .abG) (degree .abG) ((bnumer .abG).center (cnum .abG) (cden .abG) 1 1) := by
  decide +kernel
private theorem direct_check_abH : numSide .abH ∧
    certOK (directReserve .abH) (degree .abH) ((bnumer .abH).center (cnum .abH) (cden .abH) 1 1) := by
  decide +kernel

theorem direct_certificate (e : Curve) (he : direct e) :
    centered 0 (length e) (numerator e)=
      expansion (degree e) (centered 0 (length e) (numerator e)) ∧
    directReserve e<lowerOn (degree e) 0 (length e) (numerator e) := by
  have h : numSide e ∧ certOK (directReserve e) (degree e)
      ((bnumer e).center (cnum e) (cden e) 1 1) := by
    cases e
    · exact False.elim he
    · exact direct_check_lowM
    · exact direct_check_lowSH
    · exact direct_check_lowSG
    · exact False.elim he
    · exact False.elim he
    · exact False.elim he
    · exact direct_check_highB
    · exact False.elim he
    · exact direct_check_highAB
    · exact False.elim he
    · exact False.elim he
    · exact direct_check_abG
    · exact direct_check_abH
  exact of_certOK (rep_center (rep_bnumer e h.1) e) h.2

theorem direct_positive (e : Curve) (he : direct e) {x : ℝ}
    (hx : x∈Icc 0 (length e:ℝ)) : 0<aeval x (numerator e) := by
  have hh := positive_on_interval (length_positive e) (direct_certificate e he).1
    (direct_certificate e he).2 (by rw [Rat.cast_zero]; exact hx)
  have hr : (0:ℝ)<(directReserve e:ℝ) := by
    cases e <;> simp only [direct] at he <;> first | contradiction | norm_num [directReserve]
  exact hr.trans hh

def quotientCase : Curve→Prop
  | .highH | .highG | .highGA | .gaH | .gaB => True
  | _ => False
def quotientReserve : Curve→ℚ
  | .highH => 53/1000 | .highG => 119/1000 | .highGA => 1/50
  | .gaH => 221/500 | .gaB => 101/200 | _ => 0
def initialReserve : Curve→ℚ
  | .highH => 1263/1000000 | .highG => 223/20000
  | .highGA | .gaH | .gaB => 1041/1000000 | _ => 0

private theorem quotient_check_highH : numSide .highH ∧ ((bnumer .highH).s≠0 ∧
    (initialReserve .highH).num*((bnumer .highH).s:ℤ)<(bnumer .highH).l.getD 0 0*((initialReserve .highH).den:ℤ)) ∧
    certOK (quotientReserve .highH) (degree .highH) ((bnumer .highH).divX.center (cnum .highH) (cden .highH) 1 1) := by
  decide +kernel
private theorem quotient_check_highG : numSide .highG ∧ ((bnumer .highG).s≠0 ∧
    (initialReserve .highG).num*((bnumer .highG).s:ℤ)<(bnumer .highG).l.getD 0 0*((initialReserve .highG).den:ℤ)) ∧
    certOK (quotientReserve .highG) (degree .highG) ((bnumer .highG).divX.center (cnum .highG) (cden .highG) 1 1) := by
  decide +kernel
private theorem quotient_check_highGA : numSide .highGA ∧ ((bnumer .highGA).s≠0 ∧
    (initialReserve .highGA).num*((bnumer .highGA).s:ℤ)<(bnumer .highGA).l.getD 0 0*((initialReserve .highGA).den:ℤ)) ∧
    certOK (quotientReserve .highGA) (degree .highGA) ((bnumer .highGA).divX.center (cnum .highGA) (cden .highGA) 1 1) := by
  decide +kernel
private theorem quotient_check_gaH : numSide .gaH ∧ ((bnumer .gaH).s≠0 ∧
    (initialReserve .gaH).num*((bnumer .gaH).s:ℤ)<(bnumer .gaH).l.getD 0 0*((initialReserve .gaH).den:ℤ)) ∧
    certOK (quotientReserve .gaH) (degree .gaH) ((bnumer .gaH).divX.center (cnum .gaH) (cden .gaH) 1 1) := by
  decide +kernel
private theorem quotient_check_gaB : numSide .gaB ∧ ((bnumer .gaB).s≠0 ∧
    (initialReserve .gaB).num*((bnumer .gaB).s:ℤ)<(bnumer .gaB).l.getD 0 0*((initialReserve .gaB).den:ℤ)) ∧
    certOK (quotientReserve .gaB) (degree .gaB) ((bnumer .gaB).divX.center (cnum .gaB) (cden .gaB) 1 1) := by
  decide +kernel

theorem quotient_certificate (e : Curve) (he : quotientCase e) :
    initialReserve e<(numerator e).eval 0 ∧
    centered 0 (length e) (numerator e).divX=
      expansion (degree e) (centered 0 (length e) (numerator e).divX) ∧
    quotientReserve e<lowerOn (degree e) 0 (length e) (numerator e).divX := by
  have h : numSide e ∧ ((bnumer e).s≠0 ∧
      (initialReserve e).num*((bnumer e).s:ℤ)<(bnumer e).l.getD 0 0*((initialReserve e).den:ℤ)) ∧
      certOK (quotientReserve e) (degree e) ((bnumer e).divX.center (cnum e) (cden e) 1 1) := by
    cases e
    · exact False.elim he
    · exact False.elim he
    · exact False.elim he
    · exact False.elim he
    · exact False.elim he
    · exact quotient_check_highH
    · exact quotient_check_highG
    · exact False.elim he
    · exact quotient_check_highGA
    · exact False.elim he
    · exact quotient_check_gaH
    · exact quotient_check_gaB
    · exact False.elim he
    · exact False.elim he
  have hn := rep_bnumer e h.1
  refine ⟨?_,of_certOK (rep_center hn.divX e) h.2.2⟩
  rw [← coeff_zero_eq_eval_zero,hn.coeff h.2.1.1,← Rat.num_div_den (initialReserve e)]
  exact lt_coeff (initialReserve e).pos (Nat.pos_of_ne_zero h.2.1.1) h.2.1.2

theorem quotient_positive (e : Curve) (he : quotientCase e) {x : ℝ}
    (hx : x∈Icc 0 (length e:ℝ)) : 0<aeval x (numerator e) := by
  have hc := quotient_certificate e he
  have hq := positive_on_interval (length_positive e) hc.2.1 hc.2.2
    (by rw [Rat.cast_zero]; exact hx)
  have h0 : (initialReserve e:ℝ)<(((numerator e).eval 0:ℚ):ℝ) := by exact_mod_cast hc.1
  have hr0 : (0:ℝ)<(initialReserve e:ℝ) := by
    cases e <;> simp only [quotientCase] at he <;> first | contradiction | norm_num [initialReserve]
  have hrq : (0:ℝ)<(quotientReserve e:ℝ) := by
    cases e <;> simp only [quotientCase] at he <;> first | contradiction | norm_num [quotientReserve]
  exact hr0.trans (NonnegativeTotals.Certificate.initial_lower hx.1 h0 hq hrq.le)

def reversed (e : Curve) : ℚ[X] := (numerator e).comp (C (1/4)-X)
def tailCoefficient (e : Curve) (j : ℕ) : ℚ := (reversed e).coeff j
def tailBound (e : Curve) : ℚ :=
  ∑j : Fin (degree e-3),max (-(tailCoefficient e (j.val+4))) 0*(1/4)^j.val

section TailCertificates
open WholeIntervalPolynomial.Certificate

/-! #### The reversed low numerators -/

private def brev (e : Curve) : Scaled := (bnumer e).center 1 4 1 (-4)
private theorem rep_brev (e : Curve) (h : numSide e) : (brev e).Rep (reversed e) := by
  have hc := (rep_bnumer e h).centered 1 4 1 (-4) (a:=5/4) (b:=-3/4)
    (by norm_num) (by norm_num) (by norm_num)
  have he : WholeIntervalPolynomial.centered (5/4) (-3/4) (numerator e)=reversed e := by
    unfold WholeIntervalPolynomial.centered WholeIntervalPolynomial.affine reversed
    congr 1
    rw [show ((5/4:ℚ)+-3/4)/2=1/4 by norm_num,show ((-3/4:ℚ)-5/4)/2=-1 by norm_num,map_neg,
      map_one,neg_one_mul,sub_eq_add_neg]
  rwa [he] at hc
private theorem tail_split (p : ℚ[X]) (D : ℕ) (hD : 3≤D) (hp : p.natDegree≤D) :
    p=C (p.coeff 0)+C (p.coeff 1)*X+C (p.coeff 2)*X^2+C (p.coeff 3)*X^3+
      ∑ j : Fin (D-3),C (p.coeff (j.val+4))*X^(j.val+4) := by
  have hf := Fin.sum_univ_eq_sum_range (fun j => C (p.coeff (j+4))*X^(j+4)) (D-3)
  beta_reduce at hf
  have h2 : ∑ x ∈ Finset.range (D-3),C (p.coeff (4+x))*X^(4+x)=
      ∑ x ∈ Finset.range (D-3),C (p.coeff (x+4))*X^(x+4) :=
    Finset.sum_congr rfl (fun x _ => by rw [add_comm 4 x])
  conv_lhs => rw [p.as_sum_range_C_mul_X_pow' (n:=D+1) (by omega)]
  rw [hf,show D+1=4+(D-3) by omega,Finset.sum_range_add,h2]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,mul_one,pow_one]
private def tailZ (L : List ℤ) (n : ℕ) : ℤ := ∑ j : Fin n,max (-L.getD (j.val+4) 0) 0*4^(n-1-j.val)
private theorem tail_sum (L : List ℤ) {s : ℕ} (hs : 0<s) (n : ℕ) :
    (∑ j : Fin n,max (-((L.getD (j.val+4) 0:ℚ)/s)) 0*(1/4:ℚ)^j.val)=
      (tailZ L n:ℚ)/((s:ℚ)*4^(n-1)) := by
  have hs' : (0:ℚ)<s := by exact_mod_cast hs
  unfold tailZ
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hj := j.isLt
  have hpow : (4:ℚ)^(n-1)=4^(n-1-j.val)*4^j.val := by rw [← pow_add]; congr 1; omega
  have hm : max (-((L.getD (j.val+4) 0:ℚ)/s)) 0=max (-(L.getD (j.val+4) 0:ℚ)) 0/s := by
    rw [show max (-((L.getD (j.val+4) 0:ℚ)/s)) 0=max (-(L.getD (j.val+4) 0:ℚ)/s) (0/s) by
      rw [zero_div,neg_div],max_div_div_right hs'.le]
  rw [hpow,hm,one_div,inv_pow]
  field_simp

end TailCertificates

theorem tail_identity (e : Curve) (he : e=.lowH∨e=.lowGA) :
    reversed e=C (tailCoefficient e 0)+C (tailCoefficient e 1)*X+
      C (tailCoefficient e 2)*X^2+C (tailCoefficient e 3)*X^3+
      ∑j : Fin (degree e-3),C (tailCoefficient e (j.val+4))*X^(j.val+4) := by
  have h : numSide e ∧ (brev e).s≠0 ∧ (brev e).l.length≤degree e+1 := by
    rcases he with rfl|rfl <;> decide +kernel
  have hr := rep_brev e h.1
  have h3 : 3≤degree e := by rcases he with rfl|rfl <;> decide
  have hl := h.2.2
  exact tail_split (reversed e) (degree e) h3 ((hr.natDegree_le h.2.1).trans (by omega))

theorem low_H_certificate :
    (10535/10000000:ℚ)<tailCoefficient .lowH 0 ∧
    (-4581/100000:ℚ)<tailCoefficient .lowH 1 ∧
    (55939/50000:ℚ)<tailCoefficient .lowH 2 ∧
    (85067/10000:ℚ)<tailCoefficient .lowH 3 ∧ tailBound .lowH<42969/1000 := by
  have h : numSide .lowH ∧ (brev .lowH).s≠0 ∧
      (10535:ℤ)*((brev .lowH).s:ℤ)<(brev .lowH).l.getD 0 0*((10000000:ℕ):ℤ) ∧
      (-4581:ℤ)*((brev .lowH).s:ℤ)<(brev .lowH).l.getD 1 0*((100000:ℕ):ℤ) ∧
      (55939:ℤ)*((brev .lowH).s:ℤ)<(brev .lowH).l.getD 2 0*((50000:ℕ):ℤ) ∧
      (85067:ℤ)*((brev .lowH).s:ℤ)<(brev .lowH).l.getD 3 0*((10000:ℕ):ℤ) ∧
      tailZ (brev .lowH).l 18*1000<42969*(((brev .lowH).s:ℤ)*4^17) := by
    decide +kernel
  obtain ⟨hn,hs,h0,h1,h2,h3,hT⟩ := h
  have hr := rep_brev .lowH hn
  have hs0 := Nat.pos_of_ne_zero hs
  simp only [tailCoefficient,tailBound,hr.coeff hs]
  rw [show degree .lowH-3=18 from rfl,tail_sum _ hs0]
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [show (10535/10000000:ℚ)=((10535:ℤ):ℚ)/((10000000:ℕ):ℚ) by norm_num]
    exact lt_coeff (by norm_num) hs0 h0
  · rw [show (-4581/100000:ℚ)=((-4581:ℤ):ℚ)/((100000:ℕ):ℚ) by norm_num]
    exact lt_coeff (by norm_num) hs0 h1
  · rw [show (55939/50000:ℚ)=((55939:ℤ):ℚ)/((50000:ℕ):ℚ) by norm_num]
    exact lt_coeff (by norm_num) hs0 h2
  · rw [show (85067/10000:ℚ)=((85067:ℤ):ℚ)/((10000:ℕ):ℚ) by norm_num]
    exact lt_coeff (by norm_num) hs0 h3
  · have hT' : ((tailZ (brev .lowH).l 18:ℤ):ℚ)*1000<42969*(((brev .lowH).s:ℚ)*4^17) := by
      exact_mod_cast hT
    rw [div_lt_iff₀ (by positivity)]
    norm_num at hT' ⊢
    linarith

theorem low_GA_certificate :
    (16043/10000000:ℚ)<tailCoefficient .lowGA 0 ∧
    (7459/100000:ℚ)<tailCoefficient .lowGA 1 ∧
    (54229/50000:ℚ)<tailCoefficient .lowGA 2 ∧
    (878451/100000:ℚ)<tailCoefficient .lowGA 3 ∧ tailBound .lowGA<6743/125 := by
  have h : numSide .lowGA ∧ (brev .lowGA).s≠0 ∧
      (16043:ℤ)*((brev .lowGA).s:ℤ)<(brev .lowGA).l.getD 0 0*((10000000:ℕ):ℤ) ∧
      (7459:ℤ)*((brev .lowGA).s:ℤ)<(brev .lowGA).l.getD 1 0*((100000:ℕ):ℤ) ∧
      (54229:ℤ)*((brev .lowGA).s:ℤ)<(brev .lowGA).l.getD 2 0*((50000:ℕ):ℤ) ∧
      (878451:ℤ)*((brev .lowGA).s:ℤ)<(brev .lowGA).l.getD 3 0*((100000:ℕ):ℤ) ∧
      tailZ (brev .lowGA).l 31*125<6743*(((brev .lowGA).s:ℤ)*4^30) := by
    decide +kernel
  obtain ⟨hn,hs,h0,h1,h2,h3,hT⟩ := h
  have hr := rep_brev .lowGA hn
  have hs0 := Nat.pos_of_ne_zero hs
  simp only [tailCoefficient,tailBound,hr.coeff hs]
  rw [show degree .lowGA-3=31 from rfl,tail_sum _ hs0]
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [show (16043/10000000:ℚ)=((16043:ℤ):ℚ)/((10000000:ℕ):ℚ) by norm_num]
    exact lt_coeff (by norm_num) hs0 h0
  · rw [show (7459/100000:ℚ)=((7459:ℤ):ℚ)/((100000:ℕ):ℚ) by norm_num]
    exact lt_coeff (by norm_num) hs0 h1
  · rw [show (54229/50000:ℚ)=((54229:ℤ):ℚ)/((50000:ℕ):ℚ) by norm_num]
    exact lt_coeff (by norm_num) hs0 h2
  · rw [show (878451/100000:ℚ)=((878451:ℤ):ℚ)/((100000:ℕ):ℚ) by norm_num]
    exact lt_coeff (by norm_num) hs0 h3
  · have hT' : ((tailZ (brev .lowGA).l 31:ℤ):ℚ)*125<6743*(((brev .lowGA).s:ℚ)*4^30) := by
      exact_mod_cast hT
    rw [div_lt_iff₀ (by positivity)]
    norm_num at hT' ⊢
    linarith

theorem power_tail {a w : ℝ} (hw : w∈Icc 0 (1/4:ℝ)) (j : ℕ) :
    -(max (-a) 0*(1/4)^j)*w^4≤a*w^(j+4) := by
  have ha : -max (-a) 0≤a := by linarith [le_max_left (-a) 0]
  have h0 : 0≤ max (-a) 0 := le_max_right _ _
  have hp := pow_le_pow_left₀ hw.1 hw.2 j
  have h1 := mul_le_mul_of_nonneg_right ha (pow_nonneg hw.1 j)
  have h2 := mul_le_mul_of_nonneg_left hp h0
  have hh : -(max (-a) 0*(1/4)^j)≤a*w^j := by linarith
  have hs := mul_le_mul_of_nonneg_right hh (pow_nonneg hw.1 4)
  simpa only [pow_add,mul_assoc] using hs

theorem tail_lower (e : Curve) (he : e=.lowH∨e=.lowGA) {w : ℝ}
    (hw : w∈Icc 0 (1/4:ℝ)) :
    (tailCoefficient e 0:ℝ)+(tailCoefficient e 1:ℝ)*w+
      (tailCoefficient e 2:ℝ)*w^2+(tailCoefficient e 3:ℝ)*w^3-
      (tailBound e:ℝ)*w^4≤aeval w (reversed e) := by
  have hs := Finset.sum_le_sum (s:=Finset.univ)
    (fun (j : Fin (degree e-3)) _ => power_tail (a:=(tailCoefficient e (j.val+4):ℝ)) hw j.val)
  have hid := congrArg (fun p : ℚ[X] => aeval w p) (tail_identity e he)
  simp only [map_add,map_sum,map_mul,map_pow,aeval_C,aeval_X,eq_ratCast] at hid
  have heq : (∑j : Fin (degree e-3),-(max (-(tailCoefficient e (j.val+4):ℝ)) 0*(1/4)^j.val)*w^4)=
      -(tailBound e:ℝ)*w^4 := by
    simp [tailBound,Finset.sum_mul,Finset.sum_neg_distrib]
  rw [heq] at hs
  linarith

theorem low_H_positive {x : ℝ} (hx : x∈Icc 0 (1/4:ℝ)) :
    0<aeval x (numerator .lowH) := by
  let w : ℝ := 1/4-x
  have hw : w∈Icc 0 (1/4:ℝ) := ⟨by dsimp [w]; linarith [hx.2],by dsimp [w]; linarith [hx.1]⟩
  have hb := tail_lower .lowH (Or.inl rfl) hw
  have h0 : (10535/10000000:ℝ)<(tailCoefficient .lowH 0:ℝ) := by
    have hc := Rat.cast_lt (K:=ℝ) |>.mpr low_H_certificate.1
    push_cast at hc
    exact hc
  have h1 : (-4581/100000:ℝ)<(tailCoefficient .lowH 1:ℝ) := by
    have hc := Rat.cast_lt (K:=ℝ) |>.mpr low_H_certificate.2.1
    push_cast at hc
    exact hc
  have h2 : (55939/50000:ℝ)<(tailCoefficient .lowH 2:ℝ) := by
    have hc := Rat.cast_lt (K:=ℝ) |>.mpr low_H_certificate.2.2.1
    push_cast at hc
    exact hc
  have h3 : (85067/10000:ℝ)<(tailCoefficient .lowH 3:ℝ) := by
    have hc := Rat.cast_lt (K:=ℝ) |>.mpr low_H_certificate.2.2.2.1
    push_cast at hc
    exact hc
  have hT : (tailBound .lowH:ℝ)<42969/1000 := by
    have hc := Rat.cast_lt (K:=ℝ) |>.mpr low_H_certificate.2.2.2.2
    push_cast at hc
    exact hc
  have hquad : (2799/5000:ℝ)≤55939/50000+(85067/10000)*w-(42969/1000)*w^2 := by
    nlinarith [mul_nonneg hw.1 (sub_nonneg.mpr hw.2)]
  have hquad' := mul_le_mul_of_nonneg_right hquad (sq_nonneg w)
  have hlin := mul_le_mul_of_nonneg_right h1.le hw.1
  have hsq := mul_le_mul_of_nonneg_right h2.le (sq_nonneg w)
  have hcube := mul_le_mul_of_nonneg_right h3.le (pow_nonneg hw.1 3)
  have hfour := mul_le_mul_of_nonneg_right hT.le (pow_nonneg hw.1 4)
  have hpositive : 0<aeval w (reversed .lowH) := by
    nlinarith [sq_nonneg (w-(4581/100000)/(2*(2799/5000)))]
  simpa [reversed,aeval_comp,w] using hpositive

theorem low_GA_positive {x : ℝ} (hx : x∈Icc 0 (1/4:ℝ)) :
    0<aeval x (numerator .lowGA) := by
  let w : ℝ := 1/4-x
  have hw : w∈Icc 0 (1/4:ℝ) := ⟨by dsimp [w]; linarith [hx.2],by dsimp [w]; linarith [hx.1]⟩
  have hb := tail_lower .lowGA (Or.inr rfl) hw
  have h0 : (16043/10000000:ℝ)<(tailCoefficient .lowGA 0:ℝ) := by
    have hc := Rat.cast_lt (K:=ℝ) |>.mpr low_GA_certificate.1
    push_cast at hc
    exact hc
  have h1 : (7459/100000:ℝ)<(tailCoefficient .lowGA 1:ℝ) := by
    have hc := Rat.cast_lt (K:=ℝ) |>.mpr low_GA_certificate.2.1
    push_cast at hc
    exact hc
  have h2 : (54229/50000:ℝ)<(tailCoefficient .lowGA 2:ℝ) := by
    have hc := Rat.cast_lt (K:=ℝ) |>.mpr low_GA_certificate.2.2.1
    push_cast at hc
    exact hc
  have h3 : (878451/100000:ℝ)<(tailCoefficient .lowGA 3:ℝ) := by
    have hc := Rat.cast_lt (K:=ℝ) |>.mpr low_GA_certificate.2.2.2.1
    push_cast at hc
    exact hc
  have hT : (tailBound .lowGA:ℝ)<6743/125 := by
    have hc := Rat.cast_lt (K:=ℝ) |>.mpr low_GA_certificate.2.2.2.2
    push_cast at hc
    exact hc
  have hquad : -(91/1000:ℝ)≤54229/50000+(878451/100000)*w-(6743/125)*w^2 := by
    nlinarith [mul_nonneg hw.1 (sub_nonneg.mpr hw.2)]
  have hquad' := mul_le_mul_of_nonneg_right hquad (sq_nonneg w)
  have hlin := mul_le_mul_of_nonneg_right h1.le hw.1
  have hsq := mul_le_mul_of_nonneg_right h2.le (sq_nonneg w)
  have hcube := mul_le_mul_of_nonneg_right h3.le (pow_nonneg hw.1 3)
  have hfour := mul_le_mul_of_nonneg_right hT.le (pow_nonneg hw.1 4)
  have hpositive : 0<aeval w (reversed .lowGA) := by
    nlinarith [mul_nonneg hw.1 (sub_nonneg.mpr hw.2)]
  simpa [reversed,aeval_comp,w] using hpositive

/-- Every reference numerator is strictly positive on its whole native interval. -/
theorem numerator_positive (e : Curve) {x : ℝ} (hx : x∈Icc 0 (length e:ℝ)) :
    0<aeval x (numerator e) := by
  cases e
  · exact low_H_positive (by
      have h := hx; norm_num [length,right,family,start,split] at h; exact h)
  · exact direct_positive .lowM trivial hx
  · exact direct_positive .lowSH trivial hx
  · exact direct_positive .lowSG trivial hx
  · exact low_GA_positive (by
      have h := hx; norm_num [length,right,family,start,split] at h; exact h)
  · exact quotient_positive .highH trivial hx
  · exact quotient_positive .highG trivial hx
  · exact direct_positive .highB trivial hx
  · exact quotient_positive .highGA trivial hx
  · exact direct_positive .highAB trivial hx
  · exact quotient_positive .gaH trivial hx
  · exact quotient_positive .gaB trivial hx
  · exact direct_positive .abG trivial hx
  · exact direct_positive .abH trivial hx

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeABT3.Certificate

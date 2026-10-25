module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDEBT3PolynomialData
public import SquaresInCircles.Eight.TableFree.PolynomialCertificates

/-!
# Whole-interval DE3 / BT3 numerator, mass and coefficient bounds

Uncompiled Section 8 and the coefficient part of Section 7. Each
certificate is the displayed rational polynomial identity and one
coefficient aggregate on its entire native interval. The exceptional
H numerator retains its positive constant and its first quotient.
No sampled-angle premise or externally trusted computation is used.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveBT.Certificate
open WholeIntervalPolynomial
open WholeIntervalPolynomial.Certificate (Scaled lowerOn_eq_of_rep lowerZ chebList toPoly)
open PositiveTD.Certificate (S9 S11 C10 C12)

/-! ### Helpers on scaled lists -/

/-- The gcd of a scale and all entries of a list. -/
private def r73gcd (g : ℕ) (l : List ℤ) : ℕ := l.foldl (fun g x => Nat.gcd g x.natAbs) g

private theorem r73gcd_dvd : ∀ (l : List ℤ) (g : ℕ),
    r73gcd g l ∣ g ∧ ∀ x ∈ l,((r73gcd g l:ℕ):ℤ) ∣ x
  | [],g => by simp [r73gcd]
  | a :: t,g => by
    have ih := r73gcd_dvd t (Nat.gcd g a.natAbs)
    have he : r73gcd g (a :: t)=r73gcd (Nat.gcd g a.natAbs) t := rfl
    rw [he]
    refine ⟨ih.1.trans (Nat.gcd_dvd_left _ _),?_⟩
    intro x hx
    rcases List.mem_cons.1 hx with rfl|hx
    · exact Int.natCast_dvd.2 (ih.1.trans (Nat.gcd_dvd_right _ _))
    · exact ih.2 x hx

private theorem r73toPoly_map_div (g : ℤ) : ∀ l : List ℤ,(∀ x ∈ l,g ∣ x) →
    C (g:ℚ)*toPoly (l.map (fun x => x/g))=toPoly l
  | [],_ => by simp [toPoly]
  | a :: t,h => by
    have ih := r73toPoly_map_div g t (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have ha : ((a/g:ℤ):ℚ)*(g:ℚ)=(a:ℚ) := by
      exact_mod_cast Int.ediv_mul_cancel (h a (List.mem_cons_self))
    simp only [List.map_cons,toPoly]
    rw [mul_add,← ih,← map_mul,mul_comm (g:ℚ),ha]
    ring

/-- Division by the common gcd of the scale and the entries. -/
private def r73norm (c : Scaled) : Scaled :=
  if r73gcd c.s c.l=0 then c else
    ⟨c.l.map (fun x => x/((r73gcd c.s c.l:ℕ):ℤ)),c.s/r73gcd c.s c.l⟩

private theorem r73norm_rep {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) : (r73norm c).Rep p := by
  unfold r73norm
  split_ifs with hg
  · exact hc
  obtain ⟨hs,hl⟩ := r73gcd_dvd c.l c.s
  unfold Scaled.Rep at *
  have h1 := r73toPoly_map_div _ c.l hl
  have hgq : ((r73gcd c.s c.l:ℕ):ℚ)≠0 := by exact_mod_cast hg
  have hs' : ((c.s/r73gcd c.s c.l:ℕ):ℚ)*(r73gcd c.s c.l:ℕ)=c.s := by
    exact_mod_cast Nat.div_mul_cancel hs
  apply mul_left_cancel₀ (show C ((r73gcd c.s c.l:ℕ):ℚ)≠0 from C_ne_zero.2 hgq)
  push_cast at h1 ⊢
  rw [h1,hc,← mul_assoc,← map_mul,mul_comm _ ((c.s/r73gcd c.s c.l:ℕ):ℚ)]
  rw [hs']

/-- The first four entries. -/
private def r73trunc (c : Scaled) : Scaled := ⟨c.l.take 4,c.s⟩

private theorem r73trunc_rep {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) :
    (r73trunc c).Rep (truncate3 p) := by
  unfold Scaled.Rep at *
  ext n
  have hco := congrArg (fun q => q.coeff n) hc
  simp only [WholeIntervalPolynomial.Certificate.coeff_toPoly,coeff_C_mul] at hco
  rw [WholeIntervalPolynomial.Certificate.coeff_toPoly,coeff_C_mul]
  simp only [r73trunc,truncate3,NegativeEHBT3.Certificate.truncate3,Fin.sum_univ_four,
    Fin.val_zero,Fin.val_one,Fin.val_two,coeff_add,coeff_C_mul_X_pow]
  rcases Nat.lt_or_ge n 4 with hn|hn
  · interval_cases n <;> simpa [List.getD_eq_getElem?_getD] using hco
  · have ht : (c.l.take 4).getD n 0=0 := by
      rw [List.getD_eq_getElem?_getD,List.getElem?_eq_none (by simp; omega)]
      rfl
    rw [ht]
    simp [show n≠0 by omega,show n≠1 by omega,show n≠2 by omega,show n≠3 by omega]

/-- The constant `n/d`, as an integer list with its scale. -/
private def r73c (n : ℤ) (d : ℕ) : Scaled := ⟨[n],d⟩

private theorem r73c_rep {n : ℤ} {d : ℕ} {q : ℚ} (h : (n:ℚ)=d*q) : (r73c n d).Rep (C q) := by
  unfold Scaled.Rep r73c
  simp only [toPoly,mul_zero,add_zero,h,map_mul]

/-- The representation of `mass P`, given the value of `P` at zero and its rounded root. -/
private def r73mass (pn pd rn rd : ℕ) (c : Scaled) : Scaled :=
  (r73c rn rd).mul (r73trunc ((((Scaled.ofNat 1).add ((r73c 1 2).mul
    (r73norm ((r73c pd pn).mul ((r73trunc c).sub (r73c pn pd)))))).sub
    ((r73c 1 8).mul ((r73norm ((r73c pd pn).mul ((r73trunc c).sub (r73c pn pd)))).pow 2))).add
    ((r73c 1 16).mul ((r73norm ((r73c pd pn).mul ((r73trunc c).sub (r73c pn pd)))).pow 3))))

private theorem r73mass_rep {c : Scaled} {P : ℚ[X]} {pn pd rn rd : ℕ} (hc : c.Rep P)
    (hpn : pn≠0) (hpd : pd≠0) (hrd : rd≠0)
    (h0 : P.eval 0=(pn:ℚ)/pd) (hρ : root12 ((pn:ℚ)/pd)=(rn:ℚ)/rd) :
    (r73mass pn pd rn rd c).Rep (mass P) := by
  have hpn' : (pn:ℚ)≠0 := by exact_mod_cast hpn
  have hpd' : (pd:ℚ)≠0 := by exact_mod_cast hpd
  have hrd' : (rd:ℚ)≠0 := by exact_mod_cast hrd
  have e1 : ((pd:ℤ):ℚ)=(pn:ℕ)*(1/((pn:ℚ)/pd)) := by push_cast; field_simp
  have e2 : ((pn:ℤ):ℚ)=(pd:ℕ)*((pn:ℚ)/pd) := by push_cast; field_simp
  have e3 : ((rn:ℤ):ℚ)=(rd:ℕ)*((rn:ℚ)/rd) := by push_cast; field_simp
  have hw := r73norm_rep ((r73c_rep e1).mul ((r73trunc_rep hc).sub (r73c_rep e2)))
  have h := (r73c_rep e3).mul (r73trunc_rep (((Scaled.rep_one.add
    ((r73c_rep (n:=1) (d:=2) (q:=1/2) (by norm_num)).mul hw)).sub ((r73c_rep (n:=1) (d:=8) (q:=1/8) (by norm_num)).mul (hw.pow 2))).add
      ((r73c_rep (n:=1) (d:=16) (q:=1/16) (by norm_num)).mul (hw.pow 3))))
  simp only [mass,h0,hρ]
  exact h

/-- The value at zero, from an integer cross-multiplication. -/
private theorem r73_eval_zero {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) {a b : ℕ}
    (h : c.s≠0 ∧ b≠0 ∧ c.l.getD 0 0*b=a*c.s) : p.eval 0=(a:ℚ)/b := by
  rw [← coeff_zero_eq_eval_zero,hc.coeff h.1 0,div_eq_div_iff (by exact_mod_cast h.1)
    (by exact_mod_cast h.2.1)]
  exact_mod_cast h.2.2

/-- The rounded square root, reduced to one integer square root. -/
private theorem r73_root12 {a b n : ℕ} (hb : 0<b) (hab : Nat.Coprime a b)
    (hn : n*n≤a*1000000000000000000000000/b ∧ a*1000000000000000000000000/b<(n+1)*(n+1)) :
    root12 ((a:ℚ)/b)=((if ((a:ℚ)/b)*1000000000000000000000000<((n:ℚ)+1/2)^2 then n else n+1 : ℕ):ℚ)/
      1000000000000 := by
  have hnum : ((a:ℚ)/b).num=a := by
    have h := Rat.num_div_eq_of_coprime (a:=(a:ℤ)) (b:=(b:ℤ)) (by exact_mod_cast hb)
      (by simpa using hab)
    rw [Int.cast_natCast,Int.cast_natCast] at h
    exact h
  have hden : ((a:ℚ)/b).den=b := by
    have h := Rat.den_div_eq_of_coprime (a:=(a:ℤ)) (b:=(b:ℤ)) (by exact_mod_cast hb)
      (by simpa using hab)
    rw [Int.cast_natCast,Int.cast_natCast] at h
    exact_mod_cast h
  have hs := (Nat.eq_sqrt.2 hn).symm
  simp only [root12,NegativeEHBT3.Certificate.root12,hnum,hden,Int.natAbs_natCast,hs]

/-- The variable composed with the high native shift `θ = x+1/6`. -/
private theorem r73_theta {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) :
    (c.center 1 6 1 6).Rep (p.comp theta) := by
  have h := hc.centered 1 6 1 6 (a:=-5/6) (b:=7/6) (by norm_num) (by norm_num) (by norm_num)
  have he : WholeIntervalPolynomial.centered (-5/6) (7/6) p=p.comp theta := by
    unfold WholeIntervalPolynomial.centered affine theta
    rw [show ((-5/6:ℚ)+7/6)/2=L by norm_num [L],show ((7/6:ℚ)- -5/6)/2=1 by norm_num,map_one,
      one_mul,add_comm]
  rwa [he] at h

/-- The whole-interval certificate from one integer computation. -/
private theorem r73_cert {c : Scaled} {lo hi : ℚ} {p : ℚ[X]} {D : ℕ}
    (hq : c.Rep (WholeIntervalPolynomial.centered lo hi p)) {a : ℤ} {b : ℕ}
    (h : c.s≠0 ∧ c.l.length≤D+1 ∧ b≠0 ∧
      a*((c.s*2^c.l.length:ℕ):ℤ)<2*lowerZ D (fun j => (chebList c.l).getD j 0)*b) :
    WholeIntervalPolynomial.centered lo hi p=expansion D (WholeIntervalPolynomial.centered lo hi p) ∧
      (a:ℚ)/b<lowerOn D lo hi p := by
  refine ⟨hq.eq_expansion h.1 h.2.1,?_⟩
  rw [lowerOn_eq_of_rep hq h.1 h.2.1]
  have hs : (0:ℚ)<c.s := by exact_mod_cast Nat.pos_of_ne_zero h.1
  have hM : (0:ℚ)<(c.s:ℚ)*2^c.l.length := by positivity
  have hb : (0:ℚ)<b := by exact_mod_cast Nat.pos_of_ne_zero h.2.2.1
  rw [show ((lowerZ D (fun j => (chebList c.l).getD j 0):ℤ):ℚ)/((c.s:ℚ)*2^c.l.length/2)=
    (2*(lowerZ D (fun j => (chebList c.l).getD j 0):ℤ):ℚ)/((c.s:ℚ)*2^c.l.length) by
      field_simp,div_lt_div_iff₀ hb hM]
  have h4 := h.2.2.2
  exact_mod_cast h4

/-! ### Taylor polynomials -/

private def r73S5 : Scaled :=
  (Scaled.var.sub (((r73c 1 6)).mul (Scaled.var.pow 3))).add
    (((r73c 1 120)).mul (Scaled.var.pow 5))
private theorem r73S5_rep : r73S5.Rep PositiveTD.Certificate.S5 :=
  (Scaled.rep_var.sub (((r73c_rep (n:=1) (d:=6) (by norm_num))).mul (Scaled.rep_var.pow 3))).add
    (((r73c_rep (n:=1) (d:=120) (by norm_num))).mul (Scaled.rep_var.pow 5))
private def r73S9 : Scaled := r73norm
  ((r73S5.sub (((r73c 1 5040)).mul (Scaled.var.pow 7))).add
    (((r73c 1 362880)).mul (Scaled.var.pow 9)))
private theorem r73S9_rep : r73S9.Rep PositiveTD.Certificate.S9 := r73norm_rep
  ((r73S5_rep.sub (((r73c_rep (n:=1) (d:=5040) (by norm_num))).mul (Scaled.rep_var.pow 7))).add
    (((r73c_rep (n:=1) (d:=362880) (by norm_num))).mul (Scaled.rep_var.pow 9)))
private def r73S11 : Scaled := r73norm (r73S9.sub (((r73c 1 39916800)).mul (Scaled.var.pow 11)))
private theorem r73S11_rep : r73S11.Rep PositiveTD.Certificate.S11 :=
  r73norm_rep (r73S9_rep.sub (((r73c_rep (n:=1) (d:=39916800) (by norm_num))).mul (Scaled.rep_var.pow 11)))
private def r73C4 : Scaled :=
  ((Scaled.ofNat 1).sub (((r73c 1 2)).mul (Scaled.var.pow 2))).add
    (((r73c 1 24)).mul (Scaled.var.pow 4))
private theorem r73C4_rep : r73C4.Rep PositiveTD.Certificate.C4 :=
  (Scaled.rep_one.sub (((r73c_rep (n:=1) (d:=2) (by norm_num))).mul (Scaled.rep_var.pow 2))).add
    (((r73c_rep (n:=1) (d:=24) (by norm_num))).mul (Scaled.rep_var.pow 4))
private def r73C10 : Scaled := r73norm
  (((r73C4.sub (((r73c 1 720)).mul (Scaled.var.pow 6))).add
    (((r73c 1 40320)).mul (Scaled.var.pow 8))).sub
    (((r73c 1 3628800)).mul (Scaled.var.pow 10)))
private theorem r73C10_rep : r73C10.Rep PositiveTD.Certificate.C10 := r73norm_rep
  (((r73C4_rep.sub (((r73c_rep (n:=1) (d:=720) (by norm_num))).mul (Scaled.rep_var.pow 6))).add
    (((r73c_rep (n:=1) (d:=40320) (by norm_num))).mul (Scaled.rep_var.pow 8))).sub
    (((r73c_rep (n:=1) (d:=3628800) (by norm_num))).mul (Scaled.rep_var.pow 10)))
private def r73C12 : Scaled := r73norm (r73C10.add (((r73c 1 479001600)).mul (Scaled.var.pow 12)))
private theorem r73C12_rep : r73C12.Rep PositiveTD.Certificate.C12 :=
  r73norm_rep (r73C10_rep.add (((r73c_rep (n:=1) (d:=479001600) (by norm_num))).mul (Scaled.rep_var.pow 12)))

private def r73num3 (A P0 P1 P2 r0 r1 r2 : Scaled) : Scaled :=
  ((((((r73c 2 1)).mul A).mul r0).mul r1).mul r2).sub (((r73c 494696877 250000000)).mul
    (((((P0.add (r0.pow 2)).mul r1).mul r2).add (((P1.add (r1.pow 2)).mul r0).mul r2)).add
      (((P2.add (r2.pow 2)).mul r0).mul r1)))
private theorem r73num3_rep {A P0 P1 P2 r0 r1 r2 : Scaled} {a p0 p1 p2 s0 s1 s2 : ℚ[X]}
    (hA : A.Rep a) (h0 : P0.Rep p0) (h1 : P1.Rep p1) (h2 : P2.Rep p2)
    (g0 : r0.Rep s0) (g1 : r1.Rep s1) (g2 : r2.Rep s2) :
    (r73num3 A P0 P1 P2 r0 r1 r2).Rep (PositiveTD.Certificate.num3 a p0 p1 p2 s0 s1 s2) :=
  ((((((r73c_rep (n:=2) (d:=1) (q:=2) (by norm_num))).mul hA).mul g0).mul g1).mul g2).sub (((r73c_rep (n:=494696877) (d:=250000000) (by norm_num [PositiveTD.Certificate.Rbar]))).mul
    (((((h0.add (g0.pow 2)).mul g1).mul g2).add (((h1.add (g1.pow 2)).mul g0).mul g2)).add
      (((h2.add (g2.pow 2)).mul g0).mul g1)))

/-! ### The low family -/

private def r73lowK : Scaled := ((r73c 2933 5000)).add (((r73c 1239 2500)).mul Scaled.var)
private theorem r73lowK_rep : r73lowK.Rep lowK :=
  ((r73c_rep (n:=2933) (d:=5000) (by norm_num))).add (((r73c_rep (n:=1239) (d:=2500) (by norm_num))).mul Scaled.rep_var)
private def r73lowM : Scaled := ((r73c 5821 5000)).sub (((r73c 4437 5000)).mul Scaled.var)
private theorem r73lowM_rep : r73lowM.Rep lowM :=
  ((r73c_rep (n:=5821) (d:=5000) (by norm_num))).sub (((r73c_rep (n:=4437) (d:=5000) (by norm_num))).mul Scaled.rep_var)
private def r73J : Scaled := r73norm
  ((((r73c 1 2)).mul (r73C10.sub (Scaled.ofNat 1))).add (((r73c (-114321959) 125000000)).mul r73S9))
private theorem r73J_rep : r73J.Rep J := r73norm_rep
  ((((r73c_rep (n:=1) (d:=2) (by norm_num))).mul (r73C10_rep.sub Scaled.rep_one)).add (((r73c_rep (n:=(-114321959)) (d:=125000000) (by norm_num [abar]))).mul r73S9_rep))
private def r73lowBase : Split → Scaled
  | .atA => r73norm ((((((r73c 2 1)).mul r73lowK).add ((r73c 2300392967 500000000))).add
      (((r73c 800392967 500000000)).mul r73lowM)).add r73J)
  | .atT => r73norm (((((r73c 2 1)).mul r73lowK).add ((r73c 2300392967 500000000))).add
      (r73lowM.mul (((Scaled.ofNat 1).add (((r73c 300392967 500000000)).mul r73C10)).add
        (((r73c (-442973506169) 500000000000)).mul r73S9))))
private theorem r73lowBase_rep : ∀ ep,(r73lowBase ep).Rep (lowBase ep)
  | .atA => r73norm_rep ((((((r73c_rep (n:=2) (d:=1) (by norm_num))).mul r73lowK_rep).add ((r73c_rep (n:=2300392967) (d:=500000000) (by norm_num [cbar])))).add
      (((r73c_rep (n:=800392967) (d:=500000000) (by norm_num [cbar]))).mul r73lowM_rep)).add r73J_rep)
  | .atT => r73norm_rep (((((r73c_rep (n:=2) (d:=1) (by norm_num))).mul r73lowK_rep).add ((r73c_rep (n:=2300392967) (d:=500000000) (by norm_num [cbar])))).add
      (r73lowM_rep.mul ((Scaled.rep_one.add (((r73c_rep (n:=300392967) (d:=500000000) (by norm_num [cbar]))).mul r73C10_rep)).add
        (((r73c_rep (n:=(-442973506169)) (d:=500000000000) (by norm_num [sigmabar,eta0,cbar]))).mul r73S9_rep))))
private def r73lowA (ep : Split) : Scaled := r73norm
  (((r73C10.mul (r73lowBase ep)).add (((r73c 13 12)).mul r73S11)).add
    (((r73c 199607033 500000000)).mul (r73C10.sub (Scaled.ofNat 1))))
private theorem r73lowA_rep (ep : Split) : (r73lowA ep).Rep (lowA ep) := r73norm_rep
  (((r73C10_rep.mul (r73lowBase_rep ep)).add (((r73c_rep (n:=13) (d:=12) (by norm_num [K]))).mul r73S11_rep)).add
    (((r73c_rep (n:=199607033) (d:=500000000) (by norm_num [cbar]))).mul (r73C10_rep.sub Scaled.rep_one)))
private def r73lowPK : Scaled := r73norm ((r73C12.pow 2).mul ((Scaled.ofNat 1).add (r73lowK.pow 2)))
private theorem r73lowPK_rep : r73lowPK.Rep (C12^2*(1+lowK^2)) :=
  r73norm_rep ((r73C12_rep.pow 2).mul (Scaled.rep_one.add (r73lowK_rep.pow 2)))
private def r73lowPM : Scaled := r73norm ((r73C12.pow 2).mul ((Scaled.ofNat 1).add (r73lowM.pow 2)))
private theorem r73lowPM_rep : r73lowPM.Rep (C12^2*(1+lowM^2)) :=
  r73norm_rep ((r73C12_rep.pow 2).mul (Scaled.rep_one.add (r73lowM_rep.pow 2)))
private def r73lowMK : Scaled :=
  r73norm (r73mass 33602489 25000000 1159353078229 1000000000000 r73lowPK)
private def r73lowMM : Scaled :=
  r73norm (r73mass 58884041 25000000 767359374739 500000000000 r73lowPM)
private theorem r73lowMK_rep : r73lowMK.Rep (mass (C12^2*(1+lowK^2))) := by
  have h0 := r73_eval_zero r73lowPK_rep (a:=33602489) (b:=25000000) (by decide +kernel)
  have hρ := r73_root12 (a:=33602489) (b:=25000000) (n:=1159353078229) (by norm_num) (by norm_num) (by norm_num)
  rw [ite_eq_left (by norm_num)] at hρ
  exact r73norm_rep (r73mass_rep (pn:=33602489) (pd:=25000000) (rn:=1159353078229) (rd:=1000000000000) r73lowPK_rep (by norm_num)
    (by norm_num) (by norm_num) h0 (hρ.trans (by norm_num)))
private theorem r73lowMM_rep : r73lowMM.Rep (mass (C12^2*(1+lowM^2))) := by
  have h0 := r73_eval_zero r73lowPM_rep (a:=58884041) (b:=25000000) (by decide +kernel)
  have hρ := r73_root12 (a:=58884041) (b:=25000000) (n:=1534718749478) (by norm_num) (by norm_num) (by norm_num)
  rw [ite_eq_left (by norm_num)] at hρ
  exact r73norm_rep (r73mass_rep (pn:=58884041) (pd:=25000000) (rn:=767359374739) (rd:=500000000000) r73lowPM_rep (by norm_num)
    (by norm_num) (by norm_num) h0 (hρ.trans (by norm_num)))

private def r73lowNum (ep : Split) : Scaled := r73norm
  (r73num3 (r73lowA ep) r73lowPK r73lowPK r73lowPM r73lowMK r73lowMK r73lowMM)
private theorem r73lowNum_rep (ep : Split) : (r73lowNum ep).Rep (lowNumerator ep) := r73norm_rep
  (r73num3_rep (r73lowA_rep ep) r73lowPK_rep r73lowPK_rep r73lowPM_rep r73lowMK_rep r73lowMK_rep
    r73lowMM_rep)

/-! ### Derivatives of represented polynomials -/

private def r73dgo : ℕ → List ℤ → List ℤ
  | _,[] => []
  | n,a :: t => ((n:ℤ)*a) :: r73dgo (n+1) t

private theorem r73dgo_getD : ∀ (l : List ℤ) (n i : ℕ),(r73dgo n l).getD i 0=((n+i:ℕ):ℤ)*l.getD i 0
  | [],n,i => by simp [r73dgo]
  | a :: t,n,0 => by simp [r73dgo]
  | a :: t,n,i+1 => by
    simp only [r73dgo,List.getD_cons_succ,r73dgo_getD t (n+1) i]
    push_cast
    ring

private def r73deriv (c : Scaled) : Scaled := ⟨r73dgo 1 c.l.tail,c.s⟩

private theorem r73deriv_rep {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) :
    (r73deriv c).Rep (derivative p) := by
  unfold Scaled.Rep at *
  ext i
  have hco := congrArg (fun q => q.coeff (i+1)) hc
  simp only [WholeIntervalPolynomial.Certificate.coeff_toPoly,coeff_C_mul] at hco
  rw [WholeIntervalPolynomial.Certificate.coeff_toPoly,coeff_C_mul,coeff_derivative,r73deriv,
    r73dgo_getD]
  have ht : c.l.tail.getD i 0=c.l.getD (i+1) 0 := by
    cases c.l <;> simp
  rw [ht]
  push_cast
  rw [hco]
  ring

/-- Value bounds at a rational point, from one integer comparison. -/
private theorem r73_eval_rep {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) (num den : ℕ) (s : ℤ)
    {x : ℚ} (hden : den≠0) (hx : x=num*s/den) : (c.center num den s 0).Rep (C (p.eval x)) := by
  have hq := hc.centered num den s 0 (a:=x) (b:=x) hden (by rw [← hx]; ring) (by simp)
  have he : WholeIntervalPolynomial.centered x x p=C (p.eval x) := by
    rw [WholeIntervalPolynomial.centered,affine,sub_self,zero_div,map_zero,zero_mul,add_zero,
      add_self_div_two,comp_C]
  rwa [he] at hq

private theorem r73_const_value {c : Scaled} {v : ℚ} (hc : c.Rep (C v)) (hs : c.s≠0) :
    v=(c.l.getD 0 0:ℚ)/c.s := by
  have h := hc.coeff hs 0
  rwa [coeff_C_zero] at h

private theorem r73_lt_const {c : Scaled} {v : ℚ} (hc : c.Rep (C v)) {a : ℤ} {b : ℕ}
    (h : c.s≠0 ∧ b≠0 ∧ a*c.s<c.l.getD 0 0*b) : (a:ℚ)/b<v := by
  rw [r73_const_value hc h.1,div_lt_div_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero h.2.1)
    (by exact_mod_cast Nat.pos_of_ne_zero h.1)]
  exact_mod_cast h.2.2

private theorem r73_const_lt {c : Scaled} {v : ℚ} (hc : c.Rep (C v)) {a : ℤ} {b : ℕ}
    (h : c.s≠0 ∧ b≠0 ∧ c.l.getD 0 0*b<a*c.s) : v<(a:ℚ)/b := by
  rw [r73_const_value hc h.1,div_lt_div_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero h.1)
    (by exact_mod_cast Nat.pos_of_ne_zero h.2.1)]
  exact_mod_cast h.2.2

private theorem r73_rep_eval_zero {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) :
    (⟨[c.l.getD 0 0],c.s⟩ : Scaled).Rep (C (p.eval 0)) := by
  unfold Scaled.Rep at *
  have h0 := congrArg (fun q => q.coeff 0) hc
  simp only [WholeIntervalPolynomial.Certificate.coeff_toPoly,coeff_C_mul] at h0
  simp only [WholeIntervalPolynomial.Certificate.toPoly,mul_zero,add_zero,h0,map_mul,
    ← coeff_zero_eq_eval_zero]

/-! ### The high family -/

private def r73theta (c : Scaled) : Scaled := r73norm (c.center 1 6 1 6)
private theorem r73theta_rep {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) :
    (r73theta c).Rep (p.comp theta) := r73norm_rep (r73_theta hc)

private def r73C12t : Scaled := r73theta r73C12
private theorem r73C12t_rep : r73C12t.Rep (C12.comp theta) := r73theta_rep r73C12_rep
private def r73C10t : Scaled := r73theta r73C10
private theorem r73C10t_rep : r73C10t.Rep (C10.comp theta) := r73theta_rep r73C10_rep
private def r73S9t : Scaled := r73theta r73S9
private theorem r73S9t_rep : r73S9t.Rep (S9.comp theta) := r73theta_rep r73S9_rep
private def r73S11t : Scaled := r73theta r73S11
private theorem r73S11t_rep : r73S11t.Rep (S11.comp theta) := r73theta_rep r73S11_rep

private def r73param : Scaled := ((r73c 15 8)).mul Scaled.var
private theorem r73param_rep : r73param.Rep parameter := ((r73c_rep (n:=15) (d:=8) (by norm_num))).mul Scaled.rep_var
private def r73thetaX : Scaled := Scaled.var.add ((r73c 1 6))
private theorem r73thetaX_rep : r73thetaX.Rep theta := Scaled.rep_var.add ((r73c_rep (n:=1) (d:=6) (by norm_num [L])))

private def r73highK : Scaled := r73norm
  ((((((r73c 335079 500000)).add (((r73c 56859 500000)).mul r73param)).add
    (((r73c 3253 500000)).mul (r73param.pow 2))).add
    (((r73c 4513 500000)).mul (r73param.pow 3))).add
    (((r73c 1 1000)).mul (r73param.pow 4)))
private theorem r73highK_rep : r73highK.Rep highK := r73norm_rep
  ((((((r73c_rep (n:=335079) (d:=500000) (by norm_num))).add (((r73c_rep (n:=56859) (d:=500000) (by norm_num))).mul r73param_rep)).add
    (((r73c_rep (n:=3253) (d:=500000) (by norm_num))).mul (r73param_rep.pow 2))).add
    (((r73c_rep (n:=4513) (d:=500000) (by norm_num))).mul (r73param_rep.pow 3))).add
    (((r73c_rep (n:=1) (d:=1000) (by norm_num))).mul (r73param_rep.pow 4)))
private def r73highL : Scaled := r73norm
  (((((r73c 1005069 1000000)).sub (((r73c 146411 1000000)).mul r73param)).sub
    (((r73c 157739 1000000)).mul (r73param.pow 2))).add
    (((r73c 32563 200000)).mul (r73param.pow 3)))
private theorem r73highL_rep : r73highL.Rep highL := r73norm_rep
  (((((r73c_rep (n:=1005069) (d:=1000000) (by norm_num))).sub (((r73c_rep (n:=146411) (d:=1000000) (by norm_num))).mul r73param_rep)).sub
    (((r73c_rep (n:=157739) (d:=1000000) (by norm_num))).mul (r73param_rep.pow 2))).add
    (((r73c_rep (n:=32563) (d:=200000) (by norm_num))).mul (r73param_rep.pow 3)))
private def r73highM : Scaled := r73norm
  (((((r73c 15957 15625)).sub (((r73c 168873 1000000)).mul r73param)).sub
    (((r73c 165381 1000000)).mul (r73param.pow 2))).add
    (((r73c 21993 125000)).mul (r73param.pow 3)))
private theorem r73highM_rep : r73highM.Rep highM := r73norm_rep
  (((((r73c_rep (n:=15957) (d:=15625) (by norm_num))).sub (((r73c_rep (n:=168873) (d:=1000000) (by norm_num))).mul r73param_rep)).sub
    (((r73c_rep (n:=165381) (d:=1000000) (by norm_num))).mul (r73param_rep.pow 2))).add
    (((r73c_rep (n:=21993) (d:=125000) (by norm_num))).mul (r73param_rep.pow 3)))
private def r73highEta : Scaled := ((r73c 293 1000)).add (((r73c 1351 10000)).mul Scaled.var)
private theorem r73highEta_rep : r73highEta.Rep highEta :=
  ((r73c_rep (n:=293) (d:=1000) (by norm_num [eta0]))).add (((r73c_rep (n:=1351) (d:=10000) (by norm_num))).mul Scaled.rep_var)
private def r73etaInc : Scaled := r73norm
  (((r73c 1000000 1085849)).mul ((r73highEta.pow 2).sub ((r73c 85849 1000000))))
private theorem r73etaInc_rep : r73etaInc.Rep etaIncrement := r73norm_rep
  (((r73c_rep (n:=1000000) (d:=1085849) (by norm_num [eta0]))).mul ((r73highEta_rep.pow 2).sub ((r73c_rep (n:=85849) (d:=1000000) (by norm_num [eta0])))))
private def r73sigmaUpper : Scaled := r73norm
  ((((r73c 2061977291 1000000000)).mul ((((Scaled.ofNat 1).add
    (((r73c 1 2)).mul r73etaInc)).sub (((r73c 1 8)).mul (r73etaInc.pow 2))).add
    (((r73c 1 16)).mul (r73etaInc.pow 3)))).sub
    (((r73c 1 2)).mul ((Scaled.ofNat 1).add r73highEta)))
private theorem r73sigmaUpper_rep : r73sigmaUpper.Rep sigmaUpper := r73norm_rep
  ((((r73c_rep (n:=2061977291) (d:=1000000000) (by norm_num [sigmabar,eta0]))).mul (((Scaled.rep_one.add
    (((r73c_rep (n:=1) (d:=2) (by norm_num))).mul r73etaInc_rep)).sub (((r73c_rep (n:=1) (d:=8) (by norm_num))).mul (r73etaInc_rep.pow 2))).add
    (((r73c_rep (n:=1) (d:=16) (by norm_num))).mul (r73etaInc_rep.pow 3)))).sub
    (((r73c_rep (n:=1) (d:=2) (by norm_num))).mul (Scaled.rep_one.add r73highEta_rep)))
private def r73highC : Scaled := r73norm (r73highM.mul (r73C12t.add (r73highEta.mul r73S9t)))
private theorem r73highC_rep : r73highC.Rep highC :=
  r73norm_rep (r73highM_rep.mul (r73C12t_rep.add (r73highEta_rep.mul r73S9t_rep)))
private def r73highSine : Scaled := r73norm
  ((((r73c 1 2)).add (((r73c 3 2)).mul r73highEta)).sub r73sigmaUpper)
private theorem r73highSine_rep : r73highSine.Rep highSineCoefficient := r73norm_rep
  ((((r73c_rep (n:=1) (d:=2) (by norm_num))).add (((r73c_rep (n:=3) (d:=2) (by norm_num))).mul r73highEta_rep)).sub r73sigmaUpper_rep)
private def r73highBase : Scaled := r73norm
  ((((((r73c 2 1)).mul r73highK).add (((r73c 3 1)).mul r73highL)).add ((r73c 3 1))).add
    (r73highM.mul (((Scaled.ofNat 1).add (((r73c 2 1)).mul r73C10t)).add (r73highSine.mul r73S9t))))
private theorem r73highBase_rep : r73highBase.Rep highBase := r73norm_rep
  ((((((r73c_rep (n:=2) (d:=1) (by norm_num))).mul r73highK_rep).add (((r73c_rep (n:=3) (d:=1) (by norm_num))).mul r73highL_rep)).add
    ((r73c_rep (n:=3) (d:=1) (by norm_num)))).add
    (r73highM_rep.mul ((Scaled.rep_one.add (((r73c_rep (n:=2) (d:=1) (by norm_num))).mul r73C10t_rep)).add
      (r73highSine_rep.mul r73S9t_rep))))
private def r73highQStar : Scaled := r73norm
  (r73highL.add (((r73c 3 20)).mul (((r73c 7 10)).sub r73thetaX)))
private theorem r73highQStar_rep : r73highQStar.Rep highQStar := r73norm_rep
  (r73highL_rep.add (((r73c_rep (n:=3) (d:=20) (by norm_num))).mul (((r73c_rep (n:=7) (d:=10) (by norm_num [h]))).sub r73thetaX_rep)))

private def r73NZ : Fin 4 → Scaled :=
  ![r73norm ((Scaled.ofNat 1).add (r73highK.pow 2)),
    r73norm ((r73highK.pow 2).add (r73highL.pow 2)),
    r73norm ((r73highL.pow 2).add (r73highM.pow 2)),
    r73norm ((Scaled.ofNat 1).add (r73highC.pow 2))]
private theorem r73NZ_rep (i : Fin 4) : (r73NZ i).Rep (highNormZero i) := by
  fin_cases i
  · exact r73norm_rep (Scaled.rep_one.add (r73highK_rep.pow 2))
  · exact r73norm_rep ((r73highK_rep.pow 2).add (r73highL_rep.pow 2))
  · exact r73norm_rep ((r73highL_rep.pow 2).add (r73highM_rep.pow 2))
  · exact r73norm_rep (Scaled.rep_one.add (r73highC_rep.pow 2))
private def r73prod : Fin 3 → Scaled :=
  ![r73highK,r73norm (r73highK.mul r73highL),r73norm (r73highL.mul r73highM)]
private theorem r73prod_rep (i : Fin 3) : (r73prod i).Rep (highProduct i) := by
  fin_cases i
  · exact r73highK_rep
  · exact r73norm_rep (r73highK_rep.mul r73highL_rep)
  · exact r73norm_rep (r73highL_rep.mul r73highM_rep)
private def r73cos : Fin 3 → Scaled := ![Scaled.ofNat 1,r73highL,r73highQStar]
private theorem r73cos_rep (i : Fin 3) : (r73cos i).Rep (highCosineCoefficient i) := by
  fin_cases i
  · exact Scaled.rep_one
  · exact r73highL_rep
  · exact r73highQStar_rep

private def r73highA (r : HighCase) : Scaled :=
  if r=.equal then r73norm (((r73C10t.mul (r73highBase.sub (Scaled.ofNat 1))).add (Scaled.ofNat 1)).add
    (((r73c 13 12)).mul r73S11t))
  else r73norm (r73highBase.add ((r73cos (highIndex r)).mul (r73C10t.sub (Scaled.ofNat 1))))
private theorem r73highA_rep (r : HighCase) : (r73highA r).Rep (highA r) := by
  unfold r73highA highA
  split_ifs
  · exact r73norm_rep (((r73C10t_rep.mul (r73highBase_rep.sub Scaled.rep_one)).add Scaled.rep_one).add
      (((r73c_rep (n:=13) (d:=12) (by norm_num [K]))).mul r73S11t_rep))
  · exact r73norm_rep (r73highBase_rep.add ((r73cos_rep _).mul (r73C10t_rep.sub Scaled.rep_one)))

private def r73highP (r : HighCase) (i : Fin 4) : Scaled :=
  if r=.equal then
    if i=3 then r73norm ((Scaled.ofNat 1).add ((r73highC.pow 2).mul (r73C12t.pow 2)))
    else r73norm ((r73C12t.pow 2).mul (r73NZ i))
  else r73norm ((r73NZ i).sub
    (if i=(highIndex r).castSucc then (((r73c 2 1)).mul (r73prod (highIndex r))).mul r73S11t
      else ⟨[],1⟩))
private theorem r73highP_rep (r : HighCase) (i : Fin 4) : (r73highP r i).Rep (highP r i) := by
  unfold r73highP highP
  split_ifs
  · exact r73norm_rep (Scaled.rep_one.add ((r73highC_rep.pow 2).mul (r73C12t_rep.pow 2)))
  · exact r73norm_rep ((r73C12t_rep.pow 2).mul (r73NZ_rep i))
  · exact r73norm_rep ((r73NZ_rep i).sub ((((r73c_rep (n:=2) (d:=1) (by norm_num))).mul (r73prod_rep _)).mul r73S11t_rep))
  · exact r73norm_rep ((r73NZ_rep i).sub Scaled.rep_zero)

private def r73pn : HighCase → Fin 4 → ℕ
  | .H => ![308429610950386217351287,58371017589,410622234453,1092234423645234978844299752297786636118889]
  | .G => ![362277936241,165707506467540267494772073,410622234453,1092234423645234978844299752297786636118889]
  | .B => ![362277936241,58371017589,797346041684883383339651,1092234423645234978844299752297786636118889]
  | .equal => ![383023851466510906753130398742299845927185340241,6857071673551657716624192401652971787121792621,48237399461214211694603420733990516450917840717,1170220976333354656072178768459690104061402401231497054965753205591253858434889]

private def r73pd : HighCase → Fin 4 → ℕ
  | .H => ![251418359808000000000000,40000000000,200000000000,516009727743224079974400000000000000000000]
  | .G => ![250000000000,134089791897600000000000000,200000000000,516009727743224079974400000000000000000000]
  | .B => ![250000000000,40000000000,465589555200000000000000,516009727743224079974400000000000000000000]
  | .equal => ![271796553912223934458904382013440000000000000000,4831938736217314390380522346905600000000000000,24159693681086571951902611734528000000000000000,560998663143172792418520742175621836554558157822623744000000000000000000000000]

private def r73rn : HighCase → Fin 4 → ℕ
  | .H => ![1107591307287,294923031,179108520363,181860758669]
  | .G => ![300947643387,555831604481,179108520363,181860758669]
  | .B => ![300947643387,294923031,261728973847,181860758669]
  | .equal => ![296777481581,1191265693093,141301324057,72214270843]

private def r73rd : HighCase → Fin 4 → ℕ
  | .H => ![1000000000000,244140625,125000000000,125000000000]
  | .G => ![250000000000,500000000000,125000000000,125000000000]
  | .B => ![250000000000,244140625,200000000000,125000000000]
  | .equal => ![250000000000,1000000000000,100000000000,50000000000]

private def r73highMass (r : HighCase) (i : Fin 4) : Scaled :=
  r73norm (r73mass (r73pn r i) (r73pd r i) (r73rn r i) (r73rd r i) (r73highP r i))

private theorem r73hm_H_0 : (r73highMass .H 0).Rep (highMass .H 0) := by
  have h0 := r73_eval_zero (r73highP_rep .H 0) (a:=308429610950386217351287) (b:=251418359808000000000000) (by decide +kernel)
  have hρ := r73_root12 (a:=308429610950386217351287) (b:=251418359808000000000000) (n:=1107591307286) (by norm_num) (by norm_num) (by norm_num)
  rw [ite_eq_right (by norm_num)] at hρ
  exact r73norm_rep (r73mass_rep (pn:=308429610950386217351287) (pd:=251418359808000000000000) (rn:=1107591307287) (rd:=1000000000000) (r73highP_rep .H 0) (by norm_num)
    (by norm_num) (by norm_num) h0 (hρ.trans (by norm_num)))

private theorem r73hm_H_1 : (r73highMass .H 1).Rep (highMass .H 1) := by
  have h0 := r73_eval_zero (r73highP_rep .H 1) (a:=58371017589) (b:=40000000000) (by decide +kernel)
  have hρ := r73_root12 (a:=58371017589) (b:=40000000000) (n:=1208004734976) (by norm_num) (by norm_num) (by norm_num)
  rw [ite_eq_left (by norm_num)] at hρ
  exact r73norm_rep (r73mass_rep (pn:=58371017589) (pd:=40000000000) (rn:=294923031) (rd:=244140625) (r73highP_rep .H 1) (by norm_num)
    (by norm_num) (by norm_num) h0 (hρ.trans (by norm_num)))

private theorem r73hm_H_2 : (r73highMass .H 2).Rep (highMass .H 2) := by
  have h0 := r73_eval_zero (r73highP_rep .H 2) (a:=410622234453) (b:=200000000000) (by decide +kernel)
  have hρ := r73_root12 (a:=410622234453) (b:=200000000000) (n:=1432868162904) (by norm_num) (by norm_num) (by norm_num)
  rw [ite_eq_left (by norm_num)] at hρ
  exact r73norm_rep (r73mass_rep (pn:=410622234453) (pd:=200000000000) (rn:=179108520363) (rd:=125000000000) (r73highP_rep .H 2) (by norm_num)
    (by norm_num) (by norm_num) h0 (hρ.trans (by norm_num)))

private theorem r73hm_H_3 : (r73highMass .H 3).Rep (highMass .H 3) := by
  have h0 := r73_eval_zero (r73highP_rep .H 3) (a:=1092234423645234978844299752297786636118889) (b:=516009727743224079974400000000000000000000) (by decide +kernel)
  have hρ := r73_root12 (a:=1092234423645234978844299752297786636118889) (b:=516009727743224079974400000000000000000000) (n:=1454886069352) (by norm_num) (by norm_num) (by norm_num)
  rw [ite_eq_left (by norm_num)] at hρ
  exact r73norm_rep (r73mass_rep (pn:=1092234423645234978844299752297786636118889) (pd:=516009727743224079974400000000000000000000) (rn:=181860758669) (rd:=125000000000) (r73highP_rep .H 3) (by norm_num)
    (by norm_num) (by norm_num) h0 (hρ.trans (by norm_num)))

private theorem r73hm_G_0 : (r73highMass .G 0).Rep (highMass .G 0) := by
  have h0 := r73_eval_zero (r73highP_rep .G 0) (a:=362277936241) (b:=250000000000) (by decide +kernel)
  have hρ := r73_root12 (a:=362277936241) (b:=250000000000) (n:=1203790573548) (by norm_num) (by norm_num) (by norm_num)
  rw [ite_eq_left (by norm_num)] at hρ
  exact r73norm_rep (r73mass_rep (pn:=362277936241) (pd:=250000000000) (rn:=300947643387) (rd:=250000000000) (r73highP_rep .G 0) (by norm_num)
    (by norm_num) (by norm_num) h0 (hρ.trans (by norm_num)))

private theorem r73hm_G_1 : (r73highMass .G 1).Rep (highMass .G 1) := by
  have h0 := r73_eval_zero (r73highP_rep .G 1) (a:=165707506467540267494772073) (b:=134089791897600000000000000) (by decide +kernel)
  have hρ := r73_root12 (a:=165707506467540267494772073) (b:=134089791897600000000000000) (n:=1111663208961) (by norm_num) (by norm_num) (by norm_num)
  rw [ite_eq_right (by norm_num)] at hρ
  exact r73norm_rep (r73mass_rep (pn:=165707506467540267494772073) (pd:=134089791897600000000000000) (rn:=555831604481) (rd:=500000000000) (r73highP_rep .G 1) (by norm_num)
    (by norm_num) (by norm_num) h0 (hρ.trans (by norm_num)))

private theorem r73hm_G_2 : (r73highMass .G 2).Rep (highMass .G 2) := by
  have h0 := r73_eval_zero (r73highP_rep .G 2) (a:=410622234453) (b:=200000000000) (by decide +kernel)
  have hρ := r73_root12 (a:=410622234453) (b:=200000000000) (n:=1432868162904) (by norm_num) (by norm_num) (by norm_num)
  rw [ite_eq_left (by norm_num)] at hρ
  exact r73norm_rep (r73mass_rep (pn:=410622234453) (pd:=200000000000) (rn:=179108520363) (rd:=125000000000) (r73highP_rep .G 2) (by norm_num)
    (by norm_num) (by norm_num) h0 (hρ.trans (by norm_num)))

private theorem r73hm_G_3 : (r73highMass .G 3).Rep (highMass .G 3) := by
  have h0 := r73_eval_zero (r73highP_rep .G 3) (a:=1092234423645234978844299752297786636118889) (b:=516009727743224079974400000000000000000000) (by decide +kernel)
  have hρ := r73_root12 (a:=1092234423645234978844299752297786636118889) (b:=516009727743224079974400000000000000000000) (n:=1454886069352) (by norm_num) (by norm_num) (by norm_num)
  rw [ite_eq_left (by norm_num)] at hρ
  exact r73norm_rep (r73mass_rep (pn:=1092234423645234978844299752297786636118889) (pd:=516009727743224079974400000000000000000000) (rn:=181860758669) (rd:=125000000000) (r73highP_rep .G 3) (by norm_num)
    (by norm_num) (by norm_num) h0 (hρ.trans (by norm_num)))

private theorem r73hm_B_0 : (r73highMass .B 0).Rep (highMass .B 0) := by
  have h0 := r73_eval_zero (r73highP_rep .B 0) (a:=362277936241) (b:=250000000000) (by decide +kernel)
  have hρ := r73_root12 (a:=362277936241) (b:=250000000000) (n:=1203790573548) (by norm_num) (by norm_num) (by norm_num)
  rw [ite_eq_left (by norm_num)] at hρ
  exact r73norm_rep (r73mass_rep (pn:=362277936241) (pd:=250000000000) (rn:=300947643387) (rd:=250000000000) (r73highP_rep .B 0) (by norm_num)
    (by norm_num) (by norm_num) h0 (hρ.trans (by norm_num)))

private theorem r73hm_B_1 : (r73highMass .B 1).Rep (highMass .B 1) := by
  have h0 := r73_eval_zero (r73highP_rep .B 1) (a:=58371017589) (b:=40000000000) (by decide +kernel)
  have hρ := r73_root12 (a:=58371017589) (b:=40000000000) (n:=1208004734976) (by norm_num) (by norm_num) (by norm_num)
  rw [ite_eq_left (by norm_num)] at hρ
  exact r73norm_rep (r73mass_rep (pn:=58371017589) (pd:=40000000000) (rn:=294923031) (rd:=244140625) (r73highP_rep .B 1) (by norm_num)
    (by norm_num) (by norm_num) h0 (hρ.trans (by norm_num)))

private theorem r73hm_B_2 : (r73highMass .B 2).Rep (highMass .B 2) := by
  have h0 := r73_eval_zero (r73highP_rep .B 2) (a:=797346041684883383339651) (b:=465589555200000000000000) (by decide +kernel)
  have hρ := r73_root12 (a:=797346041684883383339651) (b:=465589555200000000000000) (n:=1308644869234) (by norm_num) (by norm_num) (by norm_num)
  rw [ite_eq_right (by norm_num)] at hρ
  exact r73norm_rep (r73mass_rep (pn:=797346041684883383339651) (pd:=465589555200000000000000) (rn:=261728973847) (rd:=200000000000) (r73highP_rep .B 2) (by norm_num)
    (by norm_num) (by norm_num) h0 (hρ.trans (by norm_num)))

private theorem r73hm_B_3 : (r73highMass .B 3).Rep (highMass .B 3) := by
  have h0 := r73_eval_zero (r73highP_rep .B 3) (a:=1092234423645234978844299752297786636118889) (b:=516009727743224079974400000000000000000000) (by decide +kernel)
  have hρ := r73_root12 (a:=1092234423645234978844299752297786636118889) (b:=516009727743224079974400000000000000000000) (n:=1454886069352) (by norm_num) (by norm_num) (by norm_num)
  rw [ite_eq_left (by norm_num)] at hρ
  exact r73norm_rep (r73mass_rep (pn:=1092234423645234978844299752297786636118889) (pd:=516009727743224079974400000000000000000000) (rn:=181860758669) (rd:=125000000000) (r73highP_rep .B 3) (by norm_num)
    (by norm_num) (by norm_num) h0 (hρ.trans (by norm_num)))

private theorem r73hm_equal_0 : (r73highMass .equal 0).Rep (highMass .equal 0) := by
  have h0 := r73_eval_zero (r73highP_rep .equal 0) (a:=383023851466510906753130398742299845927185340241) (b:=271796553912223934458904382013440000000000000000) (by decide +kernel)
  have hρ := r73_root12 (a:=383023851466510906753130398742299845927185340241) (b:=271796553912223934458904382013440000000000000000) (n:=1187109926324) (by norm_num) (by norm_num) (by norm_num)
  rw [ite_eq_left (by norm_num)] at hρ
  exact r73norm_rep (r73mass_rep (pn:=383023851466510906753130398742299845927185340241) (pd:=271796553912223934458904382013440000000000000000) (rn:=296777481581) (rd:=250000000000) (r73highP_rep .equal 0) (by norm_num)
    (by norm_num) (by norm_num) h0 (hρ.trans (by norm_num)))

private theorem r73hm_equal_1 : (r73highMass .equal 1).Rep (highMass .equal 1) := by
  have h0 := r73_eval_zero (r73highP_rep .equal 1) (a:=6857071673551657716624192401652971787121792621) (b:=4831938736217314390380522346905600000000000000) (by decide +kernel)
  have hρ := r73_root12 (a:=6857071673551657716624192401652971787121792621) (b:=4831938736217314390380522346905600000000000000) (n:=1191265693092) (by norm_num) (by norm_num) (by norm_num)
  rw [ite_eq_right (by norm_num)] at hρ
  exact r73norm_rep (r73mass_rep (pn:=6857071673551657716624192401652971787121792621) (pd:=4831938736217314390380522346905600000000000000) (rn:=1191265693093) (rd:=1000000000000) (r73highP_rep .equal 1) (by norm_num)
    (by norm_num) (by norm_num) h0 (hρ.trans (by norm_num)))

private theorem r73hm_equal_2 : (r73highMass .equal 2).Rep (highMass .equal 2) := by
  have h0 := r73_eval_zero (r73highP_rep .equal 2) (a:=48237399461214211694603420733990516450917840717) (b:=24159693681086571951902611734528000000000000000) (by decide +kernel)
  have hρ := r73_root12 (a:=48237399461214211694603420733990516450917840717) (b:=24159693681086571951902611734528000000000000000) (n:=1413013240570) (by norm_num) (by norm_num) (by norm_num)
  rw [ite_eq_left (by norm_num)] at hρ
  exact r73norm_rep (r73mass_rep (pn:=48237399461214211694603420733990516450917840717) (pd:=24159693681086571951902611734528000000000000000) (rn:=141301324057) (rd:=100000000000) (r73highP_rep .equal 2) (by norm_num)
    (by norm_num) (by norm_num) h0 (hρ.trans (by norm_num)))

private theorem r73hm_equal_3 : (r73highMass .equal 3).Rep (highMass .equal 3) := by
  have h0 := r73_eval_zero (r73highP_rep .equal 3) (a:=1170220976333354656072178768459690104061402401231497054965753205591253858434889) (b:=560998663143172792418520742175621836554558157822623744000000000000000000000000) (by decide +kernel)
  have hρ := r73_root12 (a:=1170220976333354656072178768459690104061402401231497054965753205591253858434889) (b:=560998663143172792418520742175621836554558157822623744000000000000000000000000) (n:=1444285416859) (by norm_num) (by norm_num) (by norm_num)
  rw [ite_eq_right (by norm_num)] at hρ
  exact r73norm_rep (r73mass_rep (pn:=1170220976333354656072178768459690104061402401231497054965753205591253858434889) (pd:=560998663143172792418520742175621836554558157822623744000000000000000000000000) (rn:=72214270843) (rd:=50000000000) (r73highP_rep .equal 3) (by norm_num)
    (by norm_num) (by norm_num) h0 (hρ.trans (by norm_num)))

private theorem r73highMass_rep (r : HighCase) (i : Fin 4) : (r73highMass r i).Rep (highMass r i) := by
  cases r <;> fin_cases i
  exacts [r73hm_H_0,r73hm_H_1,r73hm_H_2,r73hm_H_3,r73hm_G_0,r73hm_G_1,r73hm_G_2,r73hm_G_3,r73hm_B_0,r73hm_B_1,r73hm_B_2,r73hm_B_3,r73hm_equal_0,r73hm_equal_1,r73hm_equal_2,r73hm_equal_3]

private def r73num4 (A P0 P1 P2 P3 r0 r1 r2 r3 : Scaled) : Scaled :=
  (((((((r73c 2 1)).mul A).mul r0).mul r1).mul r2).mul r3).sub (((r73c 494696877 250000000)).mul
    ((((((P0.add (r0.pow 2)).mul r1).mul r2).mul r3).add
      ((((P1.add (r1.pow 2)).mul r0).mul r2).mul r3)).add
      ((((P2.add (r2.pow 2)).mul r0).mul r1).mul r3) |>.add
      ((((P3.add (r3.pow 2)).mul r0).mul r1).mul r2)))
private theorem r73num4_rep {A P0 P1 P2 P3 r0 r1 r2 r3 : Scaled}
    {a p0 p1 p2 p3 s0 s1 s2 s3 : ℚ[X]}
    (hA : A.Rep a) (h0 : P0.Rep p0) (h1 : P1.Rep p1) (h2 : P2.Rep p2) (h3 : P3.Rep p3)
    (g0 : r0.Rep s0) (g1 : r1.Rep s1) (g2 : r2.Rep s2) (g3 : r3.Rep s3) :
    (r73num4 A P0 P1 P2 P3 r0 r1 r2 r3).Rep (PositiveTD.Certificate.num4 a p0 p1 p2 p3 s0 s1 s2 s3) :=
  (((((((r73c_rep (n:=2) (d:=1) (q:=2) (by norm_num))).mul hA).mul g0).mul g1).mul g2).mul g3).sub (((r73c_rep (n:=494696877) (d:=250000000) (by norm_num [PositiveTD.Certificate.Rbar]))).mul
    ((((((h0.add (g0.pow 2)).mul g1).mul g2).mul g3).add
      ((((h1.add (g1.pow 2)).mul g0).mul g2).mul g3)).add
      ((((h2.add (g2.pow 2)).mul g0).mul g1).mul g3) |>.add
      ((((h3.add (g3.pow 2)).mul g0).mul g1).mul g2)))

private def r73highNum (r : HighCase) : Scaled := r73norm
  (r73num4 (r73highA r) (r73highP r 0) (r73highP r 1) (r73highP r 2) (r73highP r 3)
    (r73highMass r 0) (r73highMass r 1) (r73highMass r 2) (r73highMass r 3))
private theorem r73highNum_rep (r : HighCase) : (r73highNum r).Rep (highNumerator r) := r73norm_rep
  (r73num4_rep (r73highA_rep r) (r73highP_rep r 0) (r73highP_rep r 1) (r73highP_rep r 2)
    (r73highP_rep r 3) (r73highMass_rep r 0) (r73highMass_rep r 1) (r73highMass_rep r 2)
    (r73highMass_rep r 3))

/-! ### The derivative numerators -/

private def r73dP (atH : Bool) : Scaled :=
  if atH then r73norm ((Scaled.ofNat 1).add (r73highK.pow 2))
  else r73norm ((r73highK.pow 2).add (r73highL.pow 2))
private theorem r73dP_rep (atH : Bool) : (r73dP atH).Rep (derivativeP atH) := by
  unfold r73dP derivativeP
  split_ifs
  · exact r73norm_rep (Scaled.rep_one.add (r73highK_rep.pow 2))
  · exact r73norm_rep ((r73highK_rep.pow 2).add (r73highL_rep.pow 2))
private def r73dProd (atH : Bool) : Scaled := if atH then r73highK else r73norm (r73highK.mul r73highL)
private theorem r73dProd_rep (atH : Bool) : (r73dProd atH).Rep (derivativeProduct atH) := by
  unfold r73dProd derivativeProduct
  split_ifs
  · exact r73highK_rep
  · exact r73norm_rep (r73highK_rep.mul r73highL_rep)
private def r73dD : Scaled := r73norm ((Scaled.ofNat 1).add ((r73highC.pow 2).mul (r73C12t.pow 2)))
private theorem r73dD_rep : r73dD.Rep derivativeD :=
  r73norm_rep (Scaled.rep_one.add ((r73highC_rep.pow 2).mul (r73C12t_rep.pow 2)))

private def r73dMass (atH : Bool) : Scaled :=
  if atH then r73norm (r73mass 362277936241 250000000000 300947643387 250000000000 (r73dP true))
  else r73norm (r73mass 58371017589 40000000000 294923031 244140625 (r73dP false))
private def r73dDMass : Scaled := r73norm (r73mass 1170220976333354656072178768459690104061402401231497054965753205591253858434889 560998663143172792418520742175621836554558157822623744000000000000000000000000 72214270843 50000000000 r73dD)

private theorem r73dMass_true : (r73dMass true).Rep (derivativeMass true) := by
  have h0 := r73_eval_zero (r73dP_rep true) (a:=362277936241) (b:=250000000000) (by decide +kernel)
  have hρ := r73_root12 (a:=362277936241) (b:=250000000000) (n:=1203790573548) (by norm_num) (by norm_num) (by norm_num)
  rw [ite_eq_left (by norm_num)] at hρ
  exact r73norm_rep (r73mass_rep (pn:=362277936241) (pd:=250000000000) (rn:=300947643387) (rd:=250000000000) (r73dP_rep true) (by norm_num)
    (by norm_num) (by norm_num) h0 (hρ.trans (by norm_num)))

private theorem r73dMass_false : (r73dMass false).Rep (derivativeMass false) := by
  have h0 := r73_eval_zero (r73dP_rep false) (a:=58371017589) (b:=40000000000) (by decide +kernel)
  have hρ := r73_root12 (a:=58371017589) (b:=40000000000) (n:=1208004734976) (by norm_num) (by norm_num) (by norm_num)
  rw [ite_eq_left (by norm_num)] at hρ
  exact r73norm_rep (r73mass_rep (pn:=58371017589) (pd:=40000000000) (rn:=294923031) (rd:=244140625) (r73dP_rep false) (by norm_num)
    (by norm_num) (by norm_num) h0 (hρ.trans (by norm_num)))

private theorem r73dDMass_rep : r73dDMass.Rep derivativeDMass := by
  have h0 := r73_eval_zero r73dD_rep (a:=1170220976333354656072178768459690104061402401231497054965753205591253858434889) (b:=560998663143172792418520742175621836554558157822623744000000000000000000000000) (by decide +kernel)
  have hρ := r73_root12 (a:=1170220976333354656072178768459690104061402401231497054965753205591253858434889) (b:=560998663143172792418520742175621836554558157822623744000000000000000000000000) (n:=1444285416859) (by norm_num) (by norm_num) (by norm_num)
  rw [ite_eq_right (by norm_num)] at hρ
  exact r73norm_rep (r73mass_rep (pn:=1170220976333354656072178768459690104061402401231497054965753205591253858434889) (pd:=560998663143172792418520742175621836554558157822623744000000000000000000000000) (rn:=72214270843) (rd:=50000000000) r73dD_rep (by norm_num)
    (by norm_num) (by norm_num) h0 (hρ.trans (by norm_num)))

private theorem r73dMass_rep (atH : Bool) : (r73dMass atH).Rep (derivativeMass atH) := by
  cases atH
  · exact r73dMass_false
  · exact r73dMass_true

private def r73dAP (atH : Bool) : Scaled := r73norm ((r73dP atH).add ((r73dMass atH).pow 2))
private def r73dAD : Scaled := r73norm (r73dD.add (r73dDMass.pow 2))
private def r73dNum (atH : Bool) : Scaled := r73norm
  (((((((r73c 1978787 500000)).mul (r73dProd atH)).mul (r73C10t.pow 2)).mul r73dAD).mul (r73dMass atH)).add
    (((((r73c 1978787 500000)).mul r73S11t).mul (r73dAP atH)).mul r73dDMass) |>.sub
    (((((r73c 13 12)).add r73S9t).mul (r73dAP atH)).mul r73dAD))
private theorem r73dNum_rep (atH : Bool) : (r73dNum atH).Rep (derivativeNumerator atH) := by
  have hAP := r73norm_rep ((r73dP_rep atH).add ((r73dMass_rep atH).pow 2))
  have hAD := r73norm_rep (r73dD_rep.add (r73dDMass_rep.pow 2))
  have hh := r73norm_rep ((((((((r73c_rep (n:=1978787) (d:=500000) (q:=(2*Rlo)) (by norm_num [Rlo]))).mul (r73dProd_rep atH)).mul
    (r73C10t_rep.pow 2)).mul hAD).mul (r73dMass_rep atH)).add
    (((((r73c_rep (n:=1978787) (d:=500000) (q:=(2*Rlo)) (by norm_num [Rlo]))).mul r73S11t_rep).mul hAP).mul r73dDMass_rep)).sub
    (((((r73c_rep (n:=13) (d:=12) (q:=K) (by norm_num [K]))).add r73S9t_rep).mul hAP).mul hAD))
  simp only [derivativeNumerator]
  exact hh

/-! ### The late difference and the H quotient -/

private def r73lateDiff : Scaled := r73norm
  ((((r73c 2153 2000)).sub (((r73c 61 200)).mul r73thetaX)).sub r73highC)
private theorem r73lateDiff_rep : r73lateDiff.Rep lateDifference := r73norm_rep
  ((((r73c_rep (n:=2153) (d:=2000) (by norm_num))).sub (((r73c_rep (n:=61) (d:=200) (by norm_num))).mul r73thetaX_rep)).sub r73highC_rep)

private theorem r73_quot : highHQuotient=divX (highNumerator .H) := by
  have hb : (r73highNum .H).s≠0 ∧ (r73highNum .H).l.length≤40 := by decide +kernel
  have hdeg := (r73highNum_rep .H).natDegree_le hb.1
  ext n
  rw [coeff_divX]
  simp only [highHQuotient,finsetSum_coeff,coeff_C_mul_X_pow]
  rw [Fin.sum_univ_eq_sum_range (fun i => if n=i then (highNumerator .H).coeff (i+1) else 0) 39,
    Finset.sum_ite_eq]
  split_ifs with hn
  · rfl
  · rw [Finset.mem_range,not_lt] at hn
    exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm

private theorem r73_icc {lo hi : ℚ} {lo' hi' x : ℝ} (hlo : (lo:ℝ)=lo') (hhi : (hi:ℝ)=hi')
    (hx : x∈Icc lo' hi') : x∈Icc (lo:ℝ) (hi:ℝ) := by
  rw [hlo,hhi]
  exact hx

theorem low_mass_certificate (i : Fin 3) :
    centered 0 L (lowMass i)=expansion 3 (centered 0 L (lowMass i)) ∧
      (23/20:ℚ)<lowerOn 3 0 L (lowMass i) := by
  have hK := r73_cert (D:=3) (r73norm_rep (r73lowMK_rep.centered 1 12 1 1 (a:=0) (b:=L)
    (by norm_num) (by norm_num [L]) (by norm_num [L]))) (a:=23) (b:=20) (by decide +kernel)
  have hM := r73_cert (D:=3) (r73norm_rep (r73lowMM_rep.centered 1 12 1 1 (a:=0) (b:=L)
    (by norm_num) (by norm_num [L]) (by norm_num [L]))) (a:=23) (b:=20) (by decide +kernel)
  push_cast at hK hM
  fin_cases i
  · exact hK
  · exact hK
  · exact hM

theorem low_numerator_certificate (ep : Split) :
    centered 0 L (lowNumerator ep)=expansion 32 (centered 0 L (lowNumerator ep)) ∧
      (17/10000:ℚ)<lowerOn 32 0 L (lowNumerator ep) := by
  have hc := r73_cert (D:=32) (r73norm_rep ((r73lowNum_rep ep).centered 1 12 1 1 (a:=0) (b:=L)
    (by norm_num) (by norm_num [L]) (by norm_num [L]))) (a:=17) (b:=10000)
    (by cases ep <;> decide +kernel)
  push_cast at hc
  exact hc

theorem low_base_certificate (ep : Split) :
    centered 0 L (lowBase ep)=expansion 12 (centered 0 L (lowBase ep)) ∧
      (37/5:ℚ)<lowerOn 12 0 L (lowBase ep) := by
  have hc := r73_cert (D:=12) (r73norm_rep ((r73lowBase_rep ep).centered 1 12 1 1 (a:=0) (b:=L)
    (by norm_num) (by norm_num [L]) (by norm_num [L]))) (a:=37) (b:=5)
    (by cases ep <;> decide +kernel)
  push_cast at hc
  exact hc

theorem low_mass_positive (i : Fin 3) {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    0<aeval θ (lowMass i) := by
  have hh := positive_on_interval (by norm_num [L] : (0:ℚ)<L)
    (low_mass_certificate i).1 (low_mass_certificate i).2
    (r73_icc (by norm_num) (by norm_num [L]) hθ)
  have hr : (0:ℝ)<((23/20:ℚ):ℝ) := by norm_num
  linarith

theorem low_numerator_positive (ep : Split) {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    0<aeval θ (lowNumerator ep) := by
  have hh := positive_on_interval (by norm_num [L] : (0:ℚ)<L)
    (low_numerator_certificate ep).1 (low_numerator_certificate ep).2
    (r73_icc (by norm_num) (by norm_num [L]) hθ)
  have hr : (0:ℝ)<((17/10000:ℚ):ℝ) := by norm_num
  linarith

theorem low_base_positive (ep : Split) {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    0<aeval θ (lowBase ep) := by
  have hh := positive_on_interval (by norm_num [L] : (0:ℚ)<L)
    (low_base_certificate ep).1 (low_base_certificate ep).2
    (r73_icc (by norm_num) (by norm_num [L]) hθ)
  have hr : (0:ℝ)<((37/5:ℚ):ℝ) := by norm_num
  linarith

theorem high_mass_certificate (r : HighCase) (i : Fin 4) :
    centered 0 span (highMass r i)=expansion 3 (centered 0 span (highMass r i)) ∧
      (69/100:ℚ)<lowerOn 3 0 span (highMass r i) := by
  have hc := r73_cert (D:=3) (r73norm_rep ((r73highMass_rep r i).centered 4 15 1 1 (a:=0) (b:=span)
    (by norm_num) (by norm_num [span,h,L]) (by norm_num [span,h,L]))) (a:=69) (b:=100)
    (by cases r <;> fin_cases i <;> decide +kernel)
  push_cast at hc
  exact hc

theorem high_direct_certificate (r : HighCase) (hr : r≠.H) :
    centered 0 span (highNumerator r)=
      expansion (highDegree r) (centered 0 span (highNumerator r)) ∧
    highReserve r<lowerOn (highDegree r) 0 span (highNumerator r) := by
  cases r
  · exact absurd rfl hr
  · have hc := r73_cert (D:=39) (r73norm_rep ((r73highNum_rep .G).centered 4 15 1 1 (a:=0)
      (b:=span) (by norm_num) (by norm_num [span,h,L]) (by norm_num [span,h,L]))) (a:=7) (b:=5000)
      (by decide +kernel)
    push_cast at hc
    exact hc
  · have hc := r73_cert (D:=39) (r73norm_rep ((r73highNum_rep .B).centered 4 15 1 1 (a:=0)
      (b:=span) (by norm_num) (by norm_num [span,h,L]) (by norm_num [span,h,L]))) (a:=69) (b:=1000)
      (by decide +kernel)
    push_cast at hc
    exact hc
  · have hc := r73_cert (D:=63) (r73norm_rep ((r73highNum_rep .equal).centered 4 15 1 1 (a:=0)
      (b:=span) (by norm_num) (by norm_num [span,h,L]) (by norm_num [span,h,L]))) (a:=3) (b:=1250)
      (by decide +kernel)
    push_cast at hc
    exact hc

theorem high_H_certificate :
    highNumerator .H=C ((highNumerator .H).eval 0)+X*highHQuotient ∧
    (79/100000:ℚ)<(highNumerator .H).eval 0 ∧
    centered 0 span highHQuotient=expansion 38 (centered 0 span highHQuotient) ∧
    (13/100:ℚ)<lowerOn 38 0 span highHQuotient := by
  have h0 := r73_lt_const (r73_rep_eval_zero (r73highNum_rep .H)) (a:=79) (b:=100000)
    (by decide +kernel)
  have hq := (r73highNum_rep .H).divX
  rw [← r73_quot] at hq
  have hc := r73_cert (D:=38) (r73norm_rep (hq.centered 4 15 1 1 (a:=0) (b:=span) (by norm_num)
    (by norm_num [span,h,L]) (by norm_num [span,h,L]))) (a:=13) (b:=100) (by decide +kernel)
  push_cast at h0 hc
  refine ⟨?_,h0,hc⟩
  rw [r73_quot,← coeff_zero_eq_eval_zero,add_comm]
  exact (X_mul_divX_add _).symm

theorem high_mass_positive (r : HighCase) (i : Fin 4) {x : ℝ}
    (hx : x∈Icc (0:ℝ) (8/15)) : 0<aeval x (highMass r i) := by
  have hh := positive_on_interval (by norm_num [span,h,L] : (0:ℚ)<span)
    (high_mass_certificate r i).1 (high_mass_certificate r i).2
    (r73_icc (by norm_num) (by norm_num [span,h,L]) hx)
  have hr : (0:ℝ)<((69/100:ℚ):ℝ) := by norm_num
  linarith

theorem high_numerator_positive (r : HighCase) {x : ℝ}
    (hx : x∈Icc (0:ℝ) (8/15)) : 0<aeval x (highNumerator r) := by
  have hx' := r73_icc (lo:=0) (hi:=span) (by norm_num) (by norm_num [span,h,L]) hx
  by_cases hr : r=.H
  · subst r
    obtain ⟨hid,h0,hq,hres⟩ := high_H_certificate
    have hquot := positive_on_interval (by norm_num [span,h,L] : (0:ℚ)<span) hq hres hx'
    have h0' : (79/100000:ℝ)<(((highNumerator .H).eval 0:ℚ):ℝ) := by
      have hh := Rat.cast_lt (K:=ℝ).mpr h0
      push_cast at hh
      exact hh
    rw [hid]
    simp only [map_add,map_mul,aeval_C,aeval_X,eq_ratCast]
    have hq0 : (0:ℝ)≤aeval x highHQuotient := by
      have hh : (0:ℝ)<((13/100:ℚ):ℝ) := by norm_num
      linarith
    have hp := mul_nonneg hx.1 hq0
    linarith
  · have hc := high_direct_certificate r hr
    have hh := positive_on_interval (by norm_num [span,h,L] : (0:ℚ)<span) hc.1 hc.2 hx'
    have hres : (0:ℝ)<(highReserve r:ℝ) := by cases r <;> norm_num [highReserve]
    exact hres.trans hh

theorem derivative_mass_certificate (atH : Bool) :
    (centered 0 span (derivativeMass atH)=expansion 3 (centered 0 span (derivativeMass atH)) ∧
      (23/20:ℚ)<lowerOn 3 0 span (derivativeMass atH)) ∧
    (centered 0 span derivativeDMass=expansion 3 (centered 0 span derivativeDMass) ∧
      (23/20:ℚ)<lowerOn 3 0 span derivativeDMass) := by
  have hc := r73_cert (D:=3) (r73norm_rep ((r73dMass_rep atH).centered 4 15 1 1 (a:=0) (b:=span)
    (by norm_num) (by norm_num [span,h,L]) (by norm_num [span,h,L]))) (a:=23) (b:=20)
    (by cases atH <;> decide +kernel)
  have hd := r73_cert (D:=3) (r73norm_rep (r73dDMass_rep.centered 4 15 1 1 (a:=0) (b:=span)
    (by norm_num) (by norm_num [span,h,L]) (by norm_num [span,h,L]))) (a:=23) (b:=20)
    (by decide +kernel)
  push_cast at hc hd
  exact ⟨hc,hd⟩

theorem derivative_certificate (atH : Bool) :
    centered 0 span (derivativeNumerator atH)=
      expansion (derivativeDegree atH) (centered 0 span (derivativeNumerator atH)) ∧
    derivativeReserve atH<lowerOn (derivativeDegree atH) 0 span (derivativeNumerator atH) := by
  cases atH
  · have hc := r73_cert (D:=84) (r73norm_rep ((r73dNum_rep false).centered 4 15 1 1 (a:=0)
      (b:=span) (by norm_num) (by norm_num [span,h,L]) (by norm_num [span,h,L]))) (a:=1) (b:=25)
      (by decide +kernel)
    push_cast at hc
    exact hc
  · have hc := r73_cert (D:=81) (r73norm_rep ((r73dNum_rep true).centered 4 15 1 1 (a:=0)
      (b:=span) (by norm_num) (by norm_num [span,h,L]) (by norm_num [span,h,L]))) (a:=259) (b:=500)
      (by decide +kernel)
    push_cast at hc
    exact hc

theorem derivative_masses_positive (atH : Bool) {x : ℝ} (hx : x∈Icc (0:ℝ) (8/15)) :
    0<aeval x (derivativeMass atH) ∧ 0<aeval x derivativeDMass := by
  have hx' := r73_icc (lo:=0) (hi:=span) (by norm_num) (by norm_num [span,h,L]) hx
  have hc := derivative_mass_certificate atH
  have h0 := positive_on_interval (by norm_num [span,h,L] : (0:ℚ)<span) hc.1.1 hc.1.2 hx'
  have h1 := positive_on_interval (by norm_num [span,h,L] : (0:ℚ)<span) hc.2.1 hc.2.2 hx'
  have hr : (0:ℝ)<((23/20:ℚ):ℝ) := by norm_num
  exact ⟨by linarith,by linarith⟩

theorem derivative_numerator_positive (atH : Bool) {x : ℝ}
    (hx : x∈Icc (0:ℝ) (8/15)) : 0<aeval x (derivativeNumerator atH) := by
  have hx' := r73_icc (lo:=0) (hi:=span) (by norm_num) (by norm_num [span,h,L]) hx
  have hc := derivative_certificate atH
  have hh := positive_on_interval (by norm_num [span,h,L] : (0:ℚ)<span) hc.1 hc.2 hx'
  have hr : (0:ℝ)<(derivativeReserve atH:ℝ) := by cases atH <;> norm_num [derivativeReserve]
  exact hr.trans hh

theorem high_auxiliary_certificate :
    (centered 0 span (highBase-1)=expansion 20 (centered 0 span (highBase-1)) ∧
      (399/50:ℚ)<lowerOn 20 0 span (highBase-1)) ∧
    (centered 0 span (-highSineCoefficient)=expansion 6 (centered 0 span (-highSineCoefficient)) ∧
      0<lowerOn 6 0 span (-highSineCoefficient)) ∧
    (centered 0 span (-highC.derivative)=expansion 14 (centered 0 span (-highC.derivative)) ∧
      (22/125:ℚ)<lowerOn 14 0 span (-highC.derivative)) ∧
    highC.eval 0<(1057/1000:ℚ) := by
  have h1 := r73_cert (D:=20) (r73norm_rep ((r73highBase_rep.sub Scaled.rep_one).centered 4 15 1 1
    (a:=0) (b:=span) (by norm_num) (by norm_num [span,h,L]) (by norm_num [span,h,L])))
    (a:=399) (b:=50) (by decide +kernel)
  have h2 := r73_cert (D:=6) (r73norm_rep (r73highSine_rep.neg.centered 4 15 1 1
    (a:=0) (b:=span) (by norm_num) (by norm_num [span,h,L]) (by norm_num [span,h,L])))
    (a:=0) (b:=1) (by decide +kernel)
  have h3 := r73_cert (D:=14) (r73norm_rep ((r73deriv_rep r73highC_rep).neg.centered 4 15 1 1
    (a:=0) (b:=span) (by norm_num) (by norm_num [span,h,L]) (by norm_num [span,h,L])))
    (a:=22) (b:=125) (by decide +kernel)
  have h4 := r73_const_lt (r73_rep_eval_zero r73highC_rep) (a:=1057) (b:=1000) (by decide +kernel)
  push_cast at h1 h2 h3 h4
  simp only [zero_div] at h2
  exact ⟨h1,h2,h3,h4⟩

theorem late_coefficient_certificate :
    (centered lateLeft span (-lateDifference.derivative.derivative)=
      expansion 13 (centered lateLeft span (-lateDifference.derivative.derivative)) ∧
      (37/40:ℚ)<lowerOn 13 lateLeft span (-lateDifference.derivative.derivative)) ∧
    (9/50000:ℚ)<lateDifference.eval lateLeft ∧
    (3/62500:ℚ)<lateDifference.eval span := by
  have h1 := r73_cert (D:=13) (r73norm_rep ((r73deriv_rep (r73deriv_rep r73lateDiff_rep)).neg.centered
    1 120 55 9 (a:=lateLeft) (b:=span) (by norm_num) (by norm_num [lateLeft,span,h,L])
      (by norm_num [lateLeft,span,h,L]))) (a:=37) (b:=40) (by decide +kernel)
  have h2 := r73_lt_const (r73_eval_rep r73lateDiff_rep 1 60 23 (x:=lateLeft) (by norm_num)
    (by norm_num [lateLeft,L])) (a:=9) (b:=50000) (by decide +kernel)
  have h3 := r73_lt_const (r73_eval_rep r73lateDiff_rep 8 15 1 (x:=span) (by norm_num)
    (by norm_num [span,h,L])) (a:=3) (b:=62500) (by decide +kernel)
  push_cast at h1 h2 h3
  exact ⟨h1,h2,h3⟩

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveBT.Certificate

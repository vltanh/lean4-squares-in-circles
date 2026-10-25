module

public import SquaresInCircles.Eight.Owners.GA.Nonnegative.TotalsPolynomial
public import SquaresInCircles.Eight.Owners.GA.Positive.BT3Data

/-!
# Eight squares: the two small-total BT3 endpoint certificates

Both certificates use the
same three positive cubic masses. The A endpoint is bounded directly
on `[0,1/6]`; the T endpoint decreases to a positive right endpoint.
-/

@[expose] public section
noncomputable section
open Set Polynomial
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.PositiveBT3.LowCertificate
open NonnegativeTotals

abbrev L : ℚ := 1/6
abbrev C10 := PositiveTD.Certificate.C10
abbrev S9 := PositiveTD.Certificate.S9
abbrev S11 := PositiveTD.Certificate.S11
abbrev Rbar := NonnegativeTotals.Certificate.Rbar
abbrev abar := NonnegativeTotals.Certificate.abar
abbrev sigmabar := NonnegativeTotals.Certificate.sigmabar
abbrev cbar : ℚ := 449607033/500000000

def k : ℚ[X] := C (2933/5000)+C (1239/2500)*X
def m : ℚ[X] := C (5821/5000)-C (4437/5000)*X
def J : ℚ[X] := C (1/2)*(C10-1)+C (1/2-abar)*S9

def ABase : Endpoint → ℚ[X]
  | .atA => C 2*k+C (11/2-cbar)+m*C (5/2-cbar)+J
  | .atT => C 2*k+C (11/2-cbar)+m*
      (1+C (3/2-cbar)*C10+C (1/2+(293/1000)*(1-cbar)-sigmabar)*S9)
def A (ep : Endpoint) : ℚ[X] := ABase ep+C10-1

def P : Fin 3 → ℚ[X] := ![1+k^2-C 2*k*S11,1+k^2,1+m^2]
def rho : Fin 3 → ℚ := ![579676539/500000000,579676539/500000000,1534718749/1000000000]

def truncate3 (p : ℚ[X]) : ℚ[X] := ∑i : Fin 4,C (p.coeff i.val)*X^i.val
def mass (i : Fin 3) : ℚ[X] :=
  let p := P i
  let w := C (1/p.eval 0)*(truncate3 p-C (p.eval 0))
  C (rho i)*truncate3 (1+C (1/2)*w-C (1/8)*w^2+C (1/16)*w^3)
def numerator (ep : Endpoint) : ℚ[X] :=
  PositiveTD.Certificate.num3 (A ep) (P 0) (P 1) (P 2) (mass 0) (mass 1) (mass 2)
def degree : Endpoint → ℕ | .atA => 19 | .atT => 20

@[simp] theorem k_eval (t : ℝ) : aeval t k=lowK t := by
  simp [k,lowK]
@[simp] theorem m_eval (t : ℝ) : aeval t m=lowM t := by
  simp [m,lowM,Cmax]

section r81Cert
open WholeIntervalPolynomial WholeIntervalPolynomial.Certificate

/-! ### Integer certificates

Each polynomial is mirrored by a scaled integer coefficient list
(`PolynomialCertificates`), normalized by its gcd after every product;
the kernel evaluates the lists. -/

private def r81_gcd (s : ℕ) : List ℤ → ℕ
  | [] => s
  | a :: l => Nat.gcd a.natAbs (r81_gcd s l)

private theorem r81_gcd_dvd (s : ℕ) : ∀ l : List ℤ,
    r81_gcd s l ∣ s ∧ ∀ a ∈ l,((r81_gcd s l : ℕ):ℤ) ∣ a
  | [] => by simp [r81_gcd]
  | a :: l => by
    obtain ⟨h1,h2⟩ := r81_gcd_dvd s l
    refine ⟨(Nat.gcd_dvd_right _ _).trans h1,?_⟩
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact Int.natCast_dvd.mpr (Nat.gcd_dvd_left _ _)
    · exact (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right _ _)).trans (h2 b hb)

private theorem r81_smul_div (g : ℤ) : ∀ l : List ℤ,(∀ a ∈ l,g ∣ a) →
    smul g (l.map (fun a => a/g))=l
  | [],_ => rfl
  | a :: l,h => by
    simp only [List.map_cons,smul]
    rw [Int.mul_ediv_cancel' (h a List.mem_cons_self),
      r81_smul_div g l (fun b hb => h b (List.mem_cons_of_mem a hb))]

private theorem r81_toPoly_zero : ∀ l : List ℤ,toPoly (l.map (fun _ => (0:ℤ)))=0
  | [] => rfl
  | a :: l => by
    simp only [List.map_cons,toPoly,r81_toPoly_zero l,Int.cast_zero,map_zero,mul_zero,add_zero]

/-- Division of a scaled list by the gcd of its entries and its scale. -/
private def r81_red (c : Scaled) : Scaled :=
  ⟨c.l.map (fun a => a/((r81_gcd c.s c.l : ℕ):ℤ)),c.s/r81_gcd c.s c.l⟩

private theorem r81_rep_red {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) : (r81_red c).Rep p := by
  obtain ⟨h1,h2⟩ := r81_gcd_dvd c.s c.l
  set g := r81_gcd c.s c.l with hg
  have hl := r81_smul_div (g:ℤ) c.l h2
  unfold Scaled.Rep at *
  rw [← hl,toPoly_smul] at hc
  obtain ⟨k,hk⟩ := h1
  simp only [r81_red,← hg]
  rcases Nat.eq_zero_or_pos g with h0 | hpos
  · have hs : c.s=0 := by rw [hk,h0,zero_mul]
    have hz : ∀ a ∈ c.l,a=0 := fun a ha => by
      have := h2 a ha
      rw [h0,Nat.cast_zero] at this
      exact zero_dvd_iff.mp this
    rw [h0,hs]
    simp only [Nat.cast_zero,Int.ediv_zero,Nat.zero_div,map_zero,zero_mul]
    exact r81_toPoly_zero _
  · have hg0 : (g:ℚ)≠0 := by exact_mod_cast hpos.ne'
    rw [hk,Nat.mul_div_cancel_left k hpos]
    rw [hk] at hc
    push_cast at hc
    exact mul_left_cancel₀ (show C (g:ℚ)≠0 from C_ne_zero.mpr hg0)
      (hc.trans (by rw [map_mul,mul_assoc]))

private theorem r81_coeff_eq {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) (n : ℕ) :
    (c.l.getD n 0:ℚ)=c.s*p.coeff n := by
  have h := congrArg (fun q => q.coeff n) hc
  simpa only [coeff_toPoly,coeff_C_mul] using h

/-- The first four coefficients. -/
private def r81_trunc (c : Scaled) : Scaled := ⟨c.l.take 4,c.s⟩

private theorem r81_rep_trunc {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) :
    (r81_trunc c).Rep (truncate3 p) := by
  have hco := r81_coeff_eq hc
  unfold Scaled.Rep
  ext n
  rw [coeff_toPoly,coeff_C_mul]
  simp only [truncate3,Fin.sum_univ_four,Fin.val_zero,Fin.val_one,Fin.val_two,r81_trunc]
  rcases n with _|_|_|_|n
  · simp [← hco,List.getD]
  · simp [← hco,List.getD]
  · simp [← hco,List.getD]
  · simp [← hco,List.getD]
  · simp [List.getD]

/-- The constant term. -/
private def r81_c0 (c : Scaled) : Scaled := ⟨[c.l.getD 0 0],c.s⟩

private theorem r81_rep_c0 {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) :
    (r81_c0 c).Rep (C (p.eval 0)) := by
  unfold Scaled.Rep
  rw [← coeff_zero_eq_eval_zero]
  simp only [r81_c0,toPoly,mul_zero,add_zero,← map_mul,r81_coeff_eq hc 0]

/-- The reciprocal of the constant term. -/
private def r81_inv0 (c : Scaled) : Scaled :=
  ⟨[(c.s:ℤ)*(c.l.getD 0 0).sign],(c.l.getD 0 0).natAbs⟩

private theorem r81_rep_inv0 {c : Scaled} {p : ℚ[X]} (hc : c.Rep p)
    (h0 : c.l.getD 0 0≠0) : (r81_inv0 c).Rep (C (1/p.eval 0)) := by
  have hco := r81_coeff_eq hc 0
  have hz : ((c.l.getD 0 0:ℤ):ℚ)≠0 := by exact_mod_cast h0
  have hs' : (c.s:ℚ)≠0 := by intro h; rw [h,zero_mul] at hco; exact hz hco
  have hp : p.eval 0=((c.l.getD 0 0:ℤ):ℚ)/c.s := by
    rw [← coeff_zero_eq_eval_zero,hco]; field_simp
  unfold Scaled.Rep
  rw [hp]
  simp only [r81_inv0,toPoly,mul_zero,add_zero,← map_mul]
  congr 1
  set z := c.l.getD 0 0
  rcases lt_or_gt_of_ne h0 with hneg | hpos
  · rw [Int.sign_eq_neg_one_of_neg hneg]
    have ha : ((z.natAbs:ℕ):ℚ)=-(z:ℚ) := by
      rw [Nat.cast_natAbs,Int.cast_abs,abs_of_neg (by exact_mod_cast hneg)]
    rw [ha]
    push_cast
    field_simp
  · rw [Int.sign_eq_one_of_pos hpos]
    have ha : ((z.natAbs:ℕ):ℚ)=(z:ℚ) := by
      rw [Nat.cast_natAbs,Int.cast_abs,abs_of_pos (by exact_mod_cast hpos)]
    rw [ha]
    push_cast
    field_simp

private def r81_deriv : List ℤ → List ℤ
  | [] => []
  | _ :: l => WholeIntervalPolynomial.Certificate.add l (0 :: r81_deriv l)

private theorem r81_toPoly_deriv : ∀ l : List ℤ,toPoly (r81_deriv l)=derivative (toPoly l)
  | [] => by simp [r81_deriv,toPoly]
  | a :: l => by
    rw [r81_deriv,toPoly_add]
    simp only [toPoly,r81_toPoly_deriv l,derivative_add,derivative_C,derivative_mul,
      derivative_X,Int.cast_zero,map_zero]
    ring

private theorem r81_rep_deriv {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) :
    (⟨r81_deriv c.l,c.s⟩ : Scaled).Rep (derivative p) := by
  unfold Scaled.Rep at *
  rw [r81_toPoly_deriv,hc,derivative_C_mul]

private theorem r81_scale_cast (c : Scaled) :
    (c.s:ℚ)*2^c.l.length/2=(((c.s*2^c.l.length : ℕ):ℤ):ℚ)/2 := by
  push_cast
  ring

private theorem r81_lt_lowerOn {c : Scaled} {a b : ℚ} {p : ℚ[X]}
    (hc : c.Rep (WholeIntervalPolynomial.centered a b p)) (hs : c.s≠0) {D : ℕ}
    (hl : c.l.length≤D+1) {ρ : ℚ} {num : ℤ} {den : ℕ} (hρ : ρ=num/den) (hden : 0<den)
    (h : num*((c.s*2^c.l.length : ℕ):ℤ)<2*den*lowerZ D (fun j => (chebList c.l).getD j 0)) :
    ρ<lowerOn D a b p := by
  rw [lowerOn_eq_of_rep hc hs hl,r81_scale_cast]
  have hM : (0:ℤ)<((c.s*2^c.l.length : ℕ):ℤ) := by
    have := Nat.pos_of_ne_zero hs; positivity
  have hd : (0:ℚ)<den := by exact_mod_cast hden
  have hM' : (0:ℚ)<(((c.s*2^c.l.length : ℕ):ℤ):ℚ) := by exact_mod_cast hM
  have hq : ((num*((c.s*2^c.l.length : ℕ):ℤ):ℤ):ℚ)<
      ((2*den*lowerZ D (fun j => (chebList c.l).getD j 0):ℤ):ℚ) := by exact_mod_cast h
  push_cast at hq
  rw [lt_div_iff₀ (by positivity),hρ,div_mul_eq_mul_div,div_lt_iff₀ hd]
  push_cast at hM' ⊢
  linarith

private theorem r81_upperOn_lt {c : Scaled} {a b : ℚ} {p : ℚ[X]}
    (hc : c.Rep (WholeIntervalPolynomial.centered a b p)) (hs : c.s≠0) {D : ℕ}
    (hl : c.l.length≤D+1) {ρ : ℚ} {num : ℤ} {den : ℕ} (hρ : ρ=num/den) (hden : 0<den)
    (h : 2*den*upperZ D (fun j => (chebList c.l).getD j 0)<num*((c.s*2^c.l.length : ℕ):ℤ)) :
    upperOn D a b p<ρ := by
  rw [upperOn_eq_of_rep hc hs hl,r81_scale_cast]
  have hM : (0:ℤ)<((c.s*2^c.l.length : ℕ):ℤ) := by
    have := Nat.pos_of_ne_zero hs; positivity
  have hd : (0:ℚ)<den := by exact_mod_cast hden
  have hq : ((2*den*upperZ D (fun j => (chebList c.l).getD j 0):ℤ):ℚ)<
      ((num*((c.s*2^c.l.length : ℕ):ℤ):ℤ):ℚ) := by exact_mod_cast h
  push_cast at hq
  have hM' : (0:ℚ)<(((c.s*2^c.l.length : ℕ):ℤ):ℚ) := by exact_mod_cast hM
  rw [div_lt_iff₀ (by positivity),hρ,div_mul_eq_mul_div,lt_div_iff₀ hd]
  push_cast at hM' ⊢
  linarith

private theorem r81_eval_one : ∀ l : List ℤ,(toPoly l).eval 1=(l.sum:ℚ)
  | [] => by simp [toPoly]
  | a :: l => by
    simp only [toPoly,eval_add,eval_C,eval_mul,eval_X,one_mul,r81_eval_one l,List.sum_cons]
    push_cast; ring

private theorem r81_lt_eval {c : Scaled} {p : ℚ[X]}
    (hc : c.Rep (WholeIntervalPolynomial.centered 0 L p)) (hs : c.s≠0)
    {ρ : ℚ} {num : ℤ} {den : ℕ} (hρ : ρ=num/den) (hden : 0<den)
    (h : num*(c.s:ℤ)<den*c.l.sum) : ρ<p.eval L := by
  have he : (WholeIntervalPolynomial.centered 0 L p).eval 1=p.eval L := by
    simp only [WholeIntervalPolynomial.centered,WholeIntervalPolynomial.affine,eval_comp,
      eval_add,eval_C,eval_mul,eval_X,L]
    norm_num
  have h1 := congrArg (fun q => q.eval 1) hc
  simp only [r81_eval_one,eval_mul,eval_C,he] at h1
  have hs' : (0:ℚ)<c.s := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hd : (0:ℚ)<den := by exact_mod_cast hden
  have hq : (num:ℚ)*(c.s:ℚ)<(den:ℚ)*((c.l.sum:ℤ):ℚ) := by exact_mod_cast h
  have hv : p.eval L=(c.l.sum:ℚ)/c.s := by rw [h1]; field_simp
  rw [hv,lt_div_iff₀ hs',hρ,div_mul_eq_mul_div,div_lt_iff₀ hd]
  linarith

/-! ### Integer representations of the low polynomials -/

private def r81_sk : Scaled := (Scaled.const (2933/5000)).add ((Scaled.const (1239/2500)).mul Scaled.var)
private theorem r81_rk : r81_sk.Rep k := (Scaled.rep_const _).add ((Scaled.rep_const _).mul Scaled.rep_var)
private def r81_sm : Scaled := (Scaled.const (5821/5000)).sub ((Scaled.const (4437/5000)).mul Scaled.var)
private theorem r81_rm : r81_sm.Rep m := (Scaled.rep_const _).sub ((Scaled.rep_const _).mul Scaled.rep_var)
private def r81_sS5 : Scaled := r81_red ((Scaled.var.sub ((Scaled.const (1/6)).mul (Scaled.var.pow 3))).add
  ((Scaled.const (1/120)).mul (Scaled.var.pow 5)))
private theorem r81_rS5 : r81_sS5.Rep PositiveTD.Certificate.S5 :=
  r81_rep_red ((Scaled.rep_var.sub ((Scaled.rep_const _).mul (Scaled.rep_var.pow 3))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 5)))
private def r81_sS9 : Scaled := r81_red ((r81_sS5.sub ((Scaled.const (1/5040)).mul (Scaled.var.pow 7))).add
  ((Scaled.const (1/362880)).mul (Scaled.var.pow 9)))
private theorem r81_rS9 : r81_sS9.Rep S9 :=
  r81_rep_red ((r81_rS5.sub ((Scaled.rep_const _).mul (Scaled.rep_var.pow 7))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 9)))
private def r81_sS11 : Scaled := r81_red (r81_sS9.sub ((Scaled.const (1/39916800)).mul (Scaled.var.pow 11)))
private theorem r81_rS11 : r81_sS11.Rep S11 :=
  r81_rep_red (r81_rS9.sub ((Scaled.rep_const _).mul (Scaled.rep_var.pow 11)))
private def r81_sC4 : Scaled := r81_red (((Scaled.ofNat 1).sub ((Scaled.const (1/2)).mul (Scaled.var.pow 2))).add
  ((Scaled.const (1/24)).mul (Scaled.var.pow 4)))
private theorem r81_rC4 : r81_sC4.Rep PositiveTD.Certificate.C4 :=
  r81_rep_red ((Scaled.rep_one.sub ((Scaled.rep_const _).mul (Scaled.rep_var.pow 2))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 4)))
private def r81_sC10 : Scaled := r81_red (((r81_sC4.sub ((Scaled.const (1/720)).mul (Scaled.var.pow 6))).add
  ((Scaled.const (1/40320)).mul (Scaled.var.pow 8))).sub
  ((Scaled.const (1/3628800)).mul (Scaled.var.pow 10)))
private theorem r81_rC10 : r81_sC10.Rep C10 :=
  r81_rep_red (((r81_rC4.sub ((Scaled.rep_const _).mul (Scaled.rep_var.pow 6))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 8))).sub
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 10)))
private def r81_sJ : Scaled := r81_red (((Scaled.const (1/2)).mul (r81_sC10.sub (Scaled.ofNat 1))).add
  ((Scaled.const (1/2-abar)).mul r81_sS9))
private theorem r81_rJ : r81_sJ.Rep J :=
  r81_rep_red (((Scaled.rep_const _).mul (r81_rC10.sub Scaled.rep_one)).add
    ((Scaled.rep_const _).mul r81_rS9))
private def r81_sAA : Scaled := r81_red ((((((Scaled.const 2).mul r81_sk).add
  (Scaled.const (11/2-cbar))).add (r81_sm.mul (Scaled.const (5/2-cbar)))).add r81_sJ).add
  r81_sC10 |>.sub (Scaled.ofNat 1))
private theorem r81_rAA : r81_sAA.Rep (A .atA) :=
  r81_rep_red (((((((Scaled.rep_const _).mul r81_rk).add (Scaled.rep_const _)).add
    (r81_rm.mul (Scaled.rep_const _))).add r81_rJ).add r81_rC10).sub Scaled.rep_one)
private def r81_sAT : Scaled := r81_red (((((Scaled.const 2).mul r81_sk).add
  (Scaled.const (11/2-cbar))).add (r81_sm.mul (((Scaled.ofNat 1).add
    ((Scaled.const (3/2-cbar)).mul r81_sC10)).add
    ((Scaled.const (1/2+(293/1000)*(1-cbar)-sigmabar)).mul r81_sS9)))).add
  r81_sC10 |>.sub (Scaled.ofNat 1))
private theorem r81_rAT : r81_sAT.Rep (A .atT) :=
  r81_rep_red ((((((Scaled.rep_const _).mul r81_rk).add (Scaled.rep_const _)).add
    (r81_rm.mul ((Scaled.rep_one.add ((Scaled.rep_const _).mul r81_rC10)).add
      ((Scaled.rep_const _).mul r81_rS9)))).add r81_rC10).sub Scaled.rep_one)
private def r81_sP0 : Scaled := r81_red (((Scaled.ofNat 1).add (r81_sk.pow 2)).sub
  (((Scaled.const 2).mul r81_sk).mul r81_sS11))
private theorem r81_rP0 : r81_sP0.Rep (P 0) :=
  r81_rep_red ((Scaled.rep_one.add (r81_rk.pow 2)).sub (((Scaled.rep_const _).mul r81_rk).mul r81_rS11))
private def r81_sP1 : Scaled := r81_red ((Scaled.ofNat 1).add (r81_sk.pow 2))
private theorem r81_rP1 : r81_sP1.Rep (P 1) := r81_rep_red (Scaled.rep_one.add (r81_rk.pow 2))
private def r81_sP2 : Scaled := r81_red ((Scaled.ofNat 1).add (r81_sm.pow 2))
private theorem r81_rP2 : r81_sP2.Rep (P 2) := r81_rep_red (Scaled.rep_one.add (r81_rm.pow 2))

private def r81_sW (cP : Scaled) : Scaled :=
  r81_red ((r81_inv0 cP).mul ((r81_trunc cP).sub (r81_c0 cP)))
private def r81_sMass (cP : Scaled) (r : ℚ) : Scaled :=
  r81_red ((Scaled.const r).mul (r81_trunc (r81_red (((((Scaled.ofNat 1).add
    ((Scaled.const (1/2)).mul (r81_sW cP))).sub ((Scaled.const (1/8)).mul ((r81_sW cP).pow 2))).add
    ((Scaled.const (1/16)).mul ((r81_sW cP).pow 3)))))))
private theorem r81_rep_mass {cP : Scaled} {p : ℚ[X]} (hP : cP.Rep p) (h0 : cP.l.getD 0 0≠0)
    (r : ℚ) : (r81_sMass cP r).Rep (C r*truncate3 (1+C (1/2)*(C (1/p.eval 0)*(truncate3 p-C (p.eval 0)))-
      C (1/8)*(C (1/p.eval 0)*(truncate3 p-C (p.eval 0)))^2+
      C (1/16)*(C (1/p.eval 0)*(truncate3 p-C (p.eval 0)))^3)) := by
  have hW : (r81_sW cP).Rep (C (1/p.eval 0)*(truncate3 p-C (p.eval 0))) :=
    r81_rep_red ((r81_rep_inv0 hP h0).mul ((r81_rep_trunc hP).sub (r81_rep_c0 hP)))
  exact r81_rep_red ((Scaled.rep_const r).mul (r81_rep_trunc (r81_rep_red
    (((Scaled.rep_one.add ((Scaled.rep_const _).mul hW)).sub ((Scaled.rep_const _).mul (hW.pow 2))).add
      ((Scaled.rep_const _).mul (hW.pow 3))))))

private def r81_sM0 : Scaled := r81_sMass r81_sP0 (579676539/500000000)
private def r81_sM1 : Scaled := r81_sMass r81_sP1 (579676539/500000000)
private def r81_sM2 : Scaled := r81_sMass r81_sP2 (1534718749/1000000000)

private theorem r81_rM0 (h0 : r81_sP0.l.getD 0 0≠0) : r81_sM0.Rep (mass 0) :=
  r81_rep_mass r81_rP0 h0 _
private theorem r81_rM1 (h0 : r81_sP1.l.getD 0 0≠0) : r81_sM1.Rep (mass 1) :=
  r81_rep_mass r81_rP1 h0 _
private theorem r81_rM2 (h0 : r81_sP2.l.getD 0 0≠0) : r81_sM2.Rep (mass 2) :=
  r81_rep_mass r81_rP2 h0 _

private def r81_cM0 : Scaled := r81_red (r81_sM0.center 1 12 1 1)
private def r81_cM1 : Scaled := r81_red (r81_sM1.center 1 12 1 1)
private def r81_cM2 : Scaled := r81_red (r81_sM2.center 1 12 1 1)

private theorem r81_mass_facts :
    r81_sP0.l.getD 0 0≠0 ∧ r81_cM0.s≠0 ∧ r81_cM0.l.length≤3+1 ∧
      (11:ℤ)*((r81_cM0.s*2^r81_cM0.l.length : ℕ):ℤ)<
        2*((10:ℕ):ℤ)*lowerZ 3 (fun j => (chebList r81_cM0.l).getD j 0) ∧
    r81_sP1.l.getD 0 0≠0 ∧ r81_cM1.s≠0 ∧ r81_cM1.l.length≤3+1 ∧
      (11:ℤ)*((r81_cM1.s*2^r81_cM1.l.length : ℕ):ℤ)<
        2*((10:ℕ):ℤ)*lowerZ 3 (fun j => (chebList r81_cM1.l).getD j 0) ∧
    r81_sP2.l.getD 0 0≠0 ∧ r81_cM2.s≠0 ∧ r81_cM2.l.length≤3+1 ∧
      (11:ℤ)*((r81_cM2.s*2^r81_cM2.l.length : ℕ):ℤ)<
        2*((10:ℕ):ℤ)*lowerZ 3 (fun j => (chebList r81_cM2.l).getD j 0) := by
  decide +kernel

private def r81_sNum3 (A P0 P1 P2 r0 r1 r2 : Scaled) : Scaled :=
  r81_red ((r81_red ((((Scaled.const 2).mul A).mul r0).mul r1 |>.mul r2)).sub
    ((Scaled.const PositiveTD.Certificate.Rbar).mul
      (r81_red ((r81_red ((r81_red (((P0.add (r0.pow 2)).mul r1).mul r2)).add
        (r81_red (((P1.add (r1.pow 2)).mul r0).mul r2)))).add
        (r81_red (((P2.add (r2.pow 2)).mul r0).mul r1))))))
private theorem r81_rNum3 {A P0 P1 P2 r0 r1 r2 : Scaled} {a p0 p1 p2 q0 q1 q2 : ℚ[X]}
    (hA : A.Rep a) (h0 : P0.Rep p0) (h1 : P1.Rep p1) (h2 : P2.Rep p2)
    (g0 : r0.Rep q0) (g1 : r1.Rep q1) (g2 : r2.Rep q2) :
    (r81_sNum3 A P0 P1 P2 r0 r1 r2).Rep (PositiveTD.Certificate.num3 a p0 p1 p2 q0 q1 q2) :=
  r81_rep_red ((r81_rep_red (((((Scaled.rep_const _).mul hA).mul g0).mul g1).mul g2)).sub
    ((Scaled.rep_const _).mul
      (r81_rep_red ((r81_rep_red ((r81_rep_red (((h0.add (g0.pow 2)).mul g1).mul g2)).add
        (r81_rep_red (((h1.add (g1.pow 2)).mul g0).mul g2)))).add
        (r81_rep_red (((h2.add (g2.pow 2)).mul g0).mul g1))))))

private def r81_sNA : Scaled :=
  r81_sNum3 r81_sAA r81_sP0 r81_sP1 r81_sP2 r81_sM0 r81_sM1 r81_sM2
private def r81_sNT : Scaled :=
  r81_sNum3 r81_sAT r81_sP0 r81_sP1 r81_sP2 r81_sM0 r81_sM1 r81_sM2
private def r81_cNA : Scaled := r81_red (r81_sNA.center 1 12 1 1)
private def r81_cNT : Scaled := r81_red (r81_sNT.center 1 12 1 1)
private def r81_cDT : Scaled := r81_red ((⟨r81_deriv r81_sNT.l,r81_sNT.s⟩ : Scaled).center 1 12 1 1)

private theorem r81_A_facts :
    r81_cNA.s≠0 ∧ r81_cNA.l.length≤19+1 ∧
      (61:ℤ)*((r81_cNA.s*2^r81_cNA.l.length : ℕ):ℤ)<
        2*((50000:ℕ):ℤ)*lowerZ 19 (fun j => (chebList r81_cNA.l).getD j 0) := by
  decide +kernel

private theorem r81_T_facts :
    r81_cDT.s≠0 ∧ r81_cDT.l.length≤20+1 ∧
      2*((500:ℕ):ℤ)*upperZ 20 (fun j => (chebList r81_cDT.l).getD j 0)<
        (-13:ℤ)*((r81_cDT.s*2^r81_cDT.l.length : ℕ):ℤ) ∧
    r81_cNT.s≠0 ∧ (117:ℤ)*(r81_cNT.s:ℤ)<((25000:ℕ):ℤ)*r81_cNT.l.sum := by
  decide +kernel

private theorem r81_rcM0 : r81_cM0.Rep (centered 0 L (mass 0)) :=
  r81_rep_red ((r81_rM0 r81_mass_facts.1).centered 1 12 1 1 (by norm_num) (by norm_num [L])
    (by norm_num [L]))
private theorem r81_rcM1 : r81_cM1.Rep (centered 0 L (mass 1)) :=
  r81_rep_red ((r81_rM1 r81_mass_facts.2.2.2.2.1).centered 1 12 1 1 (by norm_num)
    (by norm_num [L]) (by norm_num [L]))
private theorem r81_rcM2 : r81_cM2.Rep (centered 0 L (mass 2)) :=
  r81_rep_red ((r81_rM2 r81_mass_facts.2.2.2.2.2.2.2.2.1).centered 1 12 1 1 (by norm_num)
    (by norm_num [L]) (by norm_num [L]))

private theorem r81_rNA : r81_sNA.Rep (numerator .atA) :=
  r81_rNum3 r81_rAA r81_rP0 r81_rP1 r81_rP2 (r81_rM0 r81_mass_facts.1)
    (r81_rM1 r81_mass_facts.2.2.2.2.1) (r81_rM2 r81_mass_facts.2.2.2.2.2.2.2.2.1)
private theorem r81_rNT : r81_sNT.Rep (numerator .atT) :=
  r81_rNum3 r81_rAT r81_rP0 r81_rP1 r81_rP2 (r81_rM0 r81_mass_facts.1)
    (r81_rM1 r81_mass_facts.2.2.2.2.1) (r81_rM2 r81_mass_facts.2.2.2.2.2.2.2.2.1)
private theorem r81_rcNA : r81_cNA.Rep (centered 0 L (numerator .atA)) :=
  r81_rep_red (r81_rNA.centered 1 12 1 1 (by norm_num) (by norm_num [L]) (by norm_num [L]))
private theorem r81_rcNT : r81_cNT.Rep (centered 0 L (numerator .atT)) :=
  r81_rep_red (r81_rNT.centered 1 12 1 1 (by norm_num) (by norm_num [L]) (by norm_num [L]))
private theorem r81_rcDT : r81_cDT.Rep (centered 0 L (numerator .atT).derivative) :=
  r81_rep_red ((r81_rep_deriv r81_rNT).centered 1 12 1 1 (by norm_num) (by norm_num [L])
    (by norm_num [L]))

theorem mass_certificate (i : Fin 3) :
    WholeIntervalPolynomial.centered 0 L (mass i)=
      WholeIntervalPolynomial.expansion 3 (WholeIntervalPolynomial.centered 0 L (mass i)) ∧
    (11/10:ℚ)<WholeIntervalPolynomial.lowerOn 3 0 L (mass i) := by
  obtain ⟨-,h0s,h0l,h0r,-,h1s,h1l,h1r,-,h2s,h2l,h2r⟩ := r81_mass_facts
  fin_cases i
  · exact ⟨r81_rcM0.eq_expansion h0s h0l,
      r81_lt_lowerOn r81_rcM0 h0s h0l (num:=11) (den:=10) (by norm_num) (by norm_num) h0r⟩
  · exact ⟨r81_rcM1.eq_expansion h1s h1l,
      r81_lt_lowerOn r81_rcM1 h1s h1l (num:=11) (den:=10) (by norm_num) (by norm_num) h1r⟩
  · exact ⟨r81_rcM2.eq_expansion h2s h2l,
      r81_lt_lowerOn r81_rcM2 h2s h2l (num:=11) (den:=10) (by norm_num) (by norm_num) h2r⟩

theorem A_certificate :
    WholeIntervalPolynomial.centered 0 L (numerator .atA)=
      WholeIntervalPolynomial.expansion 19 (WholeIntervalPolynomial.centered 0 L (numerator .atA)) ∧
    (61/50000:ℚ)<WholeIntervalPolynomial.lowerOn 19 0 L (numerator .atA) := by
  obtain ⟨hs,hl,hr⟩ := r81_A_facts
  exact ⟨r81_rcNA.eq_expansion hs hl,
    r81_lt_lowerOn r81_rcNA hs hl (num:=61) (den:=50000) (by norm_num) (by norm_num) hr⟩

theorem T_certificate :
    WholeIntervalPolynomial.centered 0 L (numerator .atT).derivative=
      WholeIntervalPolynomial.expansion 20
        (WholeIntervalPolynomial.centered 0 L (numerator .atT).derivative) ∧
    WholeIntervalPolynomial.upperOn 20 0 L (numerator .atT).derivative< -(13/500:ℚ) ∧
    (117/25000:ℚ)<(numerator .atT).eval L := by
  obtain ⟨hs,hl,hr,hs',hv⟩ := r81_T_facts
  exact ⟨r81_rcDT.eq_expansion hs hl,
    r81_upperOn_lt r81_rcDT hs hl (num:=-13) (den:=500) (by norm_num) (by norm_num) hr,
    r81_lt_eval r81_rcNT hs' (num:=117) (den:=25000) (by norm_num) (by norm_num) hv⟩

end r81Cert

private theorem r81_icc_L {t : ℝ} (ht : t∈Icc 0 (1/6:ℝ)) :
    t∈Icc ((0:ℚ):ℝ) ((L:ℚ):ℝ) := by
  simp only [L]; push_cast; exact ht

theorem mass_positive (i : Fin 3) {t : ℝ} (ht : t∈Icc 0 (1/6:ℝ)) :
    0<aeval t (mass i) := by
  have hh := WholeIntervalPolynomial.positive_on_interval
    (by norm_num : (0:ℚ)<L) (mass_certificate i).1 (mass_certificate i).2 (r81_icc_L ht)
  exact lt_trans (by norm_num) hh

theorem A_positive {t : ℝ} (ht : t∈Icc 0 (1/6:ℝ)) :
    (1/1000:ℝ)<aeval t (numerator .atA) := by
  have hh := WholeIntervalPolynomial.positive_on_interval
    (by norm_num : (0:ℚ)<L) A_certificate.1 A_certificate.2 (r81_icc_L ht)
  exact lt_trans (by norm_num) hh

theorem T_antitone : AntitoneOn (fun t : ℝ => aeval t (numerator .atT))
    (Icc (0:ℝ) (1/6)) := by
  apply antiOn_of_hasDeriv_nonpos
    (fun t _ => (CenteredMonomialBounds.aeval_hasDerivAt (numerator .atT) t).continuousAt.continuousWithinAt)
    (fun t _ => CenteredMonomialBounds.aeval_hasDerivAt (numerator .atT) t)
  intro t ht
  have hh := (WholeIntervalPolynomial.interval_bounds
    (by norm_num : (0:ℚ)<L) T_certificate.1 (r81_icc_L (Ioo_subset_Icc_self ht))).2
  have hr : (WholeIntervalPolynomial.upperOn 20 0 L (numerator .atT).derivative:ℝ)< -(13/500:ℝ) := by
    rw [show -(13/500:ℝ)=((-(13/500):ℚ):ℝ) by norm_num]; exact Rat.cast_lt.mpr T_certificate.2.1
  linarith

theorem T_positive {t : ℝ} (ht : t∈Icc 0 (1/6:ℝ)) :
    (1/1000:ℝ)<aeval t (numerator .atT) := by
  have hh := T_antitone ht (show (1/6:ℝ)∈Icc 0 (1/6) by norm_num) ht.2
  have he : (117/25000:ℝ)<aeval (1/6:ℝ) (numerator .atT) := by
    have hc : (117/25000:ℝ)<(((numerator .atT).eval L:ℚ):ℝ) := by
      rw [show (117/25000:ℝ)=((117/25000:ℚ):ℝ) by norm_num]; exact Rat.cast_lt.mpr T_certificate.2.2
    have h6 : ((L:ℚ):ℝ)=1/6 := by norm_num [L]
    rwa [←NonnegativeTotals.Certificate.eval_rat,h6] at hc
  dsimp only at hh
  linarith

theorem numerator_positive (ep : Endpoint) {t : ℝ} (ht : t∈Icc 0 (1/6:ℝ)) :
    (1/1000:ℝ)<aeval t (numerator ep) := by
  cases ep
  · exact A_positive ht
  · exact T_positive ht

end SquaresInCircles.Eight.GlobalGA.PositiveBT3.LowCertificate

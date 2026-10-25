module

public import SquaresInCircles.Eight.TableFree.GlobalGANonpositiveTPairedPolynomialData
public import SquaresInCircles.Eight.TableFree.BivariateCertificates

/-! # `whole_certificate` on the low trapezoid, by one exact packed `XM` check per kind -/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NonpositiveT.Paired.Certificate
open TensorWholeIntervalPolynomial TwoVariablePolynomial
open CertificateRestrictions

/-! The numerators of the kinds `equal`, `positive i` and `diagonal` live on the low trapezoid
`0 ≤ x ≤ 73/300`, `0 ≤ E ≤ 1/6 + x`. Each is an exact packed model
(`BivariateCertificate.XM`, boxes of `23 × 23` digits of `1280` bits), transformed to the square
and checked once by `decide +kernel` (`XM.lowerCheck`, degree `20` or `21`). The models of `k`,
`l`, `p`, `q`, `P`, `rho`, the masses and the transform are those of the mass certificate
(`GlobalGANonpositiveTPairedMassCertificate`); `A` and the numerator are modelled here. -/

section PWNumerators
open PackedModels BivariateCertificate

/-- The packing: boxes of `23 × 23` digits of `1280` bits. -/
private def pw_cfg : Config := ⟨0, 11, 1280⟩

/-! ### The models of the mass certificate -/

/-- Whether a kind lies on the high trapezoid `M ≤ δ ≤ h`. -/
private def pw_neg : Kind → Bool
  | .negative _ => true
  | _ => false

/-- Whether the mass `j` of a kind carries the extra Taylor term. -/
private def pw_sp : Kind → Fin 3 → Bool
  | .positive i, j => decide (i = j)
  | .negative i, j => decide (i = j)
  | _, _ => false

private def pw_kM (cf : Config) : XM :=
  XM.add cf (XM.ofInt cf 3 4) (XM.mul cf (XM.ofInt cf 7 50) (XM.varY cf))
private def pw_lM (cf : Config) : XM :=
  XM.add cf (XM.ofInt cf 19 20) (XM.mul cf (XM.ofInt cf 9 20) (XM.varY cf))

private theorem pw_rep_kM (cf : Config) : (pw_kM cf).Rep cf k :=
  XM.rep_add (XM.rep_lit cf (by norm_num))
    (XM.rep_mul (XM.rep_lit cf (by norm_num)) (XM.rep_Y cf))
private theorem pw_rep_lM (cf : Config) : (pw_lM cf).Rep cf l :=
  XM.rep_add (XM.rep_lit cf (by norm_num))
    (XM.rep_mul (XM.rep_lit cf (by norm_num)) (XM.rep_Y cf))

private def pw_pM (cf : Config) : Fin 3 → XM := ![pw_kM cf, pw_kM cf, pw_lM cf]
private def pw_qM (cf : Config) : Fin 3 → XM := ![XM.ofInt cf 1 1, pw_lM cf, XM.ofInt cf 27 20]

private theorem pw_rep_pM (cf : Config) (j : Fin 3) : (pw_pM cf j).Rep cf (p j) :=
  XM.rep_vec3 (pw_rep_kM cf) (pw_rep_kM cf) (pw_rep_lM cf) j
private theorem pw_rep_qM (cf : Config) (j : Fin 3) : (pw_qM cf j).Rep cf (q j) :=
  XM.rep_vec3 (XM.rep_one cf) (pw_rep_lM cf) (XM.rep_lit cf (by norm_num [c])) j

private def pw_P0M (cf : Config) (j : Fin 3) : XM :=
  XM.add cf (XM.pow cf (pw_pM cf j) 2) (XM.pow cf (pw_qM cf j) 2)
private theorem pw_rep_P0M (cf : Config) (j : Fin 3) : (pw_P0M cf j).Rep cf (P0 j) :=
  XM.rep_add (XM.rep_pow (pw_rep_pM cf j) 2) (XM.rep_pow (pw_rep_qM cf j) 2)

/-- `2 p_j q_j`. -/
private def pw_pqM (cf : Config) (j : Fin 3) : XM :=
  XM.mul cf (XM.mul cf (XM.ofInt cf 2 1) (pw_pM cf j)) (pw_qM cf j)
private theorem pw_rep_pqM (cf : Config) (j : Fin 3) :
    (pw_pqM cf j).Rep cf (scalar 2*p j*q j) :=
  XM.rep_mul (XM.rep_mul (XM.rep_lit cf (by norm_num)) (pw_rep_pM cf j)) (pw_rep_qM cf j)

/-- `P f j` on the low (`neg = false`) or high trapezoid, with (`sp`) or without the extra
term; `M - δ = 73/300 - x` on the low trapezoid and `δ - M = x` on the high one. -/
private def pw_PM (cf : Config) : Bool → Bool → Fin 3 → XM
  | false, true, j => XM.add cf (pw_P0M cf j) (XM.mul cf (pw_pqM cf j)
      (XM.liftM cf (XM.sub cf (XM.ofInt cf 73 300) (XM.varX cf)) XM.S9L))
  | true, true, j => XM.sub cf (pw_P0M cf j)
      (XM.mul cf (pw_pqM cf j) (XM.liftM cf (XM.varX cf) XM.S11L))
  | _, false, j => pw_P0M cf j

private theorem pw_rep_PM (cf : Config) (f : Kind) (j : Fin 3) :
    (pw_PM cf (pw_neg f) (pw_sp f j) j).Rep cf (P f j) := by
  cases f with
  | equal => exact pw_rep_P0M cf j
  | diagonal => exact pw_rep_P0M cf j
  | positive i =>
    have hu : (XM.sub cf (XM.ofInt cf 73 300) (XM.varX cf)).Rep cf
        (scalar M-delta (.positive i)) := by
      have e : scalar M-delta (.positive i)=scalar (73/300)-X := by
        rw [show (73/300:ℚ)=M-L by norm_num, BivariateCertificate.scalar_sub]
        show scalar M-(scalar L+X)=_
        ring
      rw [e]
      exact XM.rep_sub (XM.rep_lit cf (by norm_num)) (XM.rep_X cf)
    by_cases hij : i=j
    · have hsp : pw_sp (.positive i) j=true := by simp [pw_sp,hij]
      rw [hsp]
      show (pw_PM cf false true j).Rep cf (P0 j+if i=j then _ else 0)
      rw [ite_eq_left hij]
      exact XM.rep_add (pw_rep_P0M cf j) (XM.rep_mul (pw_rep_pqM cf j) (XM.rep_liftS9 hu))
    · have hsp : pw_sp (.positive i) j=false := by simp [pw_sp,hij]
      rw [hsp]
      show (pw_PM cf false false j).Rep cf (P0 j+if i=j then _ else 0)
      rw [ite_eq_right hij,add_zero]
      exact pw_rep_P0M cf j
  | negative i =>
    have hu : (XM.varX cf).Rep cf (delta (.negative i)-scalar M) := by
      have e : delta (.negative i)-scalar M=X := by
        show scalar M+X-scalar M=X
        ring
      rw [e]
      exact XM.rep_X cf
    by_cases hij : i=j
    · have hsp : pw_sp (.negative i) j=true := by simp [pw_sp,hij]
      rw [hsp]
      show (pw_PM cf true true j).Rep cf (P0 j-if i=j then _ else 0)
      rw [ite_eq_left hij]
      exact XM.rep_sub (pw_rep_P0M cf j) (XM.rep_mul (pw_rep_pqM cf j) (XM.rep_liftS11 hu))
    · have hsp : pw_sp (.negative i) j=false := by simp [pw_sp,hij]
      rw [hsp]
      show (pw_PM cf true false j).Rep cf (P0 j-if i=j then _ else 0)
      rw [ite_eq_right hij,sub_zero]
      exact pw_rep_P0M cf j

/-- `rho f j` as a numerator and a denominator. -/
private def pw_rhoP : Bool → Bool → Fin 3 → ℤ × ℕ
  | false, true, j =>
    ![(693525169,500000000),(1344744663,1000000000),(1828389667,1000000000)] j
  | _, _, j => ![(5,4),(302592961,250000000),(825378701,500000000)] j

private theorem pw_rho_eq (f : Kind) (j : Fin 3) :
    rho f j=((pw_rhoP (pw_neg f) (pw_sp f j) j).1:ℚ)/
      ((pw_rhoP (pw_neg f) (pw_sp f j) j).2:ℚ) := by
  cases f <;> (try rename_i i; fin_cases i) <;> fin_cases j <;>
    norm_num [rho,rhoBase,rhoPositive,pw_rhoP,pw_neg,pw_sp]

/-- `mass f j`, reduced. -/
private def pw_massM (cf : Config) (neg sp : Bool) (j : Fin 3) : XM :=
  XM.reduce cf (XM.cubicMassRM cf (pw_rhoP neg sp j).1 (pw_rhoP neg sp j).2
    (XM.reduce cf (pw_PM cf neg sp j)))

private theorem pw_rep_massM (cf : Config) (f : Kind) (j : Fin 3) :
    (pw_massM cf (pw_neg f) (pw_sp f j) j).Rep cf (mass f j) :=
  XM.rep_reduce (XM.rep_cubicMassRM (XM.rep_reduce (pw_rep_PM cf f j)) (pw_rho_eq f j))

/-- `transform f`, reduced: the trapezoid `0 ≤ x ≤ 73/300`, `0 ≤ E ≤ 1/6 + x` or
`0 ≤ x ≤ 29/100`, `0 ≤ E ≤ 41/100 + x`. -/
private def pw_tM (cf : Config) : Bool → XM → XM
  | false, m => XM.reduce cf (XM.fanM cf m 1 6 1 1 73 300)
  | true, m => XM.reduce cf (XM.fanM cf m 41 100 1 1 29 100)

private theorem pw_rep_tM {cf : Config} {m : XM} {pp : Bivar} (hm : m.Rep cf pp) (f : Kind) :
    (pw_tM cf (pw_neg f) m).Rep cf (transform f pp) := by
  cases f <;> exact XM.rep_reduce (XM.rep_trapezoidM hm (by norm_num [origin])
    (by norm_num [length]) (by norm_num))

/-! ### The models of the numerators -/

/-- `δ = 1/6 + x` on the low trapezoid. -/
private def pw_dM (cf : Config) : XM := XM.add cf (XM.ofInt cf 1 6) (XM.varX cf)

private theorem pw_rep_dM (cf : Config) (f : Kind) (hf : Whole f) :
    (pw_dM cf).Rep cf (delta f) := by
  have ho : origin f=((1:ℤ):ℚ)/((6:ℕ):ℚ) := by
    cases f <;> first | exact hf.elim | norm_num [origin]
  exact XM.rep_add (XM.rep_lit cf ho) (XM.rep_X cf)

/-- `M - δ = 73/300 - x` on the low trapezoid. -/
private def pw_uM (cf : Config) : XM := XM.sub cf (XM.ofInt cf 73 300) (XM.varX cf)

private theorem pw_rep_uM (cf : Config) (f : Kind) (hf : Whole f) :
    (pw_uM cf).Rep cf (scalar M-delta f) := by
  have ho : origin f=L := by
    cases f <;> first | exact hf.elim | rfl
  have e : scalar M-delta f=scalar (73/300)-X := by
    rw [show (73/300:ℚ)=M-L by norm_num, BivariateCertificate.scalar_sub]
    show scalar M-(scalar (origin f)+X)=_
    rw [ho]
    ring
  rw [e]
  exact XM.rep_sub (XM.rep_lit cf (by norm_num)) (XM.rep_X cf)

/-- `J u`; the constant `1/2 - abar` is `-114321959/125000000`. -/
private def pw_JM (cf : Config) (u : XM) : XM :=
  XM.sub cf (XM.add cf (XM.mul cf (XM.ofInt cf 1 2) (XM.sub cf (XM.liftM cf u XM.C10L)
      (XM.ofInt cf 1 1))) (XM.mul cf (XM.ofInt cf (-114321959) 125000000) (XM.liftM cf u XM.S9L)))
    (XM.mul cf (XM.ofInt cf 29 1000) (XM.pow cf u 4))

private theorem pw_rep_JM {cf : Config} {u : XM} {g : Bivar} (hu : u.Rep cf g) :
    (pw_JM cf u).Rep cf (J g) :=
  XM.rep_sub (XM.rep_add (XM.rep_mul (XM.rep_lit cf (by norm_num)) (XM.rep_sub (XM.rep_liftC10 hu)
      (XM.rep_one cf))) (XM.rep_mul (XM.rep_lit cf
        (by norm_num [NonnegativeTotals.NegativeTD.Certificate.abar])) (XM.rep_liftS9 hu)))
    (XM.rep_mul (XM.rep_lit cf (by norm_num)) (XM.rep_pow hu 4))

/-- `gain u`; the constant `c kappa` is `22869/16000`. -/
private def pw_gainM (cf : Config) (u : XM) : XM :=
  XM.mul cf (XM.ofInt cf 22869 16000)
    (XM.sub cf (XM.add cf (XM.liftM cf u XM.C10L) (XM.liftM cf u XM.S11L)) (XM.ofInt cf 1 1))

private theorem pw_rep_gainM {cf : Config} {u : XM} {g : Bivar} (hu : u.Rep cf g) :
    (pw_gainM cf u).Rep cf (gain g) :=
  XM.rep_mul (XM.rep_lit cf (by norm_num [c,kappa]))
    (XM.rep_sub (XM.rep_add (XM.rep_liftC10 hu) (XM.rep_liftS11 hu)) (XM.rep_one cf))

/-- `A0 f` on the low trapezoid; the constant `(5/2)c+5/2-(1+c)cbar` is
`37618469449/10000000000`. -/
private def pw_A0M (cf : Config) : XM :=
  XM.add cf (XM.add cf (XM.add cf (XM.add cf (XM.mul cf (XM.ofInt cf 2 1) (pw_kM cf))
    (XM.mul cf (XM.ofInt cf 3 1) (pw_lM cf))) (XM.ofInt cf 37618469449 10000000000))
    (XM.mul cf (pw_lM cf) (pw_JM cf (XM.sub cf (pw_dM cf) (XM.varY cf))))) (pw_JM cf (XM.varY cf))

private theorem pw_rep_A0M (cf : Config) (f : Kind) (hf : Whole f) : (pw_A0M cf).Rep cf (A0 f) :=
  XM.rep_add (XM.rep_add (XM.rep_add (XM.rep_add
    (XM.rep_mul (XM.rep_lit cf (by norm_num)) (pw_rep_kM cf))
    (XM.rep_mul (XM.rep_lit cf (by norm_num)) (pw_rep_lM cf)))
    (XM.rep_lit cf (by norm_num [c,NonnegativeTotals.NegativeTD.Certificate.cbar])))
    (XM.rep_mul (pw_rep_lM cf) (pw_rep_JM (XM.rep_sub (pw_rep_dM cf f hf) (XM.rep_Y cf)))))
    (pw_rep_JM (XM.rep_Y cf))

/-- `A f` for the whole kinds, reduced; the constant `cbar - 1/2` is `199607033/500000000`.
The negative kinds are not whole, and their entry is a placeholder. -/
private def pw_AM (cf : Config) : Kind → XM
  | .equal => XM.reduce cf (XM.add cf (pw_A0M cf) (pw_gainM cf (pw_dM cf)))
  | .positive i => XM.reduce cf (XM.add cf (XM.add cf (pw_A0M cf)
      (pw_gainM cf (XM.ofInt cf 41 100)))
      (XM.mul cf (pw_pM cf i) (XM.sub cf (XM.add cf (XM.liftM cf (pw_uM cf) XM.C10L)
        (XM.liftM cf (pw_uM cf) XM.S11L)) (XM.ofInt cf 1 1))))
  | .diagonal => XM.reduce cf (XM.sub cf (XM.add cf (pw_A0M cf) (pw_gainM cf (XM.ofInt cf 41 100)))
      (XM.mul cf (XM.ofInt cf 199607033 500000000) (pw_uM cf)))
  | .negative _ => XM.ofInt cf 0 1

private theorem pw_rep_AM (cf : Config) (f : Kind) (hf : Whole f) : (pw_AM cf f).Rep cf (A f) := by
  cases f with
  | equal =>
    exact XM.rep_reduce (XM.rep_add (pw_rep_A0M cf _ hf) (pw_rep_gainM (pw_rep_dM cf _ hf)))
  | positive i =>
    exact XM.rep_reduce (XM.rep_add (XM.rep_add (pw_rep_A0M cf _ hf)
      (pw_rep_gainM (XM.rep_lit cf (by norm_num))))
      (XM.rep_mul (pw_rep_pM cf i) (XM.rep_sub (XM.rep_add (XM.rep_liftC10 (pw_rep_uM cf _ hf))
        (XM.rep_liftS11 (pw_rep_uM cf _ hf))) (XM.rep_one cf))))
  | diagonal =>
    exact XM.rep_reduce (XM.rep_sub (XM.rep_add (pw_rep_A0M cf _ hf)
      (pw_rep_gainM (XM.rep_lit cf (by norm_num))))
      (XM.rep_mul (XM.rep_lit cf (by norm_num [NonnegativeTotals.NegativeTD.Certificate.cbar]))
        (pw_rep_uM cf _ hf)))
  | negative i => exact hf.elim

/-- `numerator f`, reduced. -/
private def pw_numM (cf : Config) (f : Kind) : XM :=
  let r := fun j => pw_massM cf (pw_neg f) (pw_sp f j) j
  let P' := fun j => XM.reduce cf (pw_PM cf (pw_neg f) (pw_sp f j) j)
  XM.reduce cf (XM.sub cf (XM.mul cf (XM.mul cf (XM.mul cf (XM.mul cf (XM.ofInt cf 2 1)
      (pw_AM cf f)) (r 0)) (r 1)) (r 2))
    (XM.mul cf (XM.ofInt cf 494696877 250000000) (XM.add cf (XM.add cf
      (XM.mul cf (XM.mul cf (XM.add cf (P' 0) (XM.pow cf (r 0) 2)) (r 1)) (r 2))
      (XM.mul cf (XM.mul cf (XM.add cf (P' 1) (XM.pow cf (r 1) 2)) (r 0)) (r 2)))
      (XM.mul cf (XM.mul cf (XM.add cf (P' 2) (XM.pow cf (r 2) 2)) (r 0)) (r 1)))))

private theorem pw_rep_numM (cf : Config) (f : Kind) (hf : Whole f) :
    (pw_numM cf f).Rep cf (numerator f) := by
  have hr (j : Fin 3) := pw_rep_massM cf f j
  have hP (j : Fin 3) := XM.rep_reduce (pw_rep_PM cf f j)
  exact XM.rep_reduce (XM.rep_sub (XM.rep_mul (XM.rep_mul (XM.rep_mul (XM.rep_mul
      (XM.rep_lit cf (by norm_num)) (pw_rep_AM cf f hf)) (hr 0)) (hr 1)) (hr 2))
    (XM.rep_mul (XM.rep_lit cf (by norm_num [NonnegativeTotals.NegativeTD.Certificate.Rbar]))
      (XM.rep_add (XM.rep_add
      (XM.rep_mul (XM.rep_mul (XM.rep_add (hP 0) (XM.rep_pow (hr 0) 2)) (hr 1)) (hr 2))
      (XM.rep_mul (XM.rep_mul (XM.rep_add (hP 1) (XM.rep_pow (hr 1) 2)) (hr 0)) (hr 2)))
      (XM.rep_mul (XM.rep_mul (XM.rep_add (hP 2) (XM.rep_pow (hr 2) 2)) (hr 0)) (hr 1)))))

/-! ### The checks -/

private theorem pw_check_equal :
    XM.lowerCheck pw_cfg (pw_tM pw_cfg false (pw_numM pw_cfg .equal)) 20 183 1000=true := by
  decide +kernel

private theorem pw_check_positive0 :
    XM.lowerCheck pw_cfg (pw_tM pw_cfg false (pw_numM pw_cfg (.positive 0))) 21 139 1000=true := by
  decide +kernel

private theorem pw_check_positive1 :
    XM.lowerCheck pw_cfg (pw_tM pw_cfg false (pw_numM pw_cfg (.positive 1))) 21 17 100=true := by
  decide +kernel

private theorem pw_check_positive2 :
    XM.lowerCheck pw_cfg (pw_tM pw_cfg false (pw_numM pw_cfg (.positive 2))) 21 157 1000=true := by
  decide +kernel

private theorem pw_check_diagonal :
    XM.lowerCheck pw_cfg (pw_tM pw_cfg false (pw_numM pw_cfg .diagonal)) 20 141 1000=true := by
  decide +kernel

end PWNumerators

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
theorem whole_certificate (f : Kind) (hf : Whole f) :
    transform f (numerator f)=expansion (degree f) (transform f (numerator f)) ∧
      wholeReserve f<lowerOn f (degree f) (numerator f) := by
  open PackedModels BivariateCertificate in
  rcases f with _ | i | _ | i
  · exact XM.lower_certificate (pw_rep_tM (pw_rep_numM pw_cfg .equal hf) .equal) pw_check_equal
      (by norm_num [wholeReserve])
  · fin_cases i
    · exact XM.lower_certificate (pw_rep_tM (pw_rep_numM pw_cfg (.positive 0) hf) (.positive 0))
        pw_check_positive0 (by norm_num [wholeReserve])
    · exact XM.lower_certificate (pw_rep_tM (pw_rep_numM pw_cfg (.positive 1) hf) (.positive 1))
        pw_check_positive1 (by norm_num [wholeReserve])
    · exact XM.lower_certificate (pw_rep_tM (pw_rep_numM pw_cfg (.positive 2) hf) (.positive 2))
        pw_check_positive2 (by norm_num [wholeReserve])
  · exact XM.lower_certificate (pw_rep_tM (pw_rep_numM pw_cfg .diagonal hf) .diagonal)
      pw_check_diagonal (by norm_num [wholeReserve])
  · exact hf.elim

end SquaresInCircles.Eight.TableFree.GlobalGA.NonpositiveT.Paired.Certificate

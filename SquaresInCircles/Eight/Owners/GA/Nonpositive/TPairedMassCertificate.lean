module

public import SquaresInCircles.Eight.Owners.GA.Nonpositive.TPairedPolynomialData
public import SquaresInCircles.Eight.Arithmetic.BivariateCertificates

/-! # Eight squares: `mass_certificate`: the paired nonpositive-T cubic masses exceed one, by exact `XM` checks -/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.GlobalGA.NonpositiveT.Paired.Certificate
open TensorWholeIntervalPolynomial TwoVariablePolynomial
open CertificateRestrictions

/-! The mass `mass f j` depends on `f` only through its trapezoid (`pm_neg f`) and the presence
of the extra Taylor term (`pm_sp f j`), so the 24 masses are twelve exact packed models, each
checked once by `decide +kernel` (`BivariateCertificate.XM.lowerCheck`, degree `3`, reserve `1`)
in boxes of `13 × 13` digits of `480` bits. -/

section PMMasses
open PackedModels BivariateCertificate

/-- The packing: boxes of `13 × 13` digits of `480` bits. -/
private def pm_cfg : Config := ⟨0, 6, 480⟩

/-- Whether a kind lies on the high trapezoid `M ≤ δ ≤ h`. -/
private def pm_neg : Kind → Bool
  | .negative _ => true
  | _ => false

/-- Whether the mass `j` of a kind carries the extra Taylor term. -/
private def pm_sp : Kind → Fin 3 → Bool
  | .positive i, j => decide (i = j)
  | .negative i, j => decide (i = j)
  | _, _ => false

private def pm_kM (cf : Config) : XM :=
  XM.add cf (XM.ofInt cf 3 4) (XM.mul cf (XM.ofInt cf 7 50) (XM.varY cf))
private def pm_lM (cf : Config) : XM :=
  XM.add cf (XM.ofInt cf 19 20) (XM.mul cf (XM.ofInt cf 9 20) (XM.varY cf))

private theorem pm_rep_kM (cf : Config) : (pm_kM cf).Rep cf k :=
  XM.rep_add (XM.rep_lit cf (by norm_num))
    (XM.rep_mul (XM.rep_lit cf (by norm_num)) (XM.rep_Y cf))
private theorem pm_rep_lM (cf : Config) : (pm_lM cf).Rep cf l :=
  XM.rep_add (XM.rep_lit cf (by norm_num))
    (XM.rep_mul (XM.rep_lit cf (by norm_num)) (XM.rep_Y cf))

private def pm_pM (cf : Config) : Fin 3 → XM := ![pm_kM cf, pm_kM cf, pm_lM cf]
private def pm_qM (cf : Config) : Fin 3 → XM := ![XM.ofInt cf 1 1, pm_lM cf, XM.ofInt cf 27 20]

private theorem pm_rep_pM (cf : Config) (j : Fin 3) : (pm_pM cf j).Rep cf (p j) :=
  XM.rep_vec3 (pm_rep_kM cf) (pm_rep_kM cf) (pm_rep_lM cf) j
private theorem pm_rep_qM (cf : Config) (j : Fin 3) : (pm_qM cf j).Rep cf (q j) :=
  XM.rep_vec3 (XM.rep_one cf) (pm_rep_lM cf) (XM.rep_lit cf (by norm_num [c])) j

private def pm_P0M (cf : Config) (j : Fin 3) : XM :=
  XM.add cf (XM.pow cf (pm_pM cf j) 2) (XM.pow cf (pm_qM cf j) 2)
private theorem pm_rep_P0M (cf : Config) (j : Fin 3) : (pm_P0M cf j).Rep cf (P0 j) :=
  XM.rep_add (XM.rep_pow (pm_rep_pM cf j) 2) (XM.rep_pow (pm_rep_qM cf j) 2)

/-- `2 p_j q_j`. -/
private def pm_pqM (cf : Config) (j : Fin 3) : XM :=
  XM.mul cf (XM.mul cf (XM.ofInt cf 2 1) (pm_pM cf j)) (pm_qM cf j)
private theorem pm_rep_pqM (cf : Config) (j : Fin 3) :
    (pm_pqM cf j).Rep cf (scalar 2*p j*q j) :=
  XM.rep_mul (XM.rep_mul (XM.rep_lit cf (by norm_num)) (pm_rep_pM cf j)) (pm_rep_qM cf j)

/-- `P f j` on the low (`neg = false`) or high trapezoid, with (`sp`) or without the extra
term; `M - δ = 73/300 - x` on the low trapezoid and `δ - M = x` on the high one. -/
private def pm_PM (cf : Config) : Bool → Bool → Fin 3 → XM
  | false, true, j => XM.add cf (pm_P0M cf j) (XM.mul cf (pm_pqM cf j)
      (XM.liftM cf (XM.sub cf (XM.ofInt cf 73 300) (XM.varX cf)) XM.S9L))
  | true, true, j => XM.sub cf (pm_P0M cf j)
      (XM.mul cf (pm_pqM cf j) (XM.liftM cf (XM.varX cf) XM.S11L))
  | _, false, j => pm_P0M cf j

private theorem pm_rep_PM (cf : Config) (f : Kind) (j : Fin 3) :
    (pm_PM cf (pm_neg f) (pm_sp f j) j).Rep cf (P f j) := by
  cases f with
  | equal => exact pm_rep_P0M cf j
  | diagonal => exact pm_rep_P0M cf j
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
    · have hsp : pm_sp (.positive i) j=true := by simp [pm_sp,hij]
      rw [hsp]
      show (pm_PM cf false true j).Rep cf (P0 j+if i=j then _ else 0)
      rw [ite_eq_left hij]
      exact XM.rep_add (pm_rep_P0M cf j) (XM.rep_mul (pm_rep_pqM cf j) (XM.rep_liftS9 hu))
    · have hsp : pm_sp (.positive i) j=false := by simp [pm_sp,hij]
      rw [hsp]
      show (pm_PM cf false false j).Rep cf (P0 j+if i=j then _ else 0)
      rw [ite_eq_right hij,add_zero]
      exact pm_rep_P0M cf j
  | negative i =>
    have hu : (XM.varX cf).Rep cf (delta (.negative i)-scalar M) := by
      have e : delta (.negative i)-scalar M=X := by
        show scalar M+X-scalar M=X
        ring
      rw [e]
      exact XM.rep_X cf
    by_cases hij : i=j
    · have hsp : pm_sp (.negative i) j=true := by simp [pm_sp,hij]
      rw [hsp]
      show (pm_PM cf true true j).Rep cf (P0 j-if i=j then _ else 0)
      rw [ite_eq_left hij]
      exact XM.rep_sub (pm_rep_P0M cf j) (XM.rep_mul (pm_rep_pqM cf j) (XM.rep_liftS11 hu))
    · have hsp : pm_sp (.negative i) j=false := by simp [pm_sp,hij]
      rw [hsp]
      show (pm_PM cf true false j).Rep cf (P0 j-if i=j then _ else 0)
      rw [ite_eq_right hij,sub_zero]
      exact pm_rep_P0M cf j

/-- `rho f j` as a numerator and a denominator. -/
private def pm_rhoP : Bool → Bool → Fin 3 → ℤ × ℕ
  | false, true, j =>
    ![(693525169,500000000),(1344744663,1000000000),(1828389667,1000000000)] j
  | _, _, j => ![(5,4),(302592961,250000000),(825378701,500000000)] j

private theorem pm_rho_eq (f : Kind) (j : Fin 3) :
    rho f j=((pm_rhoP (pm_neg f) (pm_sp f j) j).1:ℚ)/
      ((pm_rhoP (pm_neg f) (pm_sp f j) j).2:ℚ) := by
  cases f <;> (try rename_i i; fin_cases i) <;> fin_cases j <;>
    norm_num [rho,rhoBase,rhoPositive,pm_rhoP,pm_neg,pm_sp]

/-- `mass f j`, reduced. -/
private def pm_massM (cf : Config) (neg sp : Bool) (j : Fin 3) : XM :=
  XM.reduce cf (XM.cubicMassRM cf (pm_rhoP neg sp j).1 (pm_rhoP neg sp j).2
    (XM.reduce cf (pm_PM cf neg sp j)))

private theorem pm_rep_massM (cf : Config) (f : Kind) (j : Fin 3) :
    (pm_massM cf (pm_neg f) (pm_sp f j) j).Rep cf (mass f j) :=
  XM.rep_reduce (XM.rep_cubicMassRM (XM.rep_reduce (pm_rep_PM cf f j)) (pm_rho_eq f j))

/-- `transform f`, reduced: the trapezoid `0 ≤ x ≤ 73/300`, `0 ≤ E ≤ 1/6 + x` or
`0 ≤ x ≤ 29/100`, `0 ≤ E ≤ 41/100 + x`. -/
private def pm_tM (cf : Config) : Bool → XM → XM
  | false, m => XM.reduce cf (XM.fanM cf m 1 6 1 1 73 300)
  | true, m => XM.reduce cf (XM.fanM cf m 41 100 1 1 29 100)

private theorem pm_rep_tM {cf : Config} {m : XM} {pp : Bivar} (hm : m.Rep cf pp) (f : Kind) :
    (pm_tM cf (pm_neg f) m).Rep cf (transform f pp) := by
  cases f <;> exact XM.rep_reduce (XM.rep_trapezoidM hm (by norm_num [origin])
    (by norm_num [length]) (by norm_num))

private theorem pm_check_ff : ∀ j : Fin 3,
    XM.lowerCheck pm_cfg (pm_tM pm_cfg false (pm_massM pm_cfg false false j)) 3 1 1=true := by
  decide +kernel

private theorem pm_check_ft : ∀ j : Fin 3,
    XM.lowerCheck pm_cfg (pm_tM pm_cfg false (pm_massM pm_cfg false true j)) 3 1 1=true := by
  decide +kernel

private theorem pm_check_tf : ∀ j : Fin 3,
    XM.lowerCheck pm_cfg (pm_tM pm_cfg true (pm_massM pm_cfg true false j)) 3 1 1=true := by
  decide +kernel

private theorem pm_check_tt : ∀ j : Fin 3,
    XM.lowerCheck pm_cfg (pm_tM pm_cfg true (pm_massM pm_cfg true true j)) 3 1 1=true := by
  decide +kernel

private theorem pm_check (neg sp : Bool) (j : Fin 3) :
    XM.lowerCheck pm_cfg (pm_tM pm_cfg neg (pm_massM pm_cfg neg sp j)) 3 1 1=true := by
  cases neg <;> cases sp
  exacts [pm_check_ff j,pm_check_ft j,pm_check_tf j,pm_check_tt j]

end PMMasses

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
theorem mass_certificate (f : Kind) (j : Fin 3) :
    transform f (mass f j)=expansion 3 (transform f (mass f j)) ∧
      (1:ℚ)<lowerOn f 3 (mass f j) := by
  open PackedModels BivariateCertificate in
  exact XM.lower_certificate (pm_rep_tM (pm_rep_massM pm_cfg f j) f) (pm_check _ _ j)
    (by norm_num)

end SquaresInCircles.Eight.GlobalGA.NonpositiveT.Paired.Certificate

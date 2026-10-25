module

public import SquaresInCircles.Eight.Owners.GA.Positive.BT3LargeData
public import SquaresInCircles.Eight.Arithmetic.BivariateRounding

/-! # Eight squares: `triangle_derivative_certificate`: the three triangle `y`-derivatives, by rounded packed models -/

@[expose] public section
noncomputable section
open Polynomial
namespace SquaresInCircles.Eight.GlobalGA.PositiveBT3.LargeCertificate
open TensorWholeIntervalPolynomial TwoVariablePolynomial NonnegativeTotals
open CertificateRestrictions

/-! ### Exact models of the triangle numerators

On the triangle, `A` is the nonnegative-total `A .triangle .atT` (both endpoints have
`qB .triangle = qStar .triangle`). `baseNorm`, `P`, `rho` and `mass` differ from the
nonnegative-total ones (the rotating coefficient sits at `D`, `B` keeps the fixed `m`, and the
G curve carries opposite cubic corrections), so they are mirrored here from the shared mirrors
of `k`, `l`, `m`, `delta` and `rotation` (`M .atT`). -/

section Mirrors
open PackedModels BivariateCertificate NonnegativeTotalsMirrors

/-- `A .triangle i`, reduced. -/
private def bd_AM (c : Config) (i : Fin 3) : XM := XM.reduce c (AM c .triangle .atT i)

private theorem bd_rep_AM (c : Config) (i : Fin 3) : (bd_AM c i).Rep c (A .triangle i) :=
  XM.rep_reduce (rep_AM c .triangle .atT i)

/-- `baseNorm .triangle`; `rotation .triangle` is `M .triangle .atT`. -/
private def bd_baseNormM (c : Config) : Fin 4 → XM :=
  ![XM.add c (XM.ofInt c 1 1) (XM.pow c (kM c .triangle) 2),
    XM.add c (XM.pow c (kM c .triangle) 2) (XM.pow c (lM c .triangle) 2),
    XM.add c (XM.pow c (lM c .triangle) 2) (XM.pow c (cM c .triangle) 2),
    XM.add c (XM.ofInt c 1 1) (XM.pow c (MM c .triangle .atT) 2)]

/-- `P .triangle i j`, reduced. -/
private def bd_PM (c : Config) (i : Fin 3) (j : Fin 4) : XM :=
  XM.reduce c <| XM.sub c (bd_baseNormM c j)
    (if j.val = i.val then XM.mul c (XM.mul c (XM.ofInt c 2 1)
        (![kM c .triangle, XM.mul c (kM c .triangle) (lM c .triangle),
          XM.mul c (lM c .triangle) (cM c .triangle), XM.ofInt c 0 1] j))
        (XM.liftM c (deltaM c .triangle) XM.S11L)
      else XM.ofInt c 0 1)

private theorem bd_rep_PM (c : Config) (i : Fin 3) (j : Fin 4) :
    (bd_PM c i j).Rep c (P .triangle i j) := by
  have hb : (bd_baseNormM c j).Rep c (baseNorm .triangle j) := by
    fin_cases j
    · exact XM.rep_add (XM.rep_one c) (XM.rep_pow (rep_kM c .triangle) 2)
    · exact XM.rep_add (XM.rep_pow (rep_kM c .triangle) 2) (XM.rep_pow (rep_lM c .triangle) 2)
    · exact XM.rep_add (XM.rep_pow (rep_lM c .triangle) 2) (XM.rep_pow (rep_cM c .triangle) 2)
    · exact XM.rep_add (XM.rep_one c) (XM.rep_pow (rep_MM c .triangle .atT) 2)
  have hf : (![kM c .triangle, XM.mul c (kM c .triangle) (lM c .triangle),
      XM.mul c (lM c .triangle) (cM c .triangle), XM.ofInt c 0 1] j).Rep c
      (![k .triangle, k .triangle * l .triangle, l .triangle * m .triangle, 0] j) := by
    fin_cases j
    · exact rep_kM c .triangle
    · exact XM.rep_mul (rep_kM c .triangle) (rep_lM c .triangle)
    · exact XM.rep_mul (rep_lM c .triangle) (rep_cM c .triangle)
    · exact XM.rep_zero c
  unfold bd_PM P
  apply XM.rep_reduce
  split_ifs
  · exact XM.rep_sub hb (XM.rep_mul (XM.rep_mul (XM.rep_lit c (by norm_num)) hf)
      (XM.rep_liftS11 (rep_deltaM c .triangle)))
  · exact XM.rep_sub hb (XM.rep_zero c)

/-- `rho i j` as a numerator and a denominator. -/
private def bd_rhoP (i : Fin 3) (j : Fin 4) : ℤ × ℕ :=
  if j.val = i.val then
    if j = 2 then (81386069, 62500000) else (27678887, 25000000)
  else if j = 2 then (142578599, 100000000)
  else if j = 3 then (1451171531, 1000000000)
  else (150407189, 125000000)

private theorem bd_rho_eq (i : Fin 3) (j : Fin 4) :
    rho i j = ((bd_rhoP i j).1 : ℚ) / (bd_rhoP i j).2 := by
  unfold rho bd_rhoP
  split_ifs <;> norm_num

/-- The opposite cubic corrections of `mass` on the triangle G curve. -/
private def bd_corrM (c : Config) (r : Region) (i : Fin 3) (j : Fin 4) : XM :=
  if r = .triangle ∧ i = 1 then
    if j = 1 then XM.mul c (XM.neg (XM.ofInt c 1 4)) (XM.pow c (XM.varX c) 3)
    else if j = 3 then XM.mul c (XM.ofInt c 1 4) (XM.pow c (XM.varX c) 3) else XM.ofInt c 0 1
  else XM.ofInt c 0 1

/-- `mass .triangle i j`, reduced, in the packing `cM`: the cubic mass reads only the truncation
of `P` to total degree three, which is carried over from the packing `cP`. -/
private def bd_massM (cP cM : Config) (i : Fin 3) (j : Fin 4) : XM :=
  XM.reduce cM (XM.add cM (XM.cubicMassRM cM (bd_rhoP i j).1 (bd_rhoP i j).2
    (BivariateRounding.repackM cP cM (XM.trunc cP (bd_PM cP i j) 3))) (bd_corrM cM .triangle i j))

private theorem bd_rep_massM (cP cM : Config) (i : Fin 3) (j : Fin 4) :
    (bd_massM cP cM i j).Rep cM (mass .triangle i j) := by
  have h := XM.rep_cubicMassRM (BivariateRounding.rep_repackM (c' := cM)
    (XM.rep_trunc (bd_rep_PM cP i j) 3)) (bd_rho_eq i j)
  rw [BivariateRounding.cubicMass_truncTot] at h
  exact XM.rep_reduce (XM.rep_add h
    (XM.rep_ite (XM.rep_ite (XM.rep_mul (XM.rep_neg (XM.rep_lit cM (by norm_num)))
      (XM.rep_pow (XM.rep_X cM) 3)) (XM.rep_ite (XM.rep_mul (XM.rep_lit cM (by norm_num))
      (XM.rep_pow (XM.rep_X cM) 3)) (XM.rep_zero cM))) (XM.rep_zero cM)))

open BivariateRounding in
/-- `numerator .triangle i`, rounded to the scale `2 ^ K` in the packing `cE`: `A`, `P` and the
masses are exact in their packings, the products are rounded; the smaller factor is on the right. -/
private def bd_numE (cP cM cE : Config) (K : ℕ) (i : Fin 3) : XE :=
  let w := fun j => XE.ofXMAt cM cE K (bd_massM cP cM i j)
  let P := fun j => XE.ofXMAt cP cE K (bd_PM cP i j)
  let mr := XE.mulR cE K
  XE.sub cE (mr (mr (mr (mr (mr (XE.ofXMAt cP cE K (bd_AM cP i))
      (XE.ofXMAt cP cE K (XM.ofInt cP 2 1))) (w 0)) (w 1)) (w 2)) (w 3))
    (mr (XE.add cE (XE.add cE (XE.add cE
      (mr (mr (mr (XE.add cE (P 0) (mr (w 0) (w 0))) (w 1)) (w 2)) (w 3))
      (mr (mr (mr (XE.add cE (P 1) (mr (w 1) (w 1))) (w 0)) (w 2)) (w 3)))
      (mr (mr (mr (XE.add cE (P 2) (mr (w 2) (w 2))) (w 0)) (w 1)) (w 3)))
      (mr (mr (mr (XE.add cE (P 3) (mr (w 3) (w 3))) (w 0)) (w 1)) (w 2)))
      (XE.ofXMAt cP cE K (XM.ofInt cP 494696877 250000000)))

open BivariateRounding in
private theorem bd_rep_numE (cP cM cE : Config) (K : ℕ) (i : Fin 3) :
    (bd_numE cP cM cE K i).Rep cE (numerator .triangle i) := by
  have hw (j : Fin 4) := XE.rep_ofXMAt (c' := cE) (bd_rep_massM cP cM i j) K
  have hP (j : Fin 4) := XE.rep_ofXMAt (c' := cE) (bd_rep_PM cP i j) K
  have hs (j : Fin 4) : (XE.mulR cE K (XE.ofXMAt cM cE K (bd_massM cP cM i j))
      (XE.ofXMAt cM cE K (bd_massM cP cM i j))).Rep cE (mass .triangle i j ^ 2) := by
    rw [pow_two]; exact XE.rep_mulR (hw j) (hw j) K
  exact XE.rep_sub (XE.rep_mulR (XE.rep_mulR (XE.rep_mulR (XE.rep_mulR (XE.rep_mulR_swap
      (XE.rep_ofXMAt (XM.rep_lit cP (by norm_num)) K) (XE.rep_ofXMAt (bd_rep_AM cP i) K) K)
      (hw 0) K) (hw 1) K) (hw 2) K) (hw 3) K)
    (XE.rep_mulR_swap (XE.rep_ofXMAt (XM.rep_lit cP (by norm_num [NonnegativeTotals.Certificate.Rbar])) K)
      (XE.rep_add (XE.rep_add (XE.rep_add
      (XE.rep_mulR (XE.rep_mulR (XE.rep_mulR (XE.rep_add (hP 0) (hs 0)) (hw 1) K) (hw 2) K) (hw 3) K)
      (XE.rep_mulR (XE.rep_mulR (XE.rep_mulR (XE.rep_add (hP 1) (hs 1)) (hw 0) K) (hw 2) K) (hw 3) K))
      (XE.rep_mulR (XE.rep_mulR (XE.rep_mulR (XE.rep_add (hP 2) (hs 2)) (hw 0) K) (hw 1) K) (hw 3) K))
      (XE.rep_mulR (XE.rep_mulR (XE.rep_mulR (XE.rep_add (hP 3) (hs 3)) (hw 0) K) (hw 1) K) (hw 2) K))
      K)

end Mirrors

/-! ### The three checks

`A` and `P` are exact in boxes of `41 × 41` digits of 170 bits, the masses in digits of 600 bits.
The numerators are rounded models (`BivariateRounding.XE`) at the scale `2 ^ 60` in digits of
160 bits, so that the products stay small; the derivative, the substitution onto the triangle and
the final bound use digits of 400 bits (the substitution `x ↦ (8/15)(x + 1)/2` multiplies the
scale by `30 ^ 37`). The error of the rounding enters the final bounds. -/

section Checks
open PackedModels BivariateCertificate BivariateRounding

private def bd_cP : Config := ⟨0, 20, 170⟩
private def bd_cM : Config := ⟨0, 20, 600⟩
private def bd_cE : Config := ⟨0, 20, 160⟩
private def bd_cT : Config := ⟨0, 20, 400⟩

/-- The model of the triangle transform of the `y`-derivative of the quotient `i`. -/
private def bd_finalE (i : Fin 3) : XE :=
  XE.norm bd_cT (XE.toScale bd_cT bd_cT 60 (XE.triangle bd_cT 8 15 (XE.repack bd_cE bd_cT
    (XE.derivY bd_cE (XE.divY bd_cE (bd_numE bd_cP bd_cM bd_cE 60 i))))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
set_option Elab.async false in
private theorem bd_check_0 : XE.upperCheck bd_cT (bd_finalE 0) 39 (-231) 1000 = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
set_option Elab.async false in
private theorem bd_check_1 : XE.upperCheck bd_cT (bd_finalE 1) 39 (-21) 50 = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
set_option Elab.async false in
private theorem bd_check_2 : XE.upperCheck bd_cT (bd_finalE 2) 39 (-119) 500 = true := by
  decide +kernel

end Checks

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
theorem triangle_derivative_certificate (i : Fin 3) :
    transform .triangle (derivativeY (triangleQuotient i))=
      expansion 39 (transform .triangle (derivativeY (triangleQuotient i))) ∧
    upperOn .triangle 39 (derivativeY (triangleQuotient i))<triangleDerivativeReserve i := by
  open BivariateRounding in
  have hm (i : Fin 3) := XE.rep_norm (XE.rep_toScale (c' := bd_cT) (XE.rep_triangle
    (XE.rep_repack (c' := bd_cT) (XE.rep_derivY (XE.rep_divY (bd_rep_numE bd_cP bd_cM bd_cE 60 i))))
    (d := 8/15) (dn := 8) (dd := 15) (by norm_num) (by norm_num)) 60)
  fin_cases i
  · exact XE.upper_certificate (hm 0) bd_check_0 (by norm_num [triangleDerivativeReserve])
  · exact XE.upper_certificate (hm 1) bd_check_1 (by norm_num [triangleDerivativeReserve])
  · exact XE.upper_certificate (hm 2) bd_check_2 (by norm_num [triangleDerivativeReserve])

end SquaresInCircles.Eight.GlobalGA.PositiveBT3.LargeCertificate

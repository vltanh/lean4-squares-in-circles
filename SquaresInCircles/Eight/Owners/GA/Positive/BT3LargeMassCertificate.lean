module

public import SquaresInCircles.Eight.Owners.GA.Positive.BT3LargeData

/-! # Eight squares: `mass_certificate` of the positive-BT3 large totals: the 24 masses, by exact packed checks -/

@[expose] public section
noncomputable section
open Polynomial
namespace SquaresInCircles.Eight.GlobalGA.PositiveBT3.LargeCertificate
open TensorWholeIntervalPolynomial TwoVariablePolynomial NonnegativeTotals
open CertificateRestrictions

/-! ### Exact models of the masses

The weights `k`, `l`, `m`, `delta` and the rotating coefficient are those of the nonnegative
totals (`NonnegativeTotalsMirrors`); `rotation r` is `M r .atT`. -/

section BMModels
open PackedModels BivariateCertificate NonnegativeTotalsMirrors

private theorem bm_rep_rotation (c : Config) (r : Region) : (MM c r .atT).Rep c (rotation r) :=
  rep_MM c r .atT

private def bm_baseNormS (c : Config) (r : Region) (j : Fin 4) :
    {m : XM // m.Rep c (baseNorm r j)} := by
  apply Subtype.mk; simp only [baseNorm]
  build_xm [rep_kM c r, rep_lM c r, rep_cM c r, bm_rep_rotation c r]

private def bm_PS (c : Config) (r : Region) (i : Fin 3) (j : Fin 4) :
    {m : XM // m.Rep c (P r i j)} := by
  apply Subtype.mk; simp only [P]
  build_xm [(bm_baseNormS c r j).2, rep_kM c r, rep_lM c r, rep_cM c r, rep_deltaM c r]

/-- `P r i j`, reduced. -/
private def bm_PM (c : Config) (r : Region) (i : Fin 3) (j : Fin 4) : XM :=
  XM.reduce c (bm_PS c r i j).1

private theorem bm_rep_PM (c : Config) (r : Region) (i : Fin 3) (j : Fin 4) :
    (bm_PM c r i j).Rep c (P r i j) := XM.rep_reduce (bm_PS c r i j).2

/-- `rho i j` as a numerator and a denominator. -/
private def bm_rhoP (i : Fin 3) (j : Fin 4) : ℤ × ℕ :=
  if j.val=i.val then if j=2 then (81386069,62500000) else (27678887,25000000)
  else if j=2 then (142578599,100000000)
  else if j=3 then (1451171531,1000000000)
  else (150407189,125000000)

private theorem bm_rho_eq (i : Fin 3) (j : Fin 4) :
    rho i j=((bm_rhoP i j).1:ℚ)/((bm_rhoP i j).2:ℚ) := by
  unfold rho bm_rhoP
  split_ifs <;> norm_num

/-- The opposite cubic corrections of `mass` on the triangle G curve. -/
private def bm_corrM (c : Config) (r : Region) (i : Fin 3) (j : Fin 4) : XM :=
  if r=.triangle ∧ i=1 then
    if j=1 then XM.mul c (XM.neg (XM.ofInt c 1 4)) (XM.pow c (XM.varX c) 3)
    else if j=3 then XM.mul c (XM.ofInt c 1 4) (XM.pow c (XM.varX c) 3) else XM.ofInt c 0 1
  else XM.ofInt c 0 1

/-- `mass r i j`, reduced. -/
private def bm_massM (c : Config) (r : Region) (i : Fin 3) (j : Fin 4) : XM :=
  XM.reduce c (XM.add c (XM.cubicMassRM c (bm_rhoP i j).1 (bm_rhoP i j).2 (bm_PM c r i j))
    (bm_corrM c r i j))

private theorem bm_rep_massM (c : Config) (r : Region) (i : Fin 3) (j : Fin 4) :
    (bm_massM c r i j).Rep c (mass r i j) :=
  XM.rep_reduce (XM.rep_add (XM.rep_cubicMassRM (bm_rep_PM c r i j) (bm_rho_eq i j))
    (XM.rep_ite (XM.rep_ite (XM.rep_mul (XM.rep_neg (XM.rep_lit c (by norm_num)))
      (XM.rep_pow (XM.rep_X c) 3)) (XM.rep_ite (XM.rep_mul (XM.rep_lit c (by norm_num))
      (XM.rep_pow (XM.rep_X c) 3)) (XM.rep_zero c))) (XM.rep_zero c)))

end BMModels

/-! ### Exact bivariate checks

The masses are packed in boxes of `19 × 19` digits (`j ≤ 2`) or `33 × 33` digits (`j = 3`,
whose norm `1 + rotation ^ 2` has degree up to `30` in `x`), with digits of 600 bits. Each check
is one kernel computation on natural numbers. -/

section BMChecks
open PackedModels BivariateCertificate

/-- The packing of the masses of index `j`. -/
private def bm_cfg (j : Fin 4) : Config := if j=3 then ⟨0, 16, 600⟩ else ⟨0, 9, 600⟩

set_option Elab.async false in
private theorem bm_massT_0 : ∀ j : Fin 4, XM.lowerCheck (bm_cfg j)
    (XM.triangleM (bm_cfg j) (bm_massM (bm_cfg j) .triangle 0 j) 8 15) 3 7 10=true := by
  decide +kernel

set_option Elab.async false in
private theorem bm_massT_1 : ∀ j : Fin 4, XM.lowerCheck (bm_cfg j)
    (XM.triangleM (bm_cfg j) (bm_massM (bm_cfg j) .triangle 1 j) 8 15) 3 7 10=true := by
  decide +kernel

set_option Elab.async false in
private theorem bm_massT_2 : ∀ j : Fin 4, XM.lowerCheck (bm_cfg j)
    (XM.triangleM (bm_cfg j) (bm_massM (bm_cfg j) .triangle 2 j) 8 15) 3 7 10=true := by
  decide +kernel

set_option Elab.async false in
private theorem bm_massR_0 : ∀ j : Fin 4, XM.lowerCheck (bm_cfg j)
    (XM.rectangleM (bm_cfg j) (bm_massM (bm_cfg j) .rectangle 0 j) 1 6 8 15) 3 77 100=true := by
  decide +kernel

set_option Elab.async false in
private theorem bm_massR_1 : ∀ j : Fin 4, XM.lowerCheck (bm_cfg j)
    (XM.rectangleM (bm_cfg j) (bm_massM (bm_cfg j) .rectangle 1 j) 1 6 8 15) 3 77 100=true := by
  decide +kernel

set_option Elab.async false in
private theorem bm_massR_2 : ∀ j : Fin 4, XM.lowerCheck (bm_cfg j)
    (XM.rectangleM (bm_cfg j) (bm_massM (bm_cfg j) .rectangle 2 j) 1 6 8 15) 3 77 100=true := by
  decide +kernel

private theorem bm_massT (i : Fin 3) (j : Fin 4) : XM.lowerCheck (bm_cfg j)
    (XM.triangleM (bm_cfg j) (bm_massM (bm_cfg j) .triangle i j) 8 15) 3 7 10=true := by
  fin_cases i
  exacts [bm_massT_0 j,bm_massT_1 j,bm_massT_2 j]

private theorem bm_massR (i : Fin 3) (j : Fin 4) : XM.lowerCheck (bm_cfg j)
    (XM.rectangleM (bm_cfg j) (bm_massM (bm_cfg j) .rectangle i j) 1 6 8 15) 3 77 100=true := by
  fin_cases i
  exacts [bm_massR_0 j,bm_massR_1 j,bm_massR_2 j]

end BMChecks

theorem mass_certificate (r : Region) (i : Fin 3) (j : Fin 4) :
    transform r (mass r i j)=expansion 3 (transform r (mass r i j)) ∧
    massReserve r<lowerOn r 3 (mass r i j) := by
  open BivariateCertificate in
  cases r
  · exact XM.lower_certificate (XM.rep_triangleM (bm_rep_massM _ .triangle i j) (by norm_num))
      (bm_massT i j) (by norm_num [massReserve])
  · exact XM.lower_certificate (XM.rep_rectangleM (bm_rep_massM _ .rectangle i j) (by norm_num)
      (by norm_num)) (bm_massR i j) (by norm_num [massReserve])

end SquaresInCircles.Eight.GlobalGA.PositiveBT3.LargeCertificate

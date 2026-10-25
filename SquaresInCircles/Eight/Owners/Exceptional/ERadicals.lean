module

public import SquaresInCircles.Eight.Owners.Exceptional.EScalarData

/-!
# Eight squares: positive-mass transfer for the exceptional contact endpoints

Positive masses and exact factorization turn each
whole-interval polynomial into a strict Taylor-model inequality. The
five weighted square roots are bounded by the elementary positive-square
identity, with every denominator proved positive on the whole interval.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.ExceptionalERadicals
open Polynomial ExceptionalEPolynomials HighOrderTaylor

def radicalSum (s : ScalarCase) (z : ℝ) : ℝ :=
  ∑i : Fin 5,aeval z (rowWeight s i)*Real.sqrt (aeval z (rowSquare s i))
def rationalSum (s : ScalarCase) (z : ℝ) : ℝ :=
  ∑i : Fin 5,aeval z (rowWeight s i)*
    (aeval z (rowSquare s i)+(aeval z (massAt s i))^2)/(2*aeval z (massAt s i))

private theorem five_mass_identity (a v w : Fin 5 → ℝ) (ha : ∀i,a i≠0) :
    (∑i : Fin 5,w i*(v i+(a i)^2)*∏j : Fin 5,if j=i then 1 else a j)=
      2*(∏i : Fin 5,a i)*(∑i : Fin 5,w i*(v i+(a i)^2)/(2*a i)) := by
  simp [Fin.sum_univ_succ,Fin.prod_univ_succ]
  field_simp [ha 0,ha 1,ha 2,ha 3,ha 4]

theorem certificate_factorization (s : ScalarCase) {z : ℝ}
    (hz : z∈Set.Icc 0 (length s:ℝ)) :
    aeval z (certificate s)=2*(∏i : Fin 5,aeval z (massAt s i))*
      (aeval z (outside s)-(margin:ℝ)-(radiusUpper:ℝ)*rationalSum s z) := by
  have ha : ∀i : Fin 5,aeval z (massAt s i)≠0 := by
    intro i
    have hi := (mass_bounds s i hz).1
    linarith
  have hid := five_mass_identity (fun i => aeval z (massAt s i))
    (fun i => aeval z (rowSquare s i)) (fun i => aeval z (rowWeight s i)) ha
  simp only [certificate,mass,massExcept,map_sub,map_mul,map_add,map_ofNat,map_sum,
    map_pow,map_prod,aeval_C,map_one,apply_ite,eq_ratCast] at *
  rw [hid]
  unfold rationalSum
  ring

theorem rational_positive (s : ScalarCase) {z : ℝ} (hz : z∈Set.Icc 0 (length s:ℝ)) :
    0<aeval z (outside s)-(margin:ℝ)-(radiusUpper:ℝ)*rationalSum s z := by
  have hp := certificate_positive s hz
  rw [certificate_factorization s hz] at hp
  have hM : 0<∏i : Fin 5,aeval z (massAt s i) := by
    apply Finset.prod_pos
    intro i _
    have hi := (mass_bounds s i hz).1
    linarith
  exact (mul_pos_iff_of_pos_left (mul_pos (by norm_num) hM)).mp hp

theorem radical_le_rational (s : ScalarCase) {z : ℝ} (hz : z∈Set.Icc 0 (length s:ℝ))
    (hw : ∀i : Fin 5,0≤aeval z (rowWeight s i)) : radicalSum s z≤rationalSum s z := by
  apply Finset.sum_le_sum
  intro i _
  have hm : 0<aeval z (massAt s i) := by linarith [(mass_bounds s i hz).1]
  have hv : 0≤aeval z (rowSquare s i) := by linarith [(square_bounds s i hz).1]
  have hh := mul_le_mul_of_nonneg_left (ScalarRadicalTransfer.sqrt_le_mass_majorant hv hm) (hw i)
  simpa only [mul_div_assoc] using hh

theorem radical_reserve (s : ScalarCase) {z : ℝ} (hz : z∈Set.Icc 0 (length s:ℝ))
    (hw : ∀i : Fin 5,0≤aeval z (rowWeight s i)) :
    (margin:ℝ)<aeval z (outside s)-(radiusUpper:ℝ)*radicalSum s z := by
  have hp := rational_positive s hz
  have hm := mul_le_mul_of_nonneg_left (radical_le_rational s hz hw)
    (show (0:ℝ)≤(radiusUpper:ℝ) by norm_num [radiusUpper])
  linarith

theorem taylor_weights (s : ScalarCase) {t : ℝ} (ht : t∈domain s) :
    ∀i : Fin 5,0≤aeval (t-(origin s:ℝ)) (rowWeight s i) := by
  have hd := ExceptionalECoefficients.angle (family_domain ht)
  have hs : S15 t∈Set.Icc 0 1 := ⟨S15_nonneg hd,(S15_le_sin hd.1).trans (Real.sin_le_one t)⟩
  intro i
  rw [(ExceptionalEScalarData.polynomial_rows s t i).2]
  exact (ExceptionalEScalarData.weight_bounds hs i).1

theorem polynomial_radicalSum (s : ScalarCase) (t : ℝ) :
    radicalSum s (t-(origin s:ℝ))=ExceptionalEScalarData.taylorSum s t := by
  unfold radicalSum ExceptionalEScalarData.taylorSum ExceptionalEScalarData.rowSum
  apply Finset.sum_congr rfl
  intro i _
  rw [(ExceptionalEScalarData.polynomial_rows s t i).1,(ExceptionalEScalarData.polynomial_rows s t i).2]

theorem taylor_reserve (s : ScalarCase) {t : ℝ} (ht : t∈domain s) :
    (margin:ℝ)<ExceptionalEScalarData.taylorOutside s t-
      (radiusUpper:ℝ)*ExceptionalEScalarData.taylorSum s t := by
  have hp := radical_reserve s (local_parameter ht) (taylor_weights s ht)
  simpa only [ExceptionalEScalarData.polynomial_outside,polynomial_radicalSum] using hp

end SquaresInCircles.Eight.ExceptionalERadicals

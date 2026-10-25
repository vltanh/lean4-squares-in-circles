module

public import SquaresInCircles.Eight.TableFree.ExceptionalNegativeTScalarData

/-!
# Positive-mass transfer at the exceptional negative-T endpoints

Uncompiled source. The exact five-mass factorization retains the hand
proof's 0.00238 numerator reserve and its denominator bound of 16. The
weighted radicals are compared through a positive square at every point
of the complete interval.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.ExceptionalNegativeTRadicals
open Polynomial ExceptionalNegativeTPolynomials ExceptionalNegativeTScalarData HighOrderTaylor
open ExceptionalNegativeTScalarModel (Case origin length domain local_parameter family_domain)

def radicalSum (s : Case) (z : ℝ) : ℝ :=
  ∑i : Fin 5,aeval z (rowWeight s i)*Real.sqrt (aeval z (rowSquare s i))
def rationalSum (s : Case) (z : ℝ) : ℝ :=
  ∑i : Fin 5,aeval z (rowWeight s i)*
    (aeval z (rowSquare s i)+(aeval z (massAt s i))^2)/(2*aeval z (massAt s i))

private theorem five_mass_identity (a v w : Fin 5 → ℝ) (ha : ∀i,a i≠0) :
    (∑i : Fin 5,w i*(v i+(a i)^2)*∏j : Fin 5,if j=i then 1 else a j)=
      2*(∏i : Fin 5,a i)*(∑i : Fin 5,w i*(v i+(a i)^2)/(2*a i)) := by
  simp [Fin.sum_univ_succ,Fin.prod_univ_succ]
  field_simp [ha 0,ha 1,ha 2,ha 3,ha 4]

theorem certificate_factorization (s : Case) {z : ℝ}
    (hz : z∈Set.Icc 0 (length s.row:ℝ)) :
    aeval z (certificate s)=2*(∏i : Fin 5,aeval z (massAt s i))*
      (aeval z (outside s)-(radiusUpper:ℝ)*rationalSum s z) := by
  have ha : ∀i : Fin 5,aeval z (massAt s i)≠0 := by
    intro i
    linarith [(mass_bounds s i hz).1]
  have hid := five_mass_identity (fun i => aeval z (massAt s i))
    (fun i => aeval z (rowSquare s i)) (fun i => aeval z (rowWeight s i)) ha
  simp only [certificate,mass,massExcept,map_sub,map_mul,map_add,map_ofNat,map_sum,
    map_pow,map_prod,aeval_C,map_one,apply_ite,eq_ratCast] at *
  rw [hid]
  unfold rationalSum
  ring

theorem denominator_bounds (s : Case) {z : ℝ}
    (hz : z∈Set.Icc 0 (length s.row:ℝ)) :
    0<2*(∏i : Fin 5,aeval z (massAt s i)) ∧
      2*(∏i : Fin 5,aeval z (massAt s i))<16 := by
  have h := fun i => mass_bounds s i hz
  rw [Fin.prod_univ_five]
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3; have h4 := h 4
  have q0 : (0:ℝ) < aeval z (massAt s 0) := by linarith [h0.1]
  have q1 : (0:ℝ) < aeval z (massAt s 1) := by linarith [h1.1]
  have q2 : (0:ℝ) < aeval z (massAt s 2) := by linarith [h2.1]
  have q3 : (0:ℝ) < aeval z (massAt s 3) := by linarith [h3.1]
  have q4 : (0:ℝ) < aeval z (massAt s 4) := by linarith [h4.1]
  have p01 := mul_lt_mul'' h0.2 h1.2 q0.le q1.le
  have p012 := mul_lt_mul'' p01 h2.2 (mul_pos q0 q1).le q2.le
  have p0123 := mul_lt_mul'' p012 h3.2 (mul_pos (mul_pos q0 q1) q2).le q3.le
  have p01234 := mul_lt_mul'' p0123 h4.2 (mul_pos (mul_pos (mul_pos q0 q1) q2) q3).le q4.le
  constructor
  · exact mul_pos two_pos (mul_pos (mul_pos (mul_pos (mul_pos q0 q1) q2) q3) q4)
  · norm_num at p01234
    linarith

theorem rational_reserve (s : Case) {z : ℝ}
    (hz : z∈Set.Icc 0 (length s.row:ℝ)) :
    (119/800000:ℝ)<aeval z (outside s)-(radiusUpper:ℝ)*rationalSum s z := by
  have hp := certificate_reserve s hz
  rw [certificate_factorization s hz] at hp
  have hb := denominator_bounds s hz
  by_contra! h
  have hm := mul_le_mul_of_nonneg_left h hb.1.le
  nlinarith

theorem radical_le_rational (s : Case) {z : ℝ}
    (hz : z∈Set.Icc 0 (length s.row:ℝ))
    (hw : ∀i : Fin 5,0≤aeval z (rowWeight s i)) : radicalSum s z≤rationalSum s z := by
  apply Finset.sum_le_sum
  intro i _
  have hm : 0<aeval z (massAt s i) := by linarith [(mass_bounds s i hz).1]
  have hv : 0≤aeval z (rowSquare s i) := by linarith [(square_bounds s i hz).1]
  have hh := mul_le_mul_of_nonneg_left (ScalarRadicalTransfer.sqrt_le_mass_majorant hv hm) (hw i)
  simpa only [mul_div_assoc] using hh

theorem radical_reserve (s : Case) {z : ℝ}
    (hz : z∈Set.Icc 0 (length s.row:ℝ))
    (hw : ∀i : Fin 5,0≤aeval z (rowWeight s i)) :
    (119/800000:ℝ)<aeval z (outside s)-(radiusUpper:ℝ)*radicalSum s z := by
  have hp := rational_reserve s hz
  have hm := mul_le_mul_of_nonneg_left (radical_le_rational s hz hw)
    (show (0:ℝ)≤(radiusUpper:ℝ) by norm_num [radiusUpper])
  linarith

theorem taylor_weights (s : Case) {t : ℝ} (ht : t∈domain s.row) :
    ∀i : Fin 5,0≤aeval (t-(origin s.row:ℝ)) (rowWeight s i) := by
  have hd := ExceptionalECoefficients.angle (family_domain ht)
  have hs : S15 t∈Set.Icc 0 1 := ⟨S15_nonneg hd,(S15_le_sin hd.1).trans (Real.sin_le_one t)⟩
  intro i
  rw [(polynomial_rows s t i).2]
  exact (weight_bounds s (family_domain ht) hs i).1

theorem polynomial_radicalSum (s : Case) (t : ℝ) :
    radicalSum s (t-(origin s.row:ℝ))=taylorSum s t := by
  unfold radicalSum taylorSum ExceptionalNegativeTScalarModel.rowSum
  apply Finset.sum_congr rfl
  intro i _
  rw [(polynomial_rows s t i).1,(polynomial_rows s t i).2]

theorem taylor_reserve (s : Case) {t : ℝ} (ht : t∈domain s.row) :
    (119/800000:ℝ)<taylorOutside s t-(radiusUpper:ℝ)*taylorSum s t := by
  have hp := radical_reserve s (local_parameter ht) (taylor_weights s ht)
  simpa only [polynomial_outside,polynomial_radicalSum] using hp

end SquaresInCircles.Eight.TableFree.ExceptionalNegativeTRadicals

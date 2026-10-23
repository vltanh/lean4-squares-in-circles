module

public import SquaresInCircles.Eight.Arithmetic.Bernstein

/-! Generated source, schema eight-polynomial-v1. Uncompiled.
Exact polynomial data and full algebraic expansions; no report status is a premise. -/

@[expose] public section
open scoped BigOperators
namespace SquaresInCircles.Eight.Generated

/-- Source: CENTRAL_BAND_COMMON_POINT_LEMMAS.md, polynomial bandB V, row 0. -/
def central_bandB_V0 : Arithmetic.BernsteinRow :=
  { interval := ⟨0,(3/14)⟩
    polynomial := [(4789/40000), (-166767/200000), (15211/20000), (594767/200000), (-35211/40000)]
    degree := 4
    coefficients := [(4789/40000), (840619/11200000), (101377/2800000), (23033761/2195200000), (25928687/7683200000)] }

theorem central_bandB_V0_valid : central_bandB_V0.Valid (25928687/15366400000) := by
  constructor
  · norm_num [central_bandB_V0]
  · rfl
  · intro t
    norm_num [central_bandB_V0, Arithmetic.QPoly.eval, Arithmetic.bernsteinEval,
      Arithmetic.bernsteinBasis, Arithmetic.BernsteinRow.coefficient,
      Finset.sum_range_succ]
    ring
  · intro i hi
    have hi' : i ≤ 4 := hi
    interval_cases i <;> norm_num [central_bandB_V0,Arithmetic.BernsteinRow.coefficient]

theorem central_bandB_V0_positive {x : ℝ} (hx : (0 : ℝ) ≤ x ∧ x ≤ (3/14)) :
    0 < central_bandB_V0.polynomial.eval x :=
  central_bandB_V0_valid.positive (by norm_num) hx

/-- Source: CENTRAL_BAND_COMMON_POINT_LEMMAS.md, polynomial bandB V, row 1. -/
def central_bandB_V1 : Arithmetic.BernsteinRow :=
  { interval := ⟨(3/14),(15/56)⟩
    polynomial := [(4789/40000), (-166767/200000), (15211/20000), (594767/200000), (-35211/40000)]
    degree := 4
    coefficients := [(25928687/7683200000), (98050543/61465600000), (30053507/30732800000), (1581472597/983449600000), (1401939853/393379840000)] }

theorem central_bandB_V1_valid : central_bandB_V1.Valid (30053507/61465600000) := by
  constructor
  · norm_num [central_bandB_V1]
  · rfl
  · intro t
    norm_num [central_bandB_V1, Arithmetic.QPoly.eval, Arithmetic.bernsteinEval,
      Arithmetic.bernsteinBasis, Arithmetic.BernsteinRow.coefficient,
      Finset.sum_range_succ]
    ring
  · intro i hi
    have hi' : i ≤ 4 := hi
    interval_cases i <;> norm_num [central_bandB_V1,Arithmetic.BernsteinRow.coefficient]

theorem central_bandB_V1_positive {x : ℝ} (hx : ((3/14) : ℝ) ≤ x ∧ x ≤ (15/56)) :
    0 < central_bandB_V1.polynomial.eval x :=
  central_bandB_V1_valid.positive (by norm_num) hx

/-- Source: CENTRAL_BAND_COMMON_POINT_LEMMAS.md, polynomial bandB V, row 2. -/
def central_bandB_V2 : Arithmetic.BernsteinRow :=
  { interval := ⟨(15/56),(9/28)⟩
    polynomial := [(4789/40000), (-166767/200000), (15211/20000), (594767/200000), (-35211/40000)]
    degree := 4
    coefficients := [(1401939853/393379840000), (1357056667/245862400000), (4327610183/491724800000), (1657823819/122931200000), (2414995853/122931200000)] }

theorem central_bandB_V2_valid : central_bandB_V2.Valid (1401939853/786759680000) := by
  constructor
  · norm_num [central_bandB_V2]
  · rfl
  · intro t
    norm_num [central_bandB_V2, Arithmetic.QPoly.eval, Arithmetic.bernsteinEval,
      Arithmetic.bernsteinBasis, Arithmetic.BernsteinRow.coefficient,
      Finset.sum_range_succ]
    ring
  · intro i hi
    have hi' : i ≤ 4 := hi
    interval_cases i <;> norm_num [central_bandB_V2,Arithmetic.BernsteinRow.coefficient]

theorem central_bandB_V2_positive {x : ℝ} (hx : ((15/56) : ℝ) ≤ x ∧ x ≤ (9/28)) :
    0 < central_bandB_V2.polynomial.eval x :=
  central_bandB_V2_valid.positive (by norm_num) hx

/-- Source: CENTRAL_BAND_COMMON_POINT_LEMMAS.md, polynomial bandB V, row 3. -/
def central_bandB_V3 : Arithmetic.BernsteinRow :=
  { interval := ⟨(9/28),(3/7)⟩
    polynomial := [(4789/40000), (-166767/200000), (15211/20000), (594767/200000), (-35211/40000)]
    degree := 4
    coefficients := [(2414995853/122931200000), (3929339921/122931200000), (771085879/15366400000), (287583337/3841600000), (1277993/12005000)] }

theorem central_bandB_V3_valid : central_bandB_V3.Valid (2414995853/245862400000) := by
  constructor
  · norm_num [central_bandB_V3]
  · rfl
  · intro t
    norm_num [central_bandB_V3, Arithmetic.QPoly.eval, Arithmetic.bernsteinEval,
      Arithmetic.bernsteinBasis, Arithmetic.BernsteinRow.coefficient,
      Finset.sum_range_succ]
    ring
  · intro i hi
    have hi' : i ≤ 4 := hi
    interval_cases i <;> norm_num [central_bandB_V3,Arithmetic.BernsteinRow.coefficient]

theorem central_bandB_V3_positive {x : ℝ} (hx : ((9/28) : ℝ) ≤ x ∧ x ≤ (3/7)) :
    0 < central_bandB_V3.polynomial.eval x :=
  central_bandB_V3_valid.positive (by norm_num) hx

end SquaresInCircles.Eight.Generated

import SquaresInCircles.Six.Normalization.Constants

/-!
# An analytic obstruction to failure of the OWN moving pin

Write v = |sin t| and c = cos t. OWN separation gives
  a + 1/2 >= 1 + (1/2+x)c + (77/200)v.
Failure of the moving pin's transverse condition gives
  |b| + 1/2 >= 1 - (1+x)v.

Increasing x from zero only increases the sum of these two squares. At x=0,
c >= 5/6 and c^2+v^2=1 imply c >= 1-(6/11)v^2. The resulting quartic is
bounded below by its constant, linear and cubic terms. Their value at v=5/12
already exceeds Q0. This is one whole-interval argument, not a cell cover.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

private def radialMinorant (v : ℝ) : ℝ := 3/2+(77/200)*v-(3/11)*v^2

lemma moving_pin_polynomial {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 5/12) :
    Q0 < (radialMinorant v)^2+(1-v)^2 := by
  have h3 := pow_le_pow_left₀ hv0 hv1 3
  have hrem : 0 ≤ (1+5929/40000-9/11 : ℝ)*v^2+(9/121)*v^4 := by
    exact add_nonneg (mul_nonneg (by norm_num) (sq_nonneg v))
      (mul_nonneg (by norm_num) (pow_nonneg hv0 4))
  have hid : (radialMinorant v)^2+(1-v)^2 =
      13/4-(169/200)*v-(231/1100)*v^3+
        ((1+5929/40000-9/11)*v^2+(9/121)*v^4) := by
    dsimp [radialMinorant]
    ring
  have hnum : Q0 < (13/4 : ℝ)-(169/200)*(5/12)-(231/1100)*(5/12)^3 := by
    norm_num [Q0]
  rw [hid]
  linarith

/-- A real-algebra lemma: a failed transverse condition is incompatible with
far-corner containment, throughout the full interval 0 <= v <= 5/12. -/
theorem own_transverse_obstruction {a u x c v : ℝ}
    (hu : 0 ≤ u) (hx0 : 0 ≤ x) (hx1 : x ≤ 23/200)
    (hc0 : 5/6 ≤ c) (hc1 : c ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 5/12) (hunit : c^2+v^2=1)
    (hown : 1+(1/2+x)*c+(77/200)*v ≤ a+1/2)
    (hbox : (a+1/2)^2+(u+1/2)^2 ≤ Q0) :
    u+(1+x)*v < 1/2 := by
  by_contra! hfail
  let A0 : ℝ := 1+c/2+(77/200)*v
  let B0 : ℝ := 1-v
  let A : ℝ := A0+x*c
  let B : ℝ := B0-x*v
  have hc : 0 ≤ c := by linarith
  have hA0 : 1 ≤ A0 := by dsimp [A0]; linarith
  have hB0 : 0 ≤ B0 ∧ B0 ≤ 1 := by
    dsimp [B0]
    constructor <;> linarith
  have hxv := mul_le_mul
    (show 1+x ≤ (223:ℝ)/200 by linarith) hv1 hv0 (by norm_num)
  have hA : 0 ≤ A := by
    have hxc := mul_nonneg hx0 hc
    dsimp [A]
    linarith
  have hB : 0 ≤ B := by dsimp [B,B0]; nlinarith only [hxv]
  have hAa : A ≤ a+1/2 := by dsimp [A,A0]; nlinarith only [hown]
  have hBu : B ≤ u+1/2 := by dsimp [B,B0]; nlinarith only [hfail]
  have hsqA := mul_nonneg (sub_nonneg.mpr hAa)
    (show 0 ≤ a+1/2+A by linarith)
  have hsqB := mul_nonneg (sub_nonneg.mpr hBu)
    (show 0 ≤ u+1/2+B by linarith)
  have hAB : A^2+B^2 ≤ Q0 := by nlinarith only [hsqA,hsqB,hbox]
  have hAc := mul_nonneg (show 0 ≤ A0-1 by linarith) hc
  have hBv := mul_nonneg (show 0 ≤ 1-B0 by linarith [hB0.2]) hv0
  have hcross : 0 ≤ A0*c-B0*v := by
    nlinarith only [hAc,hBv,hc0,hv1]
  have hxx := mul_nonneg hx0 hcross
  have hid : A^2+B^2-(A0^2+B0^2) =
      2*x*(A0*c-B0*v)+x^2*(c^2+v^2) := by
    dsimp [A,B]
    ring
  rw [hunit] at hid
  have hbase : A0^2+B0^2 ≤ Q0 := by
    nlinarith only [hid,hxx,sq_nonneg x,hAB]
  have hcp := mul_nonneg (show 0 ≤ 1-c by linarith)
    (show 0 ≤ c-5/6 by linarith)
  have hcos : 1-(6/11)*v^2 ≤ c := by nlinarith only [hcp,hunit]
  have hv2 := pow_le_pow_left₀ hv0 hv1 2
  have hL : 0 ≤ radialMinorant v := by
    dsimp [radialMinorant]
    nlinarith only [hv0,hv2]
  have hLA : radialMinorant v ≤ A0 := by
    dsimp [radialMinorant,A0]
    linarith
  have hcmp := mul_nonneg (sub_nonneg.mpr hLA)
    (show 0 ≤ A0+radialMinorant v by linarith)
  have hbad := moving_pin_polynomial hv0 hv1
  change Q0 < (radialMinorant v)^2+B0^2 at hbad
  nlinarith only [hcmp,hbase,hbad]

end SquaresInCircles.Six.Analytic

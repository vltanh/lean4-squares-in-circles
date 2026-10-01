import SquaresInCircles.Six.Normalization.CapSupport

/-!
# The support of a square with a lower bound on its radial offset

Let a square with chart `(a, b)` lie in the disk of squared radius `Q0`, with
`a + 1/2 ≥ l > 0`, so that its far corner `(A, B) = (a + 1/2, |b| + 1/2)` lies
in the part `A ≥ l` of the disk. For a unit force `(s, c)` with `s, c ≥ 0` and
`R0 s ≤ l`, the maximum of `s A + c B` on that part is at its corner
`(l, √(Q0 - l²))`, so the work `a s + b c` is at most
`(l - 1/2) s + (√(Q0 - l²) - 1/2) c`.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

lemma constrained_root_bounds {a b l : ℝ}
    (hl : 0<l) (ha : l≤a+1/2)
    (hbox : (a+1/2)^2+(|b|+1/2)^2≤Q0) :
    1/2≤Real.sqrt (Q0-l^2) ∧ (Real.sqrt (Q0-l^2))^2+l^2=Q0 := by
  have hA := mul_nonneg (sub_nonneg.mpr ha) (show 0≤a+1/2+l by linarith)
  have hrad : (1/2:ℝ)^2≤Q0-l^2 := by nlinarith [abs_nonneg b,sq_nonneg b]
  refine ⟨Real.le_sqrt_of_sq_le hrad,?_⟩
  have hs := Real.sq_sqrt (show 0≤Q0-l^2 by linarith)
  linarith

/-- If `R0 s ≤ l`, the work of the unit force `(s, c)` is at most its value at
the corner of the disk on the line `A = l`. -/
theorem circle_support_above_primary {a b l s c : ℝ}
    (hl : 0<l) (ha : l≤a+1/2)
    (hbox : (a+1/2)^2+(|b|+1/2)^2≤Q0)
    (hs : 0≤ s) (hc : 0≤c) (hu : s^2+c^2=1)
    (hbranch : R0*s≤l) :
    a*s+b*c≤(l-1/2)*s+(Real.sqrt (Q0-l^2)-1/2)*c := by
  let B := Real.sqrt (Q0-l^2)
  have hb := constrained_root_bounds hl ha hbox
  have hBpos : 0<B := by dsimp [B]; linarith [hb.1]
  have hcircle : B^2+l^2=Q0 := hb.2
  have hbranchSq := mul_nonneg (sub_nonneg.mpr hbranch)
    (show 0≤l+R0*s from add_nonneg hl.le (mul_nonneg R0_nonneg hs))
  have hidentity : (B*s)^2-(l*c)^2=(R0*s)^2-l^2 := by
    have h1 := congrArg (fun z : ℝ => s^2*z) hcircle
    have h2 := congrArg (fun z : ℝ => l^2*z) hu
    have h3 := congrArg (fun z : ℝ => s^2*z) R0_sq
    nlinarith only [h1,h2,h3]
  have hslope : B*s≤l*c := by
    by_contra! hbad
    have hp := mul_pos (sub_pos.mpr hbad)
      (show 0<B*s+l*c by nlinarith [mul_nonneg hl.le hc])
    nlinarith only [hp,hidentity,hbranchSq]
  have hcorner := disk_corner_support
    (A := |b|+1/2) (B := a+1/2) (a := B) (b := l) (c := c) (s := s)
    hBpos ha hc hcircle (by linarith) hslope
  have hbproj := mul_le_mul_of_nonneg_right (le_abs_self b) hc
  change a*s+b*c≤(l-1/2)*s+(B-1/2)*c
  nlinarith only [hcorner,hbproj]

end SquaresInCircles.Six.Analytic

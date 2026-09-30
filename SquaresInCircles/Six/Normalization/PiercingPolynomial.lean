import SquaresInCircles.Six.Normalization.Constants

/-!
# An algebraic replacement for the two-variable piercing leaf S5

The estimate deliberately enlarges the parameter rectangle to
`77/200 ≤ h ≤ 5/8`, `0 ≤ s ≤ 2/5`. Here `s` is a sine VALUE, not an angle.
It proves the obstruction used in K4(iv) after weakening `1/cos(t) ≥ 1`.
No interval certificate or sampled value is an assumption of these lemmas.
Compiler validation remains pending.
-/

noncomputable section
namespace SquaresInCircles.Six.Normalization

lemma piercing_polynomial_lower {h s : ℝ}
    (hh0 : 0 ≤ h) (hh : h ≤ 5 / 8) (hs0 : 0 ≤ s) (hs : s ≤ 2 / 5) :
    (h + 1) ^ 2 + 1 ≤
      (h + 1 + (1 - (h + 1 / 2) * s) * s) ^ 2 +
      (1 - (h + 1 / 2) * s) ^ 2 := by
  let H : ℝ := h + 1 / 2
  have hH0 : 0 ≤ H := by dsimp [H]; linarith
  have hH : H ≤ 9 / 8 := by dsimp [H]; linarith
  have hHsq := mul_nonneg (sub_nonneg.mpr hH)
    (show 0 ≤ (9 : ℝ) / 8 + H by linarith)
  have hHs : H + H ^ 2 ≤ 12 / 5 := by nlinarith
  have hssq : s ^ 2 ≤ 4 / 25 := by
    have hp := mul_nonneg (sub_nonneg.mpr hs)
      (show 0 ≤ (2 : ℝ) / 5 + s by linarith)
    nlinarith
  have hlin := mul_nonneg (show 0 ≤ 12 / 5 - H - H ^ 2 by linarith) hs0
  have hquad := mul_le_mul hH hssq (sq_nonneg s) (by norm_num : (0 : ℝ) ≤ 9 / 8)
  have hcubic : 0 ≤ H ^ 2 * s ^ 3 := mul_nonneg (sq_nonneg H) (pow_nonneg hs0 3)
  have hbracket : 0 ≤ 1 + (1 - H - H ^ 2) * s - 2 * H * s ^ 2 + H ^ 2 * s ^ 3 := by
    nlinarith
  have hfactor := mul_nonneg hs0 hbracket
  have hid :
      (h + 1 + (1 - (h + 1 / 2) * s) * s) ^ 2 +
          (1 - (h + 1 / 2) * s) ^ 2 - ((h + 1) ^ 2 + 1) =
        s * (1 + (1 - H - H ^ 2) * s - 2 * H * s ^ 2 + H ^ 2 * s ^ 3) := by
    dsimp [H]
    ring
  linarith

lemma piercing_polynomial_gt_ceiling {h s : ℝ}
    (hh0 : 77 / 200 ≤ h) (hh : h ≤ 5 / 8)
    (hs0 : 0 ≤ s) (hs : s ≤ 2 / 5) :
    Q0 < (h + 1 + (1 - (h + 1 / 2) * s) * s) ^ 2 +
      (1 - (h + 1 / 2) * s) ^ 2 := by
  have hp := piercing_polynomial_lower (by linarith : 0 ≤ h) hh hs0 hs
  have hm := mul_nonneg (sub_nonneg.mpr hh0)
    (show 0 ≤ h + 77 / 200 + 2 by linarith)
  norm_num [Q0] at *
  nlinarith

/-- K4(iv): the putative transverse failure contradicts disk containment.
`c` and `s` need only the displayed real inequalities, so this lemma also
records exactly which trigonometric facts the geometric application consumes. -/
theorem piercing_transverse_upper {a b h c s : ℝ}
    (hh0 : 77 / 200 ≤ h) (hh : h ≤ 5 / 8)
    (hc : c ≤ 1) (hs0 : 0 ≤ s) (hs : s ≤ 2 / 5)
    (ha : h + 1 / 2 ≤ a)
    (hbox : (a + 1 / 2) ^ 2 + (|b| + 1 / 2) ^ 2 ≤ Q0)
    (hcap : h + (c + s) / 2 ≤ a * c - b * s) :
    b < 1 / 2 - (h + 1 / 2) * s := by
  by_contra! hb
  let V : ℝ := 1 - (h + 1 / 2) * s
  have hprod := mul_le_mul (show h + 1 / 2 ≤ (9 : ℝ) / 8 by linarith)
    hs hs0 (by norm_num : (0 : ℝ) ≤ 9 / 8)
  have hV : 0 < V := by dsimp [V]; nlinarith
  have hb0 : 0 ≤ b := by nlinarith
  have hVb : V ≤ b + 1 / 2 := by dsimp [V]; linarith
  have hcprod := mul_nonneg
    (show 0 ≤ a - 1 / 2 by linarith) (show 0 ≤ 1 - c by linarith)
  have hVprod := mul_nonneg (sub_nonneg.mpr hVb) hs0
  have hnormal : h + 1 + V * s ≤ a + 1 / 2 := by nlinarith
  have hnormal0 : 0 ≤ h + 1 + V * s := by
    have hp := mul_nonneg hV.le hs0
    linarith
  have ha2 := mul_nonneg (sub_nonneg.mpr hnormal)
    (show 0 ≤ a + 1 / 2 + (h + 1 + V * s) by linarith)
  have hb2 := mul_nonneg (sub_nonneg.mpr hVb)
    (show 0 ≤ b + 1 / 2 + V by linarith)
  rw [abs_of_nonneg hb0] at hbox
  have hbad := piercing_polynomial_gt_ceiling hh0 hh hs0 hs
  change Q0 < (h + 1 + V * s) ^ 2 + V ^ 2 at hbad
  nlinarith

end SquaresInCircles.Six.Normalization

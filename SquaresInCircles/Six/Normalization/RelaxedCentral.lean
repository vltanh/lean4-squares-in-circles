module
public import SquaresInCircles.Six.Normalization.CentralSAT

@[expose] public section

/-!
# Central-coordinate relaxation used by the normalization certificates

Every relaxed margin is an upper bound on the actual margin throughout the
specified central box. It is a necessary condition only: different relaxed
axes need not share an extremizing center. This weakening is proved here and
cannot introduce an invalid exclusion of a genuine packing.
-/

noncomputable section
namespace SquaresInCircles.Six.Normalization

def linearLow (l h v : ℝ) : ℝ := min (l*v) (h*v)
def linearHigh (l h v : ℝ) : ℝ := max (l*v) (h*v)

lemma linearRange {l h x v : ℝ} (hx : l ≤ x ∧ x ≤ h) :
    linearLow l h v ≤ x*v ∧ x*v ≤ linearHigh l h v := by
  by_cases hv : 0 ≤ v
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_right hx.1 hv),
      (mul_le_mul_of_nonneg_right hx.2 hv).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_right hx.2 (le_of_not_ge hv)),
      (mul_le_mul_of_nonpos_right hx.1 (le_of_not_ge hv)).trans (le_max_left _ _)⟩

def centralUpper (k : CentralAxis) (t a b xl xh yl yh : ℝ) : ℝ :=
  match k with
  | .own => a-1/2-linearLow xl xh (Real.cos t)-linearLow yl yh (Real.sin t)-angularWidth t
  | .secPlus => b-1/2-linearLow xl xh (-Real.sin t)-linearLow yl yh (Real.cos t)-angularWidth t
  | .secMinus => linearHigh xl xh (-Real.sin t)+linearHigh yl yh (Real.cos t)-1/2-angularWidth t-b
  | .east => centerX t a b-angularWidth t-xl-1/2
  | .west => xh-1/2-centerX t a b-angularWidth t
  | .north => centerY t a b-angularWidth t-yl-1/2
  | .south => yh-1/2-centerY t a b-angularWidth t

lemma centralMargin_le_upper {t a b cx cy xl xh yl yh : ℝ}
    (hx : xl ≤ cx ∧ cx ≤ xh) (hy : yl ≤ cy ∧ cy ≤ yh) (k : CentralAxis) :
    centralMargin k t a b cx cy ≤ centralUpper k t a b xl xh yl yh := by
  have hxc := linearRange (v := Real.cos t) hx
  have hxs := linearRange (v := -Real.sin t) hx
  have hyc := linearRange (v := Real.cos t) hy
  have hys := linearRange (v := Real.sin t) hy
  cases k <;> dsimp [centralMargin,centralUpper,centralNormal,centralTransverse] <;>
    nlinarith [hxc.1,hxc.2,hxs.1,hxs.2,hyc.1,hyc.2,hys.1,hys.2,hx.1,hx.2,hy.1,hy.2]

lemma exists_upper_of_actual {t a b cx cy xl xh yl yh : ℝ}
    (hx : xl ≤ cx ∧ cx ≤ xh) (hy : yl ≤ cy ∧ cy ≤ yh)
    (h : ∃ k, 0 ≤ centralMargin k t a b cx cy) :
    ∃ k, 0 ≤ centralUpper k t a b xl xh yl yh := by
  obtain ⟨k,hk⟩ := h
  exact ⟨k,hk.trans (centralMargin_le_upper hx hy k)⟩

end SquaresInCircles.Six.Normalization

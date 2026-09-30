import SquaresInCircles.Six.Analytic.PinSymmetry
import SquaresInCircles.Six.Normalization.SecondarySeparation

/-!
# Geometric five-pin covering by primary sectors

The secondary central separators fail from the strong box and transverse
bound. In each primary quadrant the opposite cardinal is impossible and the
two adjacent cardinals would make the short axis face a deep cap. The remaining
OWN/cardinal alternatives give the pins already proved by ray interpolation or
the uniform two-pin argument. The N/S cases are exact diagonal images.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization Normalization.Certificates

abbrev CoreBox (x y : ℝ) : Prop := (0 ≤ x ∧ x ≤ c0) ∧ (0 ≤ y ∧ y ≤ c0)

lemma east_sector_pin {a b t x y : ℝ} (h : ContainedChart a |b|)
    (hcore : AvoidsCore a |b|) (ht : |t| ≤ Real.pi/4) (hbox : CoreBox x y)
    (hsep : ∃ k, 0 ≤ centralMargin k t a b x y) :
    openSquare (orientedSquare t a b) (fixedPin 0) := by
  have hsecondary := Normalization.secondary_separators_fail (h.u_le_U0 hcore)
    hbox.1.1 hbox.2.1 hbox.1.2 hbox.2.2 (t := t)
  have hprimary := primary_projection_nonneg h ht
  have hwidth : 0 ≤ angularWidth t := by dsimp [angularWidth]; positivity
  obtain ⟨k,hk⟩ := hsep
  cases k
  · have hp := east_own_fixed_pin h hcore ht hbox.1.1 hbox.2.1 hbox.1.2 hbox.2.2 hk
    simpa only [fixedPin,pinPoint,Real.cos_zero,Real.sin_zero,mul_one,mul_zero] using hp
  · exact False.elim ((not_le_of_gt hsecondary.1) hk)
  · exact False.elim ((not_le_of_gt hsecondary.2) hk)
  · have hp := east_cap_fixed_pin h ht
      (show 1/2 ≤ x+1/2 by linarith [hbox.1.1])
      (show x+1/2+angularWidth t ≤ centerX t a b by
        dsimp [centralMargin] at hk; linarith)
    simpa only [fixedPin,pinPoint,Real.cos_zero,Real.sin_zero,mul_one,mul_zero] using hp
  · dsimp [centralMargin,centerX] at hk
    have hx1 : x < 1/2 := hbox.1.2.trans_lt (by linarith [c0_lt_23_200])
    exact False.elim (by linarith)
  · apply False.elim
    apply transverse_cap_impossible h ht
      (show coreRadius ≤ y+1/2 by linarith [hbox.2.1,half_ge_core])
    dsimp [centralMargin,centerY] at hk
    linarith
  · apply False.elim
    apply negative_transverse_cap_impossible h ht
      (show coreRadius ≤ 1/2-y by linarith [hbox.2.2,c0_add_coreRadius])
    dsimp [centralMargin,centerY] at hk
    linarith

lemma west_sector_pins {a b t x y : ℝ} (h : ContainedChart a |b|)
    (hcore : AvoidsCore a |b|) (ht : |t| ≤ Real.pi/4) (hbox : CoreBox x y)
    (hsep : ∃ k, 0 ≤ centralMargin k (Real.pi+t) a b x y) :
    openSquare (orientedSquare (Real.pi+t) a b) (fixedPin 2) ∨
      openSquare (orientedSquare (Real.pi+t) a b) (fixedPin 3) := by
  have hsecondary := Normalization.secondary_separators_fail (h.u_le_U0 hcore)
    hbox.1.1 hbox.2.1 hbox.1.2 hbox.2.2 (t := Real.pi+t)
  have hprimary := primary_projection_nonneg h ht
  have hwidth : 0 ≤ angularWidth t := by dsimp [angularWidth]; positivity
  have hnormalwidth : angularWidth (Real.pi+t)=angularWidth t := by
    simp [angularWidth,Real.cos_pi_add,Real.sin_pi_add]
  have hpins : pinPoint (11*Real.pi/12)=fixedPin 2 ∧ pinPoint (5*Real.pi/4)=fixedPin 3 := by
    constructor <;> simp only [fixedPin_eq_polar,pinDirection]
  obtain ⟨k,hk⟩ := hsep
  cases k
  · simpa only [hpins.1,hpins.2] using west_own_fixed_pins h hcore ht hbox.1.2 hbox.2.1 hk
  · exact False.elim ((not_le_of_gt hsecondary.1) hk)
  · exact False.elim ((not_le_of_gt hsecondary.2) hk)
  · dsimp [centralMargin,centerX] at hk
    rw [hnormalwidth,Real.cos_pi_add,Real.sin_pi_add] at hk
    exact False.elim (by nlinarith [hbox.1.1])
  · have hcap : 1/2-x+angularWidth t ≤ centerX t a b := by
      dsimp [centralMargin,centerX] at hk ⊢
      rw [hnormalwidth,Real.cos_pi_add,Real.sin_pi_add] at hk
      nlinarith
    simpa only [hpins.1,hpins.2] using west_cap_fixed_pins h ht
      (show coreRadius ≤ 1/2-x by linarith [hbox.1.2,c0_add_coreRadius]) hcap
  · apply False.elim
    apply negative_transverse_cap_impossible h ht
      (show coreRadius ≤ y+1/2 by linarith [hbox.2.1,half_ge_core])
    dsimp [centralMargin,centerY] at hk
    rw [hnormalwidth,Real.cos_pi_add,Real.sin_pi_add] at hk
    nlinarith
  · apply False.elim
    apply transverse_cap_impossible h ht
      (show coreRadius ≤ 1/2-y by linarith [hbox.2.2,c0_add_coreRadius])
    dsimp [centralMargin,centerY] at hk
    rw [hnormalwidth,Real.cos_pi_add,Real.sin_pi_add] at hk
    nlinarith

lemma north_sector_pin {a b t x y : ℝ} (h : ContainedChart a |b|)
    (hcore : AvoidsCore a |b|) (ht : |t-Real.pi/2| ≤ Real.pi/4) (hbox : CoreBox x y)
    (hsep : ∃ k, 0 ≤ centralMargin k t a b x y) :
    openSquare (orientedSquare t a b) (fixedPin 1) := by
  have hr := separator_reflect hsep
  have hneg : ContainedChart a |-b| := by simpa only [abs_neg] using h
  have hav : AvoidsCore a |-b| := by simpa only [abs_neg] using hcore
  have ht' : |Real.pi/2-t| ≤ Real.pi/4 := by
    simpa only [abs_sub_comm] using ht
  have hp := east_sector_pin hneg hav ht' ⟨hbox.2,hbox.1⟩ hr
  have hh := (oriented_pin_reflect t a b (fixedPin 0)).mp hp
  simpa only [fixedPin_reflect,pinReflection] using hh

lemma south_sector_pins {a b t x y : ℝ} (h : ContainedChart a |b|)
    (hcore : AvoidsCore a |b|) (ht : |t+Real.pi/2| ≤ Real.pi/4) (hbox : CoreBox x y)
    (hsep : ∃ k, 0 ≤ centralMargin k t a b x y) :
    openSquare (orientedSquare t a b) (fixedPin 3) ∨
      openSquare (orientedSquare t a b) (fixedPin 4) := by
  have hr := separator_reflect hsep
  have hneg : ContainedChart a |-b| := by simpa only [abs_neg] using h
  have hav : AvoidsCore a |-b| := by simpa only [abs_neg] using hcore
  have ht' : |-(t+Real.pi/2)| ≤ Real.pi/4 := by simpa only [abs_neg] using ht
  have he : Real.pi+(-(t+Real.pi/2))=Real.pi/2-t := by ring
  have hp := west_sector_pins hneg hav ht' ⟨hbox.2,hbox.1⟩ (by simpa only [he] using hr)
  rw [he] at hp
  rcases hp with hw | hd
  · have hh := (oriented_pin_reflect t a b (fixedPin 2)).mp hw
    exact Or.inr (by simpa only [fixedPin_reflect,pinReflection] using hh)
  · have hh := (oriented_pin_reflect t a b (fixedPin 3)).mp hd
    exact Or.inl (by simpa only [fixedPin_reflect,pinReflection] using hh)

/-- Every exterior chart in the proved strong box contains a fixed pin.
No Boolean computation or opaque cover assumption is an input. -/
theorem five_pin_cover {a b t x y : ℝ} (h : ContainedChart a |b|)
    (hcore : AvoidsCore a |b|) (ht : |t| ≤ Real.pi) (hbox : CoreBox x y)
    (hsep : ∃ k, 0 ≤ centralMargin k t a b x y) :
    ∃ i : Fin 5, openSquare (orientedSquare t a b) (fixedPin i) := by
  have htr := abs_le.mp ht
  by_cases hSW : t ≤ -3*Real.pi/4
  · have hv : |t+Real.pi| ≤ Real.pi/4 := by
      apply abs_le.mpr
      constructor <;> linarith [htr.1]
    have he : Real.pi+(t+Real.pi)=t+2*Real.pi := by ring
    have hs := separator_periodic hsep
    have hp := west_sector_pins h hcore hv hbox (by simpa only [he] using hs)
    rw [he] at hp
    rcases hp with hp | hp
    · exact ⟨2,(oriented_pin_periodic t a b _).mp hp⟩
    · exact ⟨3,(oriented_pin_periodic t a b _).mp hp⟩
  by_cases hS : t ≤ -Real.pi/4
  · have hv : |t+Real.pi/2| ≤ Real.pi/4 := by
      apply abs_le.mpr
      constructor <;> linarith
    rcases south_sector_pins h hcore hv hbox hsep with hp | hp
    · exact ⟨3,hp⟩
    · exact ⟨4,hp⟩
  by_cases hE : t ≤ Real.pi/4
  · exact ⟨0,east_sector_pin h hcore (abs_le.mpr ⟨by linarith,hE⟩) hbox hsep⟩
  by_cases hN : t ≤ 3*Real.pi/4
  · have hv : |t-Real.pi/2| ≤ Real.pi/4 := by
      apply abs_le.mpr
      constructor <;> linarith
    exact ⟨1,north_sector_pin h hcore hv hbox hsep⟩
  · have hv : |t-Real.pi| ≤ Real.pi/4 := by
      apply abs_le.mpr
      constructor <;> linarith [htr.2,Real.pi_pos]
    have he : Real.pi+(t-Real.pi)=t := by ring
    rcases west_sector_pins h hcore hv hbox (by simpa only [he] using hsep) with hp | hp
    · exact ⟨2,by simpa only [he] using hp⟩
    · exact ⟨3,by simpa only [he] using hp⟩

end SquaresInCircles.Six.Analytic

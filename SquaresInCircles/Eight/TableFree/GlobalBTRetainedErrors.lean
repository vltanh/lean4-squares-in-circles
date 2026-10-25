module

public import SquaresInCircles.Eight.TableFree.GlobalBTErrorComparisons
public import SquaresInCircles.Eight.TableFree.GlobalAllHighNegativeOuter

/-!
# Retaining exactly the original negative tail errors

Positive errors are removed only inside dual expressions.  A negative
outer-target DE3 projection is dominated by DE2 on the same original
states; no geometric frame or feasible representative is replaced.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalBT

open FramePair FrameCircleArc GlobalOuterAnchor GlobalZeroSign

def quarterDual (s t : State) (j : Fin 4) (d lambda : ℝ) : ℝ :=
  d+lambda*(GlobalOuterAnchor.width d-projection true s t d j)

theorem negative_part_range {d : ℝ} (hd : |d|≤frameCap) :
    max (-d) 0∈Icc 0 frameCap := by
  exact ⟨le_max_right _ _,max_le ((neg_le_abs d).trans hd) (by norm_num [frameCap])⟩

theorem retained_of_nonnegative {d : ℝ} (hd : 0≤d) : retainedNegative d=0 := by
  simp [retainedNegative,max_eq_right (by linarith : -d≤0)]

theorem retained_of_nonpositive {d : ℝ} (hd : d≤0) : retainedNegative d=d := by
  simp [retainedNegative,max_eq_left (by linarith : 0≤-d)]

theorem zeroDual_zero (s t : State) (primary : Bool) (lambda : ℝ) :
    zeroDual primary s t 0 lambda=lambda*(1-transverse s+transverse t) := by
  have hw : GlobalOuterAnchor.width 0=1 := by norm_num [GlobalOuterAnchor.width]
  have hp : projection false s t 0 (leftOwner primary)=transverse s-transverse t := by
    cases primary <;> simp [projection,leftOwner]
  rw [zeroDual,hw,hp]
  ring

theorem quarterDual_zero (s t : State) (j : Fin 4) (lambda : ℝ) :
    quarterDual s t j 0 lambda=lambda*(1-projection true s t 0 j) := by
  simp [quarterDual,GlobalOuterAnchor.width]

theorem retain_zero (s t : State) (primary : Bool) {d lambda : ℝ}
    (hd : |d|≤frameCap) (hl : 0≤lambda) (hlu : lambda≤kappa) :
    zeroDual primary s t (retainedNegative d) lambda≤zeroDual primary s t d lambda := by
  rcases le_total 0 d with hp | hn
  · rw [retained_of_nonnegative hp,zeroDual_zero]
    exact positive_zero_delete s t primary hl hlu ⟨hp,(le_abs_self d).trans hd⟩
  · rw [retained_of_nonpositive hn]

theorem retain_BT0 (s t : State) {d lambda : ℝ}
    (hd : |d|≤frameCap) (hl : 0≤lambda) (hlu : lambda≤kappa) :
    quarterDual s t 0 (retainedNegative d) lambda≤quarterDual s t 0 d lambda := by
  rcases le_total 0 d with hp | hn
  · rw [retained_of_nonnegative hp,quarterDual_zero]
    exact positive_BT0_delete s t hl hlu ⟨hp,(le_abs_self d).trans hd⟩
  · rw [retained_of_nonpositive hn]

theorem retain_DE2 (s t : State) {d lambda : ℝ}
    (hd : |d|≤frameCap) (hl : 0≤lambda) (hlu : lambda≤kappa) :
    quarterDual s t 2 (retainedNegative d) lambda≤quarterDual s t 2 d lambda := by
  rcases le_total 0 d with hp | hn
  · rw [retained_of_nonnegative hp,quarterDual_zero]
    exact positive_DE2_delete s t hl hlu ⟨hp,(le_abs_self d).trans hd⟩
  · rw [retained_of_nonpositive hn]

theorem negative_DE3_projection (s t : State)
    (hs : transverse s≤0) (ht : transverse t≤0) (htOuter : t.branch.type≠0)
    {z : ℝ} (hz : z∈Icc 0 frameCap) :
    projection true s t (-z) 3≤projection true s t (-z) 2 := by
  have hh := GlobalAllHigh.negative_outer_projection_comparison s t htOuter hz
  have hsy : transverse s= -s.b := transverse_nonpos_eq s hs
  have hty : transverse t= -t.b := transverse_nonpos_eq t ht
  dsimp [projection]
  rw [hsy,hty]
  simp only [Real.cos_neg,Real.sin_neg]
  linarith only [hh]

theorem retain_DE3 (s t : State) {d lambda : ℝ}
    (hs : transverse s≤0) (ht : transverse t≤0)
    (hd : |d|≤frameCap) (hl : 0≤lambda) (hlu : lambda≤kappa)
    (hordinary : 0≤d ∨ t.branch.type≠0) :
    quarterDual s t 2 (retainedNegative d) lambda≤quarterDual s t 3 d lambda := by
  rcases le_total 0 d with hp | hn
  · rw [retained_of_nonnegative hp,quarterDual_zero]
    exact positive_DE3_delete s t hl hlu ⟨hp,(le_abs_self d).trans hd⟩
  · by_cases hz : d=0
    · subst d
      simp [retainedNegative,quarterDual,projection,GlobalOuterAnchor.width]
    · have htOuter : t.branch.type≠0 := by
        rcases hordinary with hp | ho
        · exact False.elim (hz (le_antisymm hn hp))
        · exact ho
      have hp := negative_DE3_projection s t hs ht htOuter
        (show -d∈Icc 0 frameCap from ⟨by linarith,(neg_le_abs d).trans hd⟩)
      simp only [neg_neg] at hp
      have hm := mul_le_mul_of_nonneg_left hp hl
      rw [retained_of_nonpositive hn]
      dsimp [quarterDual]
      linarith

/-- This includes both owners at zero and all original DE2 witnesses;
only a strictly negative DE3 with core E belongs to the separate tail. -/
theorem retain_DE (s t : State) (j : Fin 4) {d lambda : ℝ}
    (hs : transverse s≤0) (ht : transverse t≤0) (hj : j=2 ∨ j=3)
    (hd : |d|≤frameCap) (hl : 0≤lambda) (hlu : lambda≤kappa)
    (hordinary : j=2 ∨ 0≤d ∨ t.branch.type≠0) :
    quarterDual s t 2 (retainedNegative d) lambda≤quarterDual s t j d lambda := by
  rcases hj with rfl | rfl
  · exact retain_DE2 s t hd hl hlu
  · apply retain_DE3 s t hs ht hd hl hlu
    rcases hordinary with hh | hh
    · norm_num at hh
    · exact hh

end SquaresInCircles.Eight.TableFree.GlobalBT

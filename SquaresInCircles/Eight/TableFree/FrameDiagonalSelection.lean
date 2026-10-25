module

public import SquaresInCircles.Eight.TableFree.FrameDiagonalTrigonometry

/-!
# Endpoint selection on the closed diagonal arcs

These calculus lemmas retain the actual arc point.  They do not replace
it by a contact state or choose a new separating axis.  Concavity keeps
both endpoint alternatives, including equality at an intrinsic cut.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameDiagonalSelection
open FramePair FrameDiagonalArc FrameDiagonalLabels FrameDiagonalSupport
open FrameDiagonalCuts

theorem source_first_of_derivative {m i : Bool} {lam b : ℝ}
    (hb : b∈arc m)
    (hd : ∀ z∈arc m, 0≤-sourceU m i lam*slope z+sourceV m i lam) :
    source m i lam (first m)≤ source m i lam b := by
  have hmono : MonotoneOn (source m i lam) (Icc (first m) (last m)) := by
    apply monoOn_of_hasDeriv_nonneg
    · intro z hz
      exact (FrameDiagonalSupport.source_deriv m i lam
        (by simpa only [arc_eq] using hz)).continuousAt.continuousWithinAt
    · intro z hz
      exact FrameDiagonalSupport.source_deriv m i lam
        (by simpa only [arc_eq] using Ioo_subset_Icc_self hz)
    · intro z hz
      exact hd z (by simpa only [arc_eq] using Ioo_subset_Icc_self hz)
  have hb' : b∈Icc (first m) (last m) := by simpa only [arc_eq] using hb
  exact hmono ⟨le_rfl,hb'.1.trans hb'.2⟩ hb' hb'.1

theorem source_last_of_derivative {m i : Bool} {lam b : ℝ}
    (hb : b∈arc m)
    (hd : ∀ z∈arc m, -sourceU m i lam*slope z+sourceV m i lam≤0) :
    source m i lam (last m)≤ source m i lam b := by
  have hanti : AntitoneOn (source m i lam) (Icc (first m) (last m)) := by
    apply antiOn_of_hasDeriv_nonpos
    · intro z hz
      exact (FrameDiagonalSupport.source_deriv m i lam
        (by simpa only [arc_eq] using hz)).continuousAt.continuousWithinAt
    · intro z hz
      exact FrameDiagonalSupport.source_deriv m i lam
        (by simpa only [arc_eq] using Ioo_subset_Icc_self hz)
    · intro z hz
      exact hd z (by simpa only [arc_eq] using Ioo_subset_Icc_self hz)
  have hb' : b∈Icc (first m) (last m) := by simpa only [arc_eq] using hb
  exact hanti hb' ⟨hb'.1.trans hb'.2,le_rfl⟩ hb'.2

theorem target_first_of_derivative {n j : Bool} {lam x B : ℝ}
    (hB : B∈arc n)
    (hd : ∀ z∈arc n, 0≤-targetU n j lam x*slope z+targetV n j lam x) :
    target n j lam x (first n)≤target n j lam x B := by
  have hmono : MonotoneOn (target n j lam x) (Icc (first n) (last n)) := by
    apply monoOn_of_hasDeriv_nonneg
    · intro z hz
      exact (FrameDiagonalSupport.target_deriv n j lam x
        (by simpa only [arc_eq] using hz)).continuousAt.continuousWithinAt
    · intro z hz
      exact FrameDiagonalSupport.target_deriv n j lam x
        (by simpa only [arc_eq] using Ioo_subset_Icc_self hz)
    · intro z hz
      exact hd z (by simpa only [arc_eq] using Ioo_subset_Icc_self hz)
  have hB' : B∈Icc (first n) (last n) := by simpa only [arc_eq] using hB
  exact hmono ⟨le_rfl,hB'.1.trans hB'.2⟩ hB' hB'.1

theorem target_last_of_derivative {n j : Bool} {lam x B : ℝ}
    (hB : B∈arc n)
    (hd : ∀ z∈arc n, -targetU n j lam x*slope z+targetV n j lam x≤0) :
    target n j lam x (last n)≤target n j lam x B := by
  have hanti : AntitoneOn (target n j lam x) (Icc (first n) (last n)) := by
    apply antiOn_of_hasDeriv_nonpos
    · intro z hz
      exact (FrameDiagonalSupport.target_deriv n j lam x
        (by simpa only [arc_eq] using hz)).continuousAt.continuousWithinAt
    · intro z hz
      exact FrameDiagonalSupport.target_deriv n j lam x
        (by simpa only [arc_eq] using Ioo_subset_Icc_self hz)
    · intro z hz
      exact hd z (by simpa only [arc_eq] using Ioo_subset_Icc_self hz)
  have hB' : B∈Icc (first n) (last n) := by simpa only [arc_eq] using hB
  exact hanti hB' ⟨hB'.1.trans hB'.2,le_rfl⟩ hB'.2

theorem source_endpoints {m i : Bool} {lam b : ℝ} (hb : b∈arc m)
    (hU : 0≤ sourceU m i lam) :
    min (source m i lam (first m)) (source m i lam (last m))≤ source m i lam b := by
  apply linear_endpoint_lower hU
    (arc_subset (first_mem m)).1 (arc_subset (last_mem m)).2
  simpa only [arc_eq] using hb

theorem target_endpoints {n j : Bool} {lam x B : ℝ} (hB : B∈arc n)
    (hU : 0≤targetU n j lam x) :
    min (target n j lam x (first n)) (target n j lam x (last n))≤
      target n j lam x B := by
  apply linear_endpoint_lower hU
    (arc_subset (first_mem n)).1 (arc_subset (last_mem n)).2
  simpa only [arc_eq] using hB

theorem source_first_of_coefficients {m i : Bool} {lam b : ℝ}
    (hb : b∈arc m) (hU : sourceU m i lam≤0) (hV : 0≤ sourceV m i lam) :
    source m i lam (first m)≤ source m i lam b := by
  have hb' : b∈Icc (first m) (last m) := by simpa only [arc_eq] using hb
  exact linear_monotone hU hV (arc_subset (first_mem m)) (arc_subset hb) hb'.1

theorem target_first_of_coefficients {n j : Bool} {lam x B : ℝ}
    (hB : B∈arc n) (hU : targetU n j lam x≤0) (hV : 0≤targetV n j lam x) :
    target n j lam x (first n)≤target n j lam x B := by
  have hB' : B∈Icc (first n) (last n) := by simpa only [arc_eq] using hB
  exact linear_monotone hU hV (arc_subset (first_mem n)) (arc_subset hB) hB'.1

theorem target_last_of_coefficients {n j : Bool} {lam x B : ℝ}
    (hB : B∈arc n) (hU : 0≤targetU n j lam x) (hV : targetV n j lam x≤0) :
    target n j lam x (last n)≤target n j lam x B := by
  apply target_last_of_derivative hB
  intro z hz
  have hp := mul_nonneg hU (slope_bounds (arc_subset hz)).1
  linarith

theorem target_endpoints_of_one_coefficient {n j : Bool} {lam x B : ℝ}
    (hB : B∈arc n) (hUV : 0≤targetU n j lam x ∨ 0≤targetV n j lam x) :
    min (target n j lam x (first n)) (target n j lam x (last n))≤
      target n j lam x B := by
  by_cases hU : 0≤targetU n j lam x
  · exact target_endpoints hB hU
  · have hV := hUV.resolve_left hU
    exact (min_le_left _ _).trans
      (target_first_of_coefficients hB (lt_of_not_ge hU).le hV)

end SquaresInCircles.Eight.TableFree.FrameDiagonalSelection

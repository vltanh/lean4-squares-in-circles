module

public import SquaresInCircles.Eight.TableFree.EndpointPrinciples
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Feasible-contact continuation without an assumed feasible path

Uncompiled draft. The first theorem handles a derivative estimate proved
only at feasible points. A maximum on a compact interval and its left
inward tangent rule out a first loss of feasibility. The second theorem
handles a derivative whose sign changes only from negative to positive;
no interior root or subdivision is chosen.
-/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace SquaresInCircles.Eight.TableFree

/-- At a maximum that is not the left endpoint, a negative derivative is
impossible. The derivative at the right endpoint is included. -/
theorem not_negative_at_rightward_maximum {f : ℝ → ℝ} {a b m d : ℝ}
    (hm : m∈Icc a b) (ham : a< m)
    (hmax : IsMaxOn f (Icc a b) m) (hd : HasDerivAt f d m) : 0≤d := by
  have ha : a∈Icc a b := ⟨le_rfl,hm.1.trans hm.2⟩
  have hsegment : segment ℝ m a ⊆ Icc a b :=
    (convex_Icc a b).segment_subset hm ha
  have hcone := sub_mem_posTangentConeAt_of_segment_subset hsegment
  have hlocal : IsLocalMaxOn f (Icc a b) m := hmax.isLocalMaxOn
  have h := hlocal.hasFDerivWithinAt_nonpos
    hd.hasFDerivAt.hasFDerivWithinAt hcone
  have hproduct : d*(a-m)≤0 := by simpa [mul_comm] using h
  by_contra! hn
  have hp := mul_pos_of_neg_of_neg hn (sub_neg.mpr ham)
  linarith

/-- Negative derivative at every feasible point forces strict improvement
when moving left from a feasible right endpoint. Feasibility on the path
is a conclusion, not a premise. -/
theorem feasible_left_continuation {f df : ℝ → ℝ} {l u b : ℝ}
    (hc : ContinuousOn f (Icc l u))
    (hd : ∀x∈Icc l u, HasDerivAt f (df x) x)
    (hneg : ∀x∈Icc l u, b≤f x → df x<0)
    (hu : b≤f u) :
    ∀x∈Ico l u, f u<f x := by
  intro x hx
  by_contra! hbad
  have hsub : Icc x u ⊆ Icc l u := Icc_subset_Icc hx.1 le_rfl
  have hcont := hc.mono hsub
  obtain ⟨m,hm,hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc x u).Nonempty from ⟨u,⟨hx.2.le,le_rfl⟩⟩) hcont
  have hum : f u≤f m := hmax ⟨hx.2.le,le_rfl⟩
  by_cases hxm : x< m
  · have hnn := not_negative_at_rightward_maximum hm hxm hmax (hd m (hsub hm))
    have hn := hneg m (hsub hm) (hu.trans hum)
    linarith
  · have hmx : m=x := le_antisymm (le_of_not_gt hxm) hm.1
    have hmaxu : IsMaxOn f (Icc x u) u := by
      intro y hy
      have hymax := hmax hy
      rw [hmx] at hymax
      exact hymax.trans hbad
    have hnn := not_negative_at_rightward_maximum
      (show u∈Icc x u from ⟨hx.2.le,le_rfl⟩) hx.2 hmaxu
      (hd u ⟨hx.1.trans hx.2.le,le_rfl⟩)
    have hn := hneg u ⟨hx.1.trans hx.2.le,le_rfl⟩ hu
    linarith

/-- After continuation has established feasibility, the derivative reserve
integrates on the entire motion interval. -/
theorem feasible_left_reserve {f df : ℝ → ℝ} {l u b k : ℝ}
    (hlu : l≤u) (hk : 0<k)
    (hc : ContinuousOn f (Icc l u))
    (hd : ∀x∈Icc l u, HasDerivAt f (df x) x)
    (hneg : ∀x∈Icc l u, b≤f x → df x≤ -k)
    (hu : b≤f u) :
    ∀x∈Icc l u, b≤f x ∧ k*(u-x)≤f x-f u := by
  have hstrict := feasible_left_continuation hc hd
    (fun x hx hfx => lt_of_le_of_lt (hneg x hx hfx) (by linarith)) hu
  have hfeas (x : ℝ) (hx : x∈Icc l u) : b≤f x := by
    rcases lt_or_eq_of_le hx.2 with hxlt | rfl
    · exact hu.trans (hstrict x ⟨hx.1,hxlt⟩).le
    · exact hu
  intro x hx
  refine ⟨hfeas x hx,?_⟩
  have hr := derivative_reserve (f := fun y => -f y)
    (df := fun y => -df y) (k := k) hc.neg
    (fun y hy => (hd y (Ioo_subset_Icc_self hy)).neg)
    (fun y hy => by
      have hh := hneg y (Ioo_subset_Icc_self hy)
        (hfeas y (Ioo_subset_Icc_self hy))
      linarith)
    hx (show u∈Icc l u from ⟨hlu,le_rfl⟩) hx.2
  linarith

/-- A derivative with an increasing sign-control function cannot have an
interior maximum above both endpoint values. No zero of the control
function is assumed to exist. -/
theorem valley_endpoint_bound {f df control : ℝ → ℝ} {l u x : ℝ}
    (hx : x∈Icc l u) (hc : ContinuousOn f (Icc l u))
    (hd : ∀y∈Ioo l u, HasDerivAt f (df y) y)
    (hmono : MonotoneOn control (Icc l u))
    (hnegative : ∀y∈Ioo l u, control y≤0 → df y≤0)
    (hpositive : ∀y∈Ioo l u, 0≤control y → 0≤df y) :
    f x≤ max (f l) (f u) := by
  rcases le_total (control x) 0 with hxneg | hxpos
  · have hanti : AntitoneOn f (Icc l x) := by
      apply antiOn_of_hasDeriv_nonpos
      · exact hc.mono (Icc_subset_Icc le_rfl hx.2)
      · intro y hy
        exact hd y ⟨hy.1,hy.2.trans_le hx.2⟩
      · intro y hy
        have hyleft : y∈Icc l u := ⟨hy.1.le,hy.2.le.trans hx.2⟩
        exact hnegative y ⟨hy.1,hy.2.trans_le hx.2⟩
          ((hmono hyleft hx hy.2.le).trans hxneg)
    exact (hanti ⟨le_rfl,hx.1⟩ ⟨hx.1,le_rfl⟩ hx.1).trans (le_max_left _ _)
  · have hmonof : MonotoneOn f (Icc x u) := by
      apply monoOn_of_hasDeriv_nonneg
      · exact hc.mono (Icc_subset_Icc hx.1 le_rfl)
      · intro y hy
        exact hd y ⟨hx.1.trans_lt hy.1,hy.2⟩
      · intro y hy
        have hyright : y∈Icc l u := ⟨hx.1.trans hy.1.le,hy.2.le⟩
        exact hpositive y ⟨hx.1.trans_lt hy.1,hy.2⟩
          (hxpos.trans (hmono hx hyright hy.1.le))
    exact (hmonof ⟨le_rfl,hx.2⟩ ⟨hx.2,le_rfl⟩ hx.2).trans (le_max_right _ _)

end SquaresInCircles.Eight.TableFree
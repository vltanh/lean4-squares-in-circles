module

public import SquaresInCircles.Eight.TableFree.FramePairCalculus

/-!
# An endpoint principle from the shape of the second derivative

A concave second derivative which starts nonnegative permits the first
derivative to turn only from positive to negative after its initial
increase.  The resulting endpoint minimum is proved without choosing a
critical point or subdividing an angle interval.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FramePairShape
open FramePairCalculus

theorem endpoint_minimum_of_concave_second {f d e : ℝ → ℝ} {l u x : ℝ}
    (hx : x∈Icc l u) (hd : ∀t∈Icc l u,HasDerivAt f (d t) t)
    (he : ∀t∈Icc l u,HasDerivAt d (e t) t)
    (hc : ConcaveOn ℝ (Icc l u) e) (hel : 0≤e l) (hdl : 0≤d l) :
    min (f l) (f u)≤f x := by
  have hmin {v t : ℝ} (hv : v∈Icc l u) (ht : t∈Icc l v) :
      min (d l) (d v)≤d t := by
    apply endpoint_minimum_of_concave_derivative ht
      (fun z hz => he z ⟨hz.1,hz.2.trans hv.2⟩)
      (hc.subset (Icc_subset_Icc le_rfl hv.2) (convex_Icc _ _)) hel
  by_cases hdx : 0≤d x
  · have hm : MonotoneOn f (Icc l x) := by
      apply monoOn_of_hasDeriv_nonneg
      · exact fun t ht => (hd t ⟨ht.1,ht.2.trans hx.2⟩).continuousAt.continuousWithinAt
      · exact fun t ht => hd t ⟨ht.1.le,ht.2.le.trans hx.2⟩
      · intro t ht
        exact (le_min hdl hdx).trans (hmin hx (Ioo_subset_Icc_self ht))
    exact (min_le_left _ _).trans (hm ⟨le_rfl,hx.1⟩ ⟨hx.1,le_rfl⟩ hx.1)
  · have hm : AntitoneOn f (Icc x u) := by
      apply antiOn_of_hasDeriv_nonpos
      · exact fun t ht => (hd t ⟨hx.1.trans ht.1,ht.2⟩).continuousAt.continuousWithinAt
      · exact fun t ht => hd t ⟨hx.1.trans ht.1.le,ht.2.le⟩
      · intro t ht
        by_contra! hdt
        have hh := hmin ⟨hx.1.trans ht.1.le,ht.2.le⟩ ⟨hx.1,ht.1.le⟩
        exact hdx ((le_min hdl hdt.le).trans hh)
    exact (min_le_right _ _).trans (hm ⟨le_rfl,hx.2⟩ ⟨hx.2,le_rfl⟩ hx.2)

end SquaresInCircles.Eight.TableFree.FramePairShape

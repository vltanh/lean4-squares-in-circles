module

public import SquaresInCircles.Common.Analysis

/-!
# Endpoint minima from an increasing second derivative

If the first derivative is convex and negative at the right endpoint,
the value cannot have an interior minimum below both endpoint values.
The proof splits on the actual derivative at the queried point and
uses monotonicity on the resulting two subintervals.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.MinimumCalculus

theorem endpoint_minimum {f d dd ddd : ℝ→ℝ} {l u x : ℝ}
    (hx : x∈Icc l u)
    (hf : ∀ t∈Icc l u, HasDerivAt f (d t) t)
    (hd : ∀ t∈Icc l u, HasDerivAt d (dd t) t)
    (hdd : ∀ t∈Icc l u, HasDerivAt dd (ddd t) t)
    (hthird : ∀ t∈Icc l u, 0≤ddd t)
    (hright : d u<0) : min (f l) (f u)≤f x := by
  have hmono : MonotoneOn dd (Icc l u) := monoOn_of_hasDeriv_nonneg
    (fun t ht => (hdd t ht).continuousAt.continuousWithinAt)
    (fun t ht => hdd t (Ioo_subset_Icc_self ht))
    (fun t ht => hthird t (Ioo_subset_Icc_self ht))
  have hconcave : ConcaveOn ℝ (Icc l u) (fun t => -d t) :=
    concave_of_deriv2
      (fun t ht => (hd t ht).neg)
      (fun t ht => (hdd t ht).neg)
      (fun t ht => neg_nonpos.mpr (hthird t ht))
  by_cases hdx : d x≤0
  · have hdom {t : ℝ} (ht : t∈Icc x u) : t∈Icc l u :=
      ⟨hx.1.trans ht.1,ht.2⟩
    have hdnegative {t : ℝ} (ht : t∈Icc x u) : d t≤0 := by
      have hm := hconcave.min_le_of_mem_Icc hx ⟨hx.1.trans hx.2,le_rfl⟩ ht
      have hmin : 0≤min (-d x) (-d u) := by
        exact le_min (neg_nonneg.mpr hdx) (neg_nonneg.mpr hright.le)
      linarith
    have hanti : AntitoneOn f (Icc x u) := antiOn_of_hasDeriv_nonpos
      (fun t ht => (hf t (hdom ht)).continuousAt.continuousWithinAt)
      (fun t ht => hf t (hdom (Ioo_subset_Icc_self ht)))
      (fun t ht => hdnegative (Ioo_subset_Icc_self ht))
    exact (min_le_right _ _).trans
      (hanti ⟨le_rfl,hx.2⟩ ⟨hx.2,le_rfl⟩ hx.2)
  · have hdpositive : 0<d x := lt_of_not_ge hdx
    have hddnegative : dd x<0 := by
      by_contra hbad
      have hnonneg : 0≤dd x := le_of_not_gt hbad
      have hdom {t : ℝ} (ht : t∈Icc x u) : t∈Icc l u :=
        ⟨hx.1.trans ht.1,ht.2⟩
      have hM : MonotoneOn d (Icc x u) := monoOn_of_hasDeriv_nonneg
        (fun t ht => (hd t (hdom ht)).continuousAt.continuousWithinAt)
        (fun t ht => hd t (hdom (Ioo_subset_Icc_self ht)))
        (fun t ht => hnonneg.trans (hmono hx (hdom (Ioo_subset_Icc_self ht)) ht.1.le))
      have hh := hM ⟨le_rfl,hx.2⟩ ⟨hx.2,le_rfl⟩ hx.2
      linarith
    have hdom {t : ℝ} (ht : t∈Icc l x) : t∈Icc l u :=
      ⟨ht.1,ht.2.trans hx.2⟩
    have hanti : AntitoneOn d (Icc l x) := antiOn_of_hasDeriv_nonpos
      (fun t ht => (hd t (hdom ht)).continuousAt.continuousWithinAt)
      (fun t ht => hd t (hdom (Ioo_subset_Icc_self ht)))
      (fun t ht => (hmono (hdom (Ioo_subset_Icc_self ht)) hx ht.2.le).trans hddnegative.le)
    have hM : MonotoneOn f (Icc l x) := monoOn_of_hasDeriv_nonneg
      (fun t ht => (hf t (hdom ht)).continuousAt.continuousWithinAt)
      (fun t ht => hf t (hdom (Ioo_subset_Icc_self ht)))
      (fun t ht => hdpositive.le.trans
        (hanti (Ioo_subset_Icc_self ht) ⟨hx.1,le_rfl⟩ ht.2.le))
    exact (min_le_left _ _).trans
      (hM ⟨le_rfl,hx.1⟩ ⟨hx.1,le_rfl⟩ hx.1)

end SquaresInCircles.Eight.TableFree.SecondWord.MinimumCalculus

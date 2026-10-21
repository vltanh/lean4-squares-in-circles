module

public import SquaresInCircles.Eight.TableFree.SecondOuterLabelCalculus
public import SquaresInCircles.Eight.TableFree.SecondOuterReferenceTrig

/-!
# Exact products at named analytic reference points

The bilinear enclosure follows twice from the elementary affine
endpoint inequality.  It is used only to combine exact rational
coefficient and Taylor brackets at the fixed analytic references.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.PointProducts

open Arithmetic ReferenceTrig

lemma product {x y xl xu yl yu : ℝ} (hx : x∈Icc xl xu) (hy : y∈Icc yl yu) :
    x*y∈Icc (min (min (xl*yl) (xl*yu)) (min (xu*yl) (xu*yu)))
      (max (max (xl*yl) (xl*yu)) (max (xu*yl) (xu*yu))) := by
  have hxlo : min (xl*y) (xu*y)≤x*y := by
    simpa only [mul_comm] using affine_min_le (c := y) hx
  have hxhi : x*y≤max (xl*y) (xu*y) := by
    simpa only [mul_comm] using affine_le_max (c := y) hx
  exact ⟨(min_le_min (affine_min_le (c := xl) hy)
    (affine_min_le (c := xu) hy)).trans hxlo,
    hxhi.trans (max_le_max (affine_le_max (c := xl) hy)
      (affine_le_max (c := xu) hy))⟩

lemma trig {t : ℝ} (ht : 0≤t) :
    Real.sin t∈Icc (sin11 t) (sin9 t) ∧
      Real.cos t∈Icc (cos10 t) (cos12 t) :=
  ⟨⟨sin11_le_sin ht,sin_le_sin9 ht⟩,⟨cos10_le_cos ht,cos_le_cos12 ht⟩⟩

end SquaresInCircles.Eight.TableFree.SecondWord.PointProducts

module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeThreeLowerFirstReference

/-!
# The full convex rectangle at the first lower-secondary contact

Two tangent parabolas and the uniform mixed derivative bound give a
two-coordinate lower bound.  Both tangents use the same named interior
reference and every segment stays in the original rectangle.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.LowerFirst
open CommonQuarter CorePairGeometry Arithmetic
open LowerContact LowerGeometry LowerInverse

lemma first_outer_lipschitz {b u v : ℝ} (hb : b∈Icc 0 (1/10))
    (hu : u∈Icc 0 (2/5)) (hv : v∈Icc 0 (2/5)) :
    |freeFirst false b u-freeFirst false b v|≤(1/2:ℝ)*|u-v| := by
  have hb' : b∈Icc 0 (83/200) := ⟨hb.1,by linarith [hb.2]⟩
  have hd {y : ℝ} (hy : y∈Icc 0 (2/5)) :=
    freeFirst_outer_hasDerivAt false (full_domain ⟨hy.1,by linarith [hy.2]⟩)
      (short_shift hb')
  have hp {y : ℝ} (hy : y∈Icc 0 (2/5)) :
      HasDerivAt (fun t => freeFirst false b t+(1/2)*t) (mixed b y+1/2) y :=
    ((hd hy).fun_add ((hasDerivAt_id' y).const_mul (1/2))).congr_deriv (by ring)
  have hm {y : ℝ} (hy : y∈Icc 0 (2/5)) :
      HasDerivAt (fun t => freeFirst false b t-(1/2)*t) (mixed b y-1/2) y :=
    ((hd hy).fun_sub ((hasDerivAt_id' y).const_mul (1/2))).congr_deriv (by ring)
  have hplus : MonotoneOn (fun t => freeFirst false b t+(1/2)*t) (Icc 0 (2/5)) :=
    monoOn_of_hasDeriv_nonneg (fun y hy => (hp hy).continuousAt.continuousWithinAt)
      (fun y hy => hp (Ioo_subset_Icc_self hy))
      (fun y hy => by have hh := (abs_lt.mp (early_mixed hb (Ioo_subset_Icc_self hy))).1; linarith)
  have hminus : AntitoneOn (fun t => freeFirst false b t-(1/2)*t) (Icc 0 (2/5)) :=
    antiOn_of_hasDeriv_nonpos (fun y hy => (hm hy).continuousAt.continuousWithinAt)
      (fun y hy => hm (Ioo_subset_Icc_self hy))
      (fun y hy => by have hh := (abs_lt.mp (early_mixed hb (Ioo_subset_Icc_self hy))).2; linarith)
  rcases le_total u v with huv | hvu
  · have hpv := hplus hu hv huv
    have hmv := hminus hu hv huv
    simp only at hpv hmv
    rw [abs_of_nonpos (sub_nonpos.mpr huv),abs_le]
    constructor <;> linarith
  · have hpv := hplus hv hu hvu
    have hmv := hminus hv hu hvu
    simp only at hpv hmv
    rw [abs_of_nonneg (sub_nonneg.mpr hvu),abs_le]
    constructor <;> linarith

theorem rectangle_lower {b B : ℝ} (hb : b∈Icc 0 (1/10)) (hB : B∈Icc 0 (2/5)) :
    (89777/100000:ℝ)<LowerContact.cost false b B := by
  have hB' := full_domain ⟨hB.1,by linarith [hB.2]⟩
  have hb₀ : referenceFree∈Icc 0 (83/200) :=
    ⟨reference_free_mem.1,by linarith [reference_free_mem.2]⟩
  have hf := curvature_tangent (f := fun t => LowerContact.cost false t B)
    (d := fun t => freeFirst false t B) (dd := fun t => freeSecond false t B)
    (κ := (3/2:ℝ)) hb reference_free_mem
    (fun t ht => cost_free_hasDerivAt false
      (short_domain ⟨ht.1,by linarith [ht.2]⟩) hB'
      (short_shift ⟨ht.1,by linarith [ht.2]⟩))
    (fun t ht => freeFirst_free_hasDerivAt false
      (short_domain ⟨ht.1,by linarith [ht.2]⟩) hB'
      (short_shift ⟨ht.1,by linarith [ht.2]⟩))
    (fun t ht => (early_free_curvature ht hB).le)
  have ho := curvature_tangent (f := LowerContact.cost false referenceFree)
    (d := outerFirst false referenceFree) (dd := outerSecond false referenceFree)
    (κ := (7/25:ℝ)) hB reference_outer_mem
    (fun t ht => cost_outer_hasDerivAt false
      (full_domain ⟨ht.1,by linarith [ht.2]⟩) (short_shift hb₀))
    (fun t ht => outerFirst_outer_hasDerivAt false
      (full_domain ⟨ht.1,by linarith [ht.2]⟩) (short_shift hb₀))
    (fun t ht => (early_outer_curvature reference_free_mem ht).le)
  have hx : |b-referenceFree|≤(1/10:ℝ) := by
    rw [abs_le]
    constructor <;> linarith [hb.1,hb.2,reference_free_mem.1,reference_free_mem.2]
  have hy : |B-referenceOuter|≤(2/5:ℝ) := by
    rw [abs_le]
    constructor <;> linarith [hB.1,hB.2,reference_outer_mem.1,reference_outer_mem.2]
  have hLip := first_outer_lipschitz reference_free_mem hB reference_outer_mem
  have hcrossAbs := mul_le_mul_of_nonneg_right hLip (abs_nonneg (b-referenceFree))
  rw [←abs_mul] at hcrossAbs
  have hcross := (abs_le.mp hcrossAbs).1
  have hgrad₁ := mul_le_mul reference_gradient.1.le hx (abs_nonneg _) (by norm_num)
  have hgrad₂ := mul_le_mul reference_gradient.2.le hy (abs_nonneg _) (by norm_num)
  rw [←abs_mul] at hgrad₁ hgrad₂
  have hgrad₁' := (abs_le.mp hgrad₁).1
  have hgrad₂' := (abs_le.mp hgrad₂).1
  have hquadratic : (1/2:ℝ)*|B-referenceOuter| * |b-referenceFree|≤
      (3/4:ℝ)*(b-referenceFree)^2+(7/50:ℝ)*(B-referenceOuter)^2 := by
    nlinarith [sq_nonneg (|b-referenceFree|-|B-referenceOuter|/2),
      sq_abs (b-referenceFree),sq_abs (B-referenceOuter),
      sq_nonneg (b-referenceFree),sq_nonneg (B-referenceOuter)]
  linarith [reference_value]

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.LowerFirst

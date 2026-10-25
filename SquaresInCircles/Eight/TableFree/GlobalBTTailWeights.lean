module

public import SquaresInCircles.Eight.TableFree.GlobalBTTailTransfer

/-!
# Strengthened TD weights for the complete BT0/1 tail

The same DE2 tail scalars remain strict after replacing the affine TD
weight by max(.6,c).  The lower interval is one concave constant-weight
family, joined exactly to the certified affine family.  These are the
weights needed by the negative BT1 prefix comparison. Uncompiled draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalBT

open Polynomial FrameCircleArc

def strengthenedWeight (i : Fin 3) (z : ℝ) : ℝ := max (3/5) (aeval z (TailPolynomial.weight i))
def zeroTargetNormUpper : Fin 3→ℝ := ![111931/100000,99761/100000,87727/100000]

theorem strengthened_bounds (i : Fin 3) {z : ℝ} (hz : z∈Icc 0 frameCap) :
    3/5≤ strengthenedWeight i z ∧ strengthenedWeight i z≤kappa ∧
      strengthenedWeight i z≤(TailPolynomial.e i:ℝ) := by
  have hw := TailPolynomial.weights_bounds i hz
  refine ⟨le_max_left _ _,max_le (by norm_num [kappa]) hw.2.1,?_⟩
  apply max_le _ hw.2.2
  fin_cases i <;> norm_num [TailPolynomial.e]

theorem first_zero_norm : tailNorm kappa (3/5) 0<(114909/100000:ℝ) := by
  rw [tailNorm,Real.sin_zero,Real.sqrt_lt' (by norm_num)]
  norm_num [kappa]

theorem target_zero_norm (i : Fin 3) :
    tailNorm (TailPolynomial.e i:ℝ) (3/5) 0<zeroTargetNormUpper i := by
  have hs := tailNorm_sq (TailPolynomial.chart_positive i) (c := (3/5:ℝ))
    (by norm_num) (z := 0) (by norm_num [frameCap])
  have hn : 0≤tailNorm (TailPolynomial.e i:ℝ) (3/5) 0 := Real.sqrt_nonneg _
  fin_cases i <;> norm_num [TailPolynomial.e,zeroTargetNormUpper] at hs ⊢ <;> nlinarith

theorem zero_tail_endpoint (i : Fin 3) (last : Bool) :
    pathThreshold<tailEndpoint last (TailPolynomial.e i:ℝ) (TailPolynomial.m i:ℝ) (3/5) 0 := by
  have hsum := add_lt_add first_zero_norm (target_zero_norm i)
  have hupper : 0<(114909/100000:ℝ)+zeroTargetNormUpper i := by
    fin_cases i <;> norm_num [zeroTargetNormUpper]
  have hp := (mul_lt_mul_of_pos_left hsum R_pos).trans
    (mul_lt_mul_of_pos_right radius_upper hupper)
  have hpi := Arithmetic.pi_hand_enclosure.1
  cases last <;> simp only [tailEndpoint,Bool.false_eq_true,↓reduceIte,
    sub_zero,Real.cos_zero,mul_one] <;>
    fin_cases i <;> norm_num [TailPolynomial.e,TailPolynomial.m,zeroTargetNormUpper,
      pathThreshold,kappa] at hp ⊢ <;> linarith

theorem fixed_endpoint_concave (last : Bool) {e m c : ℝ} (he : 0<e) (hc : 0<c) :
    ConcaveOn ℝ (Icc 0 frameCap) (tailEndpoint last e m c) := by
  cases last with
  | false =>
      have h := (affine_concave (-1)
        (Real.pi+(3/2)*kappa+2*c+e/2+m+e-R*tailNorm e c 0) 0 frameCap).add
        (normCos_concave (a := kappa) (by norm_num [kappa]) hc)
      convert h using 1
      funext z
      dsimp [tailEndpoint,normCos]
      ring
  | true =>
      have h := (affine_concave (-1)
        (Real.pi+(3/2)*kappa+2*c+e/2+m+kappa-R*tailNorm kappa c 0) 0 frameCap).add
        (normCos_concave he hc)
      convert h using 1
      funext z
      dsimp [tailEndpoint,normCos]
      ring

theorem strengthened_tail_endpoint (i : Fin 3) (last : Bool) {z : ℝ}
    (hz : z∈Icc 0 frameCap) :
    pathThreshold<tailEndpoint last (TailPolynomial.e i:ℝ) (TailPolynomial.m i:ℝ)
      (strengthenedWeight i z) z := by
  by_cases hbefore : z≤(TailPolynomial.join i:ℝ)
  · have hw := TailPolynomial.constant_above_before_join i hbefore
    rw [strengthenedWeight,max_eq_left hw]
    have hjoin := affine_tail_endpoint i last (TailPolynomial.join_domain i)
    rw [TailPolynomial.join_weight] at hjoin
    have hconc := (fixed_endpoint_concave last (m := (TailPolynomial.m i:ℝ))
      (TailPolynomial.chart_positive i) (by norm_num : (0:ℝ)<3/5)).subset
      (Icc_subset_Icc le_rfl (TailPolynomial.join_domain i).2) (convex_Icc _ _)
    exact concave_gt_of_endpoints hconc ⟨hz.1,hbefore⟩ (zero_tail_endpoint i last) hjoin
  · have hw := TailPolynomial.affine_above_after_join i (le_of_not_ge hbefore)
    rw [strengthenedWeight,max_eq_right hw]
    exact affine_tail_endpoint i last hz

end SquaresInCircles.Eight.TableFree.GlobalBT

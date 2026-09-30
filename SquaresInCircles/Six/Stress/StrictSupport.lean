module
public import SquaresInCircles.Six.Stress.ExactSupport
public import SquaresInCircles.Six.Stress.Reverse

@[expose] public section

/-!
# Strict support and the radius step in the uploaded conclusion

The closing argument needs more than non-strict support at the candidate
radius: every nonzero exterior force is strictly below that support when the
packing fits in a strictly smaller disk. This file proves the strict form on
BOTH support branches and its finite-stress consequence.

The final theorem is a generic stress theorem, not the unrestricted n=6 lower
bound. A concrete application must still provide the actual separating edges,
nonnegative weights, positive threshold, central support, and a proved
nonnegative defect. No closure computation or pattern classification is an
assumption hidden inside Packing. Compilation remains deferred.
-/

noncomputable section
namespace SquaresInCircles.Six.Stress

lemma dot_lt_radius {v p : Point} {R : ℝ} (hR : 0 ≤ R)
    (hv : v ≠ (0, 0)) (hp : normSq p < R ^ 2) :
    dot v p < R * vectorLength v := by
  have hn := normSq_pos_of_ne hv
  have hcs := cauchy_sq v p
  have hm := mul_lt_mul_of_pos_left hp hn
  have hs : (dot v p) ^ 2 < (R * vectorLength v) ^ 2 := by
    calc
      (dot v p) ^ 2 ≤ normSq v * normSq p := hcs
      _ < normSq v * R ^ 2 := hm
      _ = (R * vectorLength v) ^ 2 := by rw [← vectorLength_sq]; ring
  have hnonneg : 0 ≤ R * vectorLength v := mul_nonneg hR (vectorLength_nonneg v)
  by_contra! h
  have hprod := mul_nonneg (sub_nonneg.mpr h)
    (show 0 ≤ dot v p + R * vectorLength v by linarith)
  nlinarith

private lemma corner_support_strict {A B a b U V q : ℝ}
    (ha : 0 < a) (hB : b ≤ B) (hU : 0 < U)
    (hcircle : a ^ 2 + b ^ 2 = q) (hbox : A ^ 2 + B ^ 2 < q)
    (hslope : a * V ≤ b * U) : A * U + B * V < a * U + b * V := by
  have ht : a * (A - a) + b * (B - b) < 0 := by
    nlinarith [sq_nonneg (A - a), sq_nonneg (B - b)]
  have hct := mul_neg_of_pos_of_neg hU ht
  have hsl := mul_nonneg (sub_nonneg.mpr hslope) (sub_nonneg.mpr hB)
  have hp : a * (A * U + B * V - (a * U + b * V)) < 0 := by nlinarith
  by_contra! h
  have hpos := mul_nonneg ha.le (sub_nonneg.mpr h)
  linarith

private lemma strict_cap_slope {R U V : ℝ}
    (hR : 1 / 2 < R) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (h : 2 * R * V ≤ Real.sqrt (U ^ 2 + V ^ 2)) :
    Real.sqrt (R ^ 2 - 1 / 4) * V ≤ U / 2 := by
  have hR0 : 0 ≤ R := by linarith
  have hrad : 0 ≤ R ^ 2 - 1 / 4 := by nlinarith [sq_nonneg (R - 1 / 2)]
  have hs := Real.sq_sqrt hrad
  have hn := Real.sq_sqrt (show 0 ≤ U ^ 2 + V ^ 2 by positivity)
  have hp := mul_nonneg (sub_nonneg.mpr h)
    (show 0 ≤ Real.sqrt (U ^ 2 + V ^ 2) + 2 * R * V by positivity)
  have hmul := congrArg (fun z : ℝ => z * V ^ 2) hs
  have hsquare : (2 * Real.sqrt (R ^ 2 - 1 / 4) * V) ^ 2 ≤ U ^ 2 := by nlinarith
  have hnn : 0 ≤ 2 * Real.sqrt (R ^ 2 - 1 / 4) * V := by positivity
  by_contra! hbad
  have hprod := mul_pos
    (show 0 < 2 * Real.sqrt (R ^ 2 - 1 / 4) * V - U by linarith)
    (show 0 < 2 * Real.sqrt (R ^ 2 - 1 / 4) * V + U by linarith)
  nlinarith

lemma ordered_center_support_strict {R a b U V : ℝ}
    (hR : 1 / 2 < R) (hU : 0 < U) (hV : 0 ≤ V)
    (hbox : (|a| + 1 / 2) ^ 2 + (|b| + 1 / 2) ^ 2 < R ^ 2) :
    |a| * U + |b| * V < orderedSupport R U V := by
  unfold orderedSupport
  split_ifs with hswitch
  · have hrad : 0 < R ^ 2 - 1 / 4 := by nlinarith [sq_nonneg (R - 1 / 2)]
    have ha0 := Real.sqrt_pos.mpr hrad
    have hid := Real.sq_sqrt hrad.le
    have hslope := strict_cap_slope hR hU.le hV hswitch
    have hc := corner_support_strict
      (A := |a| + 1 / 2) (B := |b| + 1 / 2)
      (a := Real.sqrt (R ^ 2 - 1 / 4)) (b := (1 : ℝ) / 2) (U := U) (V := V)
      ha0 (by linarith [abs_nonneg b]) hU (by nlinarith) hbox (by linarith)
    dsimp [rhoAt]
    nlinarith
  · have hv : (U, V) ≠ (0, 0) := by
      intro he
      have heU := congrArg Prod.fst he
      dsimp only at heU
      linarith
    have hr := dot_lt_radius (v := (U, V)) (p := (|a| + 1 / 2, |b| + 1 / 2))
      (by linarith : 0 ≤ R) hv hbox
    dsimp [dot, vectorLength, normSq] at hr
    nlinarith

lemma scalar_center_support_strict {R a b x y : ℝ}
    (hR : 1 / 2 < R) (hv : x ≠ 0 ∨ y ≠ 0)
    (hbox : (|a| + 1 / 2) ^ 2 + (|b| + 1 / 2) ^ 2 < R ^ 2) :
    x * a + y * b < scalarSupport R x y := by
  have hx : x * a ≤ |a| * |x| := by
    simpa only [abs_mul, mul_comm] using le_abs_self (x * a)
  have hy : y * b ≤ |b| * |y| := by
    simpa only [abs_mul, mul_comm] using le_abs_self (y * b)
  unfold scalarSupport
  split_ifs with horder
  · have hU : 0 < |x| := by
      rcases hv with hx0 | hy0
      · exact abs_pos.mpr hx0
      · exact (abs_pos.mpr hy0).trans_le horder
    have h := ordered_center_support_strict hR hU (abs_nonneg y) hbox
    linarith
  · have hU : 0 < |y| := (abs_nonneg x).trans_lt (lt_of_not_ge horder)
    have hbox' : (|b| + 1 / 2) ^ 2 + (|a| + 1 / 2) ^ 2 < R ^ 2 := by linarith
    have h := ordered_center_support_strict hR hU (abs_nonneg x) hbox'
    linarith

/-- Strict containment at a smaller radius makes every nonzero force strict,
including a cap force with zero transverse component. -/
theorem center_lt_exactSupport {S : UnitSquare} {r R : ℝ}
    (hR : 1 / 2 < R) (hr : r ^ 2 < R ^ 2)
    (hcontain : ∀ p, closedSquare S p → inDisk (0, 0) r p)
    {g : Point} (hg : g ≠ (0, 0)) : dot g S.center < exactSupport R S g := by
  have hc := (phi_le_of_contained S (0, 0) r hcontain).trans_lt hr
  rw [alpha_frame_center, beta_frame_center] at hc
  have hv : frameX S g ≠ 0 ∨ frameY S g ≠ 0 := by
    by_contra! h
    have hf := frame_norm S g
    rw [h.1, h.2] at hf
    have hp := normSq_pos_of_ne hg
    nlinarith
  have h := scalar_center_support_strict (x := frameX S g) (y := frameY S g) hR hv hc
  rw [frame_dot] at h
  exact h

namespace System
variable {n m : ℕ}

/-- A positive separating threshold cannot be supported by zero exterior
forces: incidence balance would make the central force zero as well. -/
theorem exists_noncentral_force (E : Stress.System n m) (S : Fin n → UnitSquare)
    (central : Fin n) (hn : E.Nonnegative) (hs : E.Separates S)
    (hT : 0 < E.thresholdSum) : ∃ i, i ≠ central ∧ E.force i ≠ (0, 0) := by
  classical
  by_contra! hz
  have hbalance (v : Point) : (∑ i, dot (E.force i) v) = 0 := by
    rw [E.balance]
    simp [dot, sub]
  have hcentral (v : Point) : dot (E.force central) v = 0 := by
    calc
      dot (E.force central) v = ∑ i, dot (E.force i) v := by
        symm
        apply Finset.sum_eq_single central
        · intro i _ hi
          rw [hz i hi]
          simp [dot]
        · intro h
          exact False.elim (h (Finset.mem_univ central))
      _ = 0 := hbalance v
  have hc : E.force central = (0, 0) := by
    apply Prod.ext
    · simpa [dot] using hcentral (1, 0)
    · simpa [dot] using hcentral (0, 1)
  have hall (i : Fin n) : E.force i = (0, 0) := by
    by_cases hi : i = central
    · simpa [hi] using hc
    · exact hz i hi
  have h := E.threshold_le_forces S hn hs
  simp only [hall, dot, zero_mul, zero_add, Finset.sum_const_zero] at h
  linarith

lemma impossible_of_strict_support (E : Stress.System n m) (S : Fin n → UnitSquare)
    (U : Fin n → ℝ) (hn : E.Nonnegative) (hs : E.Separates S)
    (hu : ∀ i, dot (E.force i) (S i).center ≤ U i)
    (hstrict : ∃ i, dot (E.force i) (S i).center < U i)
    (hdefect : 0 ≤ E.thresholdSum - ∑ i, U i) : False := by
  have hsum : (∑ i, dot (E.force i) (S i).center) < ∑ i, U i := by
    apply Finset.sum_lt_sum (fun i _ => hu i)
    obtain ⟨i, hi⟩ := hstrict
    exact ⟨i, Finset.mem_univ i, hi⟩
  have hb := E.threshold_le_forces S hn hs
  linarith

/-- The exact radius step of the uploaded conclusion. A case closure supplies
hdefect; this theorem does not purport to supply any missing A2 closure. -/
theorem radius_eq_of_nonnegative_defect (E : Stress.System n m)
    (S : Fin n → UnitSquare) (central : Fin n) (centralUpper : ℝ) {r R : ℝ}
    (hp : Packing S (0, 0) r) (hR : 1 / 2 < R) (hr : r ^ 2 ≤ R ^ 2)
    (hn : E.Nonnegative) (hs : E.Separates S) (hT : 0 < E.thresholdSum)
    (hc : dot (E.force central) (S central).center ≤ centralUpper)
    (hdefect : 0 ≤ E.thresholdSum - ∑ i,
      if i = central then centralUpper else exactSupport R (S i) (E.force i)) : r = R := by
  classical
  by_contra heq
  have hrle : r ≤ R := by nlinarith [hp.1]
  have hrlt : r < R := lt_of_le_of_ne hrle heq
  have hrsq : r ^ 2 < R ^ 2 := by
    have h := mul_pos (sub_pos.mpr hrlt) (show 0 < R + r by linarith [hp.1])
    nlinarith
  let U : Fin n → ℝ := fun i =>
    if i = central then centralUpper else exactSupport R (S i) (E.force i)
  have hcontain (i : Fin n) : ∀ p, closedSquare (S i) p → inDisk (0, 0) R p := by
    intro p hpi
    exact (hp.2.1 i p hpi).trans hr
  have hu (i : Fin n) : dot (E.force i) (S i).center ≤ U i := by
    by_cases hi : i = central
    · simpa [U, hi] using hc
    · simpa [U, hi] using center_le_exactSupport hR (hcontain i) (E.force i)
  obtain ⟨i, hi, hforce⟩ := E.exists_noncentral_force S central hn hs hT
  have hstrict : dot (E.force i) (S i).center < U i := by
    simpa [U, hi] using center_lt_exactSupport hR hrsq (hp.2.1 i) hforce
  exact E.impossible_of_strict_support S U hn hs hu ⟨i, hstrict⟩ hdefect

end System
end SquaresInCircles.Six.Stress

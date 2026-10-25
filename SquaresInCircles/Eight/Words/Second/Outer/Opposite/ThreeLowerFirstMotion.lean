module

public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ThreeLowerFirstRectangle

/-!
# Eight squares: direct coordinate reductions into the first lower minimum rectangle

The free derivative increases in the free coordinate and decreases in
the outer coordinate.  The middle outer derivative is positive by one
concave comparison curve.  These motions give whole-domain reductions
without selecting or assuming a stationary point.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeThree.LowerFirst
open CommonQuarter CorePairGeometry Arithmetic
open LowerContact LowerGeometry LowerInverse

lemma free_first_monotone {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    MonotoneOn (fun b => freeFirst false b B) (Icc 0 (83/200)) :=
  monoOn_of_hasDeriv_nonneg
    (fun b hb => (freeFirst_free_hasDerivAt false (short_domain hb) hB
      (short_shift hb)).continuousAt.continuousWithinAt)
    (fun b hb => freeFirst_free_hasDerivAt false (short_domain (Ioo_subset_Icc_self hb))
      hB (short_shift (Ioo_subset_Icc_self hb)))
    (fun b hb => (free_curvature_positive (Ioo_subset_Icc_self hb) hB).le)

lemma free_first_outer_antitone {b : ℝ} (hb : b∈Icc 0 (83/200)) :
    AntitoneOn (freeFirst false b) (Icc 0 outerDiagonal) :=
  antiOn_of_hasDeriv_nonpos
    (fun B hB => (freeFirst_outer_hasDerivAt false hB (short_shift hb)).continuousAt.continuousWithinAt)
    (fun B hB => freeFirst_outer_hasDerivAt false (Ioo_subset_Icc_self hB) (short_shift hb))
    (fun B hB => (mixed_negative hb (Ioo_subset_Icc_self hB)).le)

lemma outer_first_free_antitone {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    AntitoneOn (fun b => outerFirst false b B) (Icc 0 (83/200)) :=
  antiOn_of_hasDeriv_nonpos
    (fun b hb => (outerFirst_free_hasDerivAt false hB (short_shift hb)).continuousAt.continuousWithinAt)
    (fun b hb => outerFirst_free_hasDerivAt false hB (short_shift (Ioo_subset_Icc_self hb)))
    (fun b hb => (mixed_negative (Ioo_subset_Icc_self hb) hB).le)

lemma early_free_positive {b B : ℝ} (hb : b∈Icc (1/10) (83/200))
    (hB : B∈Icc 0 (2/5)) : 0<freeFirst false b B := by
  have hB' := full_domain ⟨hB.1,by linarith [hB.2]⟩
  have h₁ := free_first_outer_antitone (by norm_num : (1/10:ℝ)∈Icc 0 (83/200))
    hB' (full_domain (by norm_num : (2/5:ℝ)∈Icc 0 (4/5))) hB.2
  have h₂ := free_first_monotone hB' (by norm_num : (1/10:ℝ)∈Icc 0 (83/200))
    ⟨by linarith [hb.1],hb.2⟩ hb.1
  linarith [free_first_references.1]

lemma middle_free_positive {b B : ℝ} (hb : b∈Icc (21/200) (83/200))
    (hB : B∈Icc (2/5) (1/2)) : 0<freeFirst false b B := by
  have hB' := full_domain ⟨by linarith [hB.1],by linarith [hB.2]⟩
  have h₁ := free_first_outer_antitone (by norm_num : (21/200:ℝ)∈Icc 0 (83/200))
    hB' (full_domain (by norm_num : (1/2:ℝ)∈Icc 0 (4/5))) hB.2
  have h₂ := free_first_monotone hB' (by norm_num : (21/200:ℝ)∈Icc 0 (83/200))
    ⟨by linarith [hb.1],hb.2⟩ hb.1
  linarith [free_first_references.2.2]

lemma middle_outer_positive {b B : ℝ} (hb : b∈Icc 0 (21/200))
    (hB : B∈Icc (2/5) (1/2)) : 0<outerFirst false b B := by
  have hz : (21/200:ℝ)+1/2∈shifts := short_shift (by norm_num)
  have hconc : ConcaveOn ℝ (Icc (2/5) (1/2)) (outerFirst false (21/200)) :=
    concave_of_deriv2
      (fun t ht => outerFirst_outer_hasDerivAt false
        (full_domain (show t∈Icc 0 (4/5) from ⟨by linarith [ht.1],by linarith [ht.2]⟩)) hz)
      (fun t ht => outerSecond_hasDerivAt false
        (full_domain (show t∈Icc 0 (4/5) from ⟨by linarith [ht.1],by linarith [ht.2]⟩)) hz)
      (fun t ht => (middle_third_negative ht).le)
  have hpos := concave_gt_of_endpoints hconc hB
    (show 0<outerFirst false (21/200) (2/5) by linarith [middle_first_endpoints.1])
    (show 0<outerFirst false (21/200) (1/2) by linarith [middle_first_endpoints.2])
  have hm := outer_first_free_antitone
    (full_domain (show B∈Icc 0 (4/5) from ⟨by linarith [hB.1],by linarith [hB.2]⟩))
    (show b∈Icc 0 (83/200) from ⟨hb.1,by linarith [hb.2]⟩)
    (by norm_num : (21/200:ℝ)∈Icc 0 (83/200)) hb.2
  exact hpos.trans_le hm

theorem early_lower {b B : ℝ} (hb : b∈Icc 0 (83/200)) (hB : B∈Icc 0 (2/5)) :
    (89777/100000:ℝ)<LowerContact.cost false b B := by
  by_cases hsmall : b≤1/10
  · exact rectangle_lower ⟨hb.1,hsmall⟩ hB
  have hB' := full_domain ⟨hB.1,by linarith [hB.2]⟩
  have hm : MonotoneOn (fun t => LowerContact.cost false t B) (Icc (1/10) (83/200)) := by
    apply monoOn_of_hasDeriv_nonneg
    · intro t ht
      have ht' : t∈Icc 0 (83/200) := ⟨by linarith [ht.1],ht.2⟩
      exact (cost_free_hasDerivAt false (short_domain ht') hB' (short_shift ht')).continuousAt.continuousWithinAt
    · intro t ht
      have ht' : t∈Icc 0 (83/200) := ⟨by linarith [ht.1],ht.2.le⟩
      exact cost_free_hasDerivAt false (short_domain ht') hB' (short_shift ht')
    · intro t ht
      exact (early_free_positive (Ioo_subset_Icc_self ht) hB).le
  exact (rectangle_lower (by norm_num : (1/10:ℝ)∈Icc 0 (1/10)) hB).trans_le
    (hm (by norm_num) ⟨by linarith,hb.2⟩ (by linarith))

theorem middle_lower {b B : ℝ} (hb : b∈Icc 0 (83/200)) (hB : B∈Icc (2/5) (1/2)) :
    (89777/100000:ℝ)<LowerContact.cost false b B := by
  let b' : ℝ := min b (21/200)
  have hb' : b'∈Icc 0 (21/200) :=
    ⟨le_min hb.1 (by norm_num),min_le_right _ _⟩
  have hbfull : b'∈Icc 0 (83/200) := ⟨hb'.1,by linarith [hb'.2]⟩
  have hB' := full_domain ⟨by linarith [hB.1],by linarith [hB.2]⟩
  have hmove : LowerContact.cost false b' B≤LowerContact.cost false b B := by
    by_cases hh : b≤21/200
    · dsimp [b']
      rw [min_eq_left hh]
    · have hm : MonotoneOn (fun t => LowerContact.cost false t B) (Icc (21/200) (83/200)) := by
        apply monoOn_of_hasDeriv_nonneg
        · intro t ht
          have ht' : t∈Icc 0 (83/200) := ⟨by linarith [ht.1],ht.2⟩
          exact (cost_free_hasDerivAt false (short_domain ht') hB' (short_shift ht')).continuousAt.continuousWithinAt
        · intro t ht
          have ht' : t∈Icc 0 (83/200) := ⟨by linarith [ht.1],ht.2.le⟩
          exact cost_free_hasDerivAt false (short_domain ht') hB' (short_shift ht')
        · intro t ht
          exact (middle_free_positive (Ioo_subset_Icc_self ht) hB).le
      dsimp [b']
      rw [min_eq_right (by linarith : (21/200:ℝ)≤b)]
      exact hm (by norm_num) ⟨by linarith,hb.2⟩ (by linarith)
  have houter : MonotoneOn (LowerContact.cost false b') (Icc (2/5) (1/2)) := by
    apply monoOn_of_hasDeriv_nonneg
    · intro t ht
      exact (cost_outer_hasDerivAt false
        (full_domain (show t∈Icc 0 (4/5) from ⟨by linarith [ht.1],by linarith [ht.2]⟩)) (short_shift hbfull)).continuousAt.continuousWithinAt
    · intro t ht
      exact cost_outer_hasDerivAt false
        (full_domain (show t∈Icc 0 (4/5) from ⟨by linarith [ht.1],by linarith [ht.2]⟩)) (short_shift hbfull)
    · intro t ht
      exact (middle_outer_positive hb' (Ioo_subset_Icc_self ht)).le
  exact (early_lower hbfull (by norm_num : (2/5:ℝ)∈Icc 0 (2/5))).trans_le
    ((houter (by norm_num) hB hB.1).trans hmove)

end SquaresInCircles.Eight.SecondWord.OppositeThree.LowerFirst

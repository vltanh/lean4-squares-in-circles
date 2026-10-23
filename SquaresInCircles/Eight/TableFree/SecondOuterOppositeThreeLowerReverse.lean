module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeThreeLowerCriticalMinimum
public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeThreeLowerFirst

/-!
# Every point of the reverse lower-secondary contact

The free coordinate has positive curvature on its whole closed
interval.  Before the source coordinate reaches three fifths, its
stationary point is the proved critical curve.  If that point lies
beyond the physical contact, monotonicity gives the actual aligned
endpoint.  The remaining source interval has a negative endpoint
derivative and reduces to the same aligned boundary.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.LowerReverse
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)
open LowerContact
open LowerFirst (short_domain short_shift)

lemma free_curvature_positive {b B : ℝ} (hb : b∈Icc 0 (83/200))
    (hB : B∈Icc 0 outerDiagonal) : 0<freeSecond true b B := by
  have hL := L_second_early (show b∈Icc 0 (1/2) from ⟨hb.1,by linarith [hb.2]⟩)
  have hv := (OppositeTwo.PrimaryInverse.data hB (short_shift hb)).2.2.1
  have hz : 0<b+1/2 := by linarith [hb.1]
  have hp := div_pos hz (pow_pos hv 3)
  dsimp [freeSecond,inner]
  linarith

lemma free_first_monotone {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    MonotoneOn (fun b => freeFirst true b B) (Icc 0 (83/200)) := by
  apply monoOn_of_hasDeriv_nonneg
  · intro b hb
    exact (freeFirst_free_hasDerivAt true (short_domain hb) hB
      (short_shift hb)).continuousAt.continuousWithinAt
  · intro b hb
    exact freeFirst_free_hasDerivAt true (short_domain (Ioo_subset_Icc_self hb)) hB
      (short_shift (Ioo_subset_Icc_self hb))
  · intro b hb
    exact (free_curvature_positive (Ioo_subset_Icc_self hb) hB).le

lemma aligned_domain {b B : ℝ} (hd : Domain b B) : Domain (Aligned.j B) B :=
  ⟨Aligned.j_mem ⟨hd.2.1.1,(domain_bounds hd).2.1⟩,hd.2.1,le_rfl⟩

lemma aligned_short {b B : ℝ} (hd : Domain b B) : Aligned.j B∈Icc 0 (83/200) := by
  have hh := Aligned.j_bounds ⟨hd.2.1.1,(domain_bounds hd).2.1⟩
  exact ⟨hh.1,by linarith [hh.2]⟩

lemma aligned_minimum {b B : ℝ} (hd : Domain b B)
    (hfirst : freeFirst true (Aligned.j B) B≤0) :
    (89777/100000:ℝ)<cost true b B := by
  have hj := aligned_short hd
  have hm := free_first_monotone hd.2.1
  have hpath {y : ℝ} (hy : y∈Icc 0 (Aligned.j B)) : y∈Icc 0 (83/200) :=
    ⟨hy.1,hy.2.trans hj.2⟩
  have ha : AntitoneOn (fun y => cost true y B) (Icc 0 (Aligned.j B)) := by
    apply antiOn_of_hasDeriv_nonpos
    · intro y hy
      exact (cost_free_hasDerivAt true (short_domain (hpath hy)) hd.2.1
        (short_shift (hpath hy))).continuousAt.continuousWithinAt
    · intro y hy
      exact cost_free_hasDerivAt true (short_domain (hpath (Ioo_subset_Icc_self hy)))
        hd.2.1 (short_shift (hpath (Ioo_subset_Icc_self hy)))
    · intro y hy
      exact (hm (hpath (Ioo_subset_Icc_self hy)) hj hy.2.le).trans hfirst
  have hcost := ha (show b∈Icc 0 (Aligned.j B) from ⟨hd.1.1,hd.2.2⟩)
    ⟨hj.1,le_rfl⟩ hd.2.2
  have hboundary := aligned_lower true (aligned_domain hd) rfl
  linarith

lemma early_lower {b B : ℝ} (hd : Domain b B) (hB : B≤3/5) :
    (89777/100000:ℝ)<cost true b B := by
  have hsource : B∈Icc 0 (3/5) := ⟨hd.2.1.1,hB⟩
  let P : ℝ := LowerCritical.parameter B hsource
  have hP : P∈Icc (3/100) (3/20) := LowerCritical.parameter_mem hsource
  have hPs : P∈Icc 0 (83/200) := LowerEnvelope.mem_short hP
  have he : LowerCritical.source P=B := LowerCritical.source_parameter hsource
  have hstation := LowerCritical.stationary hP
  rw [he] at hstation
  by_cases hphysical : P≤Aligned.j B
  · have hp : P≤arc (LowerCritical.source P)-1 := by
      rw [he]
      exact hphysical
    have hmin := LowerCritical.physical_lower (LowerCritical.parameter_domain hsource) hp
    change (89777/100000:ℝ)<cost true P (LowerCritical.source P) at hmin
    rw [he] at hmin
    have ht := curvature_tangent (f := fun y => cost true y B)
      (d := fun y => freeFirst true y B) (dd := fun y => freeSecond true y B)
      (κ := 0) (show b∈Icc 0 (83/200) from ⟨hd.1.1,(domain_bounds hd).1.le⟩) hPs
      (fun y hy => cost_free_hasDerivAt true (short_domain hy) hd.2.1 (short_shift hy))
      (fun y hy => freeFirst_free_hasDerivAt true (short_domain hy) hd.2.1 (short_shift hy))
      (fun y hy => (free_curvature_positive hy hd.2.1).le)
    rw [hstation] at ht
    linarith
  · apply aligned_minimum hd
    have hm := free_first_monotone hd.2.1 (aligned_short hd) hPs (le_of_not_ge hphysical)
    rwa [hstation] at hm

lemma late_endpoint_negative {b B : ℝ} (hd : Domain b B) (hB : (3/5:ℝ)≤B) :
    freeFirst true (Aligned.j B) B<0 := by
  have hj := aligned_short hd
  have hcircle := UW_circle (outer_domain hd.2.1)
  have hW : (11/10:ℝ)≤W B := by dsimp [W]; linarith
  have hWsq := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤11/10) hW 2
  have hU : U B<(33/20:ℝ) := by
    by_contra hn
    have hUsq := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤33/20)
      (le_of_not_gt hn) 2
    norm_num [Q0] at hcircle
    nlinarith
  have hjSmall : Aligned.j B<(3/20:ℝ) := by dsimp [Aligned.j,U] at *; linarith
  have hp := LowerEnvelope.p_antitone hj (by norm_num : (3/20:ℝ)∈Icc 0 (83/200))
    hjSmall.le
  have hpEnd := LowerEnvelope.endpoint_label_bounds.2.1
  have hv := (OppositeTwo.PrimaryInverse.data hd.2.1 (short_shift hj)).2.2.1
  have hphysical := physical_speed (aligned_domain hd)
  have hrecip : 1/LowerInverse.speed (Aligned.j B+1/2) B≤(10/11:ℝ) := by
    apply (div_le_iff₀ hv).2
    linarith
  dsimp [freeFirst,inner,LowerEnvelope.p] at *
  linarith

theorem contact_lower {b B : ℝ} (hd : Domain b B) :
    (89777/100000:ℝ)<cost true b B := by
  by_cases hB : B≤3/5
  · exact early_lower hd hB
  · exact aligned_minimum hd (late_endpoint_negative hd (le_of_not_ge hB)).le

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.LowerReverse

namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree
open CommonQuarter CorePairGeometry Arithmetic

theorem original_lower_target_secondary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 2 a b A B (-1) 1 (Real.pi/2-x)) :
    (89777/100000:ℝ)<value b B (Real.pi/2-x) := by
  obtain ⟨hd,hbetter⟩ := LowerContact.original_third_reduction hs ht hx hm
  exact (LowerReverse.contact_lower hd).trans_le hbetter

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree

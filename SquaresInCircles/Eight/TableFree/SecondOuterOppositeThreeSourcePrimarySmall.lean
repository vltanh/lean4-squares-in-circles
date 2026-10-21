module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeThreePrimaryMotion

/-!
# Original source-primary separators at and near alignment

The full lower half flows directly to its aligned contact.  In the upper
half with target coordinate at most `.2`, the first contact with the
unchanged source lies on one complete primary arc and has increasing
corrected cost.  The weak original separator and every endpoint tie are
retained.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)
open NegativeThree (TPrimaryLabel)

theorem original_lower_source_primary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 3 a b A B (-1) 1 (Real.pi/2-x)) :
    (44889/50000:ℝ)<value b B (Real.pi/2-x) := by
  have hB := NegativeTwo.source_mem ht
  have ha := NegativeTwo.primary_mem hs
  have hcut := lower_source_primary ht hx hm
  have hstart := lowerPrimary_monotone hB (by norm_num) hx hx.1
  rw [lowerPrimary_zero] at hstart
  have hzero : 1+B∈Icc outerDiagonal outerAxial :=
    ⟨by linarith [hB.1,outer_endpoint_bounds.2.2.2],hstart.trans (hcut.trans ha.2)⟩
  have hdom {t : ℝ} (htime : t∈Icc 0 x) :
      t∈Icc 0 (7/10) ∧ lowerPrimary B t∈Icc outerDiagonal outerAxial := by
    have htimeFull : t∈Icc 0 (7/10) := ⟨htime.1,htime.2.trans hx.2⟩
    have hlo := lowerPrimary_monotone hB (by norm_num) htimeFull htime.1
    have hhi := lowerPrimary_monotone hB htimeFull hx htime.2
    rw [lowerPrimary_zero] at hlo
    exact ⟨htimeFull,⟨hzero.1.trans hlo,hhi.trans (hcut.trans ha.2)⟩⟩
  have hd {t : ℝ} (htime : t∈Icc 0 x) :
      HasDerivAt (fun y => -y+TPrimaryLabel.outer (lowerPrimary B y))
        (-1+TPrimaryLabel.d1 (lowerPrimary B t)*lowerPrimarySpeed B t) t := by
    have hh := (TPrimaryLabel.outer_hasDerivAt
      (primary_domain (hdom htime).2)).comp t (lowerPrimary_hasDerivAt B t)
    convert (hasDerivAt_id t).neg.add hh using 1 <;> ring
  have hmono : MonotoneOn (fun y => -y+TPrimaryLabel.outer (lowerPrimary B y))
      (Icc 0 x) := monoOn_of_hasDeriv_nonneg
    (fun t ht' => (hd ht').continuousAt.continuousWithinAt)
    (fun t ht' => hd (Ioo_subset_Icc_self ht'))
    (fun t ht' => by
      have hh := hdom (Ioo_subset_Icc_self ht')
      linarith [lower_primary_speed_paid hB hh.1 hh.2])
  have hstep := hmono ⟨le_rfl,hx.1⟩ ⟨hx.1,le_rfl⟩ hx.1
  rw [lowerPrimary_zero] at hstep
  have hM := NegativeThree.primary_monotone (hdom ⟨hx.1,le_rfl⟩).2 ha hcut
  rw [NegativeThree.primary_actual hs] at hM
  have hs0 := ShortOuterOne.SameContact.primary_state hzero
  have hbase := aligned_last hs0 ht (show 1≤(1+B)-B by ring_nf)
  have hactual := NegativeThree.primary_actual hs0
  dsimp [value] at hbase ⊢
  linarith

theorem upper_source_primary_small_cut {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hBsmall : B≤1/5) (hcut : upperPrimary B x≤a) :
    (44889/50000:ℝ)<value b B (Real.pi/2+x) := by
  have hB := NegativeTwo.source_mem ht
  have ha := NegativeTwo.primary_mem hs
  by_cases halign : 1+B≤a
  · have hh := aligned_last hs ht (by linarith)
    dsimp [value] at *
    linarith [hx.1]
  · have hc : Continuous (fun t => -upperPrimary B t) := by
      dsimp [upperPrimary]
      fun_prop
    obtain ⟨y,hy,hycontact⟩ := intermediate_value_Icc hx.1 hc.continuousOn
      (show -a∈Icc (-upperPrimary B 0) (-upperPrimary B x) by
        rw [upperPrimary_zero]
        constructor <;> linarith)
    have he : upperPrimary B y=a := by linarith
    have hycap : y∈Icc 0 (7/10) := ⟨hy.1,hy.2.trans hx.2⟩
    have hzero : 1+B∈Icc outerDiagonal outerAxial := by
      constructor
      · linarith [hB.1,outer_endpoint_bounds.2.2.2]
      · linarith [primary_six_fifths_mem.2]
    have hdom {t : ℝ} (htime : t∈Icc 0 y) :
        t∈Icc 0 (7/10) ∧ upperPrimary B t∈Icc outerDiagonal (6/5) := by
      have htimeFull : t∈Icc 0 (7/10) := ⟨htime.1,htime.2.trans hycap.2⟩
      have hlo := upperPrimary_antitone hB htimeFull hycap htime.2
      have hhi := upperPrimary_antitone hB (by norm_num) htimeFull htime.1
      rw [he] at hlo
      rw [upperPrimary_zero] at hhi
      exact ⟨htimeFull,⟨ha.1.trans hlo,by linarith⟩⟩
    have hd {t : ℝ} (htime : t∈Icc 0 y) :
        HasDerivAt (fun z => z+TPrimaryLabel.outer (upperPrimary B z))
          (1-TPrimaryLabel.d1 (upperPrimary B t)*upperPrimarySpeed B t) t := by
      have hh := (TPrimaryLabel.outer_hasDerivAt (primary_domain
        ⟨(hdom htime).2.1,(hdom htime).2.2.trans primary_six_fifths_mem.2⟩)).comp t
          (upperPrimary_hasDerivAt B t)
      convert (hasDerivAt_id t).add hh using 1 <;> ring
    have hmono : MonotoneOn (fun z => z+TPrimaryLabel.outer (upperPrimary B z))
        (Icc 0 y) := monoOn_of_hasDeriv_nonneg
      (fun t ht' => (hd ht').continuousAt.continuousWithinAt)
      (fun t ht' => hd (Ioo_subset_Icc_self ht'))
      (fun t ht' => by
        have hh := hdom (Ioo_subset_Icc_self ht')
        linarith [upper_primary_speed_paid ⟨hB.1,hBsmall⟩ hh.1 hh.2])
    have hstep := hmono ⟨le_rfl,hy.1⟩ ⟨hy.1,le_rfl⟩ hy.1
    rw [upperPrimary_zero,he,NegativeThree.primary_actual hs] at hstep
    have hs0 := ShortOuterOne.SameContact.primary_state hzero
    have hbase := aligned_last hs0 ht (show 1≤(1+B)-B by ring_nf)
    have hactual := NegativeThree.primary_actual hs0
    dsimp [value] at hbase ⊢
    linarith [hy.2]

theorem original_upper_source_primary_small {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hBsmall : B≤1/5)
    (hm : 0≤Eight.forwardMargin 3 a b A B (-1) 1 (Real.pi/2+x)) :
    (44889/50000:ℝ)<value b B (Real.pi/2+x) :=
  upper_source_primary_small_cut hs ht hx hBsmall (upper_source_primary ht hx hm)

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree

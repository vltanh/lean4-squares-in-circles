module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeTwoLowerStripContact

/-!
# The complete original lower target-secondary short interval

The actual weak separator first places the target below its source
contact.  A zero-target source endpoint is obtained by the intermediate
value theorem between that original source and the aligned source.
The actual contact curvature and its negative endpoint derivative
concentrate the cost there; the zero-target inverse bound finishes.
No additional contact, endpoint, or strict-owner hypothesis is used.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeTwo.LowerStrip

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

theorem original {a b A B x : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hx : x∈Icc 0 (1/100))
    (hm : 0≤forwardMargin 2 a b A B (-1) 1 (Real.pi/2-x)) :
    (44889/50000:ℝ)<OppositeTwo.value b B (Real.pi/2-x) := by
  have hangle := angle_mem hx
  have hb : b∈Icc 0 outerDiagonal := ⟨hs.1,(outer_bounds hs).2.2⟩
  have hcut : B≤contact x b := by
    have hw := lower_width hangle
    norm_num [forwardMargin,Real.sin_sub,Real.cos_sub,hw] at hm
    dsimp [contact,lowerCut]
    rw [(ShortOuterOne.SameContact.actual_arc hs).1]
    linarith
  have hcontact : 0≤contact x b := ht.1.trans hcut
  have ha : 1≤a := by
    have hh := contact_upper hb hangle
    rw [(ShortOuterOne.SameContact.actual_arc hs).1] at hh
    linarith
  have ha' : a∈Icc outerDiagonal outerAxial :=
    ⟨(outer_bounds hs).1,(outer_bounds hs).2.1⟩
  have hbone := ShortOuterOne.SameContact.arc_antitone
    (primary_domain primary_one_mem) (primary_domain ha') ha
  rw [(ShortOuterOne.SameContact.actual_arc hs).2] at hbone
  change b≤bOne at hbone
  have hc : Continuous (fun y => -contact x y) := by
    dsimp [contact,lowerCut,arc]
    fun_prop
  obtain ⟨β,hβ,hzero'⟩ := intermediate_value_Icc hbone hc.continuousOn
    (show (0:ℝ)∈Icc (-contact x b) (-contact x bOne) from
      ⟨by linarith,(neg_nonneg.mpr (contact_bOne hangle))⟩)
  have hzero : contact x β=0 := by linarith
  have hβmem : β∈Icc 0 bOne := ⟨hs.1.trans hβ.1,hβ.2⟩
  have hβouter : β∈Icc 0 outerDiagonal :=
    ⟨hβmem.1,hβmem.2.trans bOne_mem.2⟩
  have hβband := zero_endpoint_band hx hβmem hzero
  have hdom {y : ℝ} (hy : y∈Icc b β) : y∈Icc 0 bOne :=
    ⟨hs.1.trans hy.1,hy.2.trans hβ.2⟩
  have houter {y : ℝ} (hy : y∈Icc b β) : y∈Icc 0 outerDiagonal :=
    ⟨(hdom hy).1,(hdom hy).2.trans bOne_mem.2⟩
  have htarget {y : ℝ} (hy : y∈Icc b β) : contact x y∈earlyTarget := by
    have hh := contact_antitone hangle (houter hy) hβouter hy.2
    rw [hzero] at hh
    exact contact_early (houter hy) hangle hh
  have hfirst : MonotoneOn (contactFirst x) (Icc b β) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun y hy =>
        (contactFirst_hasDerivAt (houter hy) (htarget hy)).continuousAt.continuousWithinAt
    · exact fun y hy =>
        contactFirst_hasDerivAt (houter (Ioo_subset_Icc_self hy))
          (htarget (Ioo_subset_Icc_self hy))
    · intro y hy
      linarith [contactSecond_lower (hdom (Ioo_subset_Icc_self hy)) hx
        (htarget (Ioo_subset_Icc_self hy))]
  have hright : contactFirst x β<0 := first_zero_negative hβband hx hzero
  have hcost : AntitoneOn (contactValue x) (Icc b β) := by
    apply antiOn_of_hasDeriv_nonpos
    · exact fun y hy =>
        (contactValue_hasDerivAt (houter hy) (htarget hy)).continuousAt.continuousWithinAt
    · exact fun y hy =>
        contactValue_hasDerivAt (houter (Ioo_subset_Icc_self hy))
          (htarget (Ioo_subset_Icc_self hy))
    · intro y hy
      have hh := hfirst (Ioo_subset_Icc_self hy) ⟨hβ.1,le_rfl⟩ hy.2.le
      linarith
  have hstep := hcost ⟨le_rfl,hβ.1⟩ ⟨hβ.1,le_rfl⟩ hβ.1
  rw [zero_contact_value hβouter hangle hzero] at hstep
  have haxis := axis_lower hβband
  have hc0 := contact_early hb hangle hcontact
  have hB : B∈earlyTarget := ⟨ht.1,hcut.trans hc0.2⟩
  have hV := target_monotone hB hc0 hcut
  dsimp [contactValue,OppositeTwo.value] at *
  linarith

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeTwo.LowerStrip


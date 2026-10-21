module

public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeThreeAligned
public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeThreeSpeed
public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeThreeDiagonal

/-!
# The original lower source-primary weak owner for negative edge three

The actual contact moves monotonically in the source primary coordinate.
Its source-label increment strictly pays the angle change, by the
whole-arc speed estimate.  The first feasible contact therefore reduces
to alignment or the actual source-diagonal boundary.  The target square
and its original circle are unchanged in both comparisons.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.NegativeThree

open CommonQuarter CorePairGeometry Arithmetic

lemma lower_active_monotone {A B l u : ℝ} (ht : OuterState A B)
    (hl : l∈Icc 0 (7/10)) (hu : u∈Icc 0 (7/10)) (hlu : l≤u)
    (hleft : outerDiagonal≤NegativeTwo.lowerSource A B l)
    (hright : NegativeTwo.lowerSource A B u≤outerAxial) :
    MonotoneOn (fun t => -t+TPrimaryLabel.outer (NegativeTwo.lowerSource A B t))
      (Icc l u) := by
  have hdom (t : ℝ) (htime : t∈Icc l u) :
      t∈Icc 0 (7/10) ∧ NegativeTwo.lowerSource A B t∈Icc outerDiagonal outerAxial := by
    have htf : t∈Icc 0 (7/10) := ⟨hl.1.trans htime.1,htime.2.trans hu.2⟩
    exact ⟨htf,⟨hleft.trans (NegativeTwo.lowerSource_monotone ht hl htf htime.1),
      (NegativeTwo.lowerSource_monotone ht htf hu htime.2).trans hright⟩⟩
  have hd (t : ℝ) (htime : t∈Icc l u) :
      HasDerivAt (fun z => -z+TPrimaryLabel.outer (NegativeTwo.lowerSource A B z))
        (-1+TPrimaryLabel.d1 (NegativeTwo.lowerSource A B t)*
          NegativeTwo.lowerSpeed A B t) t := by
    have hc := (TPrimaryLabel.outer_hasDerivAt
      (primary_domain (hdom t htime).2)).comp t (NegativeTwo.lowerSource_hasDerivAt A B t)
    convert (hasDerivAt_id t).neg.add hc using 1 <;> ring
  exact monoOn_of_hasDeriv_nonneg
    (fun t htime => (hd t htime).continuousAt.continuousWithinAt)
    (fun t htime => hd t (Ioo_subset_Icc_self htime))
    (fun t htime => by
      have h := hdom t (Ioo_subset_Icc_self htime)
      linarith [lower_active_speed ht h.1 h.2])

theorem original_lower_source_primary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 3 a b A B (-1) (-1) (Real.pi/2-x)) :
    (93/100:ℝ)<value b B (Real.pi/2-x) := by
  have hcut := NegativeTwo.lower_source_cut hx hm
  have ha := NegativeTwo.primary_mem hs
  have hactual := primary_actual hs
  by_cases hstart : outerDiagonal≤1-B
  · have hzero : outerDiagonal≤NegativeTwo.lowerSource A B 0 := by
      simpa only [NegativeTwo.lowerSource_zero] using hstart
    have hmono := lower_active_monotone ht (by norm_num) hx hx.1 hzero (hcut.trans ha.2)
    have hstep := hmono (show (0:ℝ)∈Icc 0 x from ⟨le_rfl,hx.1⟩)
      (show x∈Icc 0 x from ⟨hx.1,le_rfl⟩) hx.1
    have hxdom : NegativeTwo.lowerSource A B x∈Icc outerDiagonal outerAxial :=
      ⟨hzero.trans (NegativeTwo.lowerSource_monotone ht (by norm_num) hx hx.1),hcut.trans ha.2⟩
    have hM := primary_monotone hxdom ha hcut
    rw [hactual] at hM
    rw [NegativeTwo.lowerSource_zero] at hstep
    have hbase := aligned_lower
      (show 1-B∈Icc outerDiagonal 1 from ⟨hstart,by linarith [ht.1]⟩)
    have harg : 1-(1-B)=B := by ring
    dsimp [aligned] at hbase
    rw [harg] at hbase
    dsimp [value]
    linarith
  · have hcont : Continuous (NegativeTwo.lowerSource A B) := by
      dsimp [NegativeTwo.lowerSource]
      fun_prop
    obtain ⟨y,hy,hycontact⟩ := intermediate_value_Icc
      (show (0:ℝ)≤7/10 by norm_num) hcont.continuousOn
      (show outerDiagonal∈Icc (NegativeTwo.lowerSource A B 0)
          (NegativeTwo.lowerSource A B (7/10)) by
        rw [NegativeTwo.lowerSource_zero]
        exact ⟨by linarith,(NegativeTwo.lowerSource_cap ht).le⟩)
    have hdiag := Diagonal.original_contact ht hy hycontact
    rcases le_total x y with hxy | hyx
    · have hd : outerDiagonal∈Icc 0 outerDiagonal := ⟨outer_zero_mem.2,le_rfl⟩
      have hT := T_monotone (NegativeTwo.source_mem hs) hd (NegativeTwo.source_mem hs).2
      dsimp [value] at *
      linarith
    · have hmono := lower_active_monotone ht hy hx hyx (by rw [hycontact]) (hcut.trans ha.2)
      have hstep := hmono (show y∈Icc y x from ⟨le_rfl,hyx⟩)
        (show x∈Icc y x from ⟨hyx,le_rfl⟩) hyx
      rw [hycontact] at hstep
      have hxdom : NegativeTwo.lowerSource A B x∈Icc outerDiagonal outerAxial := by
        have hh := NegativeTwo.lowerSource_monotone ht hy hx hyx
        rw [hycontact] at hh
        exact ⟨hh,hcut.trans ha.2⟩
      have hM := primary_monotone hxdom ha hcut
      rw [hactual] at hM
      have hd : outerDiagonal∈Icc 0 outerDiagonal := ⟨outer_zero_mem.2,le_rfl⟩
      have hD : TPrimaryLabel.outer outerDiagonal= -T outerDiagonal := by
        have hh := primary_actual (ShortOuterOne.SameContact.arc_state hd)
        simpa only [ShortOuterOne.SameContact.arc_diagonal] using hh
      rw [hD] at hstep
      dsimp [value] at *
      linarith

end SquaresInCircles.Eight.TableFree.SecondWord.NegativeThree

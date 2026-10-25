module

public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeThreeAligned
public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeThreeSpeed
public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeTwoUpperTarget

/-!
# Both original upper primary/secondary owners for negative edge three

The target-secondary separator loses at most `.4*x` of its aligned
target coordinate.  The target-label increment is less than `.928`
times that loss.  For the source-primary separator the actual target
circle gives a contact-speed product below one; the first contact with
the original source therefore compares directly with alignment.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.NegativeThree

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

theorem original_upper_target_secondary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 2 a b A B (-1) (-1) (Real.pi/2+x)) :
    (93/100:ℝ)<value b B (Real.pi/2+x) := by
  have hcut := NegativeTwo.upper_target_cut hx hm
  have hdisp : 1-a-B≤(2/5)*x := by
    linarith [NegativeTwo.upper_target_displacement hs hx]
  by_cases ha : 1≤a
  · have hbase := original_aligned hs ht (by linarith [ht.1])
    dsimp [value] at *
    linarith [hx.1]
  · have hdom := NegativeTwo.aligned_domain
      (show a∈Icc outerDiagonal 1 from ⟨(NegativeTwo.primary_mem hs).1,by linarith⟩)
    have hs0 := ShortOuterOne.SameContact.arc_state hdom.2.1
    have hbase := original_aligned hs hs0 (show 1≤a+(1-a) by linarith)
    by_cases hB : 1-a≤B
    · have hK := K_monotone hdom.2.1 (NegativeTwo.source_mem ht) hB
      dsimp [value] at *
      linarith [hx.1]
    · have hK := K_increment_upper (NegativeTwo.source_mem ht) hdom.2.1 (by linarith)
      dsimp [value] at *
      nlinarith [hx.1]

theorem original_upper_source_primary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 3 a b A B (-1) (-1) (Real.pi/2+x)) :
    (93/100:ℝ)<value b B (Real.pi/2+x) := by
  by_cases halign : 1≤a+B
  · have hh := original_aligned hs ht halign
    dsimp only [value] at hh ⊢
    linarith [hx.1]
  · have hcut := NegativeTwo.upper_source_cut hx hm
    have hc : Continuous (fun t => -NegativeTwo.upperSource A B t) := by
      dsimp [NegativeTwo.upperSource]
      fun_prop
    obtain ⟨y,hy,hycontact⟩ := intermediate_value_Icc hx.1 hc.continuousOn
      (show -a∈Icc (-NegativeTwo.upperSource A B 0) (-NegativeTwo.upperSource A B x) by
        rw [NegativeTwo.upperSource_zero]
        constructor <;> linarith)
    have he : NegativeTwo.upperSource A B y=a := by linarith
    have hycap : y∈Icc 0 (7/10) := ⟨hy.1,hy.2.trans hx.2⟩
    have hstart : 1-B∈Icc outerDiagonal 1 := by
      constructor <;> linarith [(NegativeTwo.primary_mem hs).1,ht.1]
    have hdom {t : ℝ} (htime : t∈Icc 0 y) :
        t∈Icc 0 (7/10) ∧ NegativeTwo.upperSource A B t∈Icc outerDiagonal 1 := by
      have htcap : t∈Icc 0 (7/10) := ⟨htime.1,htime.2.trans hycap.2⟩
      have hlo := NegativeTwo.upperSource_antitone ht htcap hycap htime.2
      have hhi := NegativeTwo.upperSource_antitone ht (by norm_num) htcap htime.1
      rw [he] at hlo
      rw [NegativeTwo.upperSource_zero] at hhi
      exact ⟨htcap,⟨(NegativeTwo.primary_mem hs).1.trans hlo,hhi.trans hstart.2⟩⟩
    have hd {t : ℝ} (htime : t∈Icc 0 y) :
        HasDerivAt (fun s => s+TPrimaryLabel.outer (NegativeTwo.upperSource A B s))
          (1-TPrimaryLabel.d1 (NegativeTwo.upperSource A B t)*
            NegativeTwo.upperSpeed A B t) t := by
      have hh := (TPrimaryLabel.outer_hasDerivAt
        (primary_domain (NegativeTwo.aligned_domain (hdom htime).2).1)).comp t
          (NegativeTwo.upperSource_hasDerivAt A B t)
      exact ((hasDerivAt_id' t).add hh).congr_deriv (by ring)
    have hmono : MonotoneOn
        (fun s => s+TPrimaryLabel.outer (NegativeTwo.upperSource A B s)) (Icc 0 y) :=
      monoOn_of_hasDeriv_nonneg
        (fun t ht' => (hd ht').continuousAt.continuousWithinAt)
        (fun t ht' => hd (Ioo_subset_Icc_self ht'))
        (fun t ht' => by
          have hh := hdom (Ioo_subset_Icc_self ht')
          linarith [upper_active_speed ht hh.1 hh.2])
    have hstep := hmono ⟨le_rfl,hy.1⟩ ⟨hy.1,le_rfl⟩ hy.1
    dsimp only at hstep
    rw [NegativeTwo.upperSource_zero,he] at hstep
    have hbase := aligned_lower hstart
    have hactual := primary_actual hs
    dsimp only [aligned] at hbase
    dsimp only [value]
    rw [hactual] at hstep
    have harg : 1-(1-B)=B := by ring
    rw [harg] at hbase
    linarith [hy.2]

end SquaresInCircles.Eight.TableFree.SecondWord.NegativeThree

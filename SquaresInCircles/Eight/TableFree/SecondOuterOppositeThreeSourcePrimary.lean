module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeThreeSourcePrimarySmall
public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeThreeUpperInverse

/-!
# The complete original upper source-primary separator

At fixed physical source height the explicit inverse contact moves
monotonically in the target coordinate.  Its corrected cost increases
from alignment or the target `.2` boundary.  This finite comparison
covers inactive and active original inequalities together and retains
the original circle states and weak margin at both ends.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

theorem upper_source_primary_cut {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hcut : upperPrimary B x≤a) :
    (44889/50000:ℝ)<value b B (Real.pi/2+x) := by
  by_cases hsmall : B≤1/5
  · exact upper_source_primary_small_cut hs ht hx hsmall hcut
  by_cases halign : 1+B≤a
  · have hh := aligned_last hs ht (by linarith)
    dsimp [value] at *
    linarith [hx.1]
  have hB := NegativeTwo.source_mem ht
  have hz := UpperInverse.primary_shift hs
  let z : ℝ := a-1/2
  let l : ℝ := max (1/5) (a-1)
  have hlB : l≤B := by
    dsimp [l]
    exact max_le (by linarith) (by linarith)
  have hlmem : l∈Icc (1/5) outerDiagonal :=
    ⟨le_max_left _ _,hlB.trans hB.2⟩
  have hlphysical := CapRatio.domain hlmem
  have hlz : z≤W l := by
    have hh : a-1≤l := le_max_right _ _
    dsimp [z,W]
    linarith
  have hXstart : 0≤UpperInverse.X z l := UpperInverse.X_nonnegative hlphysical hlz
  have horiginal : UpperInverse.X z B≤x := by
    apply OppositeTwo.PrimaryInverse.weak_angle ht hx hz
    have hArc := (ShortOuterOne.SameContact.actual_arc ht).1
    dsimp [OppositeTwo.upperPrimary,z]
    dsimp [upperPrimary] at hcut
    rw [hArc] at hcut
    linarith
  have hdom {t : ℝ} (htime : t∈Icc l B) :
      t∈Icc (1/5) outerDiagonal ∧ UpperInverse.X z t∈Icc 0 (7/10) := by
    have htf : t∈Icc (1/5) outerDiagonal := ⟨hlmem.1.trans htime.1,htime.2.trans hB.2⟩
    have hlo := UpperInverse.X_monotone hz hlphysical (CapRatio.domain htf) htime.1
    have hhi := UpperInverse.X_monotone hz (CapRatio.domain htf) hB htime.2
    exact ⟨htf,⟨hXstart.trans hlo,hhi.trans (horiginal.trans hx.2)⟩⟩
  have hd {t : ℝ} (htime : t∈Icc l B) :
      HasDerivAt (fun y => UpperInverse.X z y-L y)
        (UpperInverse.F z t-LLabel.d1 t) t := by
    convert (OppositeTwo.PrimaryInverse.X_source_hasDerivAt
      (CapRatio.domain (hdom htime).1) hz).sub
        (LLabel.outer_hasDerivAt (outer_domain (CapRatio.domain (hdom htime).1)))
      using 1 <;> rfl
  have hmono : MonotoneOn (fun y => UpperInverse.X z y-L y) (Icc l B) :=
    monoOn_of_hasDeriv_nonneg
      (fun t ht' => (hd ht').continuousAt.continuousWithinAt)
      (fun t ht' => hd (Ioo_subset_Icc_self ht'))
      (fun t ht' => by
        have hh := hdom (Ioo_subset_Icc_self ht')
        linarith [UpperInverse.inverse_paid hh.1 hz hh.2])
  have hstep := hmono ⟨le_rfl,hlB⟩ ⟨hlB,le_rfl⟩ hlB
  have hstart : (44889/50000:ℝ)<value b l (Real.pi/2+UpperInverse.X z l) := by
    by_cases ha : (1/5:ℝ)≤a-1
    · have hl : l=a-1 := max_eq_right ha
      have he : z=W l := by dsimp [z,W]; rw [hl]; ring
      have hzero := OppositeTwo.PrimaryInverse.aligned hlphysical he
      have ht0 := ShortOuterOne.SameContact.arc_state hlphysical
      have hbase := aligned_last hs ht0 (by rw [hl]; linarith)
      simpa only [hzero,add_zero] using hbase
    · have hl : l=(1/5:ℝ) := max_eq_left (le_of_not_ge ha)
      have ht0 := ShortOuterOne.SameContact.arc_state hlphysical
      have hcontact := UpperInverse.X_contact hlphysical hz
      have htarget : upperPrimary l (UpperInverse.X z l)≤a := by
        rw [hcontact]
        dsimp [z]
        linarith
      exact upper_source_primary_small_cut hs ht0 (hdom ⟨le_rfl,hlB⟩).2
        (by rw [hl]) htarget
  dsimp [value] at hstart ⊢
  linarith

theorem original_upper_source_primary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 3 a b A B (-1) 1 (Real.pi/2+x)) :
    (44889/50000:ℝ)<value b B (Real.pi/2+x) :=
  upper_source_primary_cut hs ht hx (upper_source_primary ht hx hm)

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree

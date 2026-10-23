module

public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeThreeAligned
public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeThreeZeroTarget
public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeThreeDiagonalSource
public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeThreeDiagonalTarget

/-!
# The six actual boundary pieces of the last contact domain

Alignment, either source endpoint, either target endpoint, and the final
angle all have strict bounds.  An original weak target-secondary axis
also reaches a genuine nonnegative contact with no larger cost; its
inactive portion ends at the actual zero-target contact by IVT.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.NegativeThree.Contact

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)
open NegativeTwo

def Boundary (b x : ℝ) : Prop :=
  b=0 ∨ b=outerDiagonal ∨ x=0 ∨ x=7/10 ∨
    TargetContact.B b x=0 ∨ TargetContact.B b x=outerDiagonal

lemma aligned_contact_lower {b B : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hB : B∈Icc 0 outerDiagonal) (hc : TargetContact.B b 0=B) :
    (93/100:ℝ)<value b B (Real.pi/2) := by
  rw [TargetContact.B_zero] at hc
  exact original_aligned (ShortOuterOne.SameContact.arc_state hb)
    (ShortOuterOne.SameContact.arc_state hB) (by linarith)

lemma axial_angle_first {x : ℝ} (hd : TargetContact.Domain 0 x) : angleFirst 0 x<0 := by
  have hv := TargetContact.v_positive outer_zero_mem hd.2.1
  have hn := TargetContact.norm_identity outer_zero_mem x
  have hz : U 0=outerAxial+1/2 := by
    dsimp [U]
    rw [ShortOuterOne.SameContact.arc_zero]
  rw [hz] at hn
  have hvhi : TargetContact.v 0 x<(21/20:ℝ) := by
    norm_num [Inverse.q,Q0] at hn
    nlinarith [sq_nonneg (TargetContact.B 0 x-1/2),fine_outer_endpoint_bounds.1]
  have hK := (K_first_bounds hd.2.2).2
  have hp := mul_lt_mul hK hvhi hv (by norm_num : (0:ℝ)≤116/125)
  dsimp [angleFirst]
  norm_num at hp
  linarith

lemma axial_contact_lower {B x : ℝ} (hB : B∈Icc 0 outerDiagonal)
    (hx : x∈Icc 0 (7/10)) (hc : TargetContact.B 0 x=B) :
    (9/10:ℝ)<value 0 B (Real.pi/2-x) := by
  have hdom (t : ℝ) (ht : t∈Icc x (7/10)) : TargetContact.Domain 0 t := by
    have htf : t∈Icc 0 (7/10) := ⟨hx.1.trans ht.1,ht.2⟩
    have hlo := TargetContact.B_angle_monotone outer_zero_mem hx htf ht.1
    have hhi := TargetContact.B_angle_monotone outer_zero_mem htf (by norm_num) ht.2
    rw [hc] at hlo
    exact ⟨outer_zero_mem,htf,⟨hB.1.trans hlo,
      hhi.trans NegativeTwo.CapCurve.zero_domain.2⟩⟩
  have hanti : AntitoneOn (cost 0) (Icc x (7/10)) :=
    antiOn_of_hasDeriv_nonpos
      (fun t ht => (cost_angle_hasDerivAt (hdom t ht)).continuousAt.continuousWithinAt)
      (fun t ht => cost_angle_hasDerivAt (hdom t (Ioo_subset_Icc_self ht)))
      (fun t ht => (axial_angle_first (hdom t (Ioo_subset_Icc_self ht))).le)
  have hm := hanti ⟨le_rfl,hx.2⟩ ⟨hx.2,le_rfl⟩ hx.2
  have hcap := Cap.zero_value
  change (9/10:ℝ)<cost 0 (7/10) at hcap
  have hh := hcap.trans_le hm
  simpa only [cost,hc] using hh

theorem boundary_lower {b x : ℝ} (hd : TargetContact.Domain b x)
    (hb : Boundary b x) : (89777/100000:ℝ)<cost b x := by
  rcases hb with hzero | hdiag | halign | hcap | hBzero | hBdiag
  · have hh := axial_contact_lower (by simpa only [hzero] using hd.2.2) hd.2.1 rfl
    rw [hzero]
    dsimp [cost]
    linarith
  · have hh := DiagonalSource.original_contact
      (by simpa only [hdiag] using hd.2.2) hd.2.1 rfl
    rw [hdiag]
    dsimp [cost]
    linarith
  · have hh := aligned_contact_lower hd.1 (by simpa only [halign] using hd.2.2) rfl
    rw [halign]
    dsimp [cost]
    linarith
  · have hh := Cap.original_contact hd.1 (by simpa only [hcap] using hd.2.2) rfl
    rw [hcap]
    dsimp [cost]
    linarith
  · have hh := ZeroTarget.original_contact hd.1 hd.2.1 hBzero
    dsimp [cost]
    rw [hBzero]
    linarith
  · have hh := DiagonalTarget.original_contact hd.1 hd.2.1 hBdiag
    dsimp [cost]
    rw [hBdiag]
    linarith

theorem original_lower_contact {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 2 a b A B (-1) (-1) (Real.pi/2-x)) :
    ∃ b' B', b'∈Icc 0 outerDiagonal ∧ B'∈Icc 0 outerDiagonal ∧
      TargetContact.B b' x=B' ∧ value b' B' (Real.pi/2-x)≤value b B (Real.pi/2-x) := by
  have hb := NegativeTwo.source_mem hs
  have hB := NegativeTwo.source_mem ht
  have hcut := NegativeTwo.lower_target_cut hs hx hm
  by_cases hpos : 0≤TargetContact.B b x
  · have hd : TargetContact.B b x∈Icc 0 outerDiagonal := ⟨hpos,hcut.trans hB.2⟩
    have hK := K_monotone hd hB hcut
    refine ⟨b,TargetContact.B b x,hb,hd,rfl,?_⟩
    dsimp [value]
    linarith
  · have hd : outerDiagonal∈Icc 0 outerDiagonal := ⟨outer_zero_mem.2,le_rfl⟩
    have hdiag := TargetContact.B_angle_monotone hd (by norm_num) hx hx.1
    rw [TargetContact.B_zero,ShortOuterOne.SameContact.arc_diagonal] at hdiag
    have hcont : Continuous (fun t => TargetContact.B t x) := by
      dsimp [TargetContact.B,arc]
      fun_prop
    obtain ⟨b',hb',he⟩ := intermediate_value_Icc hb.2 hcont.continuousOn
      (show (0:ℝ)∈Icc (TargetContact.B b x) (TargetContact.B outerDiagonal x) by
        constructor <;> linarith [outer_endpoint_bounds.2.2.2])
    have hbnew : b'∈Icc 0 outerDiagonal := ⟨hb.1.trans hb'.1,hb'.2⟩
    have hT := T_monotone hb hbnew hb'.1
    have hK := K_monotone outer_zero_mem hB hB.1
    refine ⟨b',0,hbnew,outer_zero_mem,he,?_⟩
    dsimp [value]
    linarith

end SquaresInCircles.Eight.TableFree.SecondWord.NegativeThree.Contact

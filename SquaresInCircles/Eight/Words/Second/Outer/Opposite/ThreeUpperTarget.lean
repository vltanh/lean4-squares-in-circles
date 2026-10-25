module

public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ThreeAligned
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ThreeUpperDiagonal
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ThreeUpperTargetConcavity

/-!
# Eight squares: the complete original upper target-primary separator

The initial source interval reduces by whole-target concavity to its
actual aligned endpoint or the actual target diagonal.  Every later
source moves at fixed original target height to alignment or `.1`.
Both motions use the explicit inverse rotation and preserve weak ties.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeThree
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

lemma upper_inverse_before {a b A x : ℝ} (hs : OuterState a b)
    (hA : A∈Icc outerDiagonal outerAxial) (hx : x∈Icc 0 (7/10))
    (hcut : upperPrimary b x≤A) : UpperInverse.X (A-1/2) b≤x := by
  have hz : A-1/2∈UpperInverse.shifts := by
    constructor <;> linarith [hA.1,hA.2,fine_outer_endpoint_bounds.2,outer_endpoint_bounds.2.1]
  apply OppositeTwo.PrimaryInverse.weak_angle hs hx hz
  have hArc := (ShortOuterOne.SameContact.actual_arc hs).1
  dsimp [OppositeTwo.upperPrimary]
  dsimp [upperPrimary] at hcut
  rw [hArc] at hcut
  linarith

theorem upper_target_primary_early_cut {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hbsmall : b≤1/10) (hcut : upperPrimary b x≤A) :
    (89777/100000:ℝ)<value b B (Real.pi/2+x) := by
  have hb := NegativeTwo.source_mem hs
  have hB := NegativeTwo.source_mem ht
  have hA := NegativeTwo.primary_mem ht
  by_cases halign : 1+b≤A
  · have hh := aligned_first hs ht (by linarith)
    dsimp [value] at *
    linarith [hx.1]
  let l : ℝ := arc (1+b)
  have hstart : 1+b∈Icc outerDiagonal outerAxial := by
    constructor
    · linarith [hb.1,outer_endpoint_bounds.2.2.2]
    · linarith [primary_eleven_mem.2]
  have ht0 := ShortOuterOne.SameContact.primary_state hstart
  have hl : l∈Icc 0 outerDiagonal := NegativeTwo.source_mem ht0
  have hle : l≤B := by
    have hh := ShortOuterOne.SameContact.arc_antitone
      (primary_domain hA) (primary_domain hstart) (by linarith : A≤1+b)
    rw [(ShortOuterOne.SameContact.actual_arc ht).2] at hh
    exact hh
  have hlmin : (83/125:ℝ)≤l := by
    have hc := ht0.2.2
    have hleft : (1+b+1/2)^2≤(8/5:ℝ)^2 := by nlinarith [hb.1,hbsmall]
    change (1+b+1/2)^2+(l+1/2)^2=Q0 at hc
    norm_num [Q0] at hc
    nlinarith [hl.1]
  have hcost := UpperTarget.concave ⟨hb.1,hbsmall⟩
  have hmin := hcost.min_le_of_mem_Icc ⟨hlmin,hl.2⟩
    ⟨UpperTarget.target_start_mem.2,le_rfl⟩ ⟨hle,hB.2⟩
  have hleft : (89777/100000:ℝ)<UpperTarget.cost b l := by
    have hArc := (ShortOuterOne.SameContact.actual_arc ht0).1
    have hz : UpperTarget.z l=W b := by
      dsimp [UpperTarget.z,W,l]
      rw [hArc]
      ring
    have hX := OppositeTwo.PrimaryInverse.aligned hb hz
    have hh := aligned_first hs ht0 (show 1≤(1+b)-b by linarith)
    dsimp [UpperTarget.cost]
    rw [show UpperInverse.X (UpperTarget.z l) b = 0 from hX]
    dsimp [value] at hh
    linarith
  have hright : (89777/100000:ℝ)<UpperTarget.cost b outerDiagonal := by
    have hh := UpperDiagonal.lower hb
    have hz : UpperTarget.z outerDiagonal=UpperDiagonal.z := by
      dsimp [UpperTarget.z,UpperDiagonal.z,OppositeTwo.TargetRatio.z]
      rw [ShortOuterOne.SameContact.arc_diagonal]
    simpa only [UpperTarget.cost,UpperDiagonal.value,hz] using hh
  have hbase := (lt_min hleft hright).trans_le hmin
  have hbefore := upper_inverse_before hs hA hx hcut
  have hZ : UpperTarget.z B=A-1/2 := by
    dsimp [UpperTarget.z]
    rw [(ShortOuterOne.SameContact.actual_arc ht).1]
  dsimp [UpperTarget.cost] at hbase
  rw [hZ] at hbase
  dsimp [value]
  linarith

theorem upper_target_primary_cut {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hcut : upperPrimary b x≤A) :
    (89777/100000:ℝ)<value b B (Real.pi/2+x) := by
  by_cases hsmall : b≤1/10
  · exact upper_target_primary_early_cut hs ht hx hsmall hcut
  by_cases halign : 1+b≤A
  · have hh := aligned_first hs ht (by linarith)
    dsimp [value] at *
    linarith [hx.1]
  have hb := NegativeTwo.source_mem hs
  have hA := NegativeTwo.primary_mem ht
  let l : ℝ := max (1/10) (A-1)
  let z : ℝ := A-1/2
  have hz : z∈UpperInverse.shifts := UpperInverse.primary_shift ht
  have hdiag : outerDiagonal-1/2≤z := by dsimp [z]; linarith [hA.1]
  have hlb : l≤b := max_le (by linarith) (by linarith)
  have hl : l∈Icc (1/10) outerDiagonal := ⟨le_max_left _ _,hlb.trans hb.2⟩
  have hlphysical : l∈Icc 0 outerDiagonal := ⟨by linarith [hl.1],hl.2⟩
  have hs0 := ShortOuterOne.SameContact.arc_state hlphysical
  have hbefore := upper_inverse_before hs hA hx hcut
  have hXzero : 0≤UpperInverse.X z l := UpperInverse.X_nonnegative hlphysical (by
    have hh : A-1≤l := le_max_right _ _
    dsimp [z,W]
    linarith)
  have hXmono := UpperInverse.X_monotone hz hlphysical hb hlb
  have hXcap : UpperInverse.X z l∈Icc 0 (7/10) :=
    ⟨hXzero,hXmono.trans (hbefore.trans hx.2)⟩
  have hstep := UpperTarget.source_cost_monotone hz hdiag hl
    ⟨by linarith,hb.2⟩ hlb
  have hstart : (89777/100000:ℝ)<value l B (Real.pi/2+UpperInverse.X z l) := by
    by_cases hlate : (1/10:ℝ)≤A-1
    · have he : l=A-1 := max_eq_right hlate
      have hzW : z=W l := by dsimp [z,W]; rw [he]; ring
      have hzero := OppositeTwo.PrimaryInverse.aligned hlphysical hzW
      have hh := aligned_first hs0 ht (by rw [he]; linarith)
      rw [show UpperInverse.X z l = 0 from hzero,add_zero]
      linarith
    · have he : l=(1/10:ℝ) := max_eq_left (le_of_not_ge hlate)
      have hcontact := UpperInverse.X_contact hlphysical hz
      apply upper_target_primary_early_cut hs0 ht hXcap (by rw [he])
      rw [hcontact]
      dsimp [z]
      linarith
  dsimp [value] at hstart ⊢
  linarith

theorem original_upper_target_primary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 1 a b A B (-1) 1 (Real.pi/2+x)) :
    (89777/100000:ℝ)<value b B (Real.pi/2+x) :=
  upper_target_primary_cut hs ht hx (upper_target_primary hs hx hm)

end SquaresInCircles.Eight.SecondWord.OppositeThree

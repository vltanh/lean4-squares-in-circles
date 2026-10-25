module

public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ThreeAlignedShape
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ThreeUpperDiagonalData
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ThreeUpperDiagonal
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ThreeUpperTargetConcavity

/-!
# Eight squares: the complete original upper source-primary separator

At fixed physical source height the explicit inverse contact moves
monotonically in the target coordinate.  Its corrected cost increases
from alignment or the target `.2` boundary.  This finite comparison
covers inactive and active original inequalities together and retains
the original circle states and weak margin at both ends.
-/

section
/-!
## Both original aligned opposite edge-three inequalities

Each whole-arc curvature estimate is integrated from its single actual
reference.  The final statements accept only the original two circle
states and their weak aligned separator, retaining zero coordinates.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeThree
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio)

namespace Aligned

theorem forward_lower {y : ℝ} (hy : y∈Icc 0 bOne) : (89807/100000:ℝ)<cost false y := by
  have ht := curvature_tangent (f := cost false) (d := first false) (dd := second false)
    (κ := (11/50:ℝ)) hy (reference_mem false)
    (fun t ht => cost_hasDerivAt false ht) (fun t ht => first_hasDerivAt false ht)
    (fun t ht => (forward_curvature ht).le)
  have hd := abs_lt.mp (reference_first false)
  have hs : (first false (reference false))^2<(1/1000000:ℝ)^2 := by nlinarith
  have hp := sq_nonneg ((11/100:ℝ)*(y-reference false)+first false (reference false)/2)
  nlinarith [forward_reference_value]

theorem reverse_lower {y : ℝ} (hy : y∈Icc 0 bOne) : (44889/50000:ℝ)<cost true y := by
  have ht := curvature_tangent (f := cost true) (d := first true) (dd := second true)
    (κ := (87/100:ℝ)) hy (reference_mem true)
    (fun t ht => cost_hasDerivAt true ht) (fun t ht => first_hasDerivAt true ht)
    (fun t ht => (reverse_curvature ht).le)
  have hd := abs_lt.mp (reference_first true)
  have hs : (first true (reference true))^2<(1/1000000:ℝ)^2 := by nlinarith
  have hp := sq_nonneg ((87/200:ℝ)*(y-reference true)+first true (reference true)/2)
  nlinarith [reverse_reference_value]

end Aligned

lemma below_bOne_of_primary_one {a b : ℝ} (hs : OuterState a b) (ha : 1≤a) : b≤bOne := by
  have hh := ShortOuterOne.SameContact.arc_antitone (primary_domain primary_one_mem)
    (primary_domain (NegativeTwo.primary_mem hs)) ha
  rwa [(ShortOuterOne.SameContact.actual_arc hs).2] at hh

theorem aligned_first {a b A B : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hm : 1≤A-b) : (44889/50000:ℝ)<value b B (Real.pi/2) := by
  have hb := NegativeTwo.source_mem hs
  have hB := NegativeTwo.source_mem ht
  have hA : 1≤A := by linarith [hb.1]
  have hdom : B∈Icc 0 bOne := ⟨hB.1,below_bOne_of_primary_one ht hA⟩
  have hbj : b≤Aligned.j B := by
    dsimp [Aligned.j]
    rw [(ShortOuterOne.SameContact.actual_arc ht).1]
    linarith
  have hmono := T_monotone hb (Aligned.j_mem hdom) hbj
  have hl := Aligned.forward_lower hdom
  rw [Aligned.forward_value] at hl
  dsimp [value] at hl ⊢
  linarith

theorem aligned_last {a b A B : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hm : 1≤a-B) : (44889/50000:ℝ)<value b B (Real.pi/2) := by
  have hb := NegativeTwo.source_mem hs
  have hB := NegativeTwo.source_mem ht
  have ha : 1≤a := by linarith [hB.1]
  have hdom : b∈Icc 0 bOne := ⟨hb.1,below_bOne_of_primary_one hs ha⟩
  have hBj : B≤Aligned.j b := by
    dsimp [Aligned.j]
    rw [(ShortOuterOne.SameContact.actual_arc hs).1]
    linarith
  have hmono := L_monotone hB (Aligned.j_mem hdom) hBj
  have hl := Aligned.reverse_lower hdom
  rw [Aligned.reverse_value] at hl
  dsimp [value] at hl ⊢
  linarith

end SquaresInCircles.Eight.SecondWord.OppositeThree
end
end
end

section
/-!
## Original source-primary separators at and near alignment

The lower half flows directly to its aligned contact (`original_lower_source_primary`). In the
upper half with target coordinate at most `.2`, the first contact with the unchanged source lies
on one primary arc and has increasing corrected cost (`upper_source_primary_small_cut`). The weak
original separator and every endpoint tie are kept.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeThree
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

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
    exact ((hasDerivAt_id' (x := t)).neg.fun_add hh).congr_deriv (by ring)
  have hmono : MonotoneOn (fun y => -y+TPrimaryLabel.outer (lowerPrimary B y))
      (Icc 0 x) := monoOn_of_hasDeriv_nonneg
    (fun t ht' => (hd ht').continuousAt.continuousWithinAt)
    (fun t ht' => hd (Ioo_subset_Icc_self ht'))
    (fun t ht' => by
      have hh := hdom (Ioo_subset_Icc_self ht')
      linarith [lower_primary_speed_paid hB hh.1 hh.2])
  have hstep := hmono ⟨le_rfl,hx.1⟩ ⟨hx.1,le_rfl⟩ hx.1
  simp only at hstep
  rw [lowerPrimary_zero] at hstep
  have hM := NegativeThree.primary_monotone (hdom ⟨hx.1,le_rfl⟩).2 ha hcut
  rw [NegativeThree.primary_actual hs] at hM
  have hs0 := ShortOuterOne.SameContact.primary_state hzero
  have hbase := aligned_last hs0 ht (show 1≤(1+B)-B by linarith)
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
      exact ((hasDerivAt_id' (x := t)).fun_add hh).congr_deriv (by ring)
    have hmono : MonotoneOn (fun z => z+TPrimaryLabel.outer (upperPrimary B z))
        (Icc 0 y) := monoOn_of_hasDeriv_nonneg
      (fun t ht' => (hd ht').continuousAt.continuousWithinAt)
      (fun t ht' => hd (Ioo_subset_Icc_self ht'))
      (fun t ht' => by
        have hh := hdom (Ioo_subset_Icc_self ht')
        linarith [upper_primary_speed_paid ⟨hB.1,hBsmall⟩ hh.1 hh.2])
    have hstep := hmono ⟨le_rfl,hy.1⟩ ⟨hy.1,le_rfl⟩ hy.1
    simp only at hstep
    rw [upperPrimary_zero,he,NegativeThree.primary_actual hs] at hstep
    have hs0 := ShortOuterOne.SameContact.primary_state hzero
    have hbase := aligned_last hs0 ht (show 1≤(1+B)-B by linarith)
    have hactual := NegativeThree.primary_actual hs0
    dsimp [value] at hbase ⊢
    linarith [hy.2]

end SquaresInCircles.Eight.SecondWord.OppositeThree
end
end
end

section
/-!
## The complete original upper target-primary separator

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
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeThree
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
      using 1
    rfl
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
        linarith [show z=a-1/2 from rfl]
      exact upper_source_primary_small_cut hs ht0 (hdom ⟨le_rfl,hlB⟩).2
        (by rw [hl]) htarget
  dsimp [value] at hstart ⊢
  linarith

theorem original_upper_source_primary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 3 a b A B (-1) 1 (Real.pi/2+x)) :
    (44889/50000:ℝ)<value b B (Real.pi/2+x) :=
  upper_source_primary_cut hs ht hx (upper_source_primary ht hx hm)

end SquaresInCircles.Eight.SecondWord.OppositeThree
end
end
end

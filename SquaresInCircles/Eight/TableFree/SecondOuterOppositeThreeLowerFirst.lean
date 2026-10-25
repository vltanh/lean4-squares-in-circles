module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeThreeLowerFirstMotion
public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeThreeLowerOwners

/-!
# The complete first lower-secondary owner

Early and middle coordinates move directly to the proved rectangle.
On the terminal physical segment, concavity reduces to its initial
coordinate or the actual aligned contact.  All states and weak axes
remain those of the original edge.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.LowerFirst
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)
open LowerContact LowerGeometry LowerInverse

theorem contact_lower {b B : ℝ} (hd : Domain b B) :
    (89777/100000:ℝ)<LowerContact.cost false b B := by
  have hb : b∈Icc 0 (83/200) := ⟨hd.1.1,(domain_bounds hd).1.le⟩
  by_cases hB0 : B≤2/5
  · exact early_lower hb ⟨hd.2.1.1,hB0⟩
  by_cases hB1 : B≤1/2
  · exact middle_lower hb ⟨by linarith,hB1⟩
  have hB : (1/2:ℝ)≤B := by linarith
  have hA := NegativeTwo.primary_mem (ShortOuterOne.SameContact.arc_state hd.2.1)
  have ha : 1+b∈Icc outerDiagonal outerAxial := by
    constructor
    · linarith [hd.1.1,outer_endpoint_bounds.2.2.2]
    · linarith [hd.2.2,hA.2]
  let e : ℝ := arc (1+b)
  have he_state : OuterState (1+b) e := ShortOuterOne.SameContact.primary_state ha
  have he : e∈Icc 0 outerDiagonal := NegativeTwo.source_mem he_state
  have hearc : arc e=1+b := (ShortOuterOne.SameContact.actual_arc he_state).1
  have hBe : B≤e := by
    have hm := ShortOuterOne.SameContact.arc_antitone (primary_domain ha) (primary_domain hA)
      (show 1+b≤arc B by linarith [hd.2.2])
    have hback := (ShortOuterOne.SameContact.actual_arc
      (ShortOuterOne.SameContact.arc_state hd.2.1)).2
    rw [hback] at hm
    exact hm
  have hend : Domain b e := ⟨hd.1,he,by rw [hearc]; linarith⟩
  have hpath {y : ℝ} (hy : y∈Icc (1/2) e) : Domain b y :=
    domain_downward hend ⟨by linarith [hy.1],hy.2⟩
  have hconc : ConcaveOn ℝ (Icc (1/2) e) (LowerContact.cost false b) :=
    concave_of_deriv2
      (fun y hy => cost_outer_hasDerivAt false (hpath hy).2.1 (domain_bounds (hpath hy)).2.2)
      (fun y hy => outerFirst_outer_hasDerivAt false (hpath hy).2.1
        (domain_bounds (hpath hy)).2.2)
      (fun y hy => by have hh := late_outer_curvature (hpath hy) hy.1; linarith)
  have hleft : (89777/100000:ℝ)<LowerContact.cost false b (1/2) := middle_lower hb (by norm_num)
  have hright : (89777/100000:ℝ)<LowerContact.cost false b e := by
    have hh := aligned_lower false hend (by rw [hearc]; ring)
    linarith
  exact concave_gt_of_endpoints hconc ⟨hB,hBe⟩ hleft hright

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.LowerFirst

namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree
open CommonQuarter CorePairGeometry Arithmetic

theorem original_lower_source_secondary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 0 a b A B (-1) 1 (Real.pi/2-x)) :
    (89777/100000:ℝ)<value b B (Real.pi/2-x) := by
  obtain ⟨hd,hbetter⟩ := LowerContact.original_first_reduction hs ht hx hm
  exact (LowerFirst.contact_lower hd).trans_le hbetter

theorem original_lower_target_primary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 1 a b A B (-1) 1 (Real.pi/2-x)) :
    (89777/100000:ℝ)<value b B (Real.pi/2-x) :=
  original_lower_source_secondary hs ht hx
    (original_lower_target_primary_implies_first hs ht hx hm)

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree

module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeThreeLowerCriticalReferences

/-!
# The complete reverse critical minimum through its curved exit

Before the half-coordinate reference, positive source curvature gives
one tangent parabola.  Afterwards the decreasing source curvature and
positive initial slope force an endpoint minimum.  The terminal
endpoint is the proved aligned contact of the original circle.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.LowerCritical
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)
open LowerEnvelope

lemma early_second {B : ℝ} (hB : Domain B) (hb : source B≤1/2) : (3/50:ℝ)<second B := by
  have hle := (below_half_iff hB.1).2 hb
  have hm := second_antitone_between hB half_domain
    ⟨le_rfl,hle⟩ ⟨hle,le_rfl⟩ hle
  exact half_second.trans_le hm

theorem early_lower {B : ℝ} (hB : Domain B) (hb : source B≤1/2) :
    (89777/100000:ℝ)<cost B := by
  let l : ℝ := min B referencePoint
  let u : ℝ := max B referencePoint
  have hl : Domain l := by
    dsimp [l]
    rcases le_total B referencePoint with hh | hh
    · rw [min_eq_left hh]
      exact hB
    · rw [min_eq_right hh]
      exact reference_domain
  have hu : Domain u := by
    dsimp [u]
    rcases le_total B referencePoint with hh | hh
    · rw [max_eq_right hh]
      exact reference_domain
    · rw [max_eq_left hh]
      exact hB
  have hdom {y : ℝ} (hy : y∈Icc l u) : Domain y := domain_between hl hu hy
  have hmax : source u≤1/2 := by
    dsimp [u]
    rcases le_total B referencePoint with hh | hh
    · rw [max_eq_right hh,reference_source]
      norm_num
    · rw [max_eq_left hh]
      exact hb
  have hearly {y : ℝ} (hy : y∈Icc l u) : source y≤1/2 :=
    (source_monotone (hdom hy).1 hu.1 hy.2).trans hmax
  have ht := WeightedMinimum.tangent (f := cost) (d := first) (dd := second)
    (g := source) (w := sourceD) (κ := (3/50:ℝ))
    (show B∈Icc l u from ⟨min_le_left _ _,le_max_left _ _⟩)
    (show referencePoint∈Icc l u from ⟨min_le_right _ _,le_max_right _ _⟩)
    (fun y hy => cost_hasDerivAt (hdom hy))
    (fun y hy => first_hasDerivAt (hdom hy))
    (fun y hy => source_hasDerivAt (hdom hy).1)
    (fun y hy => (sourceD_positive (hdom hy).1).le)
    (fun y hy => (early_second (hdom hy) (hearly hy)).le)
  have hg := abs_lt.mp reference_first
  have hsq : (first referencePoint)^2<(1/100000000:ℝ) := by nlinarith
  have hpay := sq_nonneg ((3/50:ℝ)*(source B-source referencePoint)+first referencePoint)
  nlinarith [reference_value]

theorem physical_lower {B : ℝ} (hB : Domain B) (hp : B≤arc (source B)-1) :
    (89777/100000:ℝ)<cost B := by
  by_cases hearly : source B≤1/2
  · exact early_lower hB hearly
  have hleft : halfPoint≤B := (half_below_iff hB.1).2 (by linarith)
  have hright : B≤exitPoint := physical_before_exit hB hp
  have hdom {y : ℝ} (hy : y∈Icc halfPoint exitPoint) : Domain y :=
    domain_between half_domain exit_domain hy
  have hm := WeightedMinimum.endpoint (f := cost) (d := first) (dd := second)
    (w := sourceD) ⟨hleft,hright⟩
    (fun y hy => cost_hasDerivAt (hdom hy))
    (fun y hy => first_hasDerivAt (hdom hy))
    (fun y hy => (sourceD_positive (hdom hy).1).le)
    (second_antitone_between half_domain exit_domain)
    (show 0<first halfPoint by linarith [half_first])
  have hl : (89777/100000:ℝ)<cost halfPoint := early_lower half_domain (by rw [half_source])
  have hr : (89777/100000:ℝ)<cost exitPoint := by linarith [exit_value]
  exact (lt_min hl hr).trans_le hm

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.LowerCritical

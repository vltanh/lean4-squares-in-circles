module

public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ThreeLowerCriticalCalculus
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ThreeWeightedMinimum
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ThreeLowerCriticalReferences
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ThreeLowerFirst
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ThreeSourcePrimary
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.TwoCycle

/-!
# Eight squares: the complete original opposite-sign edge-three family in a physical cycle

The scalar bound is restored to the literal edge-three labels.
Reflected reversal exchanges edges three and five while preserving
the negative-to-positive sign pair.  The actual-cycle theorem uses
the existing selected weak owner on the original squares.
-/

section
/-!
## The complete reverse critical minimum through its curved exit

Before the half-coordinate reference, positive source curvature gives
one tangent parabola.  Afterwards the decreasing source curvature and
positive initial slope force an endpoint minimum.  The terminal
endpoint is the proved aligned contact of the original circle.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeThree.LowerCritical
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

end SquaresInCircles.Eight.SecondWord.OppositeThree.LowerCritical
end
end
end

section
/-!
## Every point of the reverse lower-secondary contact

The free coordinate has positive curvature on its whole closed
interval.  Before the source coordinate reaches three fifths, its
stationary point is the proved critical curve.  If that point lies
beyond the physical contact, monotonicity gives the actual aligned
endpoint.  The remaining source interval has a negative endpoint
derivative and reduces to the same aligned boundary.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeThree.LowerReverse
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)
open LowerContact
open LowerFirst (short_domain short_shift)

lemma free_curvature_positive {b B : ℝ} (hb : b∈Icc 0 (83/200))
    (hB : B∈Icc 0 outerDiagonal) : 0<freeSecond true b B := by
  have hL := L_second_early (show b∈Icc 0 (1/2) from ⟨hb.1,by linarith [hb.2]⟩)
  have hv := (OppositeTwo.PrimaryInverse.data hB (short_shift hb)).2.2.1
  have hz : 0<b+1/2 := by linarith [hb.1]
  have hp := div_pos hz (pow_pos hv 3)
  dsimp [freeSecond,LowerContact.inner]
  linarith

lemma free_first_monotone {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    MonotoneOn (fun b => freeFirst true b B) (Icc 0 (83/200)) := by
  apply monoOn_of_hasDeriv_nonneg
  · intro b hb
    exact (freeFirst_free_hasDerivAt true (short_domain hb) hB
      (short_shift hb)).continuousAt.continuousWithinAt
  · intro b hb
    exact freeFirst_free_hasDerivAt true (short_domain (Ioo_subset_Icc_self hb)) hB
      (short_shift (Ioo_subset_Icc_self hb))
  · intro b hb
    exact (free_curvature_positive (Ioo_subset_Icc_self hb) hB).le

lemma aligned_domain {b B : ℝ} (hd : Domain b B) : Domain (Aligned.j B) B :=
  ⟨Aligned.j_mem ⟨hd.2.1.1,(domain_bounds hd).2.1⟩,hd.2.1,le_rfl⟩

lemma aligned_short {b B : ℝ} (hd : Domain b B) : Aligned.j B∈Icc 0 (83/200) := by
  have hh := Aligned.j_bounds ⟨hd.2.1.1,(domain_bounds hd).2.1⟩
  exact ⟨hh.1,by linarith [hh.2]⟩

lemma aligned_minimum {b B : ℝ} (hd : Domain b B)
    (hfirst : freeFirst true (Aligned.j B) B≤0) :
    (89777/100000:ℝ)<LowerContact.cost true b B := by
  have hj := aligned_short hd
  have hm := free_first_monotone hd.2.1
  have hpath {y : ℝ} (hy : y∈Icc 0 (Aligned.j B)) : y∈Icc 0 (83/200) :=
    ⟨hy.1,hy.2.trans hj.2⟩
  have ha : AntitoneOn (fun y => LowerContact.cost true y B) (Icc 0 (Aligned.j B)) := by
    apply antiOn_of_hasDeriv_nonpos
    · intro y hy
      exact (cost_free_hasDerivAt true (short_domain (hpath hy)) hd.2.1
        (short_shift (hpath hy))).continuousAt.continuousWithinAt
    · intro y hy
      exact cost_free_hasDerivAt true (short_domain (hpath (Ioo_subset_Icc_self hy)))
        hd.2.1 (short_shift (hpath (Ioo_subset_Icc_self hy)))
    · intro y hy
      exact (hm (hpath (Ioo_subset_Icc_self hy)) hj hy.2.le).trans hfirst
  have hcost := ha (show b∈Icc 0 (Aligned.j B) from ⟨hd.1.1,hd.2.2⟩)
    ⟨hj.1,le_rfl⟩ hd.2.2
  have hboundary := aligned_lower true (aligned_domain hd) rfl
  linarith

lemma early_lower {b B : ℝ} (hd : Domain b B) (hB : B≤3/5) :
    (89777/100000:ℝ)<LowerContact.cost true b B := by
  have hsource : B∈Icc 0 (3/5) := ⟨hd.2.1.1,hB⟩
  let P : ℝ := LowerCritical.parameter B hsource
  have hP : P∈Icc (3/100) (3/20) := LowerCritical.parameter_mem hsource
  have hPs : P∈Icc 0 (83/200) := LowerEnvelope.mem_short hP
  have he : LowerCritical.source P=B := LowerCritical.source_parameter hsource
  have hstation := LowerCritical.stationary hP
  rw [he] at hstation
  by_cases hphysical : P≤Aligned.j B
  · have hp : P≤arc (LowerCritical.source P)-1 := by
      rw [he]
      exact hphysical
    have hmin := LowerCritical.physical_lower (LowerCritical.parameter_domain hsource) hp
    change (89777/100000:ℝ)<LowerContact.cost true P (LowerCritical.source P) at hmin
    rw [he] at hmin
    have ht := curvature_tangent (f := fun y => LowerContact.cost true y B)
      (d := fun y => freeFirst true y B) (dd := fun y => freeSecond true y B)
      (κ := 0) (show b∈Icc 0 (83/200) from ⟨hd.1.1,(domain_bounds hd).1.le⟩) hPs
      (fun y hy => cost_free_hasDerivAt true (short_domain hy) hd.2.1 (short_shift hy))
      (fun y hy => freeFirst_free_hasDerivAt true (short_domain hy) hd.2.1 (short_shift hy))
      (fun y hy => (free_curvature_positive hy hd.2.1).le)
    rw [hstation] at ht
    linarith
  · apply aligned_minimum hd
    have hm : freeFirst true (Aligned.j B) B≤freeFirst true P B :=
      free_first_monotone hd.2.1 (aligned_short hd) hPs (le_of_not_ge hphysical)
    rwa [hstation] at hm

lemma late_endpoint_negative {b B : ℝ} (hd : Domain b B) (hB : (3/5:ℝ)≤B) :
    freeFirst true (Aligned.j B) B<0 := by
  have hj := aligned_short hd
  have hcircle := UW_circle (outer_domain hd.2.1)
  have hW : (11/10:ℝ)≤W B := by dsimp [W]; linarith
  have hWsq := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤11/10) hW 2
  have hU : U B<(33/20:ℝ) := by
    by_contra hn
    have hUsq := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤33/20)
      (le_of_not_gt hn) 2
    norm_num [Q0] at hcircle
    nlinarith
  have hjSmall : Aligned.j B<(3/20:ℝ) := by dsimp [Aligned.j,U] at *; linarith
  have hp := LowerEnvelope.p_antitone hj (by norm_num : (3/20:ℝ)∈Icc 0 (83/200))
    hjSmall.le
  have hpEnd := LowerEnvelope.endpoint_label_bounds.2.1
  have hv := (OppositeTwo.PrimaryInverse.data hd.2.1 (short_shift hj)).2.2.1
  have hphysical := physical_speed (aligned_domain hd)
  have hrecip : 1/LowerInverse.speed (Aligned.j B+1/2) B≤(10/11:ℝ) := by
    apply (div_le_iff₀ hv).2
    linarith
  dsimp [freeFirst,LowerContact.inner,LowerEnvelope.p] at *
  linarith

theorem contact_lower {b B : ℝ} (hd : Domain b B) :
    (89777/100000:ℝ)<LowerContact.cost true b B := by
  by_cases hB : B≤3/5
  · exact early_lower hd hB
  · exact aligned_minimum hd (late_endpoint_negative hd (le_of_not_ge hB)).le

end SquaresInCircles.Eight.SecondWord.OppositeThree.LowerReverse

namespace SquaresInCircles.Eight.SecondWord.OppositeThree
open CommonQuarter CorePairGeometry Arithmetic

theorem original_lower_target_secondary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 2 a b A B (-1) 1 (Real.pi/2-x)) :
    (89777/100000:ℝ)<value b B (Real.pi/2-x) := by
  obtain ⟨hd,hbetter⟩ := LowerContact.original_third_reduction hs ht hx hm
  exact (LowerReverse.contact_lower hd).trans_le hbetter

end SquaresInCircles.Eight.SecondWord.OppositeThree
end
end
end

section
/-!
## All original owners of the negative-to-positive outer edge three

The four weak separating axes are covered on both sides of the
quarter angle.  The lower-secondary minima use their complete physical
contact domains; the remaining owners use the original aligned,
primary and diagonal comparisons.  Both closed angle endpoints and
all owner ties remain in the statement.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeThree
open CommonQuarter CorePairGeometry Arithmetic

theorem original_lower {a b A B x : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10)) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (-1) 1 (Real.pi/2-x)) :
    (89777/100000:ℝ)<value b B (Real.pi/2-x) := by
  fin_cases j
  · exact original_lower_source_secondary hs ht hx hm
  · exact original_lower_target_primary hs ht hx hm
  · exact original_lower_target_secondary hs ht hx hm
  · linarith [original_lower_source_primary hs ht hx hm]

theorem original_upper {a b A B x : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10)) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (-1) 1 (Real.pi/2+x)) :
    (89777/100000:ℝ)<value b B (Real.pi/2+x) := by
  fin_cases j
  · linarith [original_upper_source_secondary hs ht hx hm]
  · exact original_upper_target_primary hs ht hx hm
  · linarith [original_upper_target_secondary hs ht hx hm]
  · linarith [original_upper_source_primary hs ht hx hm]

theorem original_at_angle {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (-1) 1 φ) :
    (89777/100000:ℝ)<value b B φ := by
  by_cases hupper : Real.pi/2≤φ
  · have hx : φ-Real.pi/2∈Icc 0 (7/10) :=
      ⟨by linarith,(abs_le.mp hφ).2⟩
    have he : Real.pi/2+(φ-Real.pi/2)=φ := by ring
    have hmargin : 0≤Eight.forwardMargin j a b A B (-1) 1
        (Real.pi/2+(φ-Real.pi/2)) := by simpa only [he] using hm
    simpa only [he] using original_upper hs ht hx j hmargin
  · have hx : Real.pi/2-φ∈Icc 0 (7/10) :=
      ⟨by linarith,by linarith [(abs_le.mp hφ).1]⟩
    have he : Real.pi/2-(Real.pi/2-φ)=φ := by ring
    have hmargin : 0≤Eight.forwardMargin j a b A B (-1) 1
        (Real.pi/2-(Real.pi/2-φ)) := by simpa only [he] using hm
    simpa only [he] using original_lower hs ht hx j hmargin

end SquaresInCircles.Eight.SecondWord.OppositeThree
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeThree
open CommonQuarter CorePairGeometry Arithmetic QuarterWordGeometry

theorem original_cost {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (-1) 1 φ) :
    (89777/100000:ℝ)<SecondWord.cost 3 .outer .outer false true a b A B φ := by
  rw [cost_identity hs ht]
  exact original_at_angle hs ht hφ j hm

theorem original_reflected {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (-1) 1 φ) :
    (89777/100000:ℝ)<SecondWord.cost 5 .outer .outer false true a b A B φ := by
  have hrev : 0≤Eight.forwardMargin (reflectedOwner j) A B a b (-1) 1 φ := by
    simpa only [neg_neg] using
      (show 0≤Eight.forwardMargin (reflectedOwner j) A B a b (-(1:ℝ)) (-(-1:ℝ)) φ from by
        rw [margin_reflection]
        exact hm)
  have hh := original_cost ht hs hφ (reflectedOwner j) hrev
  have he := cost_reflection (3:Vertex) .outer .outer false true A B a b φ
  norm_num [reverseEdge] at he
  rwa [←he] at hh

theorem original_role (i : Vertex) (hi : i=3 ∨ i=5)
    {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (-1) 1 φ) :
    threshold i<SecondWord.cost i .outer .outer false true a b A B φ := by
  rw [threshold_value]
  rcases hi with rfl | rfl
  · linarith [original_cost hs ht hφ j hm]
  · linarith [original_reflected hs ht hφ j hm]

theorem actual_owner (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (i : Vertex) (hi : i=3 ∨ i=5)
    (hs : C.kind i=.outer) (ht : C.kind (next i)=.outer)
    (hσ : positiveOf C i=false) (hτ : positiveOf C (next i)=true)
    (j : Fin 4) (howner : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    threshold i<phaseValue F hgap i+wrongMarker C .second i-
      wrongMarker C .second (next i) := by
  have hk : F.word hgap pi_lt_22_over_7 i=1 := by
    rw [hw]
    rcases hi with rfl | rfl <;> norm_num [WordProblems.wrongWord]
  have he : phaseValue F hgap i-Real.pi/2=difference F i := by
    simp [phaseValue,hk]
  have hφ : |phaseValue F hgap i-Real.pi/2|≤7/10 := by
    rw [he]
    exact (difference_small F i).le
  have hsource : OuterState (C.a i) (C.b i) := by
    simpa [State,hs] using actual_state C i
  have htarget : OuterState (C.a (next i)) (C.b (next i)) := by
    simpa [State,ht] using actual_state C (next i)
  have hm := original_margin C F hgap i j howner
  simp only [hσ,hτ,WordProblems.sign,Bool.false_eq_true,↓reduceIte,
    Rat.cast_neg,Rat.cast_one] at hm
  have hh := original_role i hi hsource htarget hφ j hm
  simpa only [SecondWord.cost,label,wrongMarker,hs,ht,hσ,hτ] using hh

theorem actual (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (i : Vertex) (hi : i=3 ∨ i=5)
    (hs : C.kind i=.outer) (ht : C.kind (next i)=.outer)
    (hσ : positiveOf C i=false) (hτ : positiveOf C (next i)=true) :
    threshold i<phaseValue F hgap i+wrongMarker C .second i-
      wrongMarker C .second (next i) := by
  obtain ⟨j,hj⟩ := boundary_forward_complete C le_rfl i (C.selected i) (C.feasible i)
  have howner : (forwardAxis j).Feasible (C.square i) (C.square (next i)) := by
    simpa only [←hj] using C.feasible i
  exact actual_owner C F hgap hw i hi hs ht hσ hτ j howner

end SquaresInCircles.Eight.SecondWord.OppositeThree
end
end
end

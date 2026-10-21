module

public import SquaresInCircles.Eight.TableFree.ShortMixedZeroSameOwners
public import SquaresInCircles.Eight.TableFree.ZeroPrimaryCycle

/-!
# Complete mixed zero-quarter component of the short wrong word

Every original mixed secondary witness is covered with its original
signed role labels and both closed core pieces. The cyclic zero-primary
theorem supplies a secondary witness from the actual selected separator
once the independent continuous G1 pair theorem is available on this
same cycle. Uncompiled source draft.
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.TableFree.ShortMixedZero

open CommonQuarter CorePairGeometry WordProblems TableFreeWordGeometry

lemma zero_signs (i : Vertex) (hi : wrongWord .short i=0) (σ τ : Bool)
    (ha : allowed .short i σ τ) : σ=τ ∨ (σ=true ∧ τ=false) := by
  have hn := ha.2.2.2.2 hi
  cases σ <;> cases τ <;> simp_all

/-- The exhaustive original secondary-axis join. The only finite
case splits identify signs, radial roles and exact fixed coefficients. -/
theorem original_mixed_secondary (i : Vertex) (hi : wrongWord .short i=0)
    (source target : RadialKind) (σ τ : Bool) (ha : allowed .short i σ τ)
    {a b A B φ : ℝ} (hs : State source a b) (ht : State target A B)
    (hmixed : (source=.outer ∧ target≠.outer) ∨ (source≠.outer ∧ target=.outer))
    (hφ : |φ|≤7/10) (j : Fin 4) (hj : j=0 ∨ j=2)
    (hm : 0≤forwardMargin j a b A B (sign σ) (sign τ) φ) :
    (449/500:ℝ)<φ+wrongValue .short i source σ a b-
      wrongValue .short (next i) target τ A B := by
  rcases zero_signs i hi σ τ ha with he | ⟨rfl,rfl⟩
  · subst τ
    rcases hmixed with ⟨rfl,hcore⟩ | ⟨hcore,rfl⟩
    · have ho : OuterState a b := by simpa [State] using hs
      have hc : CoreState A B := by simpa [State,hcore] using ht
      rcases hj with rfl | rfl
      · exact same_outer_source i hi target hcore σ ha ho hc hφ hm
      · exact same_outer_target i hi target hcore σ ha ho hc hφ hm
    · have hc : CoreState a b := by simpa [State,hcore] using hs
      have ho : OuterState A B := by simpa [State] using ht
      rcases hj with rfl | rfl
      · exact same_core_source i hi source hcore σ ha hc ho hφ hm
      · exact same_core_target i hi source hcore σ ha hc ho hφ hm
  · have hr := zero_role i hi
    have hm' : 0≤forwardMargin j a b A B 1 (-1) φ := by simpa [sign] using hm
    rcases hmixed with ⟨rfl,hcore⟩ | ⟨hcore,rfl⟩
    · have ho : OuterState a b := by simpa [State] using hs
      have hc : CoreState A B := by simpa [State,hcore] using ht
      rcases hj with rfl | rfl
      · exact original_outer_secondary i hr target hcore ho hc hφ hm'
      · exact original_outer_target_secondary i hr target hcore ho hc hφ hm'
    · have hc : CoreState a b := by simpa [State,hcore] using hs
      have ho : OuterState A B := by simpa [State] using ht
      rcases hj with rfl | rfl
      · exact original_core_secondary i hr source hcore hc ho hφ hm'
      · exact original_core_target_secondary i hr source hcore hc ho hφ hm'

theorem actual_mixed_zero_secondary (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=wrongWord .short) (i : Vertex)
    (hk : F.word hgap pi_lt_22_over_7 i=0)
    (hmixed : (C.kind i=.outer ∧ C.kind (next i)≠.outer) ∨
      (C.kind i≠.outer ∧ C.kind (next i)=.outer))
    (j : Fin 4) (hj : j=0 ∨ j=2)
    (howner : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    (449/500:ℝ)<phaseValue F hgap i+wrongMarker C .short i-
      wrongMarker C .short (next i) := by
  have hi : wrongWord .short i=0 := by simpa [hw] using hk
  have hangle : |phaseValue F hgap i|≤7/10 := by
    simpa [phaseValue,hk] using (difference_small F i).le
  exact original_mixed_secondary i hi (C.kind i) (C.kind (next i))
    (positiveOf C i) (positiveOf C (next i)) (actual_allowed C F hgap .short hw i)
    (actual_state C i) (actual_state C (next i)) hmixed hangle j hj
    (original_margin C F hgap i j howner)

/-- The mixed zero-edge component on the actual closed cycle. The
upstream hypothesis is exactly the independent continuous G1 theorem;
it is used only to discharge the cyclic primary-owner alternative. -/
theorem actual_mixed_zero (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hpair : ∀k,handGamma (FramePair.branchOf C k).type (FramePair.branchOf C (next k)).type<
      (FramePair.stateOf C k).cost (FramePair.stateOf C (next k)) (FramePair.pairAngle C k))
    (hw : F.word hgap pi_lt_22_over_7=wrongWord .short) (i : Vertex)
    (hk : F.word hgap pi_lt_22_over_7 i=0)
    (hmixed : (C.kind i=.outer ∧ C.kind (next i)≠.outer) ∨
      (C.kind i≠.outer ∧ C.kind (next i)=.outer)) :
    (449/500:ℝ)<phaseValue F hgap i+wrongMarker C .short i-
      wrongMarker C .short (next i) := by
  obtain ⟨j,hj,howner⟩ := ZeroPrimary.original_zero_witness C F hgap hpair i hk
  exact actual_mixed_zero_secondary C F hgap hw i hk hmixed j hj howner

end SquaresInCircles.Eight.TableFree.ShortMixedZero

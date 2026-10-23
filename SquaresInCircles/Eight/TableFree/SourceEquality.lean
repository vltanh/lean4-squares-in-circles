module

public import SquaresInCircles.Eight.TableFree.OriginalWitnesses

/-!
# Source cases and strict original-witness comparisons

Uncompiled transcription of the finite source classification and scalar
comparisons in HAND_G5_GLOBAL_PRIMARY_ENTRY_ORIGINAL_EQUALITY_PULLBACK.md.

The seven source rows below are exhaustive, including zero totals, the
canceling HG2 owner, and already aligned negative primaries. Their reflected
version is the T table. This is a classification of inputs; the same-radius
geometric endpoint constructions attached to the rows remain separate proof
obligations and are not asserted by this module.

The final lemmas prove the strict GA1 and EH0 comparisons with exact
reserves. In particular, a weak initially retained axis cannot be replaced by
a convenient hard owner without these comparisons.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree

/-! ## Exact owner ties at zero primary error -/

theorem quarter_primary_normal_tie (K J : UnitSquare)
    (hc : J.cosine= -K.sine) (hs : J.sine=K.cosine) :
    (forwardAxis 0).normal K J=(forwardAxis 1).normal K J := by
  simp [forwardAxis,SignedAxis.normal,AxisOwner.normal,AxisSign.value,
    Eight.e,Eight.f,scale,hc,hs]

theorem reflected_quarter_primary_normal_tie (K J : UnitSquare)
    (hc : J.cosine= -K.sine) (hs : J.sine=K.cosine) :
    (forwardAxis 2).normal K J=(forwardAxis 3).normal K J := by
  simp [forwardAxis,SignedAxis.normal,AxisOwner.normal,AxisSign.value,
    Eight.e,Eight.f,scale,hc,hs]

theorem quarter_primary_feasible_tie (K J : UnitSquare)
    (hc : J.cosine= -K.sine) (hs : J.sine=K.cosine) :
    (forwardAxis 0).Feasible K J ↔ (forwardAxis 1).Feasible K J := by
  simp only [SignedAxis.Feasible,SignedAxis.projection,
    quarter_primary_normal_tie K J hc hs]

theorem reflected_quarter_primary_feasible_tie (K J : UnitSquare)
    (hc : J.cosine= -K.sine) (hs : J.sine=K.cosine) :
    (forwardAxis 2).Feasible K J ↔ (forwardAxis 3).Feasible K J := by
  simp only [SignedAxis.Feasible,SignedAxis.projection,
    reflected_quarter_primary_normal_tie K J hc hs]

/-! ## The seven genuinely missing-hard source rows -/

inductive GSourceCase
  | positiveTotal
  | wrongSignNonpositive
  | positivePrimaryNonpositive
  | negativeNoncanceling
  | positiveCanceling
  | negativeCanceling
  | alignedNegative
  deriving DecidableEq

/--
canceling=false denotes HG0; canceling=true denotes HG2.
x=thetaA-thetaG and total=thetaA-thetaH. Therefore HG is aligned
exactly when total=x. y is the actual signed G coordinate.
-/
def GSourceCase.Holds (row : GSourceCase) (canceling : Bool)
    (x total y : ℝ) : Prop :=
  match row with
  | .positiveTotal => canceling=false ∧ 0<total
  | .wrongSignNonpositive => canceling=false ∧ total≤0 ∧ 0≤y
  | .positivePrimaryNonpositive =>
      canceling=false ∧ total≤0 ∧ y<0 ∧ 0<x
  | .negativeNoncanceling =>
      canceling=false ∧ total≤0 ∧ y<0 ∧ x<0 ∧ total≠x
  | .positiveCanceling => canceling=true ∧ y<0 ∧ 0<x
  | .negativeCanceling => canceling=true ∧ y<0 ∧ x<0 ∧ total≠x
  | .alignedNegative => x<0 ∧ total=x

/-- No sign or zero-total row is discarded. The implication for HG2 is the
actual zero-owner sign consequence supplied by global owner rigidity. -/
theorem missing_hard_g_source_cases (canceling : Bool) {x total y : ℝ}
    (hx0 : x≠0) (hcanceling : canceling=true → y<0) :
    ∃ row : GSourceCase, row.Holds canceling x total y := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · by_cases ha : total=x
    · exact ⟨.alignedNegative,hx,ha⟩
    · cases hb : canceling
      · by_cases ht : 0<total
        · exact ⟨.positiveTotal,hb,ht⟩
        · have ht0 : total≤0 := le_of_not_gt ht
          by_cases hy : 0≤y
          · exact ⟨.wrongSignNonpositive,hb,ht0,hy⟩
          · exact ⟨.negativeNoncanceling,hb,ht0,lt_of_not_ge hy,hx,ha⟩
      · exact ⟨.negativeCanceling,hb,hcanceling hb,hx,ha⟩
  · exact (hx0 hx).elim
  · cases hb : canceling
    · by_cases ht : 0<total
      · exact ⟨.positiveTotal,hb,ht⟩
      · have ht0 : total≤0 := le_of_not_gt ht
        by_cases hy : 0≤y
        · exact ⟨.wrongSignNonpositive,hb,ht0,hy⟩
        · exact ⟨.positivePrimaryNonpositive,hb,ht0,lt_of_not_ge hy,hx⟩
    · exact ⟨.positiveCanceling,hb,hcanceling hb,hx⟩

/-- The exact sign substitution for (H,G,A)=(D,T,B) under reflection:
the actual T coordinate y is read as -y in the G source theorem. -/
theorem missing_hard_t_source_cases (canceling : Bool) {z total y : ℝ}
    (hz0 : z≠0) (hcanceling : canceling=true → 0<y) :
    ∃ row : GSourceCase, row.Holds canceling z total (-y) := by
  apply missing_hard_g_source_cases canceling hz0
  intro h
  have hy := hcanceling h
  linarith

/-- This is precisely the obstruction carried by a hard endpoint whose
ancestor lacked its hard primary. It is not an endpoint-existence claim. -/
def HardEndpointObstruction (total retainedSlack : ℝ) : Prop :=
  0<total ∨ 0<retainedSlack

theorem g_obstruction_incompatible_with_hard_equality
    {total retainedSlack tilt : ℝ} (ht : 0<tilt)
    (hframe : total= -tilt) (hcontact : retainedSlack=0)
    (h : HardEndpointObstruction total retainedSlack) : False := by
  rcases h with h | h <;> linarith

theorem t_obstruction_incompatible_with_hard_equality
    {total retainedSlack : ℝ}
    (hframe : total=0) (hcontact : retainedSlack=0)
    (h : HardEndpointObstruction total retainedSlack) : False := by
  rcases h with h | h <;> linarith

/-! ## True-core avoidance gives the GA reserve -/

theorem sorted_core_primary_reserve {a b : ℝ} (hba : b≤a)
    (hcore : (1/12 : ℝ)^2 ≤
      (max (a-1/2) 0)^2+(max (b-1/2) 0)^2) :
    447/800<a := by
  by_contra! ha
  have hA : max (a-1/2) 0 ≤ 47/800 :=
    max_le (by linarith) (by norm_num)
  have hBA : max (b-1/2) 0 ≤ max (a-1/2) 0 :=
    max_le_max (by linarith) le_rfl
  have hB : max (b-1/2) 0 ≤ 47/800 := hBA.trans hA
  have hA2 := pow_le_pow_left₀ (le_max_right (a-1/2) 0) hA 2
  have hB2 := pow_le_pow_left₀ (le_max_right (b-1/2) 0) hB 2
  norm_num at hA2 hB2
  nlinarith

theorem original_core_primary_reserve {K : UnitSquare} (hc : CoreAvoiding K)
    (hsorted : beta K (0,0) ≤ alpha K (0,0)) :
    447/800 < alpha K (0,0) := by
  apply sorted_core_primary_reserve hsorted
  simpa only [coreDistanceSq,coreRadius] using
    (coreAvoiding_iff_distance K).1 hc

/-- Exact whole-domain coefficient reserve in the GA0-GA1 comparison. -/
theorem ga_coefficient_reserve {aG bA A κ : ℝ}
    (haG : 447/800<aG) (hbA : bA<11/25)
    (hA : A<71/50) (hA0 : 0≤A)
    (hκ : κ<13/200) (hκ0 : 0≤κ) :
    529/20000 < aG-bA-A*κ := by
  have hp : A*κ ≤ (71/50 : ℝ)*(13/200) :=
    mul_le_mul hA.le hκ.le hκ0 (by norm_num)
  linarith

theorem ga_projection_difference {aG aA bA g s c κ : ℝ}
    (hhalf : 1-c=s*κ) :
    (aA*c-bA*s-g)-(aA-aG*s-g*c) =
      s*(aG-bA-(aA+g)*κ) := by
  linear_combination -(aA+g)*hhalf

/-- GA0 is tight on the stationary source, so the strict comparison rules
out an initially retained weak GA1. No upper radial bound on G is used. -/
theorem ga1_strictly_unavailable {aG aA bA g s c κ W : ℝ}
    (hs : 0<s) (hhalf : 1-c=s*κ)
    (haG : 447/800<aG) (hbA : bA<11/25)
    (hA : aA+g<71/50) (hA0 : 0≤aA+g)
    (hκ : κ<13/200) (hκ0 : 0≤κ)
    (hcontact : aA*c-bA*s-g=W) :
    aA-aG*s-g*c < W := by
  have hr := ga_coefficient_reserve haG hbA hA hA0 hκ hκ0
  have hr0 : 0<aG-bA-(aA+g)*κ := by linarith
  have hdiff : 0<(aA*c-bA*s-g)-(aA-aG*s-g*c) := by
    rw [ga_projection_difference hhalf]
    exact mul_pos hs hr0
  linarith

/-- The sharper displayed reserve is available when needed for the weak
selected-axis contradiction. -/
theorem ga_projection_strict_reserve {aG aA bA g s c κ : ℝ}
    (hs : 0<s) (hhalf : 1-c=s*κ)
    (haG : 447/800<aG) (hbA : bA<11/25)
    (hA : aA+g<71/50) (hA0 : 0≤aA+g)
    (hκ : κ<13/200) (hκ0 : 0≤κ) :
    (529/20000)*s <
      (aA*c-bA*s-g)-(aA-aG*s-g*c) := by
  rw [ga_projection_difference hhalf]
  have h := mul_lt_mul_of_pos_left
    (ga_coefficient_reserve haG hbA hA hA0 hκ hκ0) hs
  simpa only [mul_comm] using h

theorem eh_projection_difference (aH bH aE bE s c : ℝ) :
    (aH+aE*s-bE*c)-(aH*c+bH*s-bE) =
      (aE-bH)*s+(aH+bE)*(1-c) := by
  ring

/-- EH1 is tight on the stationary source; EH0 lies strictly below the
same required width. This keeps the sign of the original physical normal. -/
theorem eh0_strictly_unavailable {aH bH aE bE s c W : ℝ}
    (hs : 0<s) (hc : c≤1) (hgap : bH<aE)
    (hpositive : 0≤aH+bE) (hcontact : aH+aE*s-bE*c=W) :
    aH*c+bH*s-bE < W := by
  have hfirst : 0<(aE-bH)*s := mul_pos (sub_pos.mpr hgap) hs
  have hsecond : 0≤(aH+bE)*(1-c) :=
    mul_nonneg hpositive (sub_nonneg.mpr hc)
  have hdiff := eh_projection_difference aH bH aE bE s c
  linarith

end SquaresInCircles.Eight.TableFree

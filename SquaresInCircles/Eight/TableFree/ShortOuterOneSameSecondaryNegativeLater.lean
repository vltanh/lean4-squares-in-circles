module

public import SquaresInCircles.Eight.TableFree.ShortOuterOneSameSecondaryTargetDiagonal

/-!
# Complete negative halves of the second and third secondary owners

Uncompiled transcription of Sections 3--4 of
`HAND_SHORT_WORD_SAME_SIGN_SECONDARY_COMPLETE_WITHOUT_TABLES.md`.
The strict target derivative sends each genuine contact to the target
diagonal or to the source diagonal. Source slack is removed by its
actual monotone label, and zero-source target slack moves to contact.
The original weak separator is retained in the concluding theorem.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterOne.Same.Secondary.Negative.Later
open CommonQuarter CorePairGeometry Arithmetic
open SameContact (arc)

lemma interval_domain {B C D x : ℝ} (hB : Domain B x) (hC : Domain C x)
    (hD : D∈Icc B C) : Domain D x := by
  have hDouter : D∈Icc 0 outerDiagonal := ⟨hB.1.1.trans hD.1,hD.2.trans hC.1.2⟩
  have hmono := contact_target_monotone hB.2.1
  exact ⟨hDouter,hB.2.1,
    ⟨hB.2.2.1.trans (hmono hB.1 hDouter hD.1),
      (hmono hDouter hC.1 hD.2).trans hC.2.2.2⟩⟩

lemma target_motion (r : Row) (hr : r=1 ∨ r=2) {B C x : ℝ}
    (hB : Domain B x) (hC : Domain C x) (hBC : B≤C) : cost r C x≤cost r B x := by
  have ha : AntitoneOn (fun D => cost r D x) (Icc B C) := antiOn_of_hasDeriv_nonpos
    (fun D hD => (cost_target_hasDerivAt r (interval_domain hB hC hD)).continuousAt.continuousWithinAt)
    (fun D hD => cost_target_hasDerivAt r (interval_domain hB hC (Ioo_subset_Icc_self hD)))
    (fun D hD => (TargetRatio.target_negative r hr
      (interval_domain hB hC (Ioo_subset_Icc_self hD))).le)
  exact ha ⟨le_rfl,hBC⟩ ⟨hBC,le_rfl⟩ hBC

theorem contact_lower (r : Row) (hr : r=1 ∨ r=2) {B x : ℝ} (hd : Domain B x) :
    (8981/10000:ℝ)<cost r B x := by
  have hdiag : outerDiagonal∈Icc 0 outerDiagonal :=
    ⟨by linarith [outer_endpoint_bounds.2.2.1],le_rfl⟩
  by_cases hfits : contact outerDiagonal x≤outerDiagonal
  · have hD : Domain outerDiagonal x :=
      ⟨hdiag,hd.2.1,⟨(diagonal_contact_positive hd.2.1).le,hfits⟩⟩
    exact (TargetDiagonal.original_contact r hr hD).trans_le (target_motion r hr hd hD hd.1.2)
  · have hc : Continuous (fun D => contact D x) := by dsimp [contact,arc]; fun_prop
    obtain ⟨D,hD,he⟩ := intermediate_value_Icc hd.1.2 hc.continuousOn
      (show outerDiagonal∈Icc (contact B x) (contact outerDiagonal x) from
        ⟨hd.2.2.2,le_of_not_ge hfits⟩)
    beta_reduce at he
    have hDouter : D∈Icc 0 outerDiagonal := ⟨hd.1.1.trans hD.1,hD.2⟩
    have hDD : Domain D x := ⟨hDouter,hd.2.1,by rw [he]; exact hdiag⟩
    have hsource := SourceDiagonal.original_contact r hr (SameContact.arc_state hDouter)
      hd.2.1 (by simpa [contact] using he)
    have hbound : (8981/10000:ℝ)<cost r D x := by
      dsimp [cost]
      rw [he,target,SameContact.arc_diagonal,targetCost]
      linarith
    exact hbound.trans_le (target_motion r hr hd hDD hD.1)

theorem original (r : Row) (hr : r=1 ∨ r=2) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : (1+Real.cos x+Real.sin x)/2≤b+A*Real.cos x-B*Real.sin x) :
    (8981/10000:ℝ)<Real.pi/2-x+c r-P r*a+t r*b+p r*A-q r*B := by
  have hb : b∈Icc 0 outerDiagonal := ⟨hs.1,(outer_bounds hs).2.2.2.1⟩
  have hB : B∈Icc 0 outerDiagonal := ⟨ht.1,(outer_bounds ht).2.2.2.1⟩
  have hrequired : contact B x≤b := by
    dsimp [contact]
    rw [(SameContact.actual_arc ht).1]
    linarith
  have hcost : Real.pi/2-x+c r+target r b+targetCost r B=
      Real.pi/2-x+c r-P r*a+t r*b+p r*A-q r*B := by
    have hh := Secondary.original_cost r hs ht
    linarith
  rw [←hcost]
  by_cases hactive : 0≤contact B x
  · have hd : Domain B x := ⟨hB,hx,⟨hactive,hrequired.trans hb.2⟩⟩
    have hsource := target_monotone r hd.2.2 hb hrequired
    have hh := contact_lower r hr hd
    dsimp [cost] at hh
    linarith
  · have hdiag : outerDiagonal∈Icc 0 outerDiagonal :=
      ⟨by linarith [outer_endpoint_bounds.2.2.1],le_rfl⟩
    have hc : Continuous (fun D => contact D x) := by dsimp [contact,arc]; fun_prop
    obtain ⟨D,hD,he⟩ := intermediate_value_Icc hB.2 hc.continuousOn
      (show (0:ℝ)∈Icc (contact B x) (contact outerDiagonal x) from
        ⟨by linarith,(diagonal_contact_positive hx).le⟩)
    beta_reduce at he
    have hDouter : D∈Icc 0 outerDiagonal := ⟨hB.1.trans hD.1,hD.2⟩
    have htarget := targetCost_antitone r hB hDouter hD.1
    have hsource := target_monotone r (show (0:ℝ)∈Icc 0 outerDiagonal from
      ⟨le_rfl,hdiag.1⟩) hb hb.1
    have hh := contact_lower r hr (show Domain D x from
      ⟨hDouter,hx,by rw [he]; exact ⟨le_rfl,hdiag.1⟩⟩)
    dsimp [cost] at hh
    rw [he] at hh
    linarith

end SquaresInCircles.Eight.TableFree.ShortOuterOne.Same.Secondary.Negative.Later

module

public import SquaresInCircles.Eight.TableFree.NonpositiveOwnerSharp
public import SquaresInCircles.Eight.TableFree.HardMiddleAlignment

/-!
# Nonpositive outer errors with an arbitrary original middle

Uncompiled source draft.  No original AB alignment, middle tangent sum,
G/T sign, or middle frame order is assumed.  The complete hard-middle
construction changes only A/B and charges each source defect to a rigid
anchor.  Its nonpositive terminal forces all source defects to vanish.
The sharp theorem is then reapplied to the untouched original hard input.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SignedCycle
open Candidate ExactFamily GeometricModel

/-- The nonpositive outer-error domain already has its canonical middle
at the sharp ceiling.  This is original-source rigidity, not an identity
between arbitrarily constructed middle points and their ancestors. -/
theorem HardInput.nonpositive_outer_middle {q : ℝ}
    (I : HardInput q) (hqL : qLow≤q) (hqq : q≤qStar)
    (hGH : I.cycle.theta G≤I.cycle.theta H)
    (hDT : I.cycle.theta D≤I.cycle.theta T) :
    I.cycle.theta A=I.cycle.theta B ∧
      I.cycle.theta A∈Icc (I.cycle.theta T) (I.cycle.theta G) ∧
      (I.cycle.point A).y-(I.cycle.point B).y=1 := by
  have hcap : q≤qCap := hqq.trans qStar_limits.2.2.le
  obtain ⟨J,hJAB,hJrange,hJnorm,hnon,hstrict,hfixed⟩ := I.canonicalize_middle hcap
  have hH := hfixed H (by decide) (by decide)
  have hG := hfixed G (by decide) (by decide)
  have hT := hfixed T (by decide) (by decide)
  have hD := hfixed D (by decide) (by decide)
  have hJAG : J.cycle.theta A≤J.cycle.theta G := by rw [hG.2]; exact hJrange.2
  have hJGH : J.cycle.theta G≤J.cycle.theta H := by rw [hG.2,hH.2]; exact hGH
  have hJDT : J.cycle.theta D≤J.cycle.theta T := by rw [hD.2,hT.2]; exact hDT
  have hJTB : J.cycle.theta T≤J.cycle.theta B := by
    rw [hT.2,←hJAB]; exact hJrange.1
  have hs := J.nonpositive_owner_sharp hqL hqq hJAB hJnorm hJAG hJGH hJDT hJTB
  have hnoloss : ¬StrictAnchorLoss I.cycle J.cycle :=
    no_strict_loss_to_on_circle
      (fun i _ => (I.necessary.contained i).trans hqq) hs.2.2.2.2.2.2.1
  have hAB : I.cycle.theta A=I.cycle.theta B := by
    by_contra hne
    exact hnoloss (hstrict (Or.inl hne))
  have hTA : I.cycle.theta T≤I.cycle.theta A := by
    by_contra! hbad
    exact hnoloss (hstrict (Or.inr (Or.inl hbad)))
  have hAG : I.cycle.theta A≤I.cycle.theta G := by
    by_contra! hbad
    exact hnoloss (hstrict (Or.inr (Or.inr (Or.inl hbad))))
  have hsum : (I.cycle.point A).y-(I.cycle.point B).y≤1 := by
    by_contra! hbad
    exact hnoloss (hstrict (Or.inr (Or.inr (Or.inr hbad))))
  exact ⟨hAB,⟨hTA,hAG⟩,le_antisymm hsum (I.aligned_AB_gap hAB)⟩

/-- The full hard source with both nonpositive outer errors.  Only the
two original outer comparisons are inputs beyond the hard geometric
domain; all original middle identities, E alignment and sharp contacts
are conclusions. -/
theorem HardInput.nonpositive_outer_sharp {q : ℝ}
    (I : HardInput q) (hqL : qLow≤q) (hqq : q≤qStar)
    (hGH : I.cycle.theta G≤I.cycle.theta H)
    (hDT : I.cycle.theta D≤I.cycle.theta T) :
    I.cycle.theta A=I.cycle.theta B ∧
      (I.cycle.point A).y-(I.cycle.point B).y=1 ∧
      q=qStar ∧ I.cycle.theta G=I.cycle.theta H ∧
      I.cycle.theta B=I.cycle.theta T ∧ I.cycle.theta T=I.cycle.theta D ∧
      I.cycle.theta E=I.cycle.theta D ∧
      I.cycle.theta H-I.cycle.theta D=FiveCorner.selected.angle ∧
      AllAnchorsOn qStar I.cycle ∧
      ∀ i j,j∈terminalOwners i → I.cycle.slack i j=0 := by
  obtain ⟨hAB,hrange,hnorm⟩ := I.nonpositive_outer_middle hqL hqq hGH hDT
  have hTB : I.cycle.theta T≤I.cycle.theta B := by rw [←hAB]; exact hrange.1
  exact ⟨hAB,hnorm,I.nonpositive_owner_sharp hqL hqq hAB hnorm hrange.2 hGH hDT hTB⟩

theorem HardInput.nonpositive_outer_lower_bound {q : ℝ}
    (I : HardInput q) (hqL : qLow≤q)
    (hGH : I.cycle.theta G≤I.cycle.theta H)
    (hDT : I.cycle.theta D≤I.cycle.theta T) : qStar≤q := by
  by_cases h : qStar≤q
  · exact h
  · exact (I.nonpositive_outer_sharp hqL (lt_of_not_ge h).le hGH hDT).2.2.1.symm.le

end SquaresInCircles.Eight.TableFree.SignedCycle

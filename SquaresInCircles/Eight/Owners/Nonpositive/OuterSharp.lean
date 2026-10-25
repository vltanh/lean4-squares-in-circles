module

public import SquaresInCircles.Eight.Owners.Hard.Rigidity
public import SquaresInCircles.Eight.Owners.Nonpositive.HardSharp

/-!
# Eight squares: nonpositive outer errors with an arbitrary original middle

No original AB alignment, middle tangent sum,
G/T sign, or middle frame order is assumed.  The complete hard-middle
construction changes only A/B and charges each source defect to a rigid
anchor.  Its nonpositive terminal forces all source defects to vanish.
The sharp theorem is then reapplied to the untouched original hard input.
-/

section
/-!
## Every original zero owner in the nonpositive hard terminal

The original HG and TD witnesses may each
be either of their two allowed weak owners.  If the corresponding
noncanceling axis were unavailable, its actual canceling transport
would incur a strict loss at A or B.  The full nonpositive sharp
theorem excludes that loss.  Both required axes are consequently
available on the untouched source, where the sharp theorem is applied
again.  Weak aligned ties are included in the original owner tests.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.SignedCycle
open Candidate Stationary GeometricModel

private theorem feasible_congr {C C' : SignedCycle} {i k : Vertex} (hk : next i=k) {j : Fin 4}
    (h1 : C'.point i=C.point i) (h2 : C'.theta i=C.theta i)
    (h3 : C'.point k=C.point k) (h4 : C'.theta k=C.theta k) :
    C'.Feasible i j ↔ C.Feasible i j := by
  subst hk
  simp only [Feasible,slack,edge,delta,h1,h2,h3,h4]

theorem HardInput.nonpositive_original_TD_two {q : ℝ}
    (I : HardInput q) (hqL : qLow≤q) (hqq : q≤qStar)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hGH : I.cycle.theta G≤I.cycle.theta H)
    (hDT : I.cycle.theta D≤I.cycle.theta T)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hHG : I.cycle.Feasible H 0) : I.cycle.Feasible T 2 := by
  by_contra hnot
  have hcap : q≤qCap := hqq.trans qStar_limits.2.2.le
  have hTD : I.cycle.Feasible T 0 := by
    have hj : I.witnesses.owner T=0 ∨ I.witnesses.owner T=2 := by
      simpa [normalOwners,T] using I.witnesses.allowed T
    rcases hj with hj | hj
    · simpa [hj] using I.witnesses.feasible T
    · exact False.elim (hnot (by simpa [hj] using I.witnesses.feasible T))
  have hneq : I.cycle.theta T≠I.cycle.theta D := fun h =>
    hnot (I.aligned_TD_two h)
  have hstrict : I.cycle.theta D<I.cycle.theta T := lt_of_le_of_ne hDT (Ne.symm hneq)
  obtain ⟨J,hJTDframe,hJAB,hJBy,hnon,hloss,hθ,hpoint⟩ :=
    I.align_nonpositive_TD0 hqL hcap hAB hDT hTB hTD
  have hH := hpoint H (by decide) (by decide)
  have hG := hpoint G (by decide) (by decide)
  have hA := hpoint A (by decide) (by decide)
  have hJnorm : (J.cycle.point A).y-(J.cycle.point B).y=1 := by
    rw [hA,hJBy]; exact hnorm
  have hJAG : J.cycle.theta A≤J.cycle.theta G := by
    rw [hθ A (by decide),hθ G (by decide)]; exact hAG
  have hJGH : J.cycle.theta G≤J.cycle.theta H := by
    rw [hθ G (by decide),hθ H (by decide)]; exact hGH
  have hJDT : J.cycle.theta D≤J.cycle.theta T := hJTDframe.ge
  have hJTB : J.cycle.theta T≤J.cycle.theta B := by
    rw [hJTDframe,hθ D (by decide),hθ B (by decide)]
    exact hDT.trans hTB
  have hJHG : J.cycle.Feasible H 0 := by
    exact (feasible_congr (k := G) (by decide) hH (hθ H (by decide)) hG
      (hθ G (by decide))).2 hHG
  have hs := J.nonpositive_sharp hqL hqq hJAB hJnorm hJAG hJGH hJDT hJTB hJHG
    (J.aligned_TD_two hJTDframe)
  exact no_strict_loss_to_on_circle
    (fun i _ => (I.necessary.contained i).trans hqq) hs.2.2.2.2.2.2.1 (hloss hstrict)

theorem HardInput.nonpositive_original_HG_zero {q : ℝ}
    (I : HardInput q) (hqL : qLow≤q) (hqq : q≤qStar)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hGH : I.cycle.theta G≤I.cycle.theta H)
    (hDT : I.cycle.theta D≤I.cycle.theta T)
    (hTB : I.cycle.theta T≤I.cycle.theta B) : I.cycle.Feasible H 0 := by
  by_contra hnot
  have hcap : q≤qCap := hqq.trans qStar_limits.2.2.le
  have hHG : I.cycle.Feasible H 2 := by
    have hj : I.witnesses.owner H=0 ∨ I.witnesses.owner H=2 := by
      simpa [normalOwners,H] using I.witnesses.allowed H
    rcases hj with hj | hj
    · exact False.elim (hnot (by simpa [hj] using I.witnesses.feasible H))
    · simpa [hj] using I.witnesses.feasible H
  have hneq : I.cycle.theta G≠I.cycle.theta H := fun h =>
    hnot (I.aligned_HG_zero h)
  have hstrict : I.cycle.theta G<I.cycle.theta H := lt_of_le_of_ne hGH hneq
  obtain ⟨J,hJGHframe,hJAB,hJAy,hnon,hloss,hθ,hpoint⟩ :=
    I.align_nonpositive_HG2 hqL hcap hAB hAG hGH hHG
  have hB := hpoint B (by decide) (by decide)
  have hJnorm : (J.cycle.point A).y-(J.cycle.point B).y=1 := by
    rw [hJAy,hB]; exact hnorm
  have hJAG : J.cycle.theta A≤J.cycle.theta G := by
    rw [hJGHframe,hθ A (by decide),hθ H (by decide)]
    exact hAG.trans hGH
  have hJGH : J.cycle.theta G≤J.cycle.theta H := hJGHframe.le
  have hJDT : J.cycle.theta D≤J.cycle.theta T := by
    rw [hθ D (by decide),hθ T (by decide)]; exact hDT
  have hJTB : J.cycle.theta T≤J.cycle.theta B := by
    rw [hθ T (by decide),hθ B (by decide)]; exact hTB
  have hJHG : J.cycle.Feasible H 0 := J.aligned_HG_zero hJGHframe
  have hJTD := J.nonpositive_original_TD_two hqL hqq hJAB hJnorm hJAG hJGH hJDT hJTB hJHG
  have hs := J.nonpositive_sharp hqL hqq hJAB hJnorm hJAG hJGH hJDT hJTB hJHG hJTD
  exact no_strict_loss_to_on_circle
    (fun i _ => (I.necessary.contained i).trans hqq) hs.2.2.2.2.2.2.1 (hloss hstrict)

/-- The complete four-choice zero-owner matrix in the nonpositive
ordered hard class, with no E frame-order assumption.  All conclusions
refer to the source's original points, frames and physical slacks. -/
theorem HardInput.nonpositive_owner_sharp {q : ℝ}
    (I : HardInput q) (hqL : qLow≤q) (hqq : q≤qStar)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hGH : I.cycle.theta G≤I.cycle.theta H)
    (hDT : I.cycle.theta D≤I.cycle.theta T)
    (hTB : I.cycle.theta T≤I.cycle.theta B) :
    q=qStar ∧ I.cycle.theta G=I.cycle.theta H ∧
      I.cycle.theta B=I.cycle.theta T ∧ I.cycle.theta T=I.cycle.theta D ∧
      I.cycle.theta E=I.cycle.theta D ∧
      I.cycle.theta H-I.cycle.theta D=FiveCorner.selected.angle ∧
      AllAnchorsOn qStar I.cycle ∧
      ∀ i j,j∈terminalOwners i → I.cycle.slack i j=0 := by
  have hHG := I.nonpositive_original_HG_zero hqL hqq hAB hnorm hAG hGH hDT hTB
  have hTD := I.nonpositive_original_TD_two hqL hqq hAB hnorm hAG hGH hDT hTB hHG
  exact I.nonpositive_sharp hqL hqq hAB hnorm hAG hGH hDT hTB hHG hTD

end SquaresInCircles.Eight.SignedCycle
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SignedCycle
open Candidate Stationary GeometricModel

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

end SquaresInCircles.Eight.SignedCycle
end
end
end

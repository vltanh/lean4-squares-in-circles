module

public import SquaresInCircles.Eight.TableFree.EInteriorCycle
public import SquaresInCircles.Eight.TableFree.EpsilonGeometry
public import SquaresInCircles.Eight.TableFree.CanonicalHardEndpoint

/-!
# The ordered aligned hard chain reaches its unique geometric endpoint

Uncompiled draft.  The actual E-only reduction has three boundary faces.
The E-zero and E=H faces are impossible at qCap, so the surviving face is
E=D.  The genuine A/B split then reaches the five-corner endpoint.  All
circle losses are composed against the original source, and equality is
pulled back before invoking the endpoint theorem on that source itself.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree
open Candidate GeometricModel ExactFamily
namespace SignedCycle

/-- Endpoint construction for the actual aligned chain with E between
D and H.  Both source interior tests survive the successive reductions. -/
theorem HardInput.aligned_ordered_endpoint {q : ℝ} (I : HardInput q) (hq : q≤qCap)
    (hHG : I.cycle.theta G=I.cycle.theta H)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hTD : I.cycle.theta T=I.cycle.theta D)
    (hleft : I.cycle.theta A≤I.cycle.theta H)
    (hright : I.cycle.theta D≤I.cycle.theta A)
    (hDEorder : I.cycle.theta D≤I.cycle.theta E)
    (hEHorder : I.cycle.theta E≤I.cycle.theta H) :
    ∃ J : HardInput q,
      J.cycle.theta G=J.cycle.theta H ∧
      J.cycle.theta A=J.cycle.theta B ∧
      J.cycle.theta T=J.cycle.theta D ∧
      J.cycle.theta A=J.cycle.theta D ∧
      J.cycle.theta E=J.cycle.theta D ∧
      J.cycle.theta D≤J.cycle.theta H ∧
      J.cycle.Feasible D 3 ∧ J.cycle.Feasible E 1 ∧
      AnchorNonincrease I.cycle J.cycle ∧
      (((I.cycle.point E).y<0 ∧ I.cycle.theta D<I.cycle.theta E ∧
          I.cycle.theta E<I.cycle.theta H) ∨
        (I.cycle.theta A<I.cycle.theta H ∧ I.cycle.theta D<I.cycle.theta A) →
        StrictAnchorLoss I.cycle J.cycle) ∧
      (∀ i,i∈({H,G,T,D} : Finset Vertex) →
        J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i) := by
  obtain ⟨K,hfixedK,horderK,hendK,hnonK,hstrictK,hDEK,hEHK⟩ :=
    I.reduce_ordered_E hq hHG hAB hTD hleft hright hDEorder hEHorder
  have hH := hfixedK H (by decide)
  have hG := hfixedK G (by decide)
  have hA := hfixedK A (by decide)
  have hB := hfixedK B (by decide)
  have hT := hfixedK T (by decide)
  have hD := hfixedK D (by decide)
  have hKHG : K.cycle.theta G=K.cycle.theta H := by rw [hG.2,hH.2,hHG]
  have hKAB : K.cycle.theta A=K.cycle.theta B := by rw [hA.2,hB.2,hAB]
  have hKTD : K.cycle.theta T=K.cycle.theta D := by rw [hT.2,hD.2,hTD]
  have hKleft : K.cycle.theta A≤K.cycle.theta H := by rwa [hA.2,hH.2]
  have hKright : K.cycle.theta D≤K.cycle.theta A := by rwa [hD.2,hA.2]
  have hKDEorder : K.cycle.theta D≤K.cycle.theta E := by rw [hD.2]; exact horderK.1
  have hKEHorder : K.cycle.theta E≤K.cycle.theta H := by rw [hH.2]; exact horderK.2
  have hKED : K.cycle.theta E=K.cycle.theta D := by
    rcases hendK with hy | hd | hh
    · exact (K.aligned_zero_E_impossible hq hKHG hKAB hKTD hKleft hKright hy
        hKDEorder hKEHorder hDEK hEHK).elim
    · exact hd.trans hD.2.symm
    · exact (K.aligned_epsilon_zero_impossible hq hKHG hKAB hKTD hKleft hKright
        (hh.trans hH.2.symm) hDEK hEHK).elim
  obtain ⟨J,hJHG,hJAB,hJTD,hJAD,hJED,hJorder,hJDE,hJEH,hnonJ,hstrictJ,hfixedJ⟩ :=
    K.delta_zero_canonical_split hq hKHG hKAB hKTD hKleft hKright hKED hDEK hEHK
  refine ⟨J,hJHG,hJAB,hJTD,hJAD,hJED,hJorder,hJDE,hJEH,hnonK.trans hnonJ,?_,?_⟩
  · rintro (hEint | hABint)
    · exact (hstrictK hEint).then_nonincrease hnonJ
    · have hKint : K.cycle.theta A<K.cycle.theta H ∧ K.cycle.theta D<K.cycle.theta A := by
        simpa [hA.2,hH.2,hD.2] using hABint
      exact hnonK.then_strict (hstrictJ hKint)
  · intro i hi
    have hiA : i≠A := by fin_cases i <;> simp [H,G,T,D,A] at hi ⊢
    have hiB : i≠B := by fin_cases i <;> simp [H,G,T,D,B] at hi ⊢
    have hiE : i≠E := by fin_cases i <;> simp [H,G,T,D,E] at hi ⊢
    exact ⟨(hfixedJ i hiA hiB).1.trans (hfixedK i hiE).1,
      (hfixedJ i hiA hiB).2.trans (hfixedK i hiE).2⟩

theorem HardInput.aligned_ordered_lower_bound {q : ℝ} (I : HardInput q) (hq : q≤qCap)
    (hHG : I.cycle.theta G=I.cycle.theta H)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hTD : I.cycle.theta T=I.cycle.theta D)
    (hleft : I.cycle.theta A≤I.cycle.theta H)
    (hright : I.cycle.theta D≤I.cycle.theta A)
    (hDEorder : I.cycle.theta D≤I.cycle.theta E)
    (hEHorder : I.cycle.theta E≤I.cycle.theta H) : qStar≤q := by
  obtain ⟨J,hG,hAB',hT,hAD,hED,ho,_,hE,_,_,_⟩ :=
    I.aligned_ordered_endpoint hq hHG hAB hTD hleft hright hDEorder hEHorder
  exact J.canonical_lower_bound hG hAB' hT hAD hED ho hE

/-- Equality forces the original E frame to D, then the original common
A/B frame to D.  Only after these source facts are recovered is the sharp
endpoint theorem applied to the literal source points and SAT slacks. -/
theorem HardInput.aligned_ordered_sharp {q : ℝ} (I : HardInput q) (hq : q≤qStar)
    (hHG : I.cycle.theta G=I.cycle.theta H)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hTD : I.cycle.theta T=I.cycle.theta D)
    (hleft : I.cycle.theta A≤I.cycle.theta H)
    (hright : I.cycle.theta D≤I.cycle.theta A)
    (hDEorder : I.cycle.theta D≤I.cycle.theta E)
    (hEHorder : I.cycle.theta E≤I.cycle.theta H) :
    I.cycle.theta E=I.cycle.theta D ∧ I.cycle.theta A=I.cycle.theta D ∧
      q=qStar ∧ I.cycle.theta H-I.cycle.theta D=FiveCorner.selected.angle ∧
      AllAnchorsOn qStar I.cycle ∧
      ∀ i j,j∈terminalOwners i → I.cycle.slack i j=0 := by
  have hQ : q≤qCap := hq.trans qStar_limits.2.2.le
  obtain ⟨J,hG,hAB',hT,hAD,hED,ho,_,hE,hnon,hstrict,_⟩ :=
    I.aligned_ordered_endpoint hQ hHG hAB hTD hleft hright hDEorder hEHorder
  have hsharp := J.canonical_sharp hG hAB' hT hAD hED ho hE hq
  have hnoloss : ¬StrictAnchorLoss I.cycle J.cycle :=
    no_strict_loss_to_on_circle
      (fun i _ => (I.necessary.contained i).trans hq) hsharp.2.2.1
  have howners := I.aligned_primary_E_witnesses hQ hHG hAB hTD hleft hright hDEorder hEHorder
  have hE0ne : (I.cycle.point E).y≠0 := fun h =>
    I.aligned_zero_E_impossible hQ hHG hAB hTD hleft hright h hDEorder hEHorder howners.1 howners.2
  have hEHne : I.cycle.theta E≠I.cycle.theta H := fun h =>
    I.aligned_epsilon_zero_impossible hQ hHG hAB hTD hleft hright h howners.1 howners.2
  have hEDsource : I.cycle.theta E=I.cycle.theta D := by
    by_contra hne
    have hDElt := lt_of_le_of_ne hDEorder (Ne.symm hne)
    have hEHlt := lt_of_le_of_ne hEHorder hEHne
    have hEylt := lt_of_le_of_ne I.E_nonpos hE0ne
    exact hnoloss (hstrict (Or.inl ⟨hEylt,hDElt,hEHlt⟩))
  exact ⟨hEDsource,I.delta_zero_sharp hq hHG hAB hTD hleft hright hEDsource howners.1 howners.2⟩

/-- The ordered canceling HG/TD sector, including arbitrary original E
tangent and any original normal mixed owner, reaches the endpoint.  The
source loss ledger includes the outer errors, the common middle split,
and the original E interior. -/
theorem HardInput.ordered_canceling_endpoint {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hsum : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hAH : I.cycle.theta A≤I.cycle.theta H)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hDB : I.cycle.theta D≤I.cycle.theta B)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hHG : I.cycle.Feasible H 2) (hTD : I.cycle.Feasible T 0)
    (hDEorder : I.cycle.theta D≤I.cycle.theta E)
    (hEHorder : I.cycle.theta E≤I.cycle.theta H) :
    ∃ J : HardInput q,
      J.cycle.theta G=J.cycle.theta H ∧
      J.cycle.theta A=J.cycle.theta B ∧
      J.cycle.theta T=J.cycle.theta D ∧
      J.cycle.theta A=J.cycle.theta D ∧
      J.cycle.theta E=J.cycle.theta D ∧
      J.cycle.theta D≤J.cycle.theta H ∧ J.cycle.Feasible E 1 ∧
      AnchorNonincrease I.cycle J.cycle ∧
      ((I.cycle.theta G≠I.cycle.theta H ∨ I.cycle.theta T≠I.cycle.theta D ∨
        (I.cycle.theta A<I.cycle.theta H ∧ I.cycle.theta D<I.cycle.theta A) ∨
        ((I.cycle.point E).y<0 ∧ I.cycle.theta D<I.cycle.theta E ∧
          I.cycle.theta E<I.cycle.theta H)) → StrictAnchorLoss I.cycle J.cycle) := by
  obtain ⟨K,hKG,hKT,hKAB,hKend,hnonK,hstrictK,hfixedK,hslackK⟩ :=
    I.ordered_canceling_split hqL hq hAB hsum hAH hAG hDB hTB hHG hTD
  have hH := hfixedK H (by simp)
  have hD := hfixedK D (by simp)
  have hE := hfixedK E (by simp)
  have hKorder : K.cycle.theta D≤K.cycle.theta H := by
    rw [hD.2,hH.2]
    exact (by simpa [←hAB] using hDB).trans hAH
  have hKleft : K.cycle.theta A≤K.cycle.theta H := by
    rcases hKend with hh | hd
    · exact hh.le
    · rw [hd]; exact hKorder
  have hKright : K.cycle.theta D≤K.cycle.theta A := by
    rcases hKend with hh | hd
    · rw [hh]; exact hKorder
    · exact hd.ge
  have hKDEorder : K.cycle.theta D≤K.cycle.theta E := by rwa [hD.2,hE.2]
  have hKEHorder : K.cycle.theta E≤K.cycle.theta H := by rwa [hE.2,hH.2]
  obtain ⟨J,hJG,hJAB,hJT,hJAD,hJED,hJo,_,hJE,hnonJ,hstrictJ,_⟩ :=
    K.aligned_ordered_endpoint hq hKG hKAB hKT hKleft hKright hKDEorder hKEHorder
  refine ⟨J,hJG,hJAB,hJT,hJAD,hJED,hJo,hJE,hnonK.trans hnonJ,?_⟩
  rintro (hg | ht | hABint | hEint)
  · exact (hstrictK (Or.inl hg)).then_nonincrease hnonJ
  · exact (hstrictK (Or.inr (Or.inl ht))).then_nonincrease hnonJ
  · exact (hstrictK (Or.inr (Or.inr hABint))).then_nonincrease hnonJ
  · have hKint : (K.cycle.point E).y<0 ∧ K.cycle.theta D<K.cycle.theta E ∧
        K.cycle.theta E<K.cycle.theta H := by
      simpa [hE.1,hD.2,hE.2,hH.2] using hEint
    exact hnonK.then_strict (hstrictJ (Or.inl hKint))

theorem HardInput.ordered_canceling_lower_bound {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hsum : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hAH : I.cycle.theta A≤I.cycle.theta H)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hDB : I.cycle.theta D≤I.cycle.theta B)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hHG : I.cycle.Feasible H 2) (hTD : I.cycle.Feasible T 0)
    (hDEorder : I.cycle.theta D≤I.cycle.theta E)
    (hEHorder : I.cycle.theta E≤I.cycle.theta H) : qStar≤q := by
  obtain ⟨J,hG,hAB',hT,hAD,hED,ho,hE,_,_⟩ :=
    I.ordered_canceling_endpoint hqL hq hAB hsum hAH hAG hDB hTB hHG hTD hDEorder hEHorder
  exact J.canonical_lower_bound hG hAB' hT hAD hED ho hE

theorem HardInput.ordered_canceling_sharp {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qStar)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hsum : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hAH : I.cycle.theta A≤I.cycle.theta H)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hDB : I.cycle.theta D≤I.cycle.theta B)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hHG : I.cycle.Feasible H 2) (hTD : I.cycle.Feasible T 0)
    (hDEorder : I.cycle.theta D≤I.cycle.theta E)
    (hEHorder : I.cycle.theta E≤I.cycle.theta H) :
    I.cycle.theta G=I.cycle.theta H ∧ I.cycle.theta T=I.cycle.theta D ∧
      I.cycle.theta E=I.cycle.theta D ∧ I.cycle.theta A=I.cycle.theta D ∧
      q=qStar ∧ I.cycle.theta H-I.cycle.theta D=FiveCorner.selected.angle ∧
      AllAnchorsOn qStar I.cycle ∧
      ∀ i j,j∈terminalOwners i → I.cycle.slack i j=0 := by
  have hQ : q≤qCap := hq.trans qStar_limits.2.2.le
  obtain ⟨J,hG,hAB',hT,hAD,hED,ho,hE,hnon,hstrict⟩ :=
    I.ordered_canceling_endpoint hqL hQ hAB hsum hAH hAG hDB hTB hHG hTD hDEorder hEHorder
  have hsharp := J.canonical_sharp hG hAB' hT hAD hED ho hE hq
  have hnoloss : ¬StrictAnchorLoss I.cycle J.cycle :=
    no_strict_loss_to_on_circle
      (fun i _ => (I.necessary.contained i).trans hq) hsharp.2.2.1
  have hGsource : I.cycle.theta G=I.cycle.theta H := by
    by_contra h
    exact hnoloss (hstrict (Or.inl h))
  have hTsource : I.cycle.theta T=I.cycle.theta D := by
    by_contra h
    exact hnoloss (hstrict (Or.inr (Or.inl h)))
  have hDA : I.cycle.theta D≤I.cycle.theta A := by simpa [←hAB] using hDB
  exact ⟨hGsource,hTsource,I.aligned_ordered_sharp hq hGsource hAB hTsource
    hAH hDA hDEorder hEHorder⟩

end SignedCycle
end SquaresInCircles.Eight.TableFree

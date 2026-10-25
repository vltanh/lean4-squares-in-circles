module

public import SquaresInCircles.Eight.Owners.E.ZeroCapEndpoints
public import SquaresInCircles.Eight.Owners.Epsilon.Geometry
public import SquaresInCircles.Eight.Owners.Canonical.NegativeCycle
public import SquaresInCircles.Eight.Owners.E.ZeroGeometry

/-!
# Eight squares: the ordered aligned hard chain reaches its endpoint

The reduction of E alone has three boundary faces; the faces `E.y = 0` and `E = H` are impossible
below `qCap`, so E reaches the frame of D, and the split of A and B then reaches the five-corner
endpoint (`HardInput.aligned_ordered_endpoint`). The circle losses are composed against the
original cycle, and equality is pulled back to it before the endpoint theorem is applied to that
cycle itself: at `q ≤ qStar` the frames of E and of A and B are at that of D, `q = qStar`, the H–D
angle is the selected angle, every anchor is on the circle and every terminal slack vanishes
(`HardInput.aligned_ordered_sharp`).
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight
open Candidate GeometricModel Stationary
namespace SignedCycle

/-- For an aligned chain with E between D and H, a hard input at the same `q` with the frames of
the chain at that of D, the witnesses DE3 and EH1, no anchor circle larger, and a strict loss when
E or the common frame was interior: both interior tests of the original cycle survive the
successive reductions. -/
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
    have hiA : i≠A := (by decide : ∀ j∈({H,G,T,D} : Finset Vertex),j≠A) i hi
    have hiB : i≠B := (by decide : ∀ j∈({H,G,T,D} : Finset Vertex),j≠B) i hi
    have hiE : i≠E := (by decide : ∀ j∈({H,G,T,D} : Finset Vertex),j≠E) i hi
    exact ⟨(hfixedJ i hiA hiB).1.trans (hfixedK i hiE).1,
      (hfixedJ i hiA hiB).2.trans (hfixedK i hiE).2⟩

/-- At `q ≤ qStar` equality puts the frame of E, then the common frame of A and B, at that of D;
the sharp endpoint theorem then applies to the points and slacks of the cycle itself. -/
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

end SignedCycle
end SquaresInCircles.Eight

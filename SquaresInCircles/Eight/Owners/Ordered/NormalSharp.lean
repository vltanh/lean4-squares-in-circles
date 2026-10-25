module

public import SquaresInCircles.Eight.Owners.Nonpositive.OuterSharp
public import SquaresInCircles.Eight.Owners.Ordered.NormalMiddle
public import SquaresInCircles.Eight.Owners.Ordered.PositiveOuter

/-!
# Eight squares: sharpness of all four outer-owner cells in the ordered normal sector

Positive outer errors are removed on their
actual source circles, with losses charged to A/B.  The resulting hard
cycle has both nonpositive errors, so its sharp theorem forces all five
rigid anchors onto the extremal circle.  The strict-loss ledger then
rules out either positive error on the original source.  The final
sharp theorem is applied to that original source, recovering its own
frames, anchor circles, and all terminal contacts.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight
open Candidate
open Stationary (qStar qStar_limits)
namespace SignedCycle

private theorem HardInput.reduce_positive_HG_normal {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hfloor : 67/200≤(I.cycle.point A).y)
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAH : I.cycle.theta A≤I.cycle.theta H)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hGy : (I.cycle.point G).y≤0) (hTy : 0≤(I.cycle.point T).y) :
    ∃ J : HardInput q,
      J.cycle.theta G≤J.cycle.theta H ∧ J.cycle.theta A=J.cycle.theta B ∧
      (J.cycle.point A).y=(I.cycle.point A).y ∧ (J.cycle.point G).y≤0 ∧
      AnchorNonincrease I.cycle J.cycle ∧
      (I.cycle.theta H<I.cycle.theta G → StrictAnchorLoss I.cycle J.cycle) ∧
      (∀ i,i≠G → J.cycle.theta i=I.cycle.theta i) ∧
      (∀ i,i≠G → i≠A → J.cycle.point i=I.cycle.point i) ∧
      J.cycle.theta A≤J.cycle.theta G := by
  by_cases hGH : I.cycle.theta G≤I.cycle.theta H
  · exact ⟨I,hGH,hAB,rfl,hGy,anchorNonincrease_refl _,
      fun h => False.elim ((not_lt_of_ge hGH) h),
      fun _ _ => rfl,fun _ _ _ => rfl,hAG⟩
  have hHG : I.cycle.theta H<I.cycle.theta G := lt_of_not_ge hGH
  obtain ⟨J,hJG,hJAB,hJAy,hJGy,hnon,hstrict,hθ,hpoint⟩ :=
    I.align_positive_HG_normal hqL hq hAB hnorm hfloor hTA hAH hHG hGy hTy
  refine ⟨J,hJG.le,hJAB,hJAy,by linarith,hnon,fun _ => hstrict,hθ,hpoint,?_⟩
  rw [hJG,hθ A (by decide),hθ H (by decide)]
  exact hAH

/-- An actual same-q descendant with nonpositive outer errors.  The
strictness predicate still concerns either original positive error. -/
theorem HardInput.ordered_normal_to_nonpositive {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hAH : I.cycle.theta A≤I.cycle.theta H)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hDB : I.cycle.theta D≤I.cycle.theta B)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hGy : (I.cycle.point G).y≤0) (hTy : 0≤(I.cycle.point T).y) :
    ∃ J : HardInput q,
      J.cycle.theta G≤J.cycle.theta H ∧ J.cycle.theta D≤J.cycle.theta T ∧
      AnchorNonincrease I.cycle J.cycle ∧
      (I.cycle.theta H<I.cycle.theta G ∨ I.cycle.theta T<I.cycle.theta D →
        StrictAnchorLoss I.cycle J.cycle) := by
  have hrange := I.ordered_normal_middle_range hqL hq hnorm hAH hAG hDB hTB hGy hTy
  have hTA : I.cycle.theta T≤I.cycle.theta A := by rw [hAB]; exact hTB
  obtain ⟨K,hKGH,hKAB,hKAy,hKGy,hnonK,hstrictK,hKθ,hKpoint,hKAG⟩ :=
    I.reduce_positive_HG_normal hqL hq hAB hnorm hrange.1.1.le hTA hAH hAG hGy hTy
  have hKB : K.cycle.point B=I.cycle.point B := hKpoint B (by decide) (by decide)
  have hKT : K.cycle.point T=I.cycle.point T := hKpoint T (by decide) (by decide)
  have hKnorm : (K.cycle.point A).y-(K.cycle.point B).y=1 := by
    rw [hKAy,hKB]
    exact hnorm
  have hKfloor : 67/200≤ -(K.cycle.point B).y := by rw [hKB]; exact hrange.2.1.le
  have hKDB : K.cycle.theta D≤K.cycle.theta B := by
    rw [hKθ D (by decide),hKθ B (by decide)]
    exact hDB
  have hKTy : 0≤(K.cycle.point T).y := by rw [hKT]; exact hTy
  by_cases hKDT : K.cycle.theta D≤K.cycle.theta T
  · refine ⟨K,hKGH,hKDT,hnonK,?_⟩
    rintro (hG | hT)
    · exact hstrictK hG
    · have hh := hKDT
      rw [hKθ D (by decide),hKθ T (by decide)] at hh
      exact False.elim ((not_lt_of_ge hh) hT)
  · have hKTD : K.cycle.theta T<K.cycle.theta D := lt_of_not_ge hKDT
    obtain ⟨J,hJT,hJAB,hJBy,hJTy,hnonJ,hstrictJ,hJθ,hJpoint⟩ :=
      K.align_positive_TD_normal hqL hq hKAB hKnorm hKfloor hKAG hKDB hKTD hKGy hKTy
    have hJGH : J.cycle.theta G≤J.cycle.theta H := by
      rw [hJθ G (by decide),hJθ H (by decide)]
      exact hKGH
    exact ⟨J,hJGH,hJT.symm.le,hnonK.trans hnonJ,
      fun _ => hnonK.then_strict hstrictJ⟩

/-- Equality recovers the signs of both original outer errors before
the sharp theorem is applied to the literal original geometry. -/
theorem HardInput.ordered_normal_original_nonpositive {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qStar)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hAH : I.cycle.theta A≤I.cycle.theta H)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hDB : I.cycle.theta D≤I.cycle.theta B)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hGy : (I.cycle.point G).y≤0) (hTy : 0≤(I.cycle.point T).y) :
    I.cycle.theta G≤I.cycle.theta H ∧ I.cycle.theta D≤I.cycle.theta T := by
  have hQ : q≤qCap := hq.trans qStar_limits.2.2.le
  obtain ⟨J,hJGH,hJDT,hnon,hstrict⟩ :=
    I.ordered_normal_to_nonpositive hqL hQ hAB hnorm hAH hAG hDB hTB hGy hTy
  obtain ⟨_,_,_,_,_,_,_,_,hcircle,_⟩ := J.nonpositive_outer_sharp hqL hq hJGH hJDT
  have hnoloss : ¬StrictAnchorLoss I.cycle J.cycle :=
    no_strict_loss_to_on_circle
      (fun i _ => (I.necessary.contained i).trans hq) hcircle
  constructor
  · by_contra! h
    exact hnoloss (hstrict (Or.inl h))
  · by_contra! h
    exact hnoloss (hstrict (Or.inr h))

/-- All four originally selected HG/TD owner combinations have the
same source sharpness conclusion in the ordered normal sector. -/
theorem HardInput.ordered_normal_sharp {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qStar)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hAH : I.cycle.theta A≤I.cycle.theta H)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hDB : I.cycle.theta D≤I.cycle.theta B)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hGy : (I.cycle.point G).y≤0) (hTy : 0≤(I.cycle.point T).y) :
    I.cycle.theta A=I.cycle.theta B ∧
      (I.cycle.point A).y-(I.cycle.point B).y=1 ∧
      q=qStar ∧ I.cycle.theta G=I.cycle.theta H ∧
      I.cycle.theta B=I.cycle.theta T ∧ I.cycle.theta T=I.cycle.theta D ∧
      I.cycle.theta E=I.cycle.theta D ∧
      I.cycle.theta H-I.cycle.theta D=FiveCorner.selected.angle ∧
      AllAnchorsOn qStar I.cycle ∧
      ∀ i j,j∈terminalOwners i → I.cycle.slack i j=0 := by
  have hn := I.ordered_normal_original_nonpositive hqL hq hAB hnorm hAH hAG hDB hTB hGy hTy
  exact I.nonpositive_outer_sharp hqL hq hn.1 hn.2

end SignedCycle
end SquaresInCircles.Eight

module

public import SquaresInCircles.Eight.TableFree.MiddleClampCycle

/-!
# Complete middle canonicalization in the ordered intermediate sector

Uncompiled draft.  The original hard cycle is transformed to a common
A/B frame inside the unchanged G/T interval with exact transverse gap
one.  All actual middle-circle comparisons are nonincreasing.  A source
frame error, exterior common frame, or excess common gap creates strict
loss at an original middle anchor, so each is available for equality
pullback.  The global G/T order and one-tenth sign reserves remain explicit
front-end hypotheses.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
open Candidate MiddleAboveContraction
namespace SignedCycle

theorem HardInput.gap_normalization_point {q : ℝ} (I : HardInput q)
    (hq : q ≤ qCap) (hyG : (I.cycle.point G).y ≤ (1/10 : ℝ))
    (hcommon : I.cycle.theta A=I.cycle.theta B)
    (hAG : I.cycle.theta A ≤ I.cycle.theta G)
    (hgap : 1 < (I.cycle.point A).y-(I.cycle.point B).y) :
    ∃ O : AWeakContraction (I.cycle.point G) (I.cycle.point A) (I.cycle.point B)
      (I.cycle.theta B-I.cycle.theta G), O.point.y-(I.cycle.point B).y=1 := by
  let t := I.cycle.theta G-I.cycle.theta A
  let P : SignedPoint := ⟨(I.cycle.point A).a,1+(I.cycle.point B).y⟩
  have htm : t ∈ Icc 0 (7/10 : ℝ) := by
    constructor
    · exact sub_nonneg.mpr hAG
    · have hh := I.necessary.spread G A
      have ha := le_abs_self (I.cycle.theta G-I.cycle.theta A)
      dsimp [frameCap] at hh
      dsimp [t]
      linarith
  have hBbound := (SignedPoint.coordinate_bounds (I.necessary.sorted B)
    (I.necessary.core B) (I.necessary.contained B) hq).2.2
  have hnormal : 0 < P.y := by
    dsimp [P]
    linarith [neg_le_abs (I.cycle.point B).y]
  have hPY : P.y < (I.cycle.point A).y := by dsimp [P]; linarith
  have hGA : quarterFeasible (I.cycle.point G) (I.cycle.point A) (-t) 0 := by
    dsimp [t]
    rw [neg_sub]
    simpa [Feasible,slack,edge,Candidate.word,delta,next,G,A,quarterFeasible,sub_nonneg]
      using I.GA_hard
  have hcontact : 1/2-(I.cycle.point G).y ≤
      ((I.cycle.point A).a+1/2-1)*Real.cos t-
        ((I.cycle.point A).y+1/2)*Real.sin t := by
    have hh := hGA
    simp [quarterFeasible,quarterProjection] at hh
    rw [edgeWidth_positive_formula htm] at hh
    nlinarith
  have hprimary : (9/10 : ℝ) ≤ P.a := by
    have hh := MiddleHardCap.primary_lower
      (show 2/5 ≤ 1/2-(I.cycle.point G).y by linarith) htm
      (show 0 ≤ (I.cycle.point A).y+1/2 by linarith [I.anchors_normal.A_nonneg]) hcontact
    dsimp [P]
    linarith
  have hcircle : P.circle < (I.cycle.point A).circle := by
    have hs := pow_lt_pow_left₀ (show 0 ≤ P.y+1/2 by linarith)
      (show P.y+1/2 < (I.cycle.point A).y+1/2 by linarith) (by decide : (2:ℕ)≠0)
    dsimp [SignedPoint.circle]
    rw [abs_of_pos hnormal,abs_of_nonneg I.anchors_normal.A_nonneg]
    dsimp [P] at *
    linarith
  have hABexact : P.y-(I.cycle.point B).y=1 := by dsimp [P]; ring
  refine ⟨{
    point := P
    sorted := ⟨by dsimp [P]; exact (I.necessary.sorted A).1,?_⟩
    avoids := ?_
    normal := hnormal
    circle_lt := hcircle
    AB_gap := hABexact.symm.le
    AB_zero := by simpa [zeroFeasible,zeroProjection,hABexact]
    AB_two := by simpa [zeroFeasible,zeroProjection,hABexact]
    GA := ?_
  },hABexact⟩
  · have hh := (I.necessary.sorted A).2
    rw [abs_of_nonneg I.anchors_normal.A_nonneg] at hh
    rw [abs_of_pos hnormal]
    dsimp [P]
    linarith
  · dsimp [SignedPoint.AvoidsCore,SignedPoint.coreDistance]
    rw [max_eq_left (by linarith : 0 ≤ P.a-1/2)]
    have hs := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2/5)
      (show 2/5 ≤ P.a-1/2 by linarith) 2
    nlinarith [sq_nonneg (max (|P.y|-1/2) 0)]
  · rw [← hcommon,show I.cycle.theta A-I.cycle.theta G= -t by dsimp [t]; ring]
    have hs0 := (transport_trig_coarse htm).2.1
    have hp := mul_nonneg (sub_nonneg.mpr hPY.le) hs0
    have hh := hGA
    simp [quarterFeasible,quarterProjection] at hh ⊢
    dsimp [P] at *
    nlinarith

theorem HardInput.normalize_common_gap {q : ℝ} (I : HardInput q)
    (hq : q ≤ qCap) (hyG : (I.cycle.point G).y ≤ (1/10 : ℝ))
    (hcommon : I.cycle.theta A=I.cycle.theta B)
    (hAG : I.cycle.theta A ≤ I.cycle.theta G) :
    ∃ J : HardInput q,
      (∀ i, J.cycle.theta i=I.cycle.theta i) ∧
      (J.cycle.point A).y-(J.cycle.point B).y=1 ∧
      AnchorNonincrease I.cycle J.cycle ∧
      (1 < (I.cycle.point A).y-(I.cycle.point B).y → StrictAnchorLoss I.cycle J.cycle) ∧
      (∀ i, i≠A → J.cycle.point i=I.cycle.point i) := by
  have hgap := I.aligned_AB_gap hcommon
  by_cases heq : (I.cycle.point A).y-(I.cycle.point B).y=1
  · refine ⟨I,fun _ => rfl,heq,anchorNonincrease_refl _,?_,fun _ _ => rfl⟩
    intro h
    linarith
  · have hstrict : 1 < (I.cycle.point A).y-(I.cycle.point B).y := by
      rcases lt_or_eq_of_le hgap with h | h
      · exact h
      · exact (heq h.symm).elim
    obtain ⟨O,hO⟩ := I.gap_normalization_point hq hyG hcommon hAG hstrict
    let J := I.fromAboveMiddle O
    refine ⟨J,?_,?_,?_,?_,?_⟩
    · intro i
      by_cases hi : i=A
      · subst i
        simpa [J,HardInput.fromAboveMiddle,replaceA,replacePoint] using hcommon.symm
      · exact (replaceA_unchanged I.cycle O.point i hi).2
    · simpa [J,HardInput.fromAboveMiddle,replaceA,replacePoint,A,B] using hO
    · intro i hi
      by_cases ha : i=A
      · subst i
        simpa [J,HardInput.fromAboveMiddle,replaceA,replacePoint] using O.circle_lt.le
      · exact (congrArg SignedPoint.circle (replaceA_unchanged I.cycle O.point i ha).1).le
    · intro _
      refine ⟨A,by simp [anchorVertices],?_⟩
      simpa [J,HardInput.fromAboveMiddle,replaceA,replacePoint] using O.circle_lt
    · intro i hi
      exact (replaceA_unchanged I.cycle O.point i hi).1

theorem HardInput.canonicalize_common_middle {q : ℝ} (I : HardInput q)
    (hq : q ≤ qCap) (hyG : (I.cycle.point G).y ≤ (1/10 : ℝ))
    (hyT : -(1/10 : ℝ) ≤ (I.cycle.point T).y)
    (hGT : I.cycle.theta T ≤ I.cycle.theta G)
    (hcommon : I.cycle.theta A=I.cycle.theta B) :
    ∃ J : HardInput q,
      J.cycle.theta A=J.cycle.theta B ∧
      J.cycle.theta A ∈ Icc (I.cycle.theta T) (I.cycle.theta G) ∧
      (J.cycle.point A).y-(J.cycle.point B).y=1 ∧
      AnchorNonincrease I.cycle J.cycle ∧
      ((I.cycle.theta A<I.cycle.theta T ∨ I.cycle.theta G<I.cycle.theta A ∨
        1<(I.cycle.point A).y-(I.cycle.point B).y) → StrictAnchorLoss I.cycle J.cycle) ∧
      (∀ i, i≠A → i≠B → J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i) := by
  by_cases hinside : I.cycle.theta A ∈ Icc (I.cycle.theta T) (I.cycle.theta G)
  · obtain ⟨J,hframes,hgap,hnon,hstrict,hfixed⟩ :=
      I.normalize_common_gap hq hyG hcommon hinside.2
    refine ⟨J,(hframes A).trans (hcommon.trans (hframes B).symm),?_,hgap,hnon,?_,?_⟩
    · rw [hframes A]
      exact hinside
    · rintro (h | h | h)
      · exact (not_lt_of_ge hinside.1 h).elim
      · exact (not_lt_of_ge hinside.2 h).elim
      · exact hstrict h
    · intro i hiA hiB
      exact ⟨hfixed i hiA,hframes i⟩
  · have hout : I.cycle.theta A<I.cycle.theta T ∨ I.cycle.theta G<I.cycle.theta A := by
      by_cases hlo : I.cycle.theta T ≤ I.cycle.theta A
      · right
        exact lt_of_not_ge (fun hhi => hinside ⟨hlo,hhi⟩)
      · exact Or.inl (lt_of_not_ge hlo)
    obtain ⟨K,hcommonK,hintervalK,hgapK,hnonK,hstrictK,hfixedK⟩ :=
      I.clamp_common_middle hq hyG hyT hGT hcommon
    have hGK := hfixedK G (by decide : G≠A) (by decide : G≠B)
    have hyGK : (K.cycle.point G).y ≤ (1/10 : ℝ) := by rw [hGK.1]; exact hyG
    have hAGK : K.cycle.theta A ≤ K.cycle.theta G := by rw [hGK.2]; exact hintervalK.2
    obtain ⟨J,hframes,hgap,hnonJ,hstrictJ,hfixedJ⟩ :=
      K.normalize_common_gap hq hyGK hcommonK hAGK
    have hsourceStrict : StrictAnchorLoss I.cycle K.cycle :=
      ⟨A,by simp [anchorVertices],(hstrictK hout).1⟩
    refine ⟨J,(hframes A).trans (hcommonK.trans (hframes B).symm),?_,hgap,
      hnonK.trans hnonJ,fun _ => hsourceStrict.then_nonincrease hnonJ,?_⟩
    · rw [hframes A]
      exact hintervalK
    · intro i hiA hiB
      exact ⟨(hfixedJ i hiA).trans ((hfixedK i hiA hiB).1),
        (hframes i).trans ((hfixedK i hiA hiB).2)⟩

/-- Complete actual middle reduction under the ordered intermediate
front-end hypotheses.  The source strictness predicate records all
departures from the canonical middle conditions. -/
theorem HardInput.canonicalize_middle_ordered {q : ℝ} (I : HardInput q)
    (hq : q ≤ qCap) (hyG : (I.cycle.point G).y ≤ (1/10 : ℝ))
    (hyT : -(1/10 : ℝ) ≤ (I.cycle.point T).y)
    (hGT : I.cycle.theta T ≤ I.cycle.theta G) :
    ∃ J : HardInput q,
      J.cycle.theta A=J.cycle.theta B ∧
      J.cycle.theta A ∈ Icc (I.cycle.theta T) (I.cycle.theta G) ∧
      (J.cycle.point A).y-(J.cycle.point B).y=1 ∧
      AnchorNonincrease I.cycle J.cycle ∧
      ((I.cycle.theta A≠I.cycle.theta B ∨ I.cycle.theta A<I.cycle.theta T ∨
        I.cycle.theta G<I.cycle.theta A ∨ 1<(I.cycle.point A).y-(I.cycle.point B).y) →
        StrictAnchorLoss I.cycle J.cycle) ∧
      (∀ i, i≠A → i≠B → J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i) := by
  by_cases hcommon : I.cycle.theta A=I.cycle.theta B
  · obtain ⟨J,hAB,hinterval,hgap,hnon,hstrict,hfixed⟩ :=
      I.canonicalize_common_middle hq hyG hyT hGT hcommon
    refine ⟨J,hAB,hinterval,hgap,hnon,?_,hfixed⟩
    rintro (h | h)
    · exact (h hcommon).elim
    · exact hstrict h
  · obtain ⟨K,hcommonK,hgapK,hnonK,hstrictK,hfixedK⟩ :=
      I.align_middle_frames_ordered hq hyG hyT hGT
    have hGK := hfixedK G (by decide : G≠A) (by decide : G≠B)
    have hTK := hfixedK T (by decide : T≠A) (by decide : T≠B)
    have hyGK : (K.cycle.point G).y ≤ (1/10 : ℝ) := by rw [hGK.1]; exact hyG
    have hyTK : -(1/10 : ℝ) ≤ (K.cycle.point T).y := by rw [hTK.1]; exact hyT
    have hGTK : K.cycle.theta T ≤ K.cycle.theta G := by rw [hTK.2,hGK.2]; exact hGT
    obtain ⟨J,hAB,hinterval,hgap,hnonJ,hstrictJ,hfixedJ⟩ :=
      K.canonicalize_common_middle hq hyGK hyTK hGTK hcommonK
    refine ⟨J,hAB,?_,hgap,hnonK.trans hnonJ,
      fun _ => (hstrictK hcommon).then_nonincrease hnonJ,?_⟩
    · simpa only [hTK.2,hGK.2] using hinterval
    · intro i hiA hiB
      exact ⟨((hfixedJ i hiA hiB).1).trans ((hfixedK i hiA hiB).1),
        ((hfixedJ i hiA hiB).2).trans ((hfixedK i hiA hiB).2)⟩

end SignedCycle
end SquaresInCircles.Eight.TableFree

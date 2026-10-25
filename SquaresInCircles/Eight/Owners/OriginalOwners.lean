module

public import Mathlib.Data.Int.Star
public import SquaresInCircles.Eight.Frames.NearestAxisSigns
public import SquaresInCircles.Eight.Owners.BT.Exclusion
public import SquaresInCircles.Eight.Owners.E.DiagonalExclusion
public import SquaresInCircles.Eight.Owners.EH.HighRestriction
public import SquaresInCircles.Eight.Words.Second.WordExclusion
public import SquaresInCircles.Eight.Words.Short.WordExclusion

/-!
# Eight squares: the quarter owners and the outer anchors

The BT obstruction settles the owners of EH: a high EH witness makes E negative, so a BT witness
would be high, which the all-high obstruction excludes; so every EH witness is low
(`frame_EH_low`). When E is nonpositive every BT and DE witness is high, and every weak axis of an
edge other than GA has a normal owner (`frame_other_owners`). The selected axes then make H, B and
D outer anchors at the radius `q` (`frame_H_anchor`, `frame_B_anchor`, `frame_D_anchor`,
`atFrame_anchors`). The owners of GA are not restricted here.
-/

section
/-!
## All internal nearest-axis ties are excluded on the original cycle

The alternative nearest
axis is an actual same-radius representation, preserving the original
weak separators. Its unchanged integer word is carried to Q0 only to
apply the complete binary wrong-word exclusions. No owner restriction or
sign assumption at any other vertex enters the result.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.BinaryDiagonalExclusion
open Candidate Arithmetic

theorem binary_excluded {q : ℝ} (C : BoundaryCycle q) (hq : q∈Icc (5/2:ℝ) Q0)
    (F : QuarterLift C) (w : WordProblems.WrongWord) :
    ¬(F.word (boundary_gap_lower C hq.2) pi_lt_22_over_7).DihedralEquivalent (WordProblems.wrongWord w) := by
  let D := FramePhysicalTransport.auxiliary C hq
  let R := FramePhysicalTransport.auxiliary_expansion C hq
  let FD := FramePhysicalTransport.quarterPushforward F R
  have hgD : ∀i,19/25<angleGap D.beta i := boundary_gap_lower D le_rfl
  have hw := FramePhysicalTransport.quarterPushforward_word F R (boundary_gap_lower C hq.2) hgD
  intro he
  have heD : (FD.word hgD pi_lt_22_over_7).DihedralEquivalent (WordProblems.wrongWord w) := by
    rw [hw]
    exact he
  cases w
  · exact ShortWord.not_dihedral D FD hgD heD
  · exact SecondWord.not_dihedral D FD hgD heD

theorem recode_wrong {q : ℝ} (C : BoundaryCycle q) (hq : q∈Icc (5/2:ℝ) Q0)
    (F : QuarterLift C) (v : Vertex) (hd : C.b v=C.a v)
    (w : WordProblems.WrongWord) (s : Vertex) (reversed : Bool)
    (he : ∀i,integerQuarterIncrement F.quarter i+NearestAxisRecode.shift C v (next i)-
      NearestAxisRecode.shift C v i=((quarterDihedral s reversed (WordProblems.wrongWord w) i).val:ℤ)) : False := by
  let J := NearestAxisRecode.cycle C v hd
  let H := NearestAxisRecode.lift F v hd
  have hw : H.word (boundary_gap_lower J hq.2) pi_lt_22_over_7=
      quarterDihedral s reversed (WordProblems.wrongWord w) := by
    funext i
    apply Fin.ext
    have hc := H.word_cast (boundary_gap_lower J hq.2) pi_lt_22_over_7 i
    change ((H.word (boundary_gap_lower J hq.2) pi_lt_22_over_7 i).val:ℤ)=
      integerQuarterIncrement (NearestAxisRecode.lift F v hd).quarter i at hc
    rw [NearestAxisRecode.increment] at hc
    have hh := he i
    omega
  exact binary_excluded J hq H w ⟨s,reversed,hw⟩

theorem recode_negative {q : ℝ} (C : BoundaryCycle q) (hq : q∈Icc (5/2:ℝ) Q0)
    (F : QuarterLift C) (v : Vertex) (hd : C.b v=C.a v) (i : Vertex)
    (he : integerQuarterIncrement F.quarter i+NearestAxisRecode.shift C v (next i)-
      NearestAxisRecode.shift C v i= -1) : False := by
  let J := NearestAxisRecode.cycle C v hd
  let H := NearestAxisRecode.lift F v hd
  have hh := (H.digit_range (boundary_gap_lower J hq.2) pi_lt_22_over_7 i).1
  change 0≤ integerQuarterIncrement (NearestAxisRecode.lift F v hd).quarter i at hh
  rw [NearestAxisRecode.increment,he] at hh
  norm_num at hh

theorem G_negative {q : ℝ} (C : BoundaryCycle q) (hq : q∈Icc (5/2:ℝ) Q0)
    (F : QuarterLift C) (hm : F.quarter=offsets) (hd : C.b G=C.a G) (hs : C.sigma G= -1) : False := by
  have hs' : C.sigma 1= -1 := hs
  apply recode_wrong C hq F G hd .short 6 false
  intro i
  rw [hm]
  fin_cases i <;> norm_num [integerQuarterIncrement,offsets,NearestAxisRecode.shift,hs',
    quarterDihedral,WordProblems.wrongWord,G,next]
theorem A_positive {q : ℝ} (C : BoundaryCycle q) (hq : q∈Icc (5/2:ℝ) Q0)
    (F : QuarterLift C) (hm : F.quarter=offsets) (hd : C.b A=C.a A) (hs : C.sigma A=1) : False := by
  have hs' : C.sigma 2=1 := hs
  apply recode_wrong C hq F A hd .second 0 false
  intro i
  rw [hm]
  fin_cases i <;> norm_num [integerQuarterIncrement,offsets,NearestAxisRecode.shift,hs',
    quarterDihedral,WordProblems.wrongWord,A,next]
theorem B_negative {q : ℝ} (C : BoundaryCycle q) (hq : q∈Icc (5/2:ℝ) Q0)
    (F : QuarterLift C) (hm : F.quarter=offsets) (hd : C.b B=C.a B) (hs : C.sigma B= -1) : False := by
  have hs' : C.sigma 3= -1 := hs
  apply recode_wrong C hq F B hd .second 4 false
  intro i
  rw [hm]
  fin_cases i <;> norm_num [integerQuarterIncrement,offsets,NearestAxisRecode.shift,hs',
    quarterDihedral,WordProblems.wrongWord,B,next]
theorem T_positive {q : ℝ} (C : BoundaryCycle q) (hq : q∈Icc (5/2:ℝ) Q0)
    (F : QuarterLift C) (hm : F.quarter=offsets) (hd : C.b T=C.a T) (hs : C.sigma T=1) : False := by
  have hs' : C.sigma 4=1 := hs
  apply recode_wrong C hq F T hd .short 3 true
  intro i
  rw [hm]
  fin_cases i <;> norm_num [integerQuarterIncrement,offsets,NearestAxisRecode.shift,hs',
    quarterDihedral,WordProblems.wrongWord,T,next]

theorem of_offsetLift {q : ℝ} (C : BoundaryCycle q) (hq : q∈Icc (5/2:ℝ) Q0)
    (F : QuarterLift C) (hm : F.quarter=offsets) (v : Vertex)
    (hv : v=G∨v=A∨v=B∨v=T) : C.b v<C.a v := by
  by_contra! hbad
  have hd : C.b v=C.a v := le_antisymm (C.b_le_a v) hbad
  rcases hv with rfl|rfl|rfl|rfl
  · rcases C.sigma_sign G with hs|hs
    · exact G_negative C hq F hm hd hs
    · have hs' : C.sigma 1=1 := hs
      apply recode_negative C hq F G hd H
      rw [hm]
      norm_num [integerQuarterIncrement,offsets,NearestAxisRecode.shift,hs',H,G,next]
  · rcases C.sigma_sign A with hs|hs
    · have hs' : C.sigma 2= -1 := hs
      apply recode_negative C hq F A hd A
      rw [hm]
      norm_num [integerQuarterIncrement,offsets,NearestAxisRecode.shift,hs',A,next]
    · exact A_positive C hq F hm hd hs
  · rcases C.sigma_sign B with hs|hs
    · exact B_negative C hq F hm hd hs
    · have hs' : C.sigma 3=1 := hs
      apply recode_negative C hq F B hd A
      rw [hm]
      norm_num [integerQuarterIncrement,offsets,NearestAxisRecode.shift,hs',A,B,next]
  · rcases C.sigma_sign T with hs|hs
    · have hs' : C.sigma 4= -1 := hs
      apply recode_negative C hq F T hd T
      rw [hm]
      norm_num [integerQuarterIncrement,offsets,NearestAxisRecode.shift,hs',T,next]
    · exact T_positive C hq F hm hd hs

theorem of_frame {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C)
    (hq : q∈Icc (5/2:ℝ) Q0) (v : Vertex) (hv : v=G∨v=A∨v=B∨v=T) : C.b v<C.a v := by
  obtain ⟨G,hGtheta,hGquarter⟩ := EDiagonalExclusion.offsetLift_exists C F.theta
    (by simpa only [frameCap] using F.spread)
    (by intro i; simpa only [mul_div_assoc] using F.canonical_eq i)
  exact of_offsetLift C hq G hGquarter v hv

end SquaresInCircles.Eight.BinaryDiagonalExclusion

namespace SquaresInCircles.Eight.SignedCycle
open Candidate

theorem internal_strictly_sorted {q : ℝ} (C : SignedCycle)
    (hq : q∈Icc (5/2:ℝ) qCap) (hn : C.Necessary q) (ho : C.Ordered)
    (hs : C.StrictSpread) (hr : ∀i,(C.point i).Boundary q)
    (owner : Vertex→Fin 4) (hf : ∀i,C.Feasible i (owner i))
    (v : Vertex) (hv : v=G∨v=A∨v=B∨v=T) : |(C.point v).y|<(C.point v).a := by
  let K := C.realizeBoundary hn ho hr owner hf
  obtain ⟨F,hFtheta,hFquarter⟩ := EDiagonalExclusion.offsetLift_exists K C.theta
    (by simpa only [StrictSpread,frameCap] using hs)
    (by
      intro i
      change (C.realizeBoundary hn ho hr owner hf).canonicalAngle i=_
      simpa only [actualAngle,mul_div_assoc] using C.realizeBoundary_canonicalAngle hn ho hr owner hf i)
  exact BinaryDiagonalExclusion.of_offsetLift K (by simpa only [qCap,Q0] using hq) F hFquarter v hv

theorem nearest_axis_tie_locations {q : ℝ} (C : SignedCycle)
    (hq : q∈Icc (5/2:ℝ) qCap) (hn : C.Necessary q) (ho : C.Ordered)
    (hs : C.StrictSpread) (hr : ∀i,(C.point i).Boundary q)
    (owner : Vertex→Fin 4) (hf : ∀i,C.Feasible i (owner i)) :
    (∀v,v=G∨v=A∨v=B∨v=T∨v=E → |(C.point v).y|<(C.point v).a) ∧
      (C.point H).y≠ -(C.point H).a ∧ (C.point D).y≠(C.point D).a := by
  have hH := C.realized_zero_tie_exclusions hn ho hr owner hf
    (by simpa only [qCap,Q0] using hq.2) hs (i:=H) (by norm_num [Candidate.word,H])
  have hD := C.realized_zero_tie_exclusions hn ho hr owner hf
    (by simpa only [qCap,Q0] using hq.2) hs (i:=T) (by norm_num [Candidate.word,T])
  refine ⟨?_,hH.1,?_⟩
  · intro v hv
    rcases hv with hG|hA|hB|hT|rfl
    · exact C.internal_strictly_sorted hq hn ho hs hr owner hf v (Or.inl hG)
    · exact C.internal_strictly_sorted hq hn ho hs hr owner hf v (Or.inr (Or.inl hA))
    · exact C.internal_strictly_sorted hq hn ho hs hr owner hf v (Or.inr (Or.inr (Or.inl hB)))
    · exact C.internal_strictly_sorted hq hn ho hs hr owner hf v (Or.inr (Or.inr (Or.inr hT)))
    · exact C.E_strictly_sorted hq hn ho hs hr owner hf
  · simpa [next,T,D] using hD.2

namespace BoundaryInput
theorem internal_strictly_sorted {q : ℝ} (I : BoundaryInput q)
    (hq : q∈Icc (5/2:ℝ) qCap) (v : Vertex) (hv : v=G∨v=A∨v=B∨v=T) :
    |(I.cycle.point v).y|<(I.cycle.point v).a :=
  I.cycle.internal_strictly_sorted hq I.necessary I.ordered I.strict_spread I.radial
    I.witnesses.owner I.witnesses.feasible v hv
theorem G_negative_not_diagonal {q : ℝ} (I : BoundaryInput q) (hq : q∈Icc (5/2:ℝ) qCap) :
    (I.cycle.point G).y≠ -(I.cycle.point G).a := by
  intro hd
  have hh := I.internal_strictly_sorted hq G (Or.inl rfl)
  rw [hd,abs_neg,abs_of_pos (I.necessary.sorted G).1] at hh
  exact lt_irrefl _ hh
theorem T_positive_not_diagonal {q : ℝ} (I : BoundaryInput q) (hq : q∈Icc (5/2:ℝ) qCap) :
    (I.cycle.point T).y≠(I.cycle.point T).a := by
  intro hd
  have hh := I.internal_strictly_sorted hq T (Or.inr (Or.inr (Or.inr rfl)))
  rw [hd,abs_of_pos (I.necessary.sorted T).1] at hh
  exact lt_irrefl _ hh
end BoundaryInput
end SquaresInCircles.Eight.SignedCycle
end
end
end

section
@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight

open Candidate

namespace GlobalEH

/-- Every weak EH witness has owner `0` or `1`, whatever the sign of E. -/
theorem frame_EH_low {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (hq : q∈Icc (5/2:ℝ) Q0)
    (j : Fin 4) (hEH : (forwardAxis j).Feasible (C.square E) (C.square H)) :
    j=0 ∨ j=1 := by
  by_contra hn
  have hhigh : j=2 ∨ j=3 := by fin_cases j <;> simp_all
  have hE := GlobalQuarterOuter.frame_high_anchor F hq E
    (by norm_num [word,E]) j hhigh (by simpa [E,H,next] using hEH)
  let jB := SignedCycle.retainedOwner F B
  have hBT : (forwardAxis jB).Feasible (C.square B) (C.square T) := by
    have hh := (SignedCycle.atFrame_feasible F B jB).1
      (SignedCycle.retainedOwner_feasible F B)
    simpa [B,T,next] using hh
  have hB := GlobalBT.frame_BT_high F hq hE.2.le jB hBT
  exact frame_high_EH_high_BT_false F hq j jB hhigh hB hEH hBT

end GlobalEH

namespace GlobalOriginalOwners

theorem frame_H_anchor {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (hq : q∈Icc (5/2:ℝ) Q0) :
    C.kind H=.outer ∧ 0<C.tangent H := by
  have hf : (forwardAxis (SignedCycle.retainedOwner F E)).Feasible (C.square E)
      (C.square (next E)) :=
    (SignedCycle.atFrame_feasible F E _).1 (SignedCycle.retainedOwner_feasible F E)
  generalize SignedCycle.retainedOwner F E = j at hf
  have hlow := GlobalEH.frame_EH_low F hq j (by simpa [E,H,next] using hf)
  rcases GlobalQuarterOuter.frame_classify F hq E (by norm_num [word,E]) j hf with
    ⟨_,ho,hs⟩ | ⟨hbad,_⟩
  · simpa [E,H,next] using And.intro ho hs
  · rcases hlow with rfl | rfl <;> rcases hbad with hbad | hbad <;> norm_num at hbad

theorem frame_B_anchor {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (hq : q∈Icc (5/2:ℝ) Q0) (hE : C.tangent E≤0) :
    C.kind B=.outer ∧ C.tangent B<0 := by
  let j := SignedCycle.retainedOwner F B
  have hf : (forwardAxis j).Feasible (C.square B) (C.square (next B)) :=
    (SignedCycle.atFrame_feasible F B j).1 (SignedCycle.retainedOwner_feasible F B)
  have hhigh := GlobalBT.frame_BT_high F hq hE j (by simpa [B,T,next] using hf)
  exact GlobalQuarterOuter.frame_high_anchor F hq B (by norm_num [word,B]) j hhigh hf

theorem frame_D_anchor {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (hq : q∈Icc (5/2:ℝ) Q0) (hE : C.tangent E≤0) :
    C.kind D=.outer ∧ C.tangent D<0 := by
  let j := SignedCycle.retainedOwner F D
  have hf : (forwardAxis j).Feasible (C.square D) (C.square (next D)) :=
    (SignedCycle.atFrame_feasible F D j).1 (SignedCycle.retainedOwner_feasible F D)
  have hhigh := (GlobalQuarterSign.frame_DE F hq hE).2 j
    (by simpa [D,E,next] using hf)
  exact GlobalQuarterOuter.frame_high_anchor F hq D (by norm_num [word,D]) j hhigh hf

/-- When `C.tangent E ≤ 0`, every weak axis on an edge other than GA has a normal owner, each member
of a weak tie included. -/
theorem frame_other_owners {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (hq : q∈Icc (5/2:ℝ) Q0) (hE : C.tangent E≤0)
    (i : Vertex) (hi : i≠G) (j : Fin 4)
    (hj : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    j∈SignedCycle.normalOwners i := by
  have hcases : i=H ∨ i=A ∨ i=B ∨ i=T ∨ i=D ∨ i=E := by
    fin_cases i <;> simp_all [H,G,A,B,T,D,E]
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · rcases GlobalZeroSign.of_frame F hq H (by norm_num [word,H]) j hj with hh | hh
    · simp [SignedCycle.normalOwners,H,hh.1]
    · simp [SignedCycle.normalOwners,H,hh.1]
  · rcases GlobalZeroSign.of_frame F hq A (by norm_num [word,A]) j hj with hh | hh
    · simp [SignedCycle.normalOwners,A,hh.1]
    · simp [SignedCycle.normalOwners,A,hh.1]
  · have hh := GlobalBT.frame_BT_high F hq hE j (by simpa [B,T,next] using hj)
    rcases hh with rfl | rfl <;> simp [SignedCycle.normalOwners,B]
  · rcases GlobalZeroSign.of_frame F hq T (by norm_num [word,T]) j hj with hh | hh
    · simp [SignedCycle.normalOwners,T,hh.1]
    · simp [SignedCycle.normalOwners,T,hh.1]
  · have hh := (GlobalQuarterSign.frame_DE F hq hE).2 j
      (by simpa [D,E,next] using hj)
    rcases hh with rfl | rfl <;> simp [SignedCycle.normalOwners,D]
  · have hh := GlobalEH.frame_EH_low F hq j (by simpa [E,H,next] using hj)
    rcases hh with rfl | rfl <;> simp [SignedCycle.normalOwners,E]

/-- In the signed cycle of the frame, H, B and D lie on the circle of `q`, with `0 < H.y`, `B.y < 0`
and `D.y < 0`. -/
theorem atFrame_anchors {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (hq : q∈Icc (5/2:ℝ) Q0) (hE : C.tangent E≤0) :
    ((SignedCycle.atFrame F).point H).Outer q ∧
      0<((SignedCycle.atFrame F).point H).y ∧
    ((SignedCycle.atFrame F).point B).Outer q ∧
      ((SignedCycle.atFrame F).point B).y<0 ∧
    ((SignedCycle.atFrame F).point D).Outer q ∧
      ((SignedCycle.atFrame F).point D).y<0 := by
  have hH := frame_H_anchor F hq
  have hB := frame_B_anchor F hq hE
  have hD := frame_D_anchor F hq hE
  exact ⟨SignedCycle.atFrame_outer_of_kind F H hH.1,
    (SignedCycle.atFrame_y_pos_iff F H).2 hH.2,
    SignedCycle.atFrame_outer_of_kind F B hB.1,
    (SignedCycle.atFrame_y_neg_iff F B).2 hB.2,
    SignedCycle.atFrame_outer_of_kind F D hD.1,
    (SignedCycle.atFrame_y_neg_iff F D).2 hD.2⟩

end GlobalOriginalOwners
end SquaresInCircles.Eight
end
end
end

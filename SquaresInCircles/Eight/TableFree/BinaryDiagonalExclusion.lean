module

public import SquaresInCircles.Eight.TableFree.QuarterWordSelection
public import SquaresInCircles.Eight.TableFree.EDiagonalExclusion
public import SquaresInCircles.Eight.TableFree.NearestAxisSigns

/-!
# All internal nearest-axis ties are excluded on the original cycle

Uncompiled transcription of Section 4 of
`HAND_G3_GLOBAL_NEAREST_AXIS_TIE_LOCATIONS.md`. The alternative nearest
axis is an actual same-radius representation, preserving the original
weak separators. Its unchanged integer word is carried to Q0 only to
apply the complete binary wrong-word exclusions. No owner restriction or
sign assumption at any other vertex enters the result.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.BinaryDiagonalExclusion
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
  change 0≤integerQuarterIncrement (NearestAxisRecode.lift F v hd).quarter i at hh
  rw [NearestAxisRecode.increment,he] at hh
  norm_num at hh

theorem G_negative {q : ℝ} (C : BoundaryCycle q) (hq : q∈Icc (5/2:ℝ) Q0)
    (F : QuarterLift C) (hm : F.quarter=offsets) (hd : C.b G=C.a G) (hs : C.sigma G= -1) : False := by
  apply recode_wrong C hq F G hd .short 6 false
  intro i
  rw [hm]
  fin_cases i <;> norm_num [integerQuarterIncrement,offsets,NearestAxisRecode.shift,hs,
    quarterDihedral,WordProblems.wrongWord,G,next]
theorem A_positive {q : ℝ} (C : BoundaryCycle q) (hq : q∈Icc (5/2:ℝ) Q0)
    (F : QuarterLift C) (hm : F.quarter=offsets) (hd : C.b A=C.a A) (hs : C.sigma A=1) : False := by
  apply recode_wrong C hq F A hd .second 0 false
  intro i
  rw [hm]
  fin_cases i <;> norm_num [integerQuarterIncrement,offsets,NearestAxisRecode.shift,hs,
    quarterDihedral,WordProblems.wrongWord,A,next]
theorem B_negative {q : ℝ} (C : BoundaryCycle q) (hq : q∈Icc (5/2:ℝ) Q0)
    (F : QuarterLift C) (hm : F.quarter=offsets) (hd : C.b B=C.a B) (hs : C.sigma B= -1) : False := by
  apply recode_wrong C hq F B hd .second 4 false
  intro i
  rw [hm]
  fin_cases i <;> norm_num [integerQuarterIncrement,offsets,NearestAxisRecode.shift,hs,
    quarterDihedral,WordProblems.wrongWord,B,next]
theorem T_positive {q : ℝ} (C : BoundaryCycle q) (hq : q∈Icc (5/2:ℝ) Q0)
    (F : QuarterLift C) (hm : F.quarter=offsets) (hd : C.b T=C.a T) (hs : C.sigma T=1) : False := by
  apply recode_wrong C hq F T hd .short 3 true
  intro i
  rw [hm]
  fin_cases i <;> norm_num [integerQuarterIncrement,offsets,NearestAxisRecode.shift,hs,
    quarterDihedral,WordProblems.wrongWord,T,next]

theorem of_offsetLift {q : ℝ} (C : BoundaryCycle q) (hq : q∈Icc (5/2:ℝ) Q0)
    (F : QuarterLift C) (hm : F.quarter=offsets) (v : Vertex)
    (hv : v=G∨v=A∨v=B∨v=T) : C.b v<C.a v := by
  by_contra! hbad
  have hd : C.b v=C.a v := le_antisymm (C.b_le_a v) hbad
  rcases hv with rfl|rfl|rfl|rfl
  · rcases C.sigma_sign G with hs|hs
    · exact G_negative C hq F hm hd hs
    · apply recode_negative C hq F G hd H
      rw [hm]
      norm_num [integerQuarterIncrement,offsets,NearestAxisRecode.shift,hs,H,G,next]
  · rcases C.sigma_sign A with hs|hs
    · apply recode_negative C hq F A hd A
      rw [hm]
      norm_num [integerQuarterIncrement,offsets,NearestAxisRecode.shift,hs,A,next]
    · exact A_positive C hq F hm hd hs
  · rcases C.sigma_sign B with hs|hs
    · exact B_negative C hq F hm hd hs
    · apply recode_negative C hq F B hd A
      rw [hm]
      norm_num [integerQuarterIncrement,offsets,NearestAxisRecode.shift,hs,A,B,next]
  · rcases C.sigma_sign T with hs|hs
    · apply recode_negative C hq F T hd T
      rw [hm]
      norm_num [integerQuarterIncrement,offsets,NearestAxisRecode.shift,hs,T,next]
    · exact T_positive C hq F hm hd hs

theorem of_frame {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C)
    (hq : q∈Icc (5/2:ℝ) Q0) (v : Vertex) (hv : v=G∨v=A∨v=B∨v=T) : C.b v<C.a v := by
  obtain ⟨G,hGtheta,hGquarter⟩ := EDiagonalExclusion.offsetLift_exists C F.theta
    (by simpa only [frameCap] using F.spread)
    (by intro i; simpa only [mul_div_assoc] using F.canonical_eq i)
  exact of_offsetLift C hq G hGquarter v hv

end SquaresInCircles.Eight.TableFree.BinaryDiagonalExclusion

namespace SquaresInCircles.Eight.TableFree.SignedCycle
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
end SquaresInCircles.Eight.TableFree.SignedCycle

module

public import SquaresInCircles.Eight.Frames.High.HighCentral
public import SquaresInCircles.Eight.Frames.High.MidCentral
public import SquaresInCircles.Eight.Frames.Mid.HighCentral

/-!
# Eight squares: the middle/high and high/high pairs

The pair inequality `γ(s, t) < cost` for a middle state against a high one, a high state against
a middle one and two high states, on each of the four forward axes, at a gap of at least `19/25`
(`middle_high_pair`, `high_middle_pair`, `high_high_pair`), and on the edges of a boundary cycle at
`Q0` (`middle_high_cycle_pair`, `high_middle_cycle_pair`, `high_high_cycle_pair`). The states
include both ends of their arcs.
-/

section
/-!
## The middle/high and high/high pairs on every axis

In the diagonal frame, which is a change of coordinates, every separating axis of a middle/high,
high/middle or high/high pair gives `γ(s, t) < cost` (`original_pair`). An axis of the source,
`j = 0` or `j = 3`, is either the central axis of the folded arcs, past whose cut the bound holds
(`folded_central`), or is excluded by the geometry of the arcs at late angles and past the
quarter turn (`folded_late`, `folded_quarter_nonopposite`, `original_source`). An axis of the
target is an axis of the source of the reversed pair (`State.target_primary_reverse`,
`State.target_secondary_reverse`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameDiagonalOriginal
open FramePair FrameDiagonalArc FrameDiagonalLabels FrameDiagonalTransport
open FrameDiagonalGeometry

theorem folded_central (m n i j : Bool) (hhigh : m=false ∨ n=false)
    {b B x : ℝ} (hb : b∈arc m) (hB : B∈arc n) (hx : 0≤x)
    (hm : 0≤central i j (A b) b (A B) B x) :
    handGamma (kind m).type (kind n).type<cost m n i j b B x := by
  cases m <;> cases n
  · have hh := FrameHighHighCentral.central_lower i j hb hB hx hm
    norm_num [kind,Branch.type,handGamma,handGammaNumerator] at ⊢
    exact hh
  · have hh := FrameHighMidCentral.central_lower i j hb hB hx hm
    norm_num [kind,Branch.type,handGamma,handGammaNumerator] at ⊢
    exact hh
  · have hh := FrameMidHighCentral.central_lower i j hb hB hx hm
    norm_num [kind,Branch.type,handGamma,handGammaNumerator] at ⊢
    exact hh
  · rcases hhigh with h | h <;> cases h

theorem folded_late (m n i j : Bool) (hhigh : m=false ∨ n=false)
    {b B x : ℝ} (hb : b∈arc m) (hB : B∈arc n) (hx : (171/100:ℝ)≤x) :
    handGamma (kind m).type (kind n).type<cost m n i j b B x := by
  cases m <;> cases n
  · have hh := FrameDiagonalTails.high_high_late i j hb hB
      (show Real.pi/2≤x by linarith [Arithmetic.pi_hand_enclosure.2])
    norm_num [kind,Branch.type,handGamma,handGammaNumerator] at ⊢
    exact hh
  · have hh := FrameDiagonalTails.high_middle_late i j hb hB hx
    norm_num [kind,Branch.type,handGamma,handGammaNumerator] at ⊢
    exact hh
  · have hh := FrameDiagonalTails.middle_high_late i j hb hB hx
    norm_num [kind,Branch.type,handGamma,handGammaNumerator] at ⊢
    exact hh
  · rcases hhigh with h | h <;> cases h

theorem folded_quarter_nonopposite (m n i j : Bool) (hhigh : m=false ∨ n=false)
    {b B x : ℝ} (hb : b∈arc m) (hB : B∈arc n) (hx : Real.pi/2≤x)
    (hsg : i=true ∨ j=false) :
    handGamma (kind m).type (kind n).type<cost m n i j b B x := by
  cases m <;> cases n
  · have hh := FrameDiagonalTails.high_high_late i j hb hB hx
    norm_num [kind,Branch.type,handGamma,handGammaNumerator] at ⊢
    exact hh
  · have htail : FrameDiagonalTails.mhTail false i j≤x := by
      have hpi := Arithmetic.pi_hand_enclosure.1
      cases i <;> cases j <;> simp [FrameDiagonalTails.mhTail] at hsg ⊢ <;> linarith
    have hh := FrameDiagonalTails.high_middle i j hb hB htail
    norm_num [kind,Branch.type,handGamma,handGammaNumerator] at ⊢
    exact hh
  · have htail : FrameDiagonalTails.mhTail true i j≤x := by
      have hpi := Arithmetic.pi_hand_enclosure.1
      cases i <;> cases j <;> simp [FrameDiagonalTails.mhTail] at hsg ⊢ <;> linarith
    have hh := FrameDiagonalTails.middle_high i j hb hB htail
    norm_num [kind,Branch.type,handGamma,handGammaNumerator] at ⊢
    exact hh
  · rcases hhigh with h | h <;> cases h

theorem original_source (m n : Bool) (s t : FramePair.State)
    (hs : s.branch=kind m) (ht : t.branch=kind n) (hhigh : m=false ∨ n=false)
    (j : Fin 4) (hj : j=0 ∨ j=3) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t j x) :
    handGamma s.branch.type t.branch.type<s.cost t x := by
  have hb := (state_fold m s hs).1
  have hB := (state_fold n t ht).1
  rw [hs,ht,← state_cost m n s t hs ht x]
  by_cases hx : angle s.positive t.positive x≤Real.pi/2
  · have hc := source_first_central m n s t hs ht hhigh j hj hgap hx hm
    exact folded_central m n (!s.positive) (!t.positive) hhigh hb hB hc.1.le
      (state_central_feasible m n s t hs ht hc.2)
  have hquarter : Real.pi/2≤angle s.positive t.positive x := (lt_of_not_ge hx).le
  by_cases hlate : (171/100:ℝ)≤angle s.positive t.positive x
  · exact folded_late m n (!s.positive) (!t.positive) hhigh hb hB hlate
  by_cases hsg : (!s.positive)=true ∨ (!t.positive)=false
  · exact folded_quarter_nonopposite m n (!s.positive) (!t.positive)
      hhigh hb hB hquarter hsg
  have hi : s.positive=true := by
    cases he : s.positive <;> simp [he] at hsg ⊢
  have hk : t.positive=false := by
    cases he : t.positive <;> simp [he] at hsg ⊢
  have hc : s.Feasible t (centralAxis s.positive) x := by
    rcases hj with rfl | rfl
    · simpa [centralAxis,hi] using hm
    · have he := state_extra m n s t hs ht hi x
      have hn := extra_late_false m n hb hB ⟨hquarter,(lt_of_not_ge hlate).le⟩
      have he' : extra true (A (s.a-s.b)) (s.a-s.b) (A (t.a-t.b)) (t.a-t.b)
          (angle s.positive t.positive x)=
            2*forwardMargin 3 s.a s.b t.a t.b (sign s.positive) (sign t.positive) x := by
        simpa only [hk,Bool.not_false] using he
      rw [he'] at hn
      have hm' : 0≤forwardMargin 3 s.a s.b t.a t.b
          (sign s.positive) (sign t.positive) x := hm
      linarith
  exact folded_central m n (!s.positive) (!t.positive) hhigh hb hB
    (by linarith [Real.pi_pos]) (state_central_feasible m n s t hs ht hc)

theorem original_pair (m n : Bool) (s t : FramePair.State)
    (hs : s.branch=kind m) (ht : t.branch=kind n) (hhigh : m=false ∨ n=false)
    (j : Fin 4) {x : ℝ} (hgap : (19/25:ℝ)≤ s.gap t x)
    (hm : s.Feasible t j x) :
    handGamma s.branch.type t.branch.type<s.cost t x := by
  fin_cases j
  · exact original_source m n s t hs ht hhigh 0 (Or.inl rfl) hgap hm
  · have hh := original_source n m t.flip s.flip ht hs hhigh.symm 3 (Or.inr rfl)
      (by simpa using hgap) ((s.target_primary_reverse t x).mp hm)
    have hr' : handGamma t.flip.branch.type s.flip.branch.type<s.cost t x := by simpa using hh
    have hr : handGamma t.branch.type s.branch.type<s.cost t x := hr'
    simpa only [gamma_symmetric s.branch t.branch] using hr
  · have hh := original_source n m t.flip s.flip ht hs hhigh.symm 0 (Or.inl rfl)
      (by simpa using hgap) ((s.target_secondary_reverse t x).mp hm)
    have hr' : handGamma t.flip.branch.type s.flip.branch.type<s.cost t x := by simpa using hh
    have hr : handGamma t.branch.type s.branch.type<s.cost t x := hr'
    simpa only [gamma_symmetric s.branch t.branch] using hr
  · exact original_source m n s t hs ht hhigh 3 (Or.inr rfl) hgap hm

end SquaresInCircles.Eight.FrameDiagonalOriginal
end
end
end

section
@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.FrameDiagonalPair
open FramePair FrameDiagonalTransport FrameDiagonalOriginal

theorem middle_high_pair (s t : FramePair.State)
    (hs : s.branch=.middle) (ht : t.branch=.high) (j : Fin 4) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t j x) :
    handGamma s.branch.type t.branch.type<s.cost t x :=
  original_pair true false s t hs ht (Or.inr rfl) j hgap hm

theorem high_middle_pair (s t : FramePair.State)
    (hs : s.branch=.high) (ht : t.branch=.middle) (j : Fin 4) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t j x) :
    handGamma s.branch.type t.branch.type<s.cost t x :=
  original_pair false true s t hs ht (Or.inl rfl) j hgap hm

theorem high_high_pair (s t : FramePair.State)
    (hs : s.branch=.high) (ht : t.branch=.high) (j : Fin 4) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t j x) :
    handGamma s.branch.type t.branch.type<s.cost t x :=
  original_pair false false s t hs ht (Or.inl rfl) j hgap hm

theorem middle_high_cycle_pair (C : BoundaryCycle Q0) (i : Vertex)
    (hi : branchOf C i=.middle) (hj : branchOf C (next i)=.high)
    (j : Fin 4) (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    handGamma (branchOf C i).type (branchOf C (next i)).type<
      (stateOf C i).cost (stateOf C (next i)) (pairAngle C i) :=
  middle_high_pair (stateOf C i) (stateOf C (next i)) hi hj j
    (stateOf_gap_bounds C i).1.le (stateOf_feasible C i j haxis)

theorem high_middle_cycle_pair (C : BoundaryCycle Q0) (i : Vertex)
    (hi : branchOf C i=.high) (hj : branchOf C (next i)=.middle)
    (j : Fin 4) (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    handGamma (branchOf C i).type (branchOf C (next i)).type<
      (stateOf C i).cost (stateOf C (next i)) (pairAngle C i) :=
  high_middle_pair (stateOf C i) (stateOf C (next i)) hi hj j
    (stateOf_gap_bounds C i).1.le (stateOf_feasible C i j haxis)

theorem high_high_cycle_pair (C : BoundaryCycle Q0) (i : Vertex)
    (hi : branchOf C i=.high) (hj : branchOf C (next i)=.high)
    (j : Fin 4) (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    handGamma (branchOf C i).type (branchOf C (next i)).type<
      (stateOf C i).cost (stateOf C (next i)) (pairAngle C i) :=
  high_high_pair (stateOf C i) (stateOf C (next i)) hi hj j
    (stateOf_gap_bounds C i).1.le (stateOf_feasible C i j haxis)

end SquaresInCircles.Eight.FrameDiagonalPair
end
end
end

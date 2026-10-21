module

public import SquaresInCircles.Eight.TableFree.FrameHighMidCentral
public import SquaresInCircles.Eight.TableFree.FrameHighHighCentral

/-!
# Original weak owners for middle/high and high/high

The diagonal frame is only a coordinate change.  Each original source
axis is either the literal central axis or is directly excluded by the
actual arc geometry.  Target owners are transported by exact reflected
reversal.  No axis is selected by a sampled or generated comparison.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameDiagonalOriginal
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
      cases i <;> cases j <;> norm_num [FrameDiagonalTails.mhTail] at hsg ⊢
      all_goals linarith [Arithmetic.pi_hand_enclosure.1]
    have hh := FrameDiagonalTails.high_middle i j hb hB htail
    norm_num [kind,Branch.type,handGamma,handGammaNumerator] at ⊢
    exact hh
  · have htail : FrameDiagonalTails.mhTail true i j≤x := by
      cases i <;> cases j <;> norm_num [FrameDiagonalTails.mhTail] at hsg ⊢
      all_goals linarith [Arithmetic.pi_hand_enclosure.1]
    have hh := FrameDiagonalTails.middle_high i j hb hB htail
    norm_num [kind,Branch.type,handGamma,handGammaNumerator] at ⊢
    exact hh
  · rcases hhigh with h | h <;> cases h

theorem original_source (m n : Bool) (s t : FramePair.State)
    (hs : s.branch=kind m) (ht : t.branch=kind n) (hhigh : m=false ∨ n=false)
    (j : Fin 4) (hj : j=0 ∨ j=3) {x : ℝ}
    (hgap : (19/25:ℝ)≤s.gap t x) (hm : s.Feasible t j x) :
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
    (j : Fin 4) {x : ℝ} (hgap : (19/25:ℝ)≤s.gap t x)
    (hm : s.Feasible t j x) :
    handGamma s.branch.type t.branch.type<s.cost t x := by
  fin_cases j
  · exact original_source m n s t hs ht hhigh 0 (Or.inl rfl) hgap hm
  · have hh := original_source n m t.flip s.flip ht hs hhigh.symm 3 (Or.inr rfl)
      (by simpa using hgap) ((s.target_primary_reverse t x).mp hm)
    have hr : handGamma t.branch.type s.branch.type<s.cost t x := by simpa using hh
    simpa only [gamma_symmetric s.branch t.branch] using hr
  · have hh := original_source n m t.flip s.flip ht hs hhigh.symm 0 (Or.inl rfl)
      (by simpa using hgap) ((s.target_secondary_reverse t x).mp hm)
    have hr : handGamma t.branch.type s.branch.type<s.cost t x := by simpa using hh
    simpa only [gamma_symmetric s.branch t.branch] using hr
  · exact original_source m n s t hs ht hhigh 3 (Or.inr rfl) hgap hm

end SquaresInCircles.Eight.TableFree.FrameDiagonalOriginal

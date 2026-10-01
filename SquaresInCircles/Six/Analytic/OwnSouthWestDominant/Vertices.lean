import SquaresInCircles.Six.Analytic.OwnSouthWestDominant.Curvature

/-!
# The four vertices of the west-dominant shared-angle polygon

For fixed d, the admissible polygon is
  0 <= s <= v <= 2/3, v+s <= 24/25.
Concavity in v first leaves the equal-tilt boundary, the fixed west endpoint,
and the shared-angle boundary. Each boundary is a sum of concave one-variable
slices. Its four vertices are exactly
  (0,0), (2/3,0), (2/3,22/75), (12/25,12/25).
The diagonal concavity then leaves d=1/2 and d=11/14. This module proves the
geometric endpoint reduction separately from evaluating those endpoints.
Compilation and kernel acceptance remain unverified.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.OwnSouthWestDominant

def FourVertices (upper : Bool) (d : ℝ) : Prop :=
  0 < profile upper 0 0 d ∧
  0 < profile upper (2/3) 0 d ∧
  0 < profile upper (2/3) (22/75) d ∧
  0 < profile upper (12/25) (12/25) d

private lemma equal_wall_concave (upper : Bool) {d : ℝ}
    (hd : 1/2 ≤ d ∧ d ≤ 11/14) :
    ConcaveOn ℝ (Set.Icc 0 (12/25)) (fun s => profile upper s s d) := by
  have hw0 := concave_affine_argument (a := 1) (b := 0) (west_slice_concave upper hd)
    (l := 0) (u := 12/25) (by
      intro s hs
      constructor <;> linarith [hs.1,hs.2])
  have hw : ConcaveOn ℝ (Set.Icc 0 (12/25)) (westSlice upper d) := by
    simpa only [one_mul,add_zero] using hw0
  exact ((concave_constant (constantTerm+diagonalTerm upper d) 0 (12/25)).add hw).add
    (south_slice_concave upper hd)

private lemma vertical_wall_concave (upper : Bool) {d : ℝ}
    (hd : 1/2 ≤ d ∧ d ≤ 11/14) :
    ConcaveOn ℝ (Set.Icc 0 (22/75)) (fun s => profile upper (2/3) s d) := by
  have hs0 := concave_affine_argument (a := 1) (b := 0) (south_slice_concave upper hd)
    (l := 0) (u := 22/75) (by
      intro s hs
      constructor <;> linarith [hs.1,hs.2])
  have hs : ConcaveOn ℝ (Set.Icc 0 (22/75)) (southSlice upper d) := by
    simpa only [one_mul,add_zero] using hs0
  exact (concave_constant
    (constantTerm+diagonalTerm upper d+westSlice upper d (2/3)) 0 (22/75)).add hs

private lemma sum_wall_concave (upper : Bool) {d : ℝ}
    (hd : 1/2 ≤ d ∧ d ≤ 11/14) :
    ConcaveOn ℝ (Set.Icc (22/75) (12/25))
      (fun s => profile upper (24/25-s) s d) := by
  have hw0 := concave_affine_argument (a := -1) (b := 24/25) (west_slice_concave upper hd)
    (l := 22/75) (u := 12/25) (by
      intro s hs
      constructor <;> linarith [hs.1,hs.2])
  have hw : ConcaveOn ℝ (Set.Icc (22/75) (12/25))
      (fun s => westSlice upper d (24/25-s)) := by
    convert hw0 using 1
    funext s
    congr 1
    ring
  have hs0 := concave_affine_argument (a := 1) (b := 0) (south_slice_concave upper hd)
    (l := 22/75) (u := 12/25) (by
      intro s hs
      constructor <;> linarith [hs.1,hs.2])
  have hs : ConcaveOn ℝ (Set.Icc (22/75) (12/25)) (southSlice upper d) := by
    simpa only [one_mul,add_zero] using hs0
  exact ((concave_constant (constantTerm+diagonalTerm upper d) (22/75) (12/25)).add hw).add hs

/-- The polygon reduction follows from its actual boundaries, not a subdivision. -/
theorem positive_of_four_vertices (upper : Bool) {v s d : ℝ}
    (hv : v ≤ 2/3) (hs : 0 ≤ s) (horder : s ≤ v) (hsum : v+s ≤ 24/25)
    (hd : 1/2 ≤ d ∧ d ≤ 11/14) (hvertices : FourVertices upper d) :
    0 < profile upper v s d := by
  have hv0 : 0 ≤ v := hs.trans horder
  have hsmax : s ≤ 12/25 := by linarith
  have hequal : 0 < profile upper s s d :=
    positive_on_concave_interval (f := fun s => profile upper s s d)
      (equal_wall_concave upper hd) ⟨hs,hsmax⟩
      hvertices.1 hvertices.2.2.2
  have hcv : ConcaveOn ℝ (Set.Icc 0 (2/3)) (fun x => profile upper x s d) := by
    have h := ((concave_constant (constantTerm+diagonalTerm upper d) 0 (2/3)).add
      (west_slice_concave upper hd)).add (concave_constant (southSlice upper d s) 0 (2/3))
    exact h
  by_cases hcut : s ≤ 22/75
  · have htop : 0 < profile upper (2/3) s d :=
      positive_on_concave_interval (f := fun s => profile upper (2/3) s d)
        (vertical_wall_concave upper hd) ⟨hs,hcut⟩
        hvertices.2.1 hvertices.2.2.1
    have hm := hcv.min_le_of_mem_Icc
      (show s ∈ Set.Icc 0 (2/3) by constructor <;> linarith)
      (by norm_num : (2:ℝ)/3 ∈ Set.Icc 0 (2/3)) ⟨horder,hv⟩
    exact (lt_min hequal htop).trans_le hm
  · have hleft : 0 < profile upper (24/25-22/75) (22/75) d := by
      rw [show (24:ℝ)/25-22/75 = 2/3 by norm_num]
      exact hvertices.2.2.1
    have hright : 0 < profile upper (24/25-12/25) (12/25) d := by
      rw [show (24:ℝ)/25-12/25 = 12/25 by norm_num]
      exact hvertices.2.2.2
    have htop : 0 < profile upper (24/25-s) s d :=
      positive_on_concave_interval (f := fun s => profile upper (24/25-s) s d)
        (sum_wall_concave upper hd)
        ⟨le_of_not_ge hcut,hsmax⟩ hleft hright
    have hupper : 24/25-s ∈ Set.Icc 0 (2/3) := by
      constructor <;> linarith
    have hm := hcv.min_le_of_mem_Icc
      (show s ∈ Set.Icc 0 (2/3) by constructor <;> linarith) hupper
      (show s ≤ v ∧ v ≤ 24/25-s by constructor <;> linarith)
    exact (lt_min hequal htop).trans_le hm

/-- Eight geometric vertices suffice for either supporting central box face. -/
theorem positive_of_diagonal_endpoints (upper : Bool) {v s d : ℝ}
    (hv : v ≤ 2/3) (hs : 0 ≤ s) (horder : s ≤ v) (hsum : v+s ≤ 24/25)
    (hd : 1/2 ≤ d ∧ d ≤ 11/14)
    (hl : FourVertices upper (1/2)) (hu : FourVertices upper (11/14)) :
    0 < profile upper v s d := by
  have hv0 : 0 ≤ v := hs.trans horder
  have hsmax : s ≤ 12/25 := by linarith
  have hleft := positive_of_four_vertices upper hv hs horder hsum
    (d := 1/2) (by norm_num) hl
  have hright := positive_of_four_vertices upper hv hs horder hsum
    (d := 11/14) (by norm_num) hu
  exact positive_on_concave_interval
    (profile_diagonal_concave upper ⟨hv0,hv⟩ ⟨hs,hsmax⟩ horder) hd hleft hright

end SquaresInCircles.Six.Analytic.OwnSouthWestDominant

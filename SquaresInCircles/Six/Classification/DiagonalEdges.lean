module
public import SquaresInCircles.Six.Stress.RowTactics

@[expose] public section

/-!
# Preliminary D-edge classification

All W-to-D directions start from actual SAT. Cardinal W uses the eight
Pattern-10 rows; OWN W uses P17/P18 or the negative-W rows. The pin signs
supply the primary switch at pi/12. This proves d>1/2 and leaves only the two
secondary source axes, with W-secondary forced whenever OWN W has w>=0.
-/

noncomputable section
namespace SquaresInCircles.Six.Classification
open Normalization Stress

abbrev DWSelected {R : ℝ} (P : NormalizedPacking R) (i : Fin 8) : Prop :=
  Seven.SAT.threshold (P.square 2) (P.square 3) ≤
    dot (Stress.pairNormal i (P.square 2) (P.square 3))
      (sub (P.square 3).center (P.square 2).center)

abbrev DSSelected {R : ℝ} (P : NormalizedPacking R) (i : Fin 8) : Prop :=
  Seven.SAT.threshold (P.square 3) (P.square 4) ≤
    dot (Stress.pairNormal i (P.square 3) (P.square 4))
      (sub (P.square 4).center (P.square 3).center)

lemma baseline_ranges {R : ℝ} (P : NormalizedPacking R) :
    (-2/3<P.helperAngle 2 ∧ P.helperAngle 2<Real.pi/4) ∧
    (-Real.pi/4<P.helperAngle 4 ∧ P.helperAngle 4<Real.pi/4) ∧
    (0<P.diagonalAngle ∧ P.diagonalAngle≤Real.pi/4) ∧
    P.helperAngle 2<P.diagonalAngle := by
  have hw := P.helper_windows.2.2.1
  have hs := P.helper_windows.2.2.2
  have hd := P.diagonal_angle_range
  have ho : P.helperAngle 2<P.diagonalAngle := by
    have h := P.primary_order.2.2.1
    dsimp [NormalizedPacking.helperAngle,NormalizedPacking.diagonalAngle,matchingCardinal,cardinalCenter]
    linarith
  exact ⟨⟨hw.1,ho.trans_le hd.2⟩,
    ⟨by linarith [hs.1,Real.pi_gt_d2],by linarith [hs.2,Real.pi_gt_d2]⟩,hd,ho⟩

lemma DW_not_negative_secondary {R : ℝ} (P : NormalizedPacking R) (i : Fin 8)
    (hi : DWSelected P i) : i≠3 ∧ i≠7 := by
  have hp := selected_axis_points_to_pin _ _ (P.pin 2) (P.pin 3) i hi
  constructor
  · intro he; subst i
    change 0<dot (scale (-1) (normalY (P.square 2))) _ at hp
    rw [dot_scale_neg] at hp
    linarith [P.DW_chord_positive_secondary.1]
  · intro he; subst i
    change 0<dot (scale (-1) (normalY (P.square 3))) _ at hp
    rw [dot_scale_neg] at hp
    linarith [P.DW_chord_positive_secondary.2]

/-- Complete preliminary classification, retaining the actual selected axis. -/
theorem DW_restrictions {R : ℝ} (P : NormalizedPacking R) (i : Fin 8)
    (hi : DWSelected P i) :
    (i=2 ∨ i=6) ∧ 1/2<P.diagonalAngle ∧
      (P.ownBits 2=true → 0≤P.helperAngle 2 →
        i=2 ∧ Real.pi/4-1/4<P.diagonalAngle) := by
  obtain ⟨⟨hw0,hw1⟩,⟨hs0,hs1⟩,⟨hd0,hd1⟩,hwd⟩ := baseline_ranges P
  obtain ⟨h3,h7⟩ := DW_not_negative_secondary P i hi
  have hpi := Real.pi_gt_d2
  cases hb : P.ownBits 2 with
  | false =>
    have hc := abs_lt.mp (P.cardinal_angle 2 hb)
    obtain ⟨hc0,hc1⟩ := hc
    have hsec : i=2 ∨ i=6 := by
      fin_cases i
      · exclude_main 2 for P
      · exclude_main 3 for P
      · exact Or.inl rfl
      · exact False.elim (h3 rfl)
      · exclude_main 4 for P
      · exclude_main 5 for P
      · exact Or.inr rfl
      · exact False.elim (h7 rfl)
    have hhigh : 1/2<P.diagonalAngle := by
      by_contra! hlow
      rcases hsec with rfl | rfl
      · exclude_main 6 for P
      · exclude_main 8 for P
    exact ⟨hsec,hhigh,by simp [hb]⟩
  | true =>
    by_cases hw : 0≤P.helperAngle 2
    · have hsec : i=2 ∨ i=6 := by
        fin_cases i
        · exclude_main 25 for P
        · exclude_main 26 for P
        · exact Or.inl rfl
        · exact False.elim (h3 rfl)
        · exclude_main 27 for P
        · exclude_main 28 for P
        · exact Or.inr rfl
        · exact False.elim (h7 rfl)
      have hhigh : Real.pi/4-1/4<P.diagonalAngle := by
        by_contra! hlow
        rcases hsec with rfl | rfl
        · exclude_main 29 for P
        · exclude_main 30 for P
      have haxis : i=2 := by
        rcases hsec with h | h
        · exact h
        · subst i
          exclude_main 31 for P
      exact ⟨Or.inl haxis,by linarith,fun _ _ => ⟨haxis,hhigh⟩⟩
    · have hwneg : P.helperAngle 2<0 := lt_of_not_ge hw
      have hsign := P.DW_primary_sign hi
      have hsec : i=2 ∨ i=6 := by
        fin_cases i
        · have hh := hsign.1 rfl
          linarith
        · exclude_main 35 for P
        · exact Or.inl rfl
        · exact False.elim (h3 rfl)
        · have hh := hsign.2.2.1 rfl
          exclude_main 36 for P
        · have hh := hsign.2.2.2 rfl
          exclude_main 37 for P
        · exact Or.inr rfl
        · exact False.elim (h7 rfl)
      have hhigh : 1/2<P.diagonalAngle := by
        by_contra! hlow
        rcases hsec with rfl | rfl
        · exclude_main 33 for P
        · exclude_main 34 for P
      exact ⟨hsec,hhigh,fun _ hnonneg => False.elim (hw hnonneg)⟩

/-- The diagonal edge graph is supplied by real pairwise disjointness. -/
theorem diagonal_edges_exist {R : ℝ} (P : NormalizedPacking R) :
    ∃ i j : Fin 8, DWSelected P i ∧ DSSelected P j ∧ (i=2 ∨ i=6) ∧
      (j=1 ∨ j=2 ∨ j=4 ∨ j=5 ∨ j=6) ∧ 1/2<P.diagonalAngle ∧
      (P.ownBits 2=true → 0≤P.helperAngle 2 →
        i=2 ∧ Real.pi/4-1/4<P.diagonalAngle) := by
  obtain ⟨i,hi,_,_⟩ := P.DW_source
  obtain ⟨j,hj,h0,h3,h7⟩ := P.DS_source
  have hd := DW_restrictions P i hi
  have hjs : j=1 ∨ j=2 ∨ j=4 ∨ j=5 ∨ j=6 := by
    fin_cases j <;> simp_all
  exact ⟨i,j,hi,hj,hd.1,hjs,hd.2.1,hd.2.2⟩

end SquaresInCircles.Six.Classification

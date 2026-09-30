module
public import SquaresInCircles.Six.PinChords
public import SquaresInCircles.Six.PreferredAxes

@[expose] public section

/-!
# Pin-oriented downstream source inventories

N/W is oriented W-to-N, E/S is S-to-E, and the diagonal edges are W-to-D
and D-to-S. Their signs agree with the audited direct-stress data. Primary
D/W and S/D sign switches are derived, not silently discarded.
-/

noncomputable section
namespace SquaresInCircles.Six
open Normalization Normalization.Certificates

def NWsigns : Fin 4 → Bool := ![false,false,true,false]
def ESsigns : Fin 4 → Bool := ![false,true,true,true]

lemma NW_chord_projections (w n a b A B : ℝ) (i : Fin 4) :
    dot (preferredPairAxis NWsigns (orientedSquare (Real.pi+w) a b)
      (orientedSquare (Real.pi/2+n) A B) i) (sub (fixedPin 1) (fixedPin 2)) =
    adjacentChordLength *
      ![Real.cos (5*Real.pi/24-w),Real.sin (5*Real.pi/24-w),
        Real.sin (5*Real.pi/24-n),Real.cos (5*Real.pi/24-n)] i := by
  rw [pin_chord_NW]
  fin_cases i <;> simp [preferredPairAxis,unsignedPairAxis,NWsigns,normalX,normalY,
    orientedSquare,dot,scale,polar,Real.cos_add,Real.sin_add,Real.cos_sub,Real.sin_sub] <;> ring

lemma ES_chord_projections (s e a b A B : ℝ) (i : Fin 4) :
    dot (preferredPairAxis ESsigns (orientedSquare (3*Real.pi/2+s) a b)
      (orientedSquare e A B) i) (sub (fixedPin 0) (fixedPin 4)) =
    adjacentChordLength *
      ![Real.sin (7*Real.pi/24-s),Real.cos (7*Real.pi/24-s),
        Real.cos (7*Real.pi/24-e),Real.sin (7*Real.pi/24-e)] i := by
  rw [pin_chord_ES]
  fin_cases i <;> simp [preferredPairAxis,unsignedPairAxis,ESsigns,normalX,normalY,
    orientedSquare,dot,scale,polar,Real.cos_add,Real.sin_add,Real.cos_sub,Real.sin_sub,
    south_cos,south_sin] <;> ring

private lemma sine_cosine_positive {t : ℝ} (ht : 0<t ∧ t<Real.pi/2) :
    0<Real.sin t ∧ 0<Real.cos t :=
  ⟨Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2,Real.pi_pos]),
    Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1,Real.pi_pos],ht.2⟩⟩

lemma NW_chord_positive {w n : ℝ}
    (hw : -2/3<w ∧ w<5/8) (hn : -3/10<n ∧ n<5/12)
    (a b A B : ℝ) (i : Fin 4) :
    0 < dot (preferredPairAxis NWsigns (orientedSquare (Real.pi+w) a b)
      (orientedSquare (Real.pi/2+n) A B) i) (sub (fixedPin 1) (fixedPin 2)) := by
  have hW := sine_cosine_positive
    (show 0<5*Real.pi/24-w ∧ 5*Real.pi/24-w<Real.pi/2 by
      constructor <;> linarith [hw.1,hw.2,Real.pi_gt_d2])
  have hN := sine_cosine_positive
    (show 0<5*Real.pi/24-n ∧ 5*Real.pi/24-n<Real.pi/2 by
      constructor <;> linarith [hn.1,hn.2,Real.pi_gt_d2])
  rw [NW_chord_projections]
  apply mul_pos adjacentChordLength_pos
  fin_cases i
  · exact hW.2
  · exact hW.1
  · exact hN.1
  · exact hN.2

lemma ES_chord_positive {s e : ℝ}
    (hs : -5/8<s ∧ s<2/3) (he : -5/12<e ∧ e<3/10)
    (a b A B : ℝ) (i : Fin 4) :
    0 < dot (preferredPairAxis ESsigns (orientedSquare (3*Real.pi/2+s) a b)
      (orientedSquare e A B) i) (sub (fixedPin 0) (fixedPin 4)) := by
  have hS := sine_cosine_positive
    (show 0<7*Real.pi/24-s ∧ 7*Real.pi/24-s<Real.pi/2 by
      constructor <;> linarith [hs.1,hs.2,Real.pi_gt_d2])
  have hE := sine_cosine_positive
    (show 0<7*Real.pi/24-e ∧ 7*Real.pi/24-e<Real.pi/2 by
      constructor <;> linarith [he.1,he.2,Real.pi_gt_d2])
  rw [ES_chord_projections]
  apply mul_pos adjacentChordLength_pos
  fin_cases i
  · exact hS.1
  · exact hS.2
  · exact hE.2
  · exact hE.1

private lemma positive_sin_forces_positive {t : ℝ} (ht : -Real.pi≤t)
    (hs : 0<Real.sin t) : 0<t := by
  by_contra! h
  have hh := Real.sin_nonneg_of_nonneg_of_le_pi (show 0≤-t by linarith)
    (show -t≤Real.pi by linarith)
  rw [Real.sin_neg] at hh
  linarith

private lemma negative_sin_forces_negative {t : ℝ} (ht : t≤Real.pi)
    (hs : Real.sin t<0) : t<0 := by
  by_contra! h
  linarith [Real.sin_nonneg_of_nonneg_of_le_pi h ht]

namespace Normalization.NormalizedPacking
variable {R : ℝ} (P : NormalizedPacking R)

def square (i : Fin 5) : UnitSquare := P.model i.succ

lemma square_def (i : Fin 5) : P.square i=orientedSquare (P.phase i) (P.radial i) (P.transverse i) := rfl

lemma phase_from_deviation (i : Fin 5) :
    P.phase i=cardinalCenter (matchingCardinal i)+P.helperAngle i := by
  dsimp [helperAngle]
  ring

lemma helper_windows :
    (-5/12<P.helperAngle 0 ∧ P.helperAngle 0<3/10) ∧
    (-3/10<P.helperAngle 1 ∧ P.helperAngle 1<5/12) ∧
    (-2/3<P.helperAngle 2 ∧ P.helperAngle 2<5/8) ∧
    (-5/8<P.helperAngle 4 ∧ P.helperAngle 4<2/3) := by
  have he := P.window 0
  have hn := P.window 1
  have hw := P.window 2
  have hs := P.window 4
  simpa [helperAngle,matchingCardinal,cardinalCenter,windowLower,windowUpper,phaseCenter]
    using And.intro he (And.intro hn (And.intro hw hs))

lemma pair_disjoint (i j : Fin 5) (hij : i≠j) :
    ∀ p, ¬ (openSquare (P.square i) p ∧ openSquare (P.square j) p) :=
  P.toPinPacking.exterior_disjoint i j hij

/-- Exactly the four N/W source normals in the manuscript, all oriented W-to-N. -/
theorem NW_source : ∃ i : Fin 4,
    Seven.SAT.threshold (P.square 2) (P.square 1) ≤
      dot (preferredPairAxis NWsigns (P.square 2) (P.square 1) i)
        (sub (P.square 1).center (P.square 2).center) := by
  apply preferred_separators_complete NWsigns _ _ (P.pin 2) (P.pin 1) _
    (P.pair_disjoint 2 1 (by decide))
  intro i
  rw [P.square_def 2,P.square_def 1,P.phase_from_deviation 2,P.phase_from_deviation 1]
  exact NW_chord_positive P.helper_windows.2.2.1 P.helper_windows.2.1 _ _ _ _ i

/-- Exactly the four E/S source normals in the manuscript, all oriented S-to-E. -/
theorem ES_source : ∃ i : Fin 4,
    Seven.SAT.threshold (P.square 4) (P.square 0) ≤
      dot (preferredPairAxis ESsigns (P.square 4) (P.square 0) i)
        (sub (P.square 0).center (P.square 4).center) := by
  apply preferred_separators_complete ESsigns _ _ (P.pin 4) (P.pin 0) _
    (P.pair_disjoint 4 0 (by decide))
  intro i
  rw [P.square_def 4,P.square_def 0,P.phase_from_deviation 4,P.phase_from_deviation 0]
  simpa only [matchingCardinal,cardinalCenter,zero_add] using
    ES_chord_positive P.helper_windows.2.2.2 P.helper_windows.1 _ _ _ _ i

lemma DW_chord_positive_secondary :
    0<dot (normalY (P.square 2)) (sub (fixedPin 3) (fixedPin 2)) ∧
    0<dot (normalY (P.square 3)) (sub (fixedPin 3) (fixedPin 2)) := by
  have hw := P.helper_windows.2.2.1
  have hd := P.diagonal_angle_range
  have hcw := Real.cos_pos_of_mem_Ioo
    (show P.helperAngle 2-Real.pi/12 ∈ Set.Ioo (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hw.1,hw.2,Real.pi_gt_d2])
  have hcd := Real.cos_pos_of_mem_Ioo
    (show P.diagonalAngle-Real.pi/12 ∈ Set.Ioo (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hd.1,hd.2,Real.pi_pos])
  constructor
  · change 0<dot (secondary (P.phase 2)) (sub (fixedPin 3) (fixedPin 2))
    rw [P.phase_from_deviation 2]
    change 0<dot (secondary (Real.pi+P.helperAngle 2)) _
    rw [WD_secondary_projection]
    exact mul_pos (by norm_num) hcw
  · change 0<dot (secondary (P.phase 3)) (sub (fixedPin 3) (fixedPin 2))
    rw [show P.phase 3=Real.pi+P.diagonalAngle by dsimp [diagonalAngle]; ring,
      WD_secondary_projection]
    exact mul_pos (by norm_num) hcd

/-- Negative secondary D/W orientations are impossible. -/
theorem DW_source : ∃ i : Fin 8,
    Seven.SAT.threshold (P.square 2) (P.square 3) ≤
      dot (Stress.pairNormal i (P.square 2) (P.square 3))
        (sub (P.square 3).center (P.square 2).center) ∧ i≠3 ∧ i≠7 := by
  obtain ⟨i,hi⟩ := Stress.directed_pair_separator _ _ (P.pair_disjoint 2 3 (by decide))
  have hp := selected_axis_points_to_pin _ _ (P.pin 2) (P.pin 3) i hi
  refine ⟨i,hi,?_,?_⟩
  · intro h
    subst i
    change 0<dot (scale (-1) (normalY (P.square 2))) _ at hp
    rw [dot_scale_neg] at hp
    linarith [P.DW_chord_positive_secondary.1]
  · intro h
    subst i
    change 0<dot (scale (-1) (normalY (P.square 3))) _ at hp
    rw [dot_scale_neg] at hp
    linarith [P.DW_chord_positive_secondary.2]

lemma DS_chord_signs :
    dot (normalX (P.square 3)) (sub (fixedPin 4) (fixedPin 3))<0 ∧
    0<dot (normalY (P.square 3)) (sub (fixedPin 4) (fixedPin 3)) ∧
    0<dot (normalY (P.square 4)) (sub (fixedPin 4) (fixedPin 3)) := by
  have hd := P.diagonal_angle_range
  have hs := P.helper_windows.2.2.2
  have hds := sine_cosine_positive
    (show 0<P.diagonalAngle+Real.pi/12 ∧ P.diagonalAngle+Real.pi/12<Real.pi/2 by
      constructor <;> linarith [hd.1,hd.2,Real.pi_pos])
  have hsc := Real.cos_pos_of_mem_Ioo
    (show P.helperAngle 4+Real.pi/12 ∈ Set.Ioo (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hs.1,hs.2,Real.pi_gt_d2])
  have hD : P.phase 3=Real.pi+P.diagonalAngle := by dsimp [diagonalAngle]; ring
  have hS : P.phase 4=3*Real.pi/2+P.helperAngle 4 := P.phase_from_deviation 4
  change dot (primary (P.phase 3)) _<0 ∧ 0<dot (secondary (P.phase 3)) _ ∧
    0<dot (secondary (P.phase 4)) _
  rw [hD,hS,DS_primary_D_projection,DS_secondary_D_projection,DS_secondary_S_projection]
  exact ⟨mul_neg_of_neg_of_pos (by norm_num) hds.2,
    mul_pos (by norm_num) hds.1,mul_pos (by norm_num) hsc⟩

/-- D/S retains both primary S signs, but only -e_D, +f_D and +f_S. -/
theorem DS_source : ∃ i : Fin 8,
    Seven.SAT.threshold (P.square 3) (P.square 4) ≤
      dot (Stress.pairNormal i (P.square 3) (P.square 4))
        (sub (P.square 4).center (P.square 3).center) ∧ i≠0 ∧ i≠3 ∧ i≠7 := by
  obtain ⟨i,hi⟩ := Stress.directed_pair_separator _ _ (P.pair_disjoint 3 4 (by decide))
  have hp := selected_axis_points_to_pin _ _ (P.pin 3) (P.pin 4) i hi
  refine ⟨i,hi,?_,?_,?_⟩
  · intro h; subst i
    linarith [P.DS_chord_signs.1]
  · intro h; subst i
    change 0<dot (scale (-1) (normalY (P.square 3))) _ at hp
    rw [dot_scale_neg] at hp
    linarith [P.DS_chord_signs.2.1]
  · intro h; subst i
    change 0<dot (scale (-1) (normalY (P.square 4))) _ at hp
    rw [dot_scale_neg] at hp
    linarith [P.DS_chord_signs.2.2]

/-- The S-primary sign switch is the exact pin wall s=-pi/12. -/
lemma DS_primary_sign {i : Fin 8}
    (hi : Seven.SAT.threshold (P.square 3) (P.square 4) ≤
      dot (Stress.pairNormal i (P.square 3) (P.square 4))
        (sub (P.square 4).center (P.square 3).center)) :
    (i=4 → -Real.pi/12<P.helperAngle 4) ∧
    (i=5 → P.helperAngle 4< -Real.pi/12) := by
  have hp := selected_axis_points_to_pin _ _ (P.pin 3) (P.pin 4) i hi
  have hs := P.helper_windows.2.2.2
  have hS : P.phase 4=3*Real.pi/2+P.helperAngle 4 := P.phase_from_deviation 4
  constructor
  · intro h; subst i
    change 0<dot (primary (P.phase 4)) _ at hp
    rw [hS,DS_primary_S_projection] at hp
    have hh := positive_sin_forces_positive
      (show -Real.pi≤P.helperAngle 4+Real.pi/12 by linarith [hs.1,Real.pi_gt_d2])
      (show 0<Real.sin (P.helperAngle 4+Real.pi/12) by nlinarith)
    linarith
  · intro h; subst i
    change 0<dot (scale (-1) (primary (P.phase 4))) _ at hp
    rw [dot_scale_neg,hS,DS_primary_S_projection] at hp
    have hh := negative_sin_forces_negative
      (show P.helperAngle 4+Real.pi/12≤Real.pi by linarith [hs.2,Real.pi_gt_d2])
      (show Real.sin (P.helperAngle 4+Real.pi/12)<0 by nlinarith)
    linarith

/-- D-primary D/W switches at d=pi/12; W-primary switches at w=pi/12. -/
lemma DW_primary_sign {i : Fin 8}
    (hi : Seven.SAT.threshold (P.square 2) (P.square 3) ≤
      dot (Stress.pairNormal i (P.square 2) (P.square 3))
        (sub (P.square 3).center (P.square 2).center)) :
    (i=0 → Real.pi/12<P.helperAngle 2) ∧ (i=1 → P.helperAngle 2<Real.pi/12) ∧
    (i=4 → Real.pi/12<P.diagonalAngle) ∧ (i=5 → P.diagonalAngle<Real.pi/12) := by
  have hp := selected_axis_points_to_pin _ _ (P.pin 2) (P.pin 3) i hi
  have hw := P.helper_windows.2.2.1
  have hd := P.diagonal_angle_range
  have hW : P.phase 2=Real.pi+P.helperAngle 2 := P.phase_from_deviation 2
  have hD : P.phase 3=Real.pi+P.diagonalAngle := by dsimp [diagonalAngle]; ring
  refine ⟨?_,?_,?_,?_⟩
  · intro h; subst i
    change 0<dot (primary (P.phase 2)) _ at hp
    rw [hW,WD_primary_projection] at hp
    have hh := positive_sin_forces_positive
      (show -Real.pi≤P.helperAngle 2-Real.pi/12 by linarith [hw.1,Real.pi_gt_d2])
      (show 0<Real.sin (P.helperAngle 2-Real.pi/12) by nlinarith)
    linarith
  · intro h; subst i
    change 0<dot (scale (-1) (primary (P.phase 2))) _ at hp
    rw [dot_scale_neg,hW,WD_primary_projection] at hp
    have hh := negative_sin_forces_negative
      (show P.helperAngle 2-Real.pi/12≤Real.pi by linarith [hw.2,Real.pi_gt_d2])
      (show Real.sin (P.helperAngle 2-Real.pi/12)<0 by nlinarith)
    linarith
  · intro h; subst i
    change 0<dot (primary (P.phase 3)) _ at hp
    rw [hD,WD_primary_projection] at hp
    have hh := positive_sin_forces_positive
      (show -Real.pi≤P.diagonalAngle-Real.pi/12 by linarith [hd.1,Real.pi_pos])
      (show 0<Real.sin (P.diagonalAngle-Real.pi/12) by nlinarith)
    linarith
  · intro h; subst i
    change 0<dot (scale (-1) (primary (P.phase 3))) _ at hp
    rw [dot_scale_neg,hD,WD_primary_projection] at hp
    have hh := negative_sin_forces_negative
      (show P.diagonalAngle-Real.pi/12≤Real.pi by linarith [hd.2,Real.pi_pos])
      (show Real.sin (P.diagonalAngle-Real.pi/12)<0 by nlinarith)
    linarith

end Normalization.NormalizedPacking
end SquaresInCircles.Six

module
public import SquaresInCircles.Six.Analytic.NonnegativeWestSecondary

@[expose] public section

/-!
# Nonpositive S has only the two forward secondary D/S sources

The new analytic d>1/2 bound puts the D/S phase gap below 11/10 when s<=0.
At that gap the core radial bound and |b|<1/2 exclude both nontrivial primary
axes. The two outward directions are excluded uniformly, and the reverse
secondary directions are excluded by the actual pin chord.

The conclusion is deliberately the two-source inventory, not the final
S-secondary choice. For s>0 the remaining primary cases still require their
separate joint classification.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

lemma cosine_lower_eleven_tenths {q : ℝ} (hq : |q|≤11/10) : 9/20≤Real.cos q := by
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg q)
    (show (11:ℝ)/10≤Real.pi by linarith [Real.pi_gt_d2]) hq
  rw [Real.cos_abs] at hc
  have he := Seven.cos_lower_six (x := (11:ℝ)/10) (by norm_num)
  nlinarith only [hc,he]

lemma inward_primary_eleven_tenths {a A B q : ℝ}
    (ha : a≤rho0) (hA : aMin≤A) (hB : |B|<1/2) (hq : |q|≤11/10) :
    a-A*Real.cos q+B*Real.sin q<1/2+angularWidth q := by
  have hc := cosine_lower_eleven_tenths hq
  have hA0 : 0≤A+1/2 := by dsimp [aMin] at hA; linarith [rho0_upper]
  have hprod := mul_le_mul_of_nonneg_left hc hA0
  have hBproj : B*Real.sin q≤|B|*|Real.sin q| := by
    simpa only [abs_mul] using le_abs_self (B*Real.sin q)
  have hBwidth := mul_le_mul_of_nonneg_right hB.le (abs_nonneg (Real.sin q))
  rw [angularWidth,abs_of_nonneg (show 0≤Real.cos q by linarith)]
  dsimp [aMin] at hA
  nlinarith [rho0_upper]

lemma destination_primary_eleven_tenths {a b A q : ℝ}
    (hA : A≤rho0) (ha : aMin≤a) (hb : |b|<1/2) (hq : |q|≤11/10) :
    A-a*Real.cos q-b*Real.sin q<1/2+angularWidth q := by
  have h := inward_primary_eleven_tenths (a := A) (A := a) (B := -b)
    hA ha (by simpa only [abs_neg] using hb) hq
  nlinarith only [h]

/-- All selected primary directions are excluded, not just a preferred source. -/
theorem DS_selected_secondary_nonpositive_S {R : ℝ} (P : NormalizedPacking R)
    (hs : P.helperAngle 4≤0) (k : Fin 8)
    (hsep : Seven.SAT.threshold (P.square 3) (P.square 4)≤
      dot (Stress.pairNormal k (P.square 3) (P.square 4))
        (sub (P.square 4).center (P.square 3).center)) : k=2 ∨ k=6 := by
  have hd := normalized_diagonal_gt_half P
  have hdphase : P.phase 3=Real.pi+P.diagonalAngle := by
    dsimp [NormalizedPacking.diagonalAngle]
    ring
  have hsphase : P.phase 4=3*Real.pi/2+P.helperAngle 4 := P.phase_from_deviation 4
  have horder := P.primary_order.2.2.2.1
  have hq : |P.phase 4-P.phase 3|≤11/10 := by
    rw [abs_of_nonneg (sub_nonneg.mpr horder.le),hsphase,hdphase]
    linarith [Real.pi_lt_d2]
  have hi := inward_primary_eleven_tenths (P.contained 3).a_le_rho0
    ((P.contained 4).aMin_le (P.avoidsCore 4))
    ((P.contained 4).u_lt_half (P.avoidsCore 4)) hq
  have hdest := destination_primary_eleven_tenths (P.contained 4).a_le_rho0
    ((P.contained 3).aMin_le (P.avoidsCore 3))
    ((P.contained 3).u_lt_half (P.avoidsCore 3)) hq
  have hout := normalized_outward_axes_excluded P 3 4 k hsep
  have hp := selected_axis_points_to_pin _ _ (P.pin 3) (P.pin 4) k hsep
  have hnot3 : k≠3 := by
    intro hk
    subst k
    change 0<dot (scale (-1) (normalY (P.square 3))) (sub (fixedPin 4) (fixedPin 3)) at hp
    rw [dot_scale_neg] at hp
    linarith [P.DS_chord_signs.2.1]
  have hnot7 : k≠7 := by
    intro hk
    subst k
    change 0<dot (scale (-1) (normalY (P.square 4))) (sub (fixedPin 4) (fixedPin 3)) at hp
    rw [dot_scale_neg] at hp
    linarith [P.DS_chord_signs.2.2]
  fin_cases k
  · exact False.elim (hout.1 rfl)
  · change Seven.SAT.threshold (P.square 3) (P.square 4)≤
      -frameX (P.square 3) (sub (P.square 4).center (P.square 3).center) at hsep
    rw [P.square_def 3,P.square_def 4,oriented_pair_threshold,pair_frameX_left] at hsep
    linarith
  · exact Or.inl rfl
  · exact False.elim (hnot3 rfl)
  · change Seven.SAT.threshold (P.square 3) (P.square 4)≤
      frameX (P.square 4) (sub (P.square 4).center (P.square 3).center) at hsep
    rw [P.square_def 3,P.square_def 4,oriented_pair_threshold,pair_frameX_right] at hsep
    linarith
  · exact False.elim (hout.2 rfl)
  · exact Or.inr rfl
  · exact False.elim (hnot7 rfl)

/-- Any primary D/S separator lies in the genuine positive-S sign half. -/
theorem DS_primary_forces_positive_S {R : ℝ} (P : NormalizedPacking R) (k : Fin 8)
    (hk : k=1 ∨ k=4)
    (hsep : Seven.SAT.threshold (P.square 3) (P.square 4)≤
      dot (Stress.pairNormal k (P.square 3) (P.square 4))
        (sub (P.square 4).center (P.square 3).center)) : 0<P.helperAngle 4 := by
  by_contra! hs
  have h := DS_selected_secondary_nonpositive_S P hs k hsep
  rcases hk with rfl | rfl <;> rcases h with h | h <;> norm_num at h

end SquaresInCircles.Six.Analytic

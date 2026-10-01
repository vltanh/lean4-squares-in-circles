import SquaresInCircles.Six.Analytic.DiagonalHalfBound

/-!
# Primary-axis exclusion from a positive cosine reserve

The former sixty-degree estimate only needs cos(q)>=9/20. A sixth-order
Taylor endpoint at 11/10 gives that bound on the entire symmetric interval.
Since d>1/2, every nonpositive S deviation puts the D/S phase gap in this
interval. This eliminates both nontrivial primary axes for either S bit,
without reflecting the global D half-window.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

lemma cosine_lower_eleven_tenths {q : ℝ} (hq : |q|≤11/10) : 9/20≤Real.cos q := by
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg q)
    (show (11:ℝ)/10≤Real.pi by linarith [Real.pi_gt_d2]) hq
  have hp := Seven.cos_lower_six (x := (11:ℝ)/10) (by norm_num)
  rw [Real.cos_abs] at hc
  norm_num at hp
  linarith

lemma inward_primary_cosine_bound {a A B q : ℝ}
    (ha : a≤rho0) (hA : aMin≤A) (hB : |B|<1/2) (hq : 9/20≤Real.cos q) :
    a-A*Real.cos q+B*Real.sin q<1/2+angularWidth q := by
  have hA0 : 0≤A+1/2 := by dsimp [aMin] at hA; linarith [rho0_upper]
  have hp := mul_le_mul_of_nonneg_left hq hA0
  have hb : B*Real.sin q≤|B| *|Real.sin q| := by
    simpa only [abs_mul] using le_abs_self (B*Real.sin q)
  have hb' := mul_le_mul_of_nonneg_right hB.le (abs_nonneg (Real.sin q))
  dsimp [angularWidth]
  rw [abs_of_nonneg (show 0≤Real.cos q by linarith)]
  dsimp [aMin] at hA
  nlinarith [rho0_upper]

lemma destination_primary_cosine_bound {a b A q : ℝ}
    (hA : A≤rho0) (ha : aMin≤a) (hb : |b|<1/2) (hq : 9/20≤Real.cos q) :
    A-a*Real.cos q-b*Real.sin q<1/2+angularWidth q := by
  have hh := inward_primary_cosine_bound (a := A) (A := a) (B := -b)
    hA ha (by simpa only [abs_neg] using hb) hq
  nlinarith only [hh]

/-- Both primary directions are excluded for any selected D/S separator
when s<=0. The primary directions already eliminated by outward support
and all reversed secondary axes are handled by the existing pin geometry. -/
theorem DS_selected_secondary_nonpositive_s {R : ℝ} (P : NormalizedPacking R)
    (hs : P.helperAngle 4≤0) (k : Fin 8)
    (hsep : Seven.SAT.threshold (P.square 3) (P.square 4)≤
      dot (Stress.pairNormal k (P.square 3) (P.square 4))
        (sub (P.square 4).center (P.square 3).center)) : k=2 ∨ k=6 := by
  have hout := normalized_outward_axes_excluded P 3 4 k hsep
  have hpin := selected_axis_points_to_pin _ _ (P.pin 3) (P.pin 4) k hsep
  have hchord := P.DS_chord_signs
  have hk3 : k≠3 := by
    intro hk
    subst k
    change 0<dot (scale (-1) (normalY (P.square 3)))
      (sub (Certificates.fixedPin 4) (Certificates.fixedPin 3)) at hpin
    rw [dot_scale_neg] at hpin
    linarith [hchord.2.1]
  have hk7 : k≠7 := by
    intro hk
    subst k
    change 0<dot (scale (-1) (normalY (P.square 4)))
      (sub (Certificates.fixedPin 4) (Certificates.fixedPin 3)) at hpin
    rw [dot_scale_neg] at hpin
    linarith [hchord.2.2]
  have hDphase : P.phase 3=Real.pi+P.diagonalAngle := by
    dsimp [NormalizedPacking.diagonalAngle]
    ring
  have hSphase : P.phase 4=3*Real.pi/2+P.helperAngle 4 := P.phase_from_deviation 4
  have hq : |P.phase 4-P.phase 3|≤11/10 := by
    rw [abs_of_nonneg (sub_nonneg.mpr P.primary_order.2.2.2.1.le),hDphase,hSphase]
    linarith [normalized_diagonal_gt_half P,Real.pi_lt_d2]
  have hcos := cosine_lower_eleven_tenths hq
  have hleft := inward_primary_cosine_bound
    (P.contained 3).a_le_rho0 ((P.contained 4).aMin_le (P.avoidsCore 4))
    ((P.contained 4).u_lt_half (P.avoidsCore 4)) hcos
  have hright := destination_primary_cosine_bound
    (P.contained 4).a_le_rho0 ((P.contained 3).aMin_le (P.avoidsCore 3))
    ((P.contained 3).u_lt_half (P.avoidsCore 3)) hcos
  fin_cases k
  · exact False.elim (hout.1 rfl)
  · change Seven.SAT.threshold (P.square 3) (P.square 4)≤
      dot (scale (-1) (normalX (P.square 3))) (sub (P.square 4).center (P.square 3).center) at hsep
    rw [dot_scale_neg] at hsep
    change Seven.SAT.threshold (P.square 3) (P.square 4)≤
      -frameX (P.square 3) (sub (P.square 4).center (P.square 3).center) at hsep
    rw [P.square_def 3,P.square_def 4,oriented_pair_threshold,pair_frameX_left] at hsep
    linarith
  · exact Or.inl rfl
  · exact False.elim (hk3 rfl)
  · change Seven.SAT.threshold (P.square 3) (P.square 4)≤
      frameX (P.square 4) (sub (P.square 4).center (P.square 3).center) at hsep
    rw [P.square_def 3,P.square_def 4,oriented_pair_threshold,pair_frameX_right] at hsep
    linarith
  · exact False.elim (hout.2 rfl)
  · exact Or.inr rfl
  · exact False.elim (hk7 rfl)

end SquaresInCircles.Six.Analytic

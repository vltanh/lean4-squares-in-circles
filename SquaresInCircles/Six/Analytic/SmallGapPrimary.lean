import SquaresInCircles.Six.Analytic.OutwardAxes

/-!
# Primary separators cannot occur across a sixty-degree phase gap

The near-edge radial lower bound and the transverse bound below 1/2 suffice.
For the two nontrivial primary directions, the threshold's transverse term
absorbs the other center's transverse projection, while cos(q)>=1/2 leaves a
uniform radial reserve. The two outward directions are already excluded by
OutwardAxes. This is a whole-domain geometric argument with no fixed rows.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

lemma cosine_half_of_small_gap {q : ℝ} (hq : |q|≤Real.pi/3) : 1/2≤Real.cos q := by
  have h := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg q)
    (show Real.pi/3≤Real.pi by linarith [Real.pi_pos]) hq
  simpa only [Real.cos_pi_div_three,Real.cos_abs] using h

lemma inward_primary_small_gap {a A B q : ℝ}
    (ha : a≤rho0) (hA : aMin≤A) (hB : |B|<1/2) (hq : |q|≤Real.pi/3) :
    a-A*Real.cos q+B*Real.sin q<1/2+angularWidth q := by
  have hcos := cosine_half_of_small_gap hq
  have hA0 : 0≤A+1/2 := by dsimp [aMin] at hA; linarith [rho0_upper]
  have hp := mul_le_mul_of_nonneg_left hcos hA0
  have hb : B*Real.sin q≤|B|*|Real.sin q| := by
    simpa only [abs_mul] using le_abs_self (B*Real.sin q)
  have hb' := mul_le_mul_of_nonneg_right hB.le (abs_nonneg (Real.sin q))
  dsimp [angularWidth]
  rw [abs_of_nonneg (show 0≤Real.cos q by linarith)]
  dsimp [aMin] at hA
  nlinarith [rho0_upper]

lemma destination_primary_small_gap {a b A q : ℝ}
    (hA : A≤rho0) (ha : aMin≤a) (hb : |b|<1/2) (hq : |q|≤Real.pi/3) :
    A-a*Real.cos q-b*Real.sin q<1/2+angularWidth q := by
  have h := inward_primary_small_gap (a := A) (A := a) (B := -b)
    hA ha (by simpa only [abs_neg] using hb) hq
  nlinarith only [h]

/-- The negative primary of the first square, uniformly on the small-gap set. -/
lemma oriented_inward_primary_excluded {t T a b A B : ℝ}
    (hc : ContainedChart a |b|) (hC : ContainedChart A |B|)
    (hcore : AvoidsCore a |b|) (hCore : AvoidsCore A |B|)
    (hq : |T-t|≤Real.pi/3) :
    dot (scale (-1) (normalX (orientedSquare t a b)))
      (sub (orientedSquare T A B).center (orientedSquare t a b).center)<
      Seven.SAT.threshold (orientedSquare t a b) (orientedSquare T A B) := by
  have h := inward_primary_small_gap hc.a_le_rho0 (hC.aMin_le hCore)
    (hC.u_lt_half hCore) hq
  have hproj := pair_frameX_left t a b T A B
  have hid : dot (scale (-1) (normalX (orientedSquare t a b)))
      (sub (orientedSquare T A B).center (orientedSquare t a b).center)=
      -frameX (orientedSquare t a b)
        (sub (orientedSquare T A B).center (orientedSquare t a b).center) := by
    dsimp [dot,scale,normalX,frameX]
    ring
  rw [hid,hproj,oriented_pair_threshold]
  linarith

/-- The positive primary of the second square, on the same full small-gap set. -/
lemma oriented_destination_primary_excluded {t T a b A B : ℝ}
    (hc : ContainedChart a |b|) (hC : ContainedChart A |B|)
    (hcore : AvoidsCore a |b|) (hCore : AvoidsCore A |B|)
    (hq : |T-t|≤Real.pi/3) :
    dot (normalX (orientedSquare T A B))
      (sub (orientedSquare T A B).center (orientedSquare t a b).center)<
      Seven.SAT.threshold (orientedSquare t a b) (orientedSquare T A B) := by
  have h := destination_primary_small_gap hC.a_le_rho0 (hc.aMin_le hcore)
    (hc.u_lt_half hcore) hq
  change frameX (orientedSquare T A B)
      (sub (orientedSquare T A B).center (orientedSquare t a b).center)<_
  rw [pair_frameX_right,oriented_pair_threshold]
  exact h

/-- In particular nonnegative W leaves only forward secondary W/D axes.
This statement is independent of W's central bit and of any candidate table. -/
theorem normalized_DW_nonnegative_secondary {R : ℝ} (P : NormalizedPacking R)
    (hw : 0≤P.helperAngle 2) : ∃ k : Fin 8,
      Seven.SAT.threshold (P.square 2) (P.square 3)≤
        dot (Stress.pairNormal k (P.square 2) (P.square 3))
          (sub (P.square 3).center (P.square 2).center) ∧ (k=2 ∨ k=6) := by
  obtain ⟨k,hk,hcases⟩ := analytic_DW_four_sources P
  have ht : P.phase 2<P.phase 3 := P.primary_order.2.2.1
  have hq : |P.phase 3-P.phase 2|≤Real.pi/3 := by
    rw [abs_of_nonneg (sub_nonneg.mpr ht.le)]
    have hwphase : P.phase 2=Real.pi+P.helperAngle 2 := P.phase_from_deviation 2
    have hd := P.diagonal_angle_range
    dsimp [NormalizedPacking.diagonalAngle] at hd
    linarith [Real.pi_pos]
  have hn := oriented_inward_primary_excluded (P.contained 2) (P.contained 3)
    (P.avoidsCore 2) (P.avoidsCore 3) hq
  have hN := oriented_destination_primary_excluded (P.contained 2) (P.contained 3)
    (P.avoidsCore 2) (P.avoidsCore 3) hq
  refine ⟨k,hk,?_⟩
  rcases hcases with rfl | rfl | rfl | rfl
  · change Seven.SAT.threshold (P.square 2) (P.square 3)≤
      dot (scale (-1) (normalX (P.square 2))) _ at hk
    exact False.elim (not_le_of_gt hn hk)
  · exact Or.inl rfl
  · change Seven.SAT.threshold (P.square 2) (P.square 3)≤dot (normalX (P.square 3)) _ at hk
    exact False.elim (not_le_of_gt hN hk)
  · exact Or.inr rfl

end SquaresInCircles.Six.Analytic

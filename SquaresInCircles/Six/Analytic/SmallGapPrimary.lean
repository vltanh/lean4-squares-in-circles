import SquaresInCircles.Six.Analytic.OutwardAxes

/-!
# The first axes across a phase gap of at most `π/3`

Two exterior squares in the disk that avoid the core, with phases at most `π/3`
apart, are not separated along the axis `-e₁` of the first square, nor along the
axis `e₁` of the second. Since `cos q ≥ 1/2`, the radial coordinates, at most
`ρ0` for one square and at least `aMin` for the other, and the transverse
coordinate of absolute value below `1/2` keep the projection of the centre
difference below the threshold `1/2 + (|cos q| + |sin q|)/2`.
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
  have hb : B*Real.sin q≤|B| *|Real.sin q| := by
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

/-- Across a phase gap of at most `π/3`, the axis `-e₁` of the first square does
not separate. -/
lemma oriented_inward_primary_excluded {t T a b A B : ℝ}
    (hc : ContainedChart a |b|) (hC : ContainedChart A |B|)
    (hCore : AvoidsCore A |B|)
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

/-- Across a phase gap of at most `π/3`, the axis `e₁` of the second square does
not separate. -/
lemma oriented_destination_primary_excluded {t T a b A B : ℝ}
    (hc : ContainedChart a |b|) (hC : ContainedChart A |B|)
    (hcore : AvoidsCore a |b|)
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

end SquaresInCircles.Six.Analytic

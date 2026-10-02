module

public import SquaresInCircles.Five.Exterior

/-!
# Five squares: the containing square

A square that contains the disk centre, slid outward along the ray through its
centre until that centre is at distance `1/√2`, has an inscribed disk that
covers a fifth of the circle of radius `5/6`. So the radial sweep of the square
holds that fifth, unless the square is centred at the disk centre.
-/

@[expose] public section

noncomputable section
open Set
namespace SquaresInCircles.Five

/-- The sweep of a containing square not centred at `o` holds a 72-degree arc
of the circle of radius `5/6`, centred at the direction of its centre. -/
theorem containing_arc {S : UnitSquare} {o : Point} (C : SquareChart S o)
    (ho : openSquare S o) (hne : S.center ≠ o) :
    ∃ A : OpenArc o aux (openRay S o), A.halfWidth=Real.pi/5 := by
  have hin := C.origin.mp ho
  have hpos : 0 < C.a^2+C.b^2 := by
    have h := normSq_pos_of_ne (sub_ne_origin hne)
    rw [local_center_norm] at h
    rcases C.coordinates with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩ <;> rw [h₁,h₂] <;> linarith
  -- the chart centre in polar form, `(a, b) = ℓ (cos δ, sin δ)` with `ℓ ≤ 1/√2`
  obtain ⟨ℓ,δ,hℓ,hc,hs⟩ : ∃ ℓ δ : ℝ, 0 < ℓ ∧ ℓ*Real.cos δ=C.a ∧ ℓ*Real.sin δ=C.b := by
    refine ⟨‖(⟨C.a,C.b⟩ : ℂ)‖,Complex.arg ⟨C.a,C.b⟩,norm_pos_iff.mpr fun h => ?_,
      Complex.norm_mul_cos_arg _,Complex.norm_mul_sin_arg _⟩
    have h₁ : C.a=0 := congrArg Complex.re h
    have h₂ : C.b=0 := congrArg Complex.im h
    rw [h₁,h₂] at hpos
    norm_num at hpos
  have hℓ2 : ℓ^2=C.a^2+C.b^2 := by
    rw [← hc,← hs]
    linear_combination (-ℓ^2)*Real.sin_sq_add_cos_sq δ
  have hℓh : ℓ ≤ halfDiagonal := by
    nlinarith [halfDiagonal_sq,halfDiagonal_pos,C.nonneg.1,C.nonneg.2,hin.1,hin.2]
  obtain ⟨A,hA,-⟩ := arcFromChartInterval o aux (openRay S o) C.phase C.reversed
    (δ-Real.pi/5) (δ+Real.pi/5) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    fun t ht => C.ray_mem (by
      -- slide the centre to `(cos δ, sin δ)/√2`, at distance below `1/2` from the point
      refine ⟨halfDiagonal/ℓ-1,by rw [sub_nonneg,le_div_iff₀ hℓ]; linarith,?_⟩
      have he : (1+(halfDiagonal/ℓ-1))*ℓ=halfDiagonal := by field_simp; ring
      rw [← hc,← hs,← mul_assoc,← mul_assoc,he]
      -- `cos (t-δ) ≥ cos (π/5) = (1+√5)/4`, and `(1+√5)/(4√2) > 17/30` by squaring
      have hcos : Real.cos (Real.pi/5) ≤ Real.cos (t-δ) := by
        rw [← Real.cos_abs (t-δ)]
        exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos])
          (abs_le.mpr ⟨by linarith [ht.1],by linarith [ht.2]⟩)
      have hkey : 17/30 < halfDiagonal*Real.cos (Real.pi/5) := by
        rw [Real.cos_pi_div_five]
        refine lt_of_pow_lt_pow_left₀ 2 (mul_pos halfDiagonal_pos (by positivity)).le ?_
        rw [mul_pow,halfDiagonal_sq]
        nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num),sqrt_five_gt]
      have hprod := mul_le_mul_of_nonneg_left hcos halfDiagonal_pos.le
      have hid : (aux*Real.cos t-halfDiagonal*Real.cos δ)^2+
          (aux*Real.sin t-halfDiagonal*Real.sin δ)^2 =
          aux^2+halfDiagonal^2-2*aux*(halfDiagonal*Real.cos (t-δ)) := by
        rw [Real.cos_sub]
        linear_combination aux^2*Real.sin_sq_add_cos_sq t+
          halfDiagonal^2*Real.sin_sq_add_cos_sq δ
      have hsq : (aux*Real.cos t-halfDiagonal*Real.cos δ)^2+
          (aux*Real.sin t-halfDiagonal*Real.sin δ)^2 < 1/4 := by
        rw [hid,aux]
        linarith [halfDiagonal_sq]
      exact ⟨abs_lt_of_sq_lt_sq (by nlinarith) (by norm_num),
        abs_lt_of_sq_lt_sq (by nlinarith) (by norm_num)⟩)
  exact ⟨A,by rw [hA]; ring⟩

end SquaresInCircles.Five

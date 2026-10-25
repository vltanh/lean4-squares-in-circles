module

public import SquaresInCircles.Eight.Owners.GA.Nonnegative.TotalsNorms

/-!
# Eight squares: all twelve actual A/E endpoints are strictly positive

Positive auxiliary masses are used only in the elementary
square inequality. The twelve whole-domain numerator certificates are
consumed here; no approximation of a radical is an input hypothesis.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.GlobalGA.NonnegativeTotals.Analytic
open Secondary TensorWholeIntervalPolynomial TwoVariablePolynomial

theorem endpoint_positive (r : Region) (ep : Endpoint) (i : Fin 3)
    {x y : ℝ} (hd : Explicit.Domain r x y) : 0<endpoint r ep i x y := by
  have hm (j : Fin 4) := Certificate.mass_positive r ep i j hd
  have hn (j : Fin 4) := norm_nonnegative r ep i j x y
  have hs (j : Fin 4) := norm_square_upper r ep i j hd
  have hA := nonradical_lower r ep i hd
  have hpoly := Certificate.numerator_positive r ep i hd
  have hpoly0 : 0<evaluate x y (Certificate.numerator r ep i) := by linarith
  have hR : (Certificate.Rbar:ℝ)=(PositiveTD.Certificate.Rbar:ℝ) := by
    norm_num [Certificate.Rbar,PositiveTD.Certificate.Rbar]
  have hP : 0<2*evaluate x y (Certificate.A r ep i)*
      evaluate x y (Certificate.mass r ep i 0)*evaluate x y (Certificate.mass r ep i 1)*
      evaluate x y (Certificate.mass r ep i 2)*evaluate x y (Certificate.mass r ep i 3)-
        (PositiveTD.Certificate.Rbar:ℝ)*
          ((evaluate x y (Certificate.P r ep i 0)+(evaluate x y (Certificate.mass r ep i 0))^2)*
              evaluate x y (Certificate.mass r ep i 1)*evaluate x y (Certificate.mass r ep i 2)*
              evaluate x y (Certificate.mass r ep i 3)+
            (evaluate x y (Certificate.P r ep i 1)+(evaluate x y (Certificate.mass r ep i 1))^2)*
              evaluate x y (Certificate.mass r ep i 0)*evaluate x y (Certificate.mass r ep i 2)*
              evaluate x y (Certificate.mass r ep i 3)+
            (evaluate x y (Certificate.P r ep i 2)+(evaluate x y (Certificate.mass r ep i 2))^2)*
              evaluate x y (Certificate.mass r ep i 0)*evaluate x y (Certificate.mass r ep i 1)*
              evaluate x y (Certificate.mass r ep i 3)+
            (evaluate x y (Certificate.P r ep i 3)+(evaluate x y (Certificate.mass r ep i 3))^2)*
              evaluate x y (Certificate.mass r ep i 0)*evaluate x y (Certificate.mass r ep i 1)*
              evaluate x y (Certificate.mass r ep i 2)) := by
    simp only [Certificate.numerator,map_sub,map_add,map_mul,map_pow,evaluate_scalar,
      Rat.cast_ofNat] at hpoly0
    rw [←hR]
    exact hpoly0
  have hh := PositiveTD.Certificate.four_norm_transfer
    (hm 0) (hm 1) (hm 2) (hm 3) (hn 0) (hn 1) (hn 2) (hn 3)
    (hs 0) (hs 1) (hs 2) (hs 3) hA hP
  rwa [endpoint_identity r ep i hd]

end SquaresInCircles.Eight.GlobalGA.NonnegativeTotals.Analytic

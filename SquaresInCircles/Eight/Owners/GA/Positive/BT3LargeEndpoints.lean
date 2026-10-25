module

public import SquaresInCircles.Eight.Owners.GA.Positive.BT3LargeBounds
public import SquaresInCircles.Eight.Owners.GA.Positive.BT3LargePolynomial

/-!
# Eight squares: positivity of the six actual BT3 large-total T endpoints

Each original squared norm is
bounded by its displayed polynomial, and all four auxiliary masses
are positive on the complete native domain. The resulting positive
numerator proves the strict actual endpoint stress inequality.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.GlobalGA.PositiveBT3.Analytic
open Secondary TensorWholeIntervalPolynomial TwoVariablePolynomial NonnegativeTotals

theorem T_endpoint_positive (r : Region) (i : Fin 3)
    {x y : ℝ} (hd : Explicit.Domain r x y) : 0<largeEndpoint r .atT i x y := by
  have hm (j : Fin 4) := LargeCertificate.mass_positive r i j hd
  have hn (j : Fin 4) := norm_nonnegative r i j x y
  have hs (j : Fin 4) := norm_square_upper r i j hd
  have hA := nonradical_lower r i hd
  have hpoly := LargeCertificate.numerator_positive r i hd
  have hpoly0 : 0<evaluate x y (LargeCertificate.numerator r i) := by linarith
  have hR : ((PositiveTD.Certificate.Rbar:ℚ):ℝ)=494696877/250000000 := by
    norm_num [PositiveTD.Certificate.Rbar]
  have hP : 0<2*evaluate x y (LargeCertificate.A r i)*
      evaluate x y (LargeCertificate.mass r i 0)*evaluate x y (LargeCertificate.mass r i 1)*
      evaluate x y (LargeCertificate.mass r i 2)*evaluate x y (LargeCertificate.mass r i 3)-
        (PositiveTD.Certificate.Rbar:ℝ)*
          ((evaluate x y (LargeCertificate.P r i 0)+(evaluate x y (LargeCertificate.mass r i 0))^2)*
              evaluate x y (LargeCertificate.mass r i 1)*evaluate x y (LargeCertificate.mass r i 2)*
              evaluate x y (LargeCertificate.mass r i 3)+
            (evaluate x y (LargeCertificate.P r i 1)+(evaluate x y (LargeCertificate.mass r i 1))^2)*
              evaluate x y (LargeCertificate.mass r i 0)*evaluate x y (LargeCertificate.mass r i 2)*
              evaluate x y (LargeCertificate.mass r i 3)+
            (evaluate x y (LargeCertificate.P r i 2)+(evaluate x y (LargeCertificate.mass r i 2))^2)*
              evaluate x y (LargeCertificate.mass r i 0)*evaluate x y (LargeCertificate.mass r i 1)*
              evaluate x y (LargeCertificate.mass r i 3)+
            (evaluate x y (LargeCertificate.P r i 3)+(evaluate x y (LargeCertificate.mass r i 3))^2)*
              evaluate x y (LargeCertificate.mass r i 0)*evaluate x y (LargeCertificate.mass r i 1)*
              evaluate x y (LargeCertificate.mass r i 2)) := by
    rw [hR]
    simpa only [LargeCertificate.numerator,map_sub,map_add,map_mul,map_pow,evaluate_scalar,
      LargeCertificate.Rbar,NonnegativeTotals.Certificate.Rbar,Rat.cast_ofNat,Rat.cast_div]
      using hpoly0
  have hh := PositiveTD.Certificate.four_norm_transfer
    (hm 0) (hm 1) (hm 2) (hm 3) (hn 0) (hn 1) (hn 2) (hn 3)
    (hs 0) (hs 1) (hs 2) (hs 3) hA hP
  rwa [T_endpoint_identity r i hd]

end SquaresInCircles.Eight.GlobalGA.PositiveBT3.Analytic

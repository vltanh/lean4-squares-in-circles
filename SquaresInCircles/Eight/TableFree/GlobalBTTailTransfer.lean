module

public import SquaresInCircles.Eight.TableFree.GlobalBTTailPolynomials

/-!
# Exact radical transfer for all six DE2 tail scalars

The two positive quadratic envelopes are used only through square
completion.  Their explicit polynomial certificates imply the actual
two-circle inequalities for the full affine multiplier families.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalBT

open Polynomial FrameCircleArc

def tailEndpoint (last : Bool) (e m c z : ℝ) : ℝ :=
  Real.pi-z+(3/2)*kappa+2*c+e/2+m+
    (if last then kappa+e*Real.cos z else kappa*Real.cos z+e)-
    R*(tailNorm kappa c (if last then 0 else z)+tailNorm e c (if last then z else 0))

theorem radius_upper : R<1979/1000 := by
  have hh := FrameHighArc.radius_bound
  dsimp [FrameHighArc.radiusUpper] at hh
  linarith

theorem sin7_lower {z : ℝ} (hz : 0≤z) : Arithmetic.sin7 z≤Real.sin z := by
  simpa only [Arithmetic.sin7] using sin_lower_seven hz

/-- One reusable two-norm square completion.  X1 and X2 need no
independent positivity assumption: they dominate the actual squares. -/
theorem two_norm_envelope {N1 N2 X1 X2 P1 P2 L : ℝ}
    (hN1 : 0≤N1) (hN2 : 0≤N2) (hP1 : 0<P1) (hP2 : 0<P2)
    (hX1 : N1^2≤X1) (hX2 : N2^2≤X2)
    (hpoly : 0<2*P1*P2*L-(1979/1000)*
      (P2*(X1+P1^2)+P1*(X2+P2^2))) : R*(N1+N2)<L := by
  have h1 : 2*P1*N1≤X1+P1^2 := by nlinarith [sq_nonneg (N1-P1)]
  have h2 : 2*P2*N2≤X2+P2^2 := by nlinarith [sq_nonneg (N2-P2)]
  have hh1 := mul_le_mul_of_nonneg_left h1 (by positivity : 0≤(1979/1000:ℝ)*P2)
  have hh2 := mul_le_mul_of_nonneg_left h2 (by positivity : 0≤(1979/1000:ℝ)*P1)
  have hprod : 0<2*P1*P2 := by positivity
  have hmain : (1979/1000)*(N1+N2)<L := by
    apply (mul_lt_mul_iff_left₀ hprod).1
    nlinarith only [hpoly,hh1,hh2]
  have hr := mul_le_mul_of_nonneg_right radius_upper.le (add_nonneg hN1 hN2)
  exact hr.trans_lt hmain

theorem first_square_upper (i : Fin 3) (last : Bool) {z : ℝ}
    (hz : z∈Icc 0 frameCap) :
    (tailNorm kappa (aeval z (TailPolynomial.weight i)) (if last then 0 else z))^2≤
      aeval z (TailPolynomial.x1 i last) := by
  have hw := (TailPolynomial.weights_bounds i hz).1
  have hk : 0<kappa := by norm_num [kappa]
  have hs := mul_le_mul_of_nonneg_left (sin7_lower hz.1)
    (show 0≤2*kappa*aeval z (TailPolynomial.weight i) by positivity)
  cases last
  · simp only [Bool.false_eq_true,↓reduceIte]
    rw [tailNorm_sq hk hw hz]
    simp only [TailPolynomial.x1,Bool.false_eq_true,↓reduceIte,map_sub,map_add,map_mul,
      map_pow,aeval_C,TailPolynomial.S7_eval]
    norm_num [kappa] at hs ⊢
    linarith
  · simp only [↓reduceIte]
    rw [tailNorm_sq hk hw (by norm_num [frameCap])]
    simp [TailPolynomial.x1,kappa]

theorem second_square_upper (i : Fin 3) (last : Bool) {z : ℝ}
    (hz : z∈Icc 0 frameCap) :
    (tailNorm (TailPolynomial.e i:ℝ) (aeval z (TailPolynomial.weight i))
      (if last then z else 0))^2≤aeval z (TailPolynomial.x2 i last) := by
  have hw := (TailPolynomial.weights_bounds i hz).1
  have he := TailPolynomial.chart_positive i
  have hs := mul_le_mul_of_nonneg_left (sin7_lower hz.1)
    (show 0≤2*(TailPolynomial.e i:ℝ)*aeval z (TailPolynomial.weight i) by positivity)
  cases last
  · simp only [Bool.false_eq_true,↓reduceIte]
    rw [tailNorm_sq he hw (by norm_num [frameCap])]
    simp [TailPolynomial.x2]
  · simp only [↓reduceIte]
    rw [tailNorm_sq he hw hz]
    simp only [TailPolynomial.x2,↓reduceIte,map_sub,map_add,map_mul,
      map_pow,aeval_C,TailPolynomial.S7_eval,eq_ratCast]
    push_cast
    linarith

theorem endpoint_distance_lower (i : Fin 3) (last : Bool) {z : ℝ}
    (hz : z∈Icc 0 frameCap) :
    aeval z (TailPolynomial.distance i last)≤
      Real.pi-z+(3/2)*kappa+2*aeval z (TailPolynomial.weight i)+(TailPolynomial.e i:ℝ)/2+
        (TailPolynomial.m i:ℝ)+
        (if last then kappa+(TailPolynomial.e i:ℝ)*Real.cos z
          else kappa*Real.cos z+(TailPolynomial.e i:ℝ))-pathThreshold := by
  have hc := cos_lower_six hz.1
  have hk := mul_le_mul_of_nonneg_left hc (show 0≤kappa by norm_num [kappa])
  have he := mul_le_mul_of_nonneg_left hc (TailPolynomial.chart_positive i).le
  have hp := Arithmetic.pi_hand_enclosure.1.le
  cases last <;>
    simp only [TailPolynomial.distance,TailPolynomial.cosinePart,
      Bool.false_eq_true,↓reduceIte,map_add,map_sub,map_mul,
      aeval_C,aeval_X,TailPolynomial.C6_eval,eq_ratCast] <;>
    push_cast <;> dsimp [kappa,pathThreshold] at hk ⊢ <;> linarith

/-- The actual two-circle endpoint scalar, for every intrinsic chart,
both error endpoints and the full affine TD multiplier family. -/
theorem affine_tail_endpoint (i : Fin 3) (last : Bool) {z : ℝ}
    (hz : z∈Icc 0 frameCap) :
    pathThreshold<tailEndpoint last (TailPolynomial.e i:ℝ) (TailPolynomial.m i:ℝ)
      (aeval z (TailPolynomial.weight i)) z := by
  let c : ℝ := aeval z (TailPolynomial.weight i)
  let P1 : ℝ := aeval z (TailPolynomial.p1 i last)
  let P2 : ℝ := aeval z (TailPolynomial.p2 i last)
  let X1 : ℝ := aeval z (TailPolynomial.x1 i last)
  let X2 : ℝ := aeval z (TailPolynomial.x2 i last)
  let L : ℝ := aeval z (TailPolynomial.distance i last)
  have hP := TailPolynomial.envelopes_positive i last hz
  have hcert : 0<2*P1*P2*L-(1979/1000)*(P2*(X1+P1^2)+P1*(X2+P2^2)) := by
    have hh := TailPolynomial.positive i last hz
    simpa [TailPolynomial.certificate,P1,P2,X1,X2,L] using hh
  have hN := two_norm_envelope
    (N1 := tailNorm kappa c (if last then 0 else z))
    (N2 := tailNorm (TailPolynomial.e i:ℝ) c (if last then z else 0))
    (X1 := X1) (X2 := X2) (P1 := P1) (P2 := P2) (L := L)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (by dsimp [P1]; linarith [hP.1]) (by dsimp [P2]; linarith [hP.2])
    (first_square_upper i last hz) (second_square_upper i last hz) hcert
  have hd := endpoint_distance_lower i last hz
  dsimp [L,c] at hN
  dsimp [tailEndpoint]
  linarith

end SquaresInCircles.Eight.TableFree.GlobalBT

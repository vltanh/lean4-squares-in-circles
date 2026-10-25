module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeABT3LongPolynomial
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeALongEEndpoints
public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveBT3Source

/-!
# Radical transfer for all twelve BT3 longer-E endpoints

Uncompiled Sections 11--12. The nonradical charge and gain bounds
are the previously proved ones. The three possible negative norms
have the fixed H/G/B coefficients, while only D's zero-angle norm
uses the upper bound on the actual positive rotating coefficient.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeABT3.LongE
open Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PairNormCalculus
open NegativeA.LongE (Region)
open TensorWholeIntervalPolynomial TwoVariablePolynomial

abbrev gain := NegativeA.LongE.gain

def scalar (k l c z e s : ℝ) (i : Fin 3) : ℝ :=
  PositiveBT3.Analytic.fullBaseline k l c z+l*gain s+
    TwoPositive.ASupport.charge e+
      NonnegativeTotals.Analytic.negative k l c (z+e-s) i

namespace Analytic

def endpoint (r : Region) (i : Fin 3) (x y : ℝ) : ℝ :=
  scalar (Explicit.k r x y) (Explicit.l r x y) (Explicit.m r x y)
    (Explicit.z r x y) (Explicit.e r x y) (Explicit.s r x y) i
def pAt (r : Region) (x y : ℝ) : Fin 4 → ℝ :=
  ![Explicit.k r x y,Explicit.k r x y,Explicit.l r x y,1]
def qAt (r : Region) (x y : ℝ) : Fin 4 → ℝ :=
  ![1,Explicit.l r x y,Explicit.m r x y,PositiveBT3.tilted (Explicit.m r x y) (Explicit.z r x y)]
def largeCoefficient (r : Region) (x y : ℝ) : Fin 3 → ℝ :=
  ![1,Explicit.l r x y,max (Explicit.l r x y) (Explicit.m r x y)]
def normAt (r : Region) (i : Fin 3) (j : Fin 4) (x y : ℝ) : ℝ :=
  pairNorm (pAt r x y j) (qAt r x y j) (if j.val=i.val then -Explicit.delta r x y else 0)
def nonradicalBase (r : Region) (x y : ℝ) : ℝ :=
  2*Explicit.k r x y+3*Explicit.l r x y+3+
    Explicit.m r x y*(1+2*Real.cos (Explicit.z r x y)+
      ((3/2)*PositiveTD.eta+1/2-PositiveTD.sigma)*Real.sin (Explicit.z r x y))+
      TwoPositive.ASupport.charge (Explicit.e r x y)+Explicit.l r x y*gain (Explicit.s r x y)
def nonradical (r : Region) (i : Fin 3) (x y : ℝ) : ℝ :=
  nonradicalBase r x y+largeCoefficient r x y i*(Real.cos (Explicit.delta r x y)-1)

theorem endpoint_identity (r : Region) (i : Fin 3) {x y : ℝ}
    (hd : Explicit.Domain r x y) :
    endpoint r i x y=nonradical r i x y-
      R*(normAt r i 0 x y+normAt r i 1 x y+normAt r i 2 x y+normAt r i 3 x y) := by
  have hz := (Explicit.domains hd).1
  unfold endpoint scalar
  rw [PositiveBT3.Analytic.fullBaseline_norms,NonnegativeTotals.Analytic.negative_identity,
    edgeWidth_positive_formula hz]
  fin_cases i <;>
    simp (config := {decide := true}) only [nonradical,nonradicalBase,largeCoefficient,normAt,pAt,
      qAt,Fin.reduceFinMk,Matrix.cons_val,Fin.isValue,↓reduceIte,PositiveBT3.tilted,
      Explicit.delta,NegativeA.LongE.Explicit.delta] <;> ring

theorem coefficient_data (r : Region) {x y : ℝ} (hd : Explicit.Domain r x y) :
    NonnegativeTotals.Explicit.BaseBounds (Explicit.k r x y) (Explicit.l r x y) (Explicit.m r x y) :=
  NonnegativeTotals.Explicit.base_bounds (Explicit.baseRegion r) (Explicit.base_domain hd)

theorem rotation_data (r : Region) {x y : ℝ} (hd : Explicit.Domain r x y) :
    0<PositiveBT3.tilted (Explicit.m r x y) (Explicit.z r x y) ∧
    PositiveBT3.tilted (Explicit.m r x y) (Explicit.z r x y)≤
      evaluate x y (Certificate.rotation r) := by
  have hh := NegativeA.LongE.Analytic.m_data r hd
  exact ⟨hh.1,hh.2.1⟩

theorem qB_envelope (r : Region) {x y : ℝ} (hd : Explicit.Domain r x y) :
    max (Explicit.l r x y) (Explicit.m r x y)≤evaluate x y (Certificate.qB r) := by
  have hh := PositiveBT3.Analytic.largeCoefficient_upper
    (Explicit.baseRegion r) 2 (Explicit.base_domain hd)
  cases r <;>
    simpa [PositiveBT3.Analytic.largeCoefficient,PositiveBT3.LargeCertificate.qB,
      PositiveBT3.LargeCertificate.m,Certificate.qB,Explicit.baseRegion,Explicit.baseY,
      Explicit.m,Explicit.l,NegativeA.LongE.Explicit.baseRegion,NegativeA.LongE.Explicit.baseY,
      NegativeA.LongE.Explicit.c,NegativeA.LongE.Explicit.l,
      NonnegativeTotals.Certificate.qStar] using hh

theorem E_charge (r : Region) {x y : ℝ} (hd : Explicit.Domain r x y) :
    evaluate x y (Certificate.jE r)≤TwoPositive.ASupport.charge (Explicit.e r x y) :=
  NegativeA.LongE.Analytic.E_charge r hd

theorem nonradicalBase_lower (r : Region) {x y : ℝ} (hd : Explicit.Domain r x y) :
    evaluate x y (Certificate.ABase r)≤nonradicalBase r x y :=
  NegativeA.LongE.Analytic.nonradicalBase_lower r hd

theorem largeCoefficient_bounds (r : Region) (i : Fin 3) {x y : ℝ}
    (hd : Explicit.Domain r x y) : 0≤largeCoefficient r x y i ∧
      largeCoefficient r x y i≤evaluate x y (![1,Certificate.l r,Certificate.qB r] i) := by
  have hb := coefficient_data r hd
  fin_cases i
  · simp [largeCoefficient]
  · simpa [largeCoefficient] using And.intro hb.l_positive.le (le_refl (Explicit.l r x y))
  · exact ⟨hb.l_positive.le.trans (le_max_left _ _),qB_envelope r hd⟩

theorem nonradical_lower (r : Region) (i : Fin 3) {x y : ℝ} (hd : Explicit.Domain r x y) :
    evaluate x y (Certificate.A r i)≤nonradical r i x y := by
  have hδ := (Explicit.domains hd).2.2.2.2
  have ht := PositiveTD.Certificate.taylor_bounds hδ
  have hC : aeval (Explicit.delta r x y) PositiveTD.Certificate.C10-1≤0 := by
    linarith [ht.2.2.2.2.1,Real.cos_le_one (Explicit.delta r x y)]
  have h1 := mul_le_mul_of_nonpos_right (largeCoefficient_bounds r i hd).2 hC
  have h2 := mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2.2.2.2.1 1)
    (largeCoefficient_bounds r i hd).1
  have hb := nonradicalBase_lower r hd
  simp only [Certificate.A,map_add,map_mul,map_sub,map_one,evaluate_lift,Certificate.evaluate_delta]
  dsimp [nonradical]
  linarith

theorem norm_square_upper (r : Region) (i : Fin 3) (j : Fin 4) {x y : ℝ}
    (hd : Explicit.Domain r x y) : (normAt r i j x y)^2≤evaluate x y (Certificate.P r i j) := by
  have hb := coefficient_data r hd
  have hk : 0<Explicit.k r x y := by linarith [hb.k_lower]
  have hc := rotation_data r hd
  have hδ := (Explicit.domains hd).2.2.2.2
  have n0 := NonnegativeTotals.Analytic.norm_negative_polynomial hk (by norm_num : (0:ℝ)<1) hδ
  have n1 := NonnegativeTotals.Analytic.norm_negative_polynomial hk hb.l_positive hδ
  have n2 := NonnegativeTotals.Analytic.norm_negative_polynomial hb.l_positive hb.c_positive hδ
  have z0 := NonnegativeTotals.Analytic.norm_zero_square (Explicit.k r x y) 1
  have z1 := NonnegativeTotals.Analytic.norm_zero_square (Explicit.k r x y) (Explicit.l r x y)
  have z2 := NonnegativeTotals.Analytic.norm_zero_square (Explicit.l r x y) (Explicit.m r x y)
  have z3 := NonnegativeTotals.Analytic.norm_zero_coefficient_upper (p:=1) hc.1.le hc.2
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) only [normAt,pAt,qAt,Certificate.P,Certificate.baseNorm,
      Fin.reduceFinMk,Matrix.cons_val,↓reduceIte,map_sub,map_add,map_mul,map_pow,
      map_one,sub_zero,evaluate_scalar,evaluate_lift,Certificate.evaluate_k,
      Certificate.evaluate_l,Certificate.evaluate_m,Certificate.evaluate_delta,Rat.cast_ofNat] <;>
    linarith

theorem endpoint_positive (r : Region) (i : Fin 3) {x y : ℝ}
    (hd : Explicit.Domain r x y) : 0<endpoint r i x y := by
  have hm (j : Fin 4) := Certificate.mass_positive r i j hd
  have hn (j : Fin 4) : 0≤normAt r i j x y := Real.sqrt_nonneg _
  have hs (j : Fin 4) := norm_square_upper r i j hd
  have hA := nonradical_lower r i hd
  have hpoly := Certificate.numerator_positive r i hd
  have hR : (PositiveTD.Certificate.Rbar:ℝ)=(NonnegativeTotals.Certificate.Rbar:ℝ) := by
    norm_num [PositiveTD.Certificate.Rbar,NonnegativeTotals.Certificate.Rbar]
  have hP : 0<2*evaluate x y (Certificate.A r i)*
      evaluate x y (Certificate.mass r i 0)*evaluate x y (Certificate.mass r i 1)*
      evaluate x y (Certificate.mass r i 2)*evaluate x y (Certificate.mass r i 3)-
        (PositiveTD.Certificate.Rbar:ℝ)*
          ((evaluate x y (Certificate.P r i 0)+(evaluate x y (Certificate.mass r i 0))^2)*
              evaluate x y (Certificate.mass r i 1)*evaluate x y (Certificate.mass r i 2)*
              evaluate x y (Certificate.mass r i 3)+
            (evaluate x y (Certificate.P r i 1)+(evaluate x y (Certificate.mass r i 1))^2)*
              evaluate x y (Certificate.mass r i 0)*evaluate x y (Certificate.mass r i 2)*
              evaluate x y (Certificate.mass r i 3)+
            (evaluate x y (Certificate.P r i 2)+(evaluate x y (Certificate.mass r i 2))^2)*
              evaluate x y (Certificate.mass r i 0)*evaluate x y (Certificate.mass r i 1)*
              evaluate x y (Certificate.mass r i 3)+
            (evaluate x y (Certificate.P r i 3)+(evaluate x y (Certificate.mass r i 3))^2)*
              evaluate x y (Certificate.mass r i 0)*evaluate x y (Certificate.mass r i 1)*
              evaluate x y (Certificate.mass r i 2)) := by
    rw [hR]
    simpa only [Certificate.numerator,map_sub,map_add,map_mul,map_pow,evaluate_scalar,
      Rat.cast_ofNat] using hpoly
  have hh := PositiveTD.Certificate.four_norm_transfer
    (hm 0) (hm 1) (hm 2) (hm 3) (hn 0) (hn 1) (hn 2) (hn 3)
    (hs 0) (hs 1) (hs 2) (hs 3) hA hP
  rwa [endpoint_identity r i hd]

end Analytic
end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeABT3.LongE

module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeALongEGain

/-!
# The twelve longer-E endpoint scalars

Uncompiled transcription of equations (23)--(35). The B norm is enlarged
only after its actual coefficient exceeds l sin(delta). The same four
positive masses then transfer each exact numerator to its radical scalar.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeA.LongE
open Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PairNormCalculus
open TensorWholeIntervalPolynomial TwoVariablePolynomial

def scalar (k l c z e s : ℝ) (i : Fin 3) : ℝ :=
  NonnegativeTotals.Analytic.fullBaseline k l c z+l*gain s+
    TwoPositive.ASupport.charge e+
      NonnegativeTotals.Analytic.negative k l (PositiveTD.tilted c z) (z+e-s) i

namespace Analytic

def endpoint (r : Region) (i : Fin 3) (x y : ℝ) : ℝ :=
  scalar (Explicit.k r x y) (Explicit.l r x y) (Explicit.c r x y)
    (Explicit.z r x y) (Explicit.e r x y) (Explicit.s r x y) i
def pAt (r : Region) (x y : ℝ) : Fin 4 → ℝ :=
  ![Explicit.k r x y,Explicit.k r x y,Explicit.l r x y,Explicit.c r x y]
def qAt (r : Region) (x y : ℝ) : Fin 4 → ℝ :=
  ![1,Explicit.l r x y,PositiveTD.tilted (Explicit.c r x y) (Explicit.z r x y),1]
def largeCoefficient (r : Region) (x y : ℝ) : Fin 3 → ℝ :=
  ![1,Explicit.l r x y,max (Explicit.l r x y) (PositiveTD.tilted (Explicit.c r x y) (Explicit.z r x y))]
def normAt (r : Region) (i : Fin 3) (j : Fin 4) (x y : ℝ) : ℝ :=
  pairNorm (pAt r x y j) (qAt r x y j) (if j.val=i.val then -Explicit.delta r x y else 0)
def nonradicalBase (r : Region) (x y : ℝ) : ℝ :=
  2*Explicit.k r x y+3*Explicit.l r x y+3+
    Explicit.c r x y*(1+2*Real.cos (Explicit.z r x y)+
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
  rw [NonnegativeTotals.Analytic.fullBaseline_norms,NonnegativeTotals.Analytic.negative_identity,
    edgeWidth_positive_formula hz]
  fin_cases i <;>
    simp only [nonradical,nonradicalBase,largeCoefficient,normAt,pAt,qAt,
      Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.reduceFinMk,ite_true,ite_false,
      PositiveTD.tilted,Explicit.delta] <;> ring

theorem coefficient_data (r : Region) {x y : ℝ} (hd : Explicit.Domain r x y) :
    NonnegativeTotals.Explicit.BaseBounds (Explicit.k r x y) (Explicit.l r x y) (Explicit.c r x y) :=
  NonnegativeTotals.Explicit.base_bounds (Explicit.baseRegion r) (Explicit.base_domain hd)

theorem m_data (r : Region) {x y : ℝ} (hd : Explicit.Domain r x y) :
    0<PositiveTD.tilted (Explicit.c r x y) (Explicit.z r x y) ∧
    PositiveTD.tilted (Explicit.c r x y) (Explicit.z r x y)≤evaluate x y (Certificate.M r) ∧
    (2/3)*Explicit.l r x y<PositiveTD.tilted (Explicit.c r x y) (Explicit.z r x y) := by
  have hh := NonnegativeTotals.Analytic.mAt_data (Explicit.baseRegion r) .atT (Explicit.base_domain hd)
  simpa [NonnegativeTotals.Analytic.mAt,NonnegativeTotals.Analytic.zAt,
    NonnegativeTotals.Analytic.polyM,NonnegativeTotals.Certificate.M,
    Certificate.M,Explicit.z,Explicit.c,Explicit.l] using hh

theorem qB_envelope (r : Region) {x y : ℝ} (hd : Explicit.Domain r x y) :
    max (Explicit.l r x y) (PositiveTD.tilted (Explicit.c r x y) (Explicit.z r x y))≤
      evaluate x y (Certificate.qB r) := by
  have hh := NonnegativeTotals.Analytic.qB_envelope (Explicit.baseRegion r) .atT (Explicit.base_domain hd)
  cases r <;>
    simpa [Certificate.qB,Certificate.M,Explicit.baseRegion,Explicit.baseY,
      Explicit.z,Explicit.c,Explicit.l,NonnegativeTotals.Certificate.qB,
      NonnegativeTotals.Certificate.M,NonnegativeTotals.Certificate.qStar,
      NonnegativeTotals.Analytic.mAt,NonnegativeTotals.Analytic.zAt] using hh

theorem E_charge (r : Region) {x y : ℝ} (hd : Explicit.Domain r x y) :
    evaluate x y (Certificate.jE r)≤TwoPositive.ASupport.charge (Explicit.e r x y) := by
  have he := (Explicit.domains hd).2.1
  cases r with
  | TE =>
    have hh := NonnegativeTotals.Charges.triangle_E_charge
      (show Explicit.e .TE x y∈Icc 0 (8/15:ℝ) from
        ⟨he.1,by dsimp [Explicit.e,Explicit.baseRegion,Explicit.baseY,NonnegativeTotals.Explicit.e];
          linarith [hd.1,hd.2.2]⟩)
    simpa only [Certificate.jE,map_sub,map_mul,map_pow,evaluate_scalar,
      NonnegativeTotals.Charges.evaluate_J,Certificate.evaluate_e] using hh
  | TC =>
    have hh := NonnegativeTotals.Charges.triangle_E_charge
      (show Explicit.e .TC x y∈Icc 0 (8/15:ℝ) from
        ⟨he.1,by dsimp [Explicit.e,Explicit.baseRegion,Explicit.baseY,NonnegativeTotals.Explicit.e];
          linarith [hd.1,hd.2.2]⟩)
    simpa only [Certificate.jE,map_sub,map_mul,map_pow,evaluate_scalar,
      NonnegativeTotals.Charges.evaluate_J,Certificate.evaluate_e] using hh
  | RE =>
    have hcut : Explicit.e .RE x y≤TwoPositive.ASupport.alpha := by
      dsimp [Explicit.e,Explicit.baseRegion,Explicit.baseY,NonnegativeTotals.Explicit.e]
      linarith [hd.2.2,TwoPositive.ASupport.alpha_bounds.1]
    rw [TwoPositive.ASupport.charge,if_pos hcut]
    simpa [Certificate.jE,NonnegativeTotals.Charges.evaluate_J] using
      NonnegativeTotals.Charges.J_lower_axial he
  | RC =>
    simpa only [Certificate.jE,map_sub,map_mul,map_pow,evaluate_scalar,
      NonnegativeTotals.Charges.evaluate_J,Certificate.evaluate_e] using
        NonnegativeTotals.Charges.rectangle_E_charge he

theorem nonradicalBase_lower (r : Region) {x y : ℝ} (hd : Explicit.Domain r x y) :
    evaluate x y (Certificate.ABase r)≤nonradicalBase r x y := by
  have hb := coefficient_data r hd
  have hz := (Explicit.domains hd).1
  have ht := PositiveTD.Certificate.taylor_bounds hz
  have hE := E_charge r hd
  have hg := mul_le_mul_of_nonneg_left (polynomial_gain_lower (Explicit.domains hd).2.2.1) hb.l_positive.le
  have hcoeff : (3/2)*(293/1000:ℝ)+1/2-(NonnegativeTotals.Certificate.sigmabar:ℝ)≤0 := by
    norm_num [NonnegativeTotals.Certificate.sigmabar]
  have hsin := mul_le_mul_of_nonpos_left ht.2.2.1 hcoeff
  have hσ := mul_le_mul_of_nonneg_right NonnegativeTotals.Charges.sigma_upper (transport_trig hz).2.2.1
  have hinner : 1+2*aeval (Explicit.z r x y) PositiveTD.Certificate.C10+
      ((3/2)*(293/1000)+1/2-(NonnegativeTotals.Certificate.sigmabar:ℝ))*
        aeval (Explicit.z r x y) PositiveTD.Certificate.S9≤
      1+2*Real.cos (Explicit.z r x y)+
        ((3/2)*PositiveTD.eta+1/2-PositiveTD.sigma)*Real.sin (Explicit.z r x y) := by
    dsimp [PositiveTD.eta]
    linarith [ht.2.2.2.2.1]
  have hprod := mul_le_mul_of_nonneg_left hinner hb.c_positive.le
  simp only [Certificate.ABase,Certificate.gain,map_add,map_mul,map_sub,map_one,
    evaluate_scalar,evaluate_lift,Certificate.evaluate_k,Certificate.evaluate_l,
    Certificate.evaluate_c,Certificate.evaluate_z,Certificate.evaluate_s]
  push_cast
  dsimp [nonradicalBase]
  linarith

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
  have hm := m_data r hd
  have hδ := (Explicit.domains hd).2.2.2.2
  have hcharge : Explicit.l r x y*Real.sin (Explicit.delta r x y)≤
      PositiveTD.tilted (Explicit.c r x y) (Explicit.z r x y) := by
    have hh := mul_lt_mul_of_pos_left (transport_trig hδ).2.2.2.1 hb.l_positive
    linarith [hm.2.2,hb.l_positive]
  fin_cases j
  · by_cases hi : (0:ℕ)=i.val
    · simpa [normAt,pAt,qAt,Certificate.P,Certificate.baseNorm,hi] using
        NonnegativeTotals.Analytic.norm_negative_polynomial hk (by norm_num : (0:ℝ)<1) hδ
    · simp [normAt,pAt,qAt,Certificate.P,Certificate.baseNorm,hi,
        NonnegativeTotals.Analytic.norm_zero_square,add_comm]
  · by_cases hi : (1:ℕ)=i.val
    · simpa [normAt,pAt,qAt,Certificate.P,Certificate.baseNorm,hi] using
        NonnegativeTotals.Analytic.norm_negative_polynomial hk hb.l_positive hδ
    · simp [normAt,pAt,qAt,Certificate.P,Certificate.baseNorm,hi,
        NonnegativeTotals.Analytic.norm_zero_square]
  · by_cases hi : (2:ℕ)=i.val
    · simpa [normAt,pAt,qAt,Certificate.P,Certificate.baseNorm,hi] using
        NonnegativeTotals.Analytic.norm_negative_coefficient_upper hb.l_positive hm.1 hm.2.1 hδ hcharge
    · simpa [normAt,pAt,qAt,Certificate.P,Certificate.baseNorm,hi] using
        NonnegativeTotals.Analytic.norm_zero_coefficient_upper (p:=Explicit.l r x y) hm.1.le hm.2.1
  · have hi : ¬(3:ℕ)=i.val := by omega
    simp [normAt,pAt,qAt,Certificate.P,Certificate.baseNorm,hi,
      NonnegativeTotals.Analytic.norm_zero_square,add_comm]

theorem endpoint_positive (r : Region) (i : Fin 3) {x y : ℝ}
    (hd : Explicit.Domain r x y) : 0<endpoint r i x y := by
  have hm (j : Fin 4) := Certificate.mass_positive r i j hd
  have hn (j : Fin 4) : 0≤normAt r i j x y := Real.sqrt_nonneg _
  have hs (j : Fin 4) := norm_square_upper r i j hd
  have hA := nonradical_lower r i hd
  have hpoly := Certificate.numerator_positive r i hd
  have hP : 0<2*evaluate x y (Certificate.A r i)*
      evaluate x y (Certificate.mass r i 0)*evaluate x y (Certificate.mass r i 1)*
      evaluate x y (Certificate.mass r i 2)*evaluate x y (Certificate.mass r i 3)-
        (PositiveTD.Certificate.Rbar:ℝ)*
          ((evaluate x y (Certificate.P r i 0)+(evaluate x y (Certificate.mass r i 0))^2)*
              evaluate x y (Certificate.mass r i 1)*evaluate x y (Certificate.mass r i 2)*evaluate x y (Certificate.mass r i 3)+
            (evaluate x y (Certificate.P r i 1)+(evaluate x y (Certificate.mass r i 1))^2)*
              evaluate x y (Certificate.mass r i 0)*evaluate x y (Certificate.mass r i 2)*evaluate x y (Certificate.mass r i 3)+
            (evaluate x y (Certificate.P r i 2)+(evaluate x y (Certificate.mass r i 2))^2)*
              evaluate x y (Certificate.mass r i 0)*evaluate x y (Certificate.mass r i 1)*evaluate x y (Certificate.mass r i 3)+
            (evaluate x y (Certificate.P r i 3)+(evaluate x y (Certificate.mass r i 3))^2)*
              evaluate x y (Certificate.mass r i 0)*evaluate x y (Certificate.mass r i 1)*evaluate x y (Certificate.mass r i 2)) := by
    simpa only [Certificate.numerator,map_sub,map_add,map_mul,map_pow,evaluate_scalar,
      NonnegativeTotals.Certificate.Rbar,PositiveTD.Certificate.Rbar,Rat.cast_ofNat,Rat.cast_div] using hpoly
  have hh := PositiveTD.Certificate.four_norm_transfer
    (hm 0) (hm 1) (hm 2) (hm 3) (hn 0) (hn 1) (hn 2) (hn 3)
    (hs 0) (hs 1) (hs 2) (hs 3) hA hP
  rwa [endpoint_identity r i hd]

end Analytic
end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeA.LongE

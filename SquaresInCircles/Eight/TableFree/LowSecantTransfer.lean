module

public import SquaresInCircles.Eight.TableFree.LowSecantPolynomials
public import SquaresInCircles.Eight.TableFree.PositiveSecantGain
public import SquaresInCircles.Eight.TableFree.OrdinaryLongSecantGrowth

/-!
# Whole-interval low-coefficient comparison with the full secant bound

Uncompiled source. The two already drafted polynomial reserves are
transferred to the original negative-angle radicals. Their positive
reserve also pays for the common factor 1.0345, so the same gamma is
valid in both coefficient families. Separate concavity then covers
every intermediate larger coefficient, without a coefficient table.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.TableFree.LowSecantTransfer
open PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryNegativeEnvelope
open PositiveStressCoefficients NegativeEOneAngle OrdinaryLongSecantGrowth

abbrev p₀ : ℝ := 1263/2500

theorem trigonometric_reserve (i : LowSecantPolynomials.Case) {u : ℝ}
    (hu : u∈Ioc 0 frameCap) :
    (35643/50000)*u-(1199/5000)*u^2+(LowSecantPolynomials.reserve i:ℝ)*u<
      (LowSecantPolynomials.q i:ℝ)*(Real.cos u-1)+
        (LowSecantPolynomials.a i:ℝ)*Real.sin u+
        (LowSecantPolynomials.b i:ℝ)*(Real.sin u)^2 := by
  have hpoly := mul_lt_mul_of_pos_right
    (LowSecantPolynomials.polynomial_positive i (Ioc_subset_Icc_self hu)) hu.1
  have hid := congrArg (fun p : ℚ[X] => Polynomial.aeval u p)
    (LowSecantPolynomials.zero_identity i)
  simp only [map_mul,Polynomial.aeval_X] at hid
  have hs0 := SecantGainPolynomial.sine11_nonneg (Ioc_subset_Icc_self hu)
  have hs := HighOrderTaylor.S11_le_sin hu.1.le
  have hc := Arithmetic.cos10_le_cos hu.1.le
  have hs2 := pow_le_pow_left₀ hs0 hs 2
  have hq0 : (0:ℝ)≤(LowSecantPolynomials.q i:ℝ) := by cases i <;> norm_num [LowSecantPolynomials.q]
  have ha0 : (0:ℝ)≤(LowSecantPolynomials.a i:ℝ) := by cases i <;> norm_num [LowSecantPolynomials.a]
  have hb0 : (0:ℝ)≤(LowSecantPolynomials.b i:ℝ) := by cases i <;> norm_num [LowSecantPolynomials.b]
  have hcos := mul_le_mul_of_nonneg_left hc hq0
  have hsin := mul_le_mul_of_nonneg_left hs ha0
  have hsine := mul_le_mul_of_nonneg_left hs2 hb0
  simp only [LowSecantPolynomials.numerator,map_add,map_sub,map_mul,map_pow,map_one,
    Polynomial.aeval_C,Polynomial.aeval_X,VaryingBCertificate.C10_eval,
    VaryingBCertificate.S11_eval] at hid
  norm_num at hid
  nlinarith

theorem radical_coefficients (i : LowSecantPolynomials.Case) :
    (LowSecantPolynomials.a i:ℝ)<
      Real.sqrt qCap*p₀*(LowSecantPolynomials.q i:ℝ)/
        Real.sqrt (p₀^2+(LowSecantPolynomials.q i:ℝ)^2) ∧
    (LowSecantPolynomials.b i:ℝ)<
      Real.sqrt qCap*p₀^2*(LowSecantPolynomials.q i:ℝ)^2/
        (2*(Real.sqrt (p₀^2+(LowSecantPolynomials.q i:ℝ)^2))^3) := by
  let q : ℝ := LowSecantPolynomials.q i
  let v := Real.sqrt (p₀^2+q^2)
  have hq : 0<q := by cases i <;> norm_num [q,LowSecantPolynomials.q]
  have hv : 0<v := Real.sqrt_pos.mpr (by dsimp [p₀]; positivity)
  have hv2 : v^2=p₀^2+q^2 := Real.sq_sqrt (by positivity)
  have hv6 : (v^3)^2=(p₀^2+q^2)^3 := by
    calc (v^3)^2=(v^2)^3 := by ring
         _=_ := by rw [hv2]
  have hR0 : 0<Real.sqrt qCap := Real.sqrt_pos.mpr (by norm_num [qCap])
  have hR2 := Real.sq_sqrt (show 0≤qCap by norm_num [qCap])
  have hA0 : (0:ℝ)<(LowSecantPolynomials.a i:ℝ) := by cases i <;> norm_num [LowSecantPolynomials.a]
  have hB0 : (0:ℝ)<(LowSecantPolynomials.b i:ℝ) := by cases i <;> norm_num [LowSecantPolynomials.b]
  have hsq := LowSecantPolynomials.coefficient_squares i
  have hA : (LowSecantPolynomials.a i:ℝ)*v<Real.sqrt qCap*p₀*q := by
    have hleft : ((LowSecantPolynomials.a i:ℝ)*v)^2=
        (LowSecantPolynomials.a i:ℝ)^2*(p₀^2+q^2) := by rw [mul_pow,hv2]
    have hright : (Real.sqrt qCap*p₀*q)^2=qCap*p₀^2*q^2 := by
      simp only [mul_pow,hR2]
    have hr0 : 0<Real.sqrt qCap*p₀*q := by positivity
    have hs := hsq.1
    change (LowSecantPolynomials.a i:ℝ)^2*(p₀^2+q^2)<qCap*p₀^2*q^2 at hs
    nlinarith
  have hB : (LowSecantPolynomials.b i:ℝ)*(2*v^3)<Real.sqrt qCap*p₀^2*q^2 := by
    have hleft : ((LowSecantPolynomials.b i:ℝ)*(2*v^3))^2=
        4*(LowSecantPolynomials.b i:ℝ)^2*(p₀^2+q^2)^3 := by
      rw [mul_pow,mul_pow,hv6]
      ring
    have hright : (Real.sqrt qCap*p₀^2*q^2)^2=qCap*p₀^4*q^4 := by
      simp only [mul_pow,hR2]
      ring
    have hr0 : 0<Real.sqrt qCap*p₀^2*q^2 := by positivity
    have hs := hsq.2
    change 4*(LowSecantPolynomials.b i:ℝ)^2*(p₀^2+q^2)^3<qCap*p₀^4*q^4 at hs
    nlinarith
  exact ⟨(lt_div_iff₀ hv).2 hA,(lt_div_iff₀ (by positivity : 0<2*v^3)).2 hB⟩

theorem quadratic_lower (i : LowSecantPolynomials.Case) {u : ℝ}
    (hu : u∈Icc 0 frameCap) :
    (LowSecantPolynomials.q i:ℝ)*(Real.cos u-1)+
      (LowSecantPolynomials.a i:ℝ)*Real.sin u+
      (LowSecantPolynomials.b i:ℝ)*(Real.sin u)^2≤
        V (Real.sqrt qCap) p₀ (LowSecantPolynomials.q i:ℝ) u := by
  let q : ℝ := LowSecantPolynomials.q i
  let v := Real.sqrt (p₀^2+q^2)
  have hq : 0<q := by cases i <;> norm_num [q,LowSecantPolynomials.q]
  have hv : 0<v := Real.sqrt_pos.mpr (by dsimp [p₀]; positivity)
  have hv2 : v^2=p₀^2+q^2 := Real.sq_sqrt (by positivity)
  have hs0 := (transport_trig hu).2.2.1
  have hprod0 : 0≤2*p₀*q*Real.sin u := by positivity
  have hprodU : 2*p₀*q*Real.sin u≤v^2 := by
    have hh := mul_le_mul_of_nonneg_left (Real.sin_le_one u)
      (show 0≤2*p₀*q by positivity)
    nlinarith [sq_nonneg (p₀-q)]
  have hroot := PositiveSecantGain.sqrt_sub_upper hv hprod0 hprodU
  have hroot' : Real.sqrt (v^2-2*p₀*q*Real.sin u)≤
      v-(p₀*q/v)*Real.sin u-(p₀^2*q^2/(2*v^3))*(Real.sin u)^2 := by
    convert hroot using 1
    field_simp [hv.ne']
    ring
  have hnorm : pairNorm p₀ q (-u)=Real.sqrt (v^2-2*p₀*q*Real.sin u) := by
    simp only [pairNorm,Real.sin_neg,hv2]
    congr 1
    ring
  have hzero : pairNorm p₀ q 0=v := by simp [pairNorm,v]
  have hrad := mul_le_mul_of_nonneg_left hroot' (Real.sqrt_nonneg qCap)
  have hcoef : (LowSecantPolynomials.a i:ℝ)<Real.sqrt qCap*p₀*q/v ∧
      (LowSecantPolynomials.b i:ℝ)<Real.sqrt qCap*p₀^2*q^2/(2*v^3) :=
    radical_coefficients i
  have hAs := mul_le_mul_of_nonneg_right hcoef.1.le hs0
  have hBs := mul_le_mul_of_nonneg_right hcoef.2.le (sq_nonneg (Real.sin u))
  show q*(Real.cos u-1)+(LowSecantPolynomials.a i:ℝ)*Real.sin u+
    (LowSecantPolynomials.b i:ℝ)*(Real.sin u)^2≤V (Real.sqrt qCap) p₀ q u
  rw [V,hnorm,hzero]
  linear_combination hrad+hAs+hBs

theorem endpoint_lower (i : LowSecantPolynomials.Case) {s u : ℝ}
    (hs : s∈Icc 0 frameCap) (hu : u∈Icc 0 (frameCap-s)) :
    gamma s*u≤V (Real.sqrt qCap) p₀ (LowSecantPolynomials.q i:ℝ) u := by
  by_cases hz : u=0
  · simp [hz]
  have hu0 : 0<u := lt_of_le_of_ne hu.1 (Ne.symm hz)
  have hu' : u∈Icc 0 frameCap := ⟨hu.1,by linarith [hu.2,hs.1]⟩
  have hpoly := trigonometric_reserve i ⟨hu0,hu'.2⟩
  have hquad := quadratic_lower i hu'
  have hsec := secant_chord hs
  have hgamma : gamma s≤(109/200)*(2069/2000)*(1+(11/25)*s) := by
    have hh := mul_le_mul_of_nonneg_left hsec
      (by norm_num : (0:ℝ)≤(109/200)*(2069/2000))
    simpa [gamma,div_eq_mul_inv,mul_assoc] using hh
  have hmul := mul_le_mul_of_nonneg_right hgamma hu.1
  have hsu := mul_nonneg hu.1 (show 0≤frameCap-s-u by linarith [hu.2])
  have hpay : (109/200)*(2069/2000)*(1+(11/25)*s)*u≤
      (35643/50000)*u-(1199/5000)*u^2+(LowSecantPolynomials.reserve i:ℝ)*u := by
    cases i <;> norm_num [LowSecantPolynomials.reserve,frameCap] at * <;> nlinarith
  exact (hmul.trans hpay).trans (hpoly.le.trans hquad)

theorem coefficient_interval {p q s u : ℝ} (hp : p₀≤p) (hq : q∈Icc k 1) (hpq : p≤q)
    (hs : s∈Icc 0 frameCap) (hu : u∈Icc 0 (frameCap-s)) :
    gamma s*u≤V (Real.sqrt qCap) p q u := by
  have hu' : u∈Icc 0 frameCap := ⟨hu.1,by linarith [hu.2,hs.1]⟩
  have hc := V_concave_larger (R := Real.sqrt qCap) (Real.sqrt_nonneg _)
    (show 0<p₀ by norm_num [p₀]) hu'
  have hmin := hc.min_le_of_mem_Icc
    (show k∈Icc p₀ (2*p₀) by norm_num [k,p₀])
    (show (1:ℝ)∈Icc p₀ (2*p₀) by norm_num [p₀]) hq
  have htilt := endpoint_lower .tilted hs hu
  have hunit := endpoint_lower .unit hs hu
  have hbase : gamma s*u≤V (Real.sqrt qCap) p₀ q u := by
    apply le_trans (le_min ?_ ?_) hmin
    · simpa [LowSecantPolynomials.q,k] using htilt
    · simpa [LowSecantPolynomials.q] using hunit
  have hq0 : 0<q := by norm_num [k] at hq; linarith
  have hq1 : k≤q := hq.1
  have hq2 : q≤1 := hq.2
  norm_num [k] at hq1
  have hmono := V_monotone_smaller (R := Real.sqrt qCap) (Real.sqrt_nonneg _) hq0 hu'
    (show p₀∈Icc (q/2) q from ⟨by norm_num [p₀]; linarith, by norm_num [p₀]; linarith⟩)
    (show p∈Icc (q/2) q from ⟨by norm_num [p₀] at hp; linarith [hq.2],hpq⟩) hp
  exact hbase.trans hmono

theorem canonical {s u : ℝ} (hs : s∈Icc 0 frameCap) (hu : u∈Icc 0 (frameCap-s)) :
    gamma s*u≤V (Real.sqrt qCap) k 1 u :=
  coefficient_interval (by norm_num [p₀,k]) (by norm_num [k]) (by norm_num [k]) hs hu

end SquaresInCircles.Eight.TableFree.LowSecantTransfer

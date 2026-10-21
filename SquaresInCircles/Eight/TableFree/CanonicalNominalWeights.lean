module

public import SquaresInCircles.Eight.TableFree.CanonicalNegativeCorrection
public import SquaresInCircles.Eight.TableFree.GeometricExistenceStress

/-!
# The continuous nominal family in the two-error identity

Uncompiled reconstruction.  The single nominal stress is expressed in
the original five-anchor completion used for the canonical negative
branch.  Its baseline is exactly the previously proved nominal gap.
All coefficient bounds below hold on the whole sine interval [0,3/10].
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.CanonicalNominal
open GeometricModel.FiveCorner CanonicalNegativeStress

def parameters (s : ℝ) : Parameters where
  a := Nominal.alpha s
  beta := Nominal.beta s
  delta := Nominal.delta s
  epsilon := Nominal.epsilon s
  omega := 1
  mu := Nominal.mass s

def atTilt (α : ℝ) : Parameters := parameters (Real.sin α)

theorem positive {s : ℝ} (hs : s∈Icc 0 (3/10:ℝ)) (hp : 0<s) :
    (parameters s).Positive := by
  obtain ⟨ha,hb,hd,he⟩ := Nominal.weights_pos hs
  exact ⟨ha.le,hb.le,hd.le,he.le,by norm_num,Nominal.mass_pos hs hp⟩

theorem KA_formula {s : ℝ} (hs : s∈Icc 0 (3/10:ℝ)) :
    KA (parameters s)=Nominal.alpha s*(41/24)*(1+13*s/60) := by
  have hd := Nominal.denominator_bounds hs
  dsimp [KA,parameters,Nominal.mass,Nominal.mA]
  field_simp [hd.1.ne']
  ring

theorem KB_formula {s : ℝ} (hs : s∈Icc 0 (3/10:ℝ)) :
    KB (parameters s)=Nominal.alpha s*Nominal.beta s*(41/24)*(1-9*s/50) := by
  have hd := Nominal.denominator_bounds hs
  dsimp [KB,parameters,Nominal.mass,Nominal.mB]
  field_simp [hd.2.1.ne']
  ring

theorem gamma_formula {s : ℝ} (hs : s∈Icc 0 (3/10:ℝ)) :
    (parameters s).beta^2/(2*(parameters s).mu 2)=
      Nominal.beta s^2*(31/24)*(1+9*s/25) := by
  have hd := Nominal.denominator_bounds hs
  dsimp [parameters,Nominal.mass,Nominal.mD]
  field_simp [hd.2.2.1.ne']
  ring

theorem KA_polynomial {s : ℝ} (hs : s∈Icc 0 (3/10:ℝ)) :
    KA (parameters s)=1+(843/800)*s+(13817/144000)*s^2-(533/28800)*s^3 := by
  rw [KA_formula hs]
  dsimp [Nominal.alpha]
  ring

theorem KB_polynomial {s : ℝ} (hs : s∈Icc 0 (3/10:ℝ)) :
    KB (parameters s)=1+(1457/2400)*s-(34849/80000)*s^2-
      (592807/7200000)*s^3+(11111/288000)*s^4-(41/16000)*s^5 := by
  rw [KB_formula hs]
  dsimp [Nominal.alpha,Nominal.beta]
  ring

theorem beta_bounds {s : ℝ} (hs : s∈Icc 0 (3/10:ℝ)) :
    Nominal.beta s∈Icc (97/100:ℝ) 1 := by
  have hs2 := pow_le_pow_left₀ hs.1 hs.2 2
  dsimp [Nominal.beta]
  constructor <;> nlinarith [hs.1,hs.2,sq_nonneg s]

theorem KA_bounds {s : ℝ} (hs : s∈Icc 0 (3/10:ℝ)) :
    KA (parameters s)∈Icc (1:ℝ) (4/3) := by
  have hs2 := pow_le_pow_left₀ hs.1 hs.2 2
  have hs3 := pow_nonneg hs.1 3
  have hb : 0≤843/800+(13817/144000)*s-(533/28800)*s^2 := by
    nlinarith [hs.1]
  have hp := mul_nonneg hs.1 hb
  rw [KA_polynomial hs]
  constructor <;> nlinarith [hs.2]

theorem KB_bounds {s : ℝ} (hs : s∈Icc 0 (3/10:ℝ)) :
    KB (parameters s)∈Icc (0:ℝ) (6/5) := by
  obtain ⟨ha,hb,_,_⟩ := Nominal.weights_pos hs
  have hd : 0<1-9*s/50 := (Nominal.denominator_bounds hs).2.1
  have hlow : 0≤KB (parameters s) := by
    rw [KB_formula hs]
    positivity
  have hs4 := pow_le_pow_left₀ hs.1 hs.2 4
  have hs3 := pow_nonneg hs.1 3
  have hs5 := pow_nonneg hs.1 5
  refine ⟨hlow,?_⟩
  rw [KB_polynomial hs]
  nlinarith [hs.2,sq_nonneg s]

theorem gamma_bounds {s : ℝ} (hs : s∈Icc 0 (3/10:ℝ)) :
    (parameters s).beta^2/(2*(parameters s).mu 2)∈Icc (0:ℝ) (3/2) := by
  have hs0 := hs.1
  have hb := beta_bounds hs
  have hb0 : 0≤Nominal.beta s := by linarith [hb.1]
  have hb2 : Nominal.beta s^2≤1 := by nlinarith [hb.1,hb.2]
  have hd : 0≤(31/24:ℝ)*(1+9*s/25) := by positivity
  have hm := mul_le_mul_of_nonneg_right hb2 hd
  rw [gamma_formula hs]
  constructor
  · positivity
  · nlinarith [hs.2]

theorem nominal_force_norm (α : ℝ) (i : Fin 5) :
    normSq (forces (atTilt α) α 0 α 0 i)=normSq (Nominal.forces α i) := by
  rw [Nominal.force_norm]
  fin_cases i <;> simp only [forces,atTilt,parameters,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_succ,normSq,Prod.fst_mk,Prod.snd_mk,
    Real.cos_zero,Real.sin_zero,mul_one,mul_zero,sub_zero,div_one]
  · nlinarith [Real.sin_sq_add_cos_sq α]
  · ring
  · ring
  · nlinarith [congrArg (fun x : ℝ => Nominal.epsilon (Real.sin α)^2*x)
      (Real.sin_sq_add_cos_sq α)]
  · ring

theorem nominal_corner_demand (α : ℝ) :
    demand (atTilt α) α 0 α 0+
      ∑i : Fin 5,((forces (atTilt α) α 0 α 0 i).1+
        (forces (atTilt α) α 0 α 0 i).2)/2=Nominal.demand α := by
  simp only [demand,forces,atTilt,parameters,Fin.sum_univ_succ,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_succ,
    Prod.fst_mk,Prod.snd_mk,Real.cos_zero,Real.sin_zero,Real.tan_zero]
  dsimp [Nominal.demand,spanDemand,W,NegativeCaptureStress.W,NegativeLargeDEStress.W]
  ring

/-- The baseline agrees with the existing nominal gap even at zero
sine, where the E force and mass both vanish. -/
theorem baseline_gap (q α : ℝ) :
    CanonicalNegativeStress.defect q (atTilt α) α 0 α 0=Nominal.gap q α := by
  have henergy : (∑i : Fin 5,normSq (forces (atTilt α) α 0 α 0 i)/
      (4*(atTilt α).mu i))=Nominal.energy α := by
    apply Finset.sum_congr rfl
    intro i _
    rw [nominal_force_norm]
    rfl
  have hmass : massSum (atTilt α)=Nominal.massSum (Real.sin α) := rfl
  have hdemand := nominal_corner_demand α
  dsimp only [CanonicalNegativeStress.defect,circleSupport]
  rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum]
  change demand (atTilt α) α 0 α 0-
    (q*massSum (atTilt α)+
      (∑i : Fin 5,normSq (forces (atTilt α) α 0 α 0 i)/(4*(atTilt α).mu i))-
      (∑i : Fin 5,((forces (atTilt α) α 0 α 0 i).1+
        (forces (atTilt α) α 0 α 0 i).2)/2))=Nominal.gap q α
  rw [henergy,hmass]
  dsimp only [Nominal.gap]
  linarith

end SquaresInCircles.Eight.TableFree.CanonicalNominal

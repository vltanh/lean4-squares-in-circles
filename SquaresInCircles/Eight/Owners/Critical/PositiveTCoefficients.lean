module

public import SquaresInCircles.Eight.Owners.Critical.ECoefficients
public import SquaresInCircles.Eight.Owners.Exceptional.PositiveTBlocks

/-!
# Eight squares: adapted exact-dual coefficients in the critical positive-T triangle

The starting coefficients are the actual supporting-chain dual.
The T coefficient decreases with its actual primary error, yielding
the correlated l/m, l/c and m-k bounds used by the ordinary envelope.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CriticalPositiveTCoefficients
open Candidate ExceptionalContactStress PositiveAngularEnvelope OrdinaryNegativeEnvelope

def adaptedK (K z : ℝ) : ℝ := K+3/50*z
def adaptedL (L z : ℝ) : ℝ := L-23/100*z
def adaptedC (C z : ℝ) : ℝ := C-53/100*z
def adaptedM (C eta z : ℝ) : ℝ := adaptedC C z*tilt eta z
def mDerivative (C eta z : ℝ) : ℝ :=
  -(53/100)*tilt eta z+adaptedC C z*(-Real.sin z+eta*Real.cos z)

theorem tilt_bounds {eta s : ℝ} (heta : eta∈Icc (27/100:ℝ) (31/100))
    (hs : s∈Icc 0 (4/25:ℝ)) : 1≤tilt eta s ∧ tilt eta s<26/25 := by
  have heta' : eta∈Icc (1/4:ℝ) (7/10) := ⟨by linarith [heta.1],by linarith [heta.2]⟩
  have hs' : s∈Icc 0 (1/5:ℝ) := ⟨hs.1,by linarith [hs.2]⟩
  have hsin := (transport_trig (show s∈Icc 0 (7/10:ℝ) from ⟨hs.1,by linarith [hs.2]⟩)).2.2.1
  have hη := mul_le_mul heta.2 (Real.sin_le hs.1) hsin (by norm_num : (0:ℝ)≤31/100)
  have hcos := cos_upper_four hs.1
  have h4 : s^4≤(4/25:ℝ)^4 := pow_le_pow_left₀ hs.1 hs.2 4
  have hq := mul_nonneg (show 0≤4/25-s by linarith [hs.2]) (show 0≤23/50-s by linarith [hs.2])
  refine ⟨SoleLowCoefficientBounds.tilted_lower heta' hs',?_⟩
  unfold ExceptionalContactStress.tilt
  nlinarith

theorem tilt_derivative {eta s : ℝ} (heta : eta∈Icc (27/100:ℝ) (31/100))
    (hs : s∈Icc 0 (4/25:ℝ)) :
    53/500< -Real.sin s+eta*Real.cos s ∧ -Real.sin s+eta*Real.cos s≤31/100 := by
  have hc := Real.one_sub_sq_div_two_le_cos (x := s)
  have hs2 : s^2≤(4/25:ℝ)^2 := pow_le_pow_left₀ hs.1 hs.2 2
  have hcl : (617/625:ℝ)≤Real.cos s := by linarith
  have hm := mul_le_mul heta.1 hcl (by norm_num : (0:ℝ)≤617/625)
    (by linarith [heta.1] : 0≤eta)
  have hmu := mul_le_mul_of_nonneg_left (Real.cos_le_one s)
    (by linarith [heta.1] : 0≤eta)
  have hsin := (transport_trig (show s∈Icc 0 (7/10:ℝ) from ⟨hs.1,by linarith [hs.2]⟩)).2.2.1
  constructor <;> linarith [(Real.sin_le hs.1).trans hs.2,heta.2]

theorem m_hasDerivAt (C eta z : ℝ) : HasDerivAt (adaptedM C eta) (mDerivative C eta z) z := by
  have hc : HasDerivAt (fun y => C-53/100*y) (-(53/100*1)) z :=
    ((hasDerivAt_id' z).const_mul (53/100)).const_sub C
  have hf : HasDerivAt (fun y => Real.cos y+eta*Real.sin y) (-Real.sin z+eta*Real.cos z) z :=
    (Real.hasDerivAt_cos z).fun_add ((Real.hasDerivAt_sin z).const_mul eta)
  have h := hc.fun_mul hf
  have he : adaptedM C eta=fun y => (C-53/100*y)*(Real.cos y+eta*Real.sin y) := rfl
  rw [he]
  convert h using 1
  simp only [mDerivative,adaptedC,ExceptionalContactStress.tilt]
  ring

theorem m_decreases {C eta z : ℝ} (hC : C∈Icc (37/40:ℝ) 1)
    (heta : eta∈Icc (27/100:ℝ) (31/100)) (hz : z∈Icc 0 (4/25:ℝ)) :
    adaptedM C eta z≤C-(11/50)*z := by
  have hd (s : ℝ) (hs : s∈Icc 0 (4/25:ℝ)) : mDerivative C eta s≤ -(11/50) := by
    have hf := tilt_bounds heta hs
    have hdf := tilt_derivative heta hs
    have hc : adaptedC C s∈Icc 0 1 := by
      dsimp [adaptedC]
      constructor <;> linarith [hC.1,hC.2,hs.1,hs.2]
    have hm := mul_le_mul hc.2 hdf.2
      (by linarith [hdf.1] : 0≤ -Real.sin s+eta*Real.cos s) (by norm_num : (0:ℝ)≤1)
    dsimp [mDerivative]
    linarith [hf.1]
  have h := derivative_reserve (f:=fun s => -adaptedM C eta s)
    (df:=fun s => -mDerivative C eta s) (k:=11/50)
    (fun s _ => (m_hasDerivAt C eta s).neg.continuousAt.continuousWithinAt)
    (fun s _ => (m_hasDerivAt C eta s).neg)
    (fun s hs => by linarith [hd s (Ioo_subset_Icc_self hs)])
    (show (0:ℝ)∈Icc 0 (4/25:ℝ) by norm_num) hz hz.1
  have h0 : adaptedM C eta 0=C := by
    simp [adaptedM,adaptedC,ExceptionalContactStress.tilt]
  linarith

structure Bounds (t z k l c m eta : ℝ) : Prop where
  angle_lower : 1/10≤t
  angle_upper : t≤4/25
  z_nonneg : 0≤z
  z_le : z≤t
  k_lower : 37/40<k
  k_upper : k<199/200
  c_lower : 4201/5000<c
  c_le_m : c≤ m
  m_upper : m<1
  ell_pos : 0<l
  ell_upper : l<67/100
  ell_k : l<(27/40)*k
  ell_m_lower : (61/100)*m<l
  ell_m_upper : l< m
  ell_c_upper : l<(71/100)*c
  difference : m-k<1/50
  gap : 31/125< m-l
  delta_upper : m-c≤(31/100)*z
  refined_gap : 37/125-(3/10)*z+(m-c)< m-l
  eta_lower : 27/100<eta
  eta_upper : eta<31/100

theorem adapted_bounds {t z K L C eta : ℝ}
    (h : CriticalECoefficients.Bounds t K L C eta) (hz : z∈Icc 0 t) :
    Bounds t z (adaptedK K z) (adaptedL L z) (adaptedC C z) (adaptedM C eta z) eta := by
  have heta : eta∈Icc (27/100:ℝ) (31/100) := ⟨h.eta_lower.le,h.eta_upper.le⟩
  have hz' : z∈Icc 0 (4/25:ℝ) := ⟨hz.1,hz.2.trans h.angle_upper⟩
  have hc : (4201/5000:ℝ)<adaptedC C z := by
    dsimp [adaptedC]
    linarith [h.c_lower,hz'.2]
  have hf := tilt_bounds heta hz'
  have hcm : adaptedC C z≤adaptedM C eta z := by
    have hh := mul_le_mul_of_nonneg_left hf.1 (show 0≤adaptedC C z by linarith)
    simpa [adaptedM] using hh
  have hmd := m_decreases ⟨h.c_lower.le,h.c_upper.le⟩ heta hz'
  have hmu : adaptedM C eta z<1 := by linarith [h.c_upper,hz'.1]
  have hgap0 : (37/125:ℝ)<C-L := by linarith [h.ell_c_upper,h.c_lower]
  have hdelta : adaptedM C eta z-adaptedC C z≤(31/100)*z := by
    have hs := (transport_trig (show z∈Icc 0 (7/10:ℝ) from ⟨hz'.1,by linarith [hz'.2]⟩)).2.2.1
    have hsU := Real.sin_le hz'.1
    have hη := mul_le_mul h.eta_upper.le hsU hs (by norm_num : (0:ℝ)≤31/100)
    have hcU : adaptedC C z≤1 := by dsimp [adaptedC]; linarith [h.c_upper,hz'.1]
    have htilt : 0≤ExceptionalContactStress.tilt eta z-1 := by linarith [hf.1]
    have hcoef : ExceptionalContactStress.tilt eta z-1≤(31/100)*z := by
      dsimp [ExceptionalContactStress.tilt]; linarith [Real.cos_le_one z]
    have hh := mul_le_mul hcU hcoef htilt (by norm_num : (0:ℝ)≤1)
    have he : adaptedM C eta z-adaptedC C z=adaptedC C z*(ExceptionalContactStress.tilt eta z-1) := by
      dsimp [adaptedM]; ring
    rw [he]
    linarith
  refine ⟨h.angle_lower,h.angle_upper,hz.1,hz.2,?_,?_,hc,hcm,hmu,?_,?_,?_,?_,?_,?_,?_,?_,hdelta,?_,
    h.eta_lower,h.eta_upper⟩
  all_goals dsimp only [adaptedK,adaptedL] at *
  all_goals dsimp only [adaptedC] at hc hcm hdelta hmd ⊢
  all_goals linarith [h.k_lower,h.k_upper,h.c_lower,h.c_upper,h.ell_pos,h.ell_upper,
    h.ell_k,h.ell_c_lower,h.ell_c_upper,h.difference,hz'.1,hz'.2]

theorem Bounds.angle {t z k l c m eta : ℝ} (h : Bounds t z k l c m eta) : t∈Icc 0 frameCap :=
  ⟨by linarith [h.angle_lower],by dsimp [frameCap]; linarith [h.angle_upper]⟩
theorem Bounds.tilt {t z k l c m eta s : ℝ} (h : Bounds t z k l c m eta) (hs : s∈Icc 0 t) :
    1≤tilt eta s ∧ tilt eta s<26/25 :=
  tilt_bounds ⟨h.eta_lower.le,h.eta_upper.le⟩ ⟨hs.1,hs.2.trans h.angle_upper⟩
theorem Bounds.order {t z k l c m eta : ℝ} (h : Bounds t z k l c m eta) :
    0<k ∧ l≤k ∧ l≤c ∧ l≤ m ∧ k≤2*l ∧ c≤2*l ∧ m≤2*l := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩ <;> linarith [h.k_lower,h.k_upper,h.c_lower,h.c_le_m,h.ell_pos,
    h.ell_k,h.ell_m_lower,h.ell_m_upper,h.ell_c_upper]

def weights (td : Bool) (k l c m eta x e : ℝ) : ExceptionalPositiveTBlocks.Weights :=
  ⟨k*tilt eta x,k,l,if td then m else c,if td then c else m,tilt eta e⟩

end SquaresInCircles.Eight.CriticalPositiveTCoefficients

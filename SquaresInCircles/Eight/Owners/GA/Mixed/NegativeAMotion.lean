module

public import Mathlib.Algebra.Order.Star.Real
public import SquaresInCircles.Eight.Owners.GA.HybridConcentration

/-!
# Eight squares: the two unchanged-neighbor mixed A transports

Negative GA uses precisely
max(b,Lplus), while negative AB uses precisely min(b,Uplus). The whole
motion stays on the true flat core and inside the original containing
circle. At the terminal aligned edge the secondary owner is an exact
projection identity, not a selected virtual inequality.
-/

section
/-!
## The four original flat-core A caps

The upper caps have constant term -1/2. Their parameter P is the
unchanged primary coordinate of G minus 1/2; the lower parameter B
is the unchanged positive tangent magnitude of the outer B point.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.MixedNegativeA
open Candidate Secondary

abbrev cut : ℝ := 19/50
abbrev K : ℝ := 13/12
abbrev k0 : ℝ := 1/12

def cap (d P k r : ℝ) : ℝ := d+(P+k*Real.sin r)/Real.cos r
def capD (P k r : ℝ) : ℝ := (P*Real.sin r+k)/Real.cos r^2

def Uminus (P r : ℝ) : ℝ := cap (-1/2) P (-K) r
def Uplus (P r : ℝ) : ℝ := cap (-1/2) P k0 r
def Lminus (B r : ℝ) : ℝ := cap (1/2) (1/2-B) K r
def Lplus (B r : ℝ) : ℝ := cap (1/2) (1/2-B) (-k0) r

def flat (b : ℝ) : SignedPoint := ⟨7/12,b⟩

theorem angle_domain {r : ℝ} (hr : r∈Icc 0 cut) : r∈Icc 0 frameCap :=
  ⟨hr.1,hr.2.trans (by norm_num [cut,frameCap])⟩

theorem cosine_positive {r : ℝ} (hr : r∈Icc 0 cut) : 0<Real.cos r := by
  linarith [(transport_trig (angle_domain hr)).1]

theorem cap_hasDerivAt (d P k : ℝ) {r : ℝ} (hr : r∈Icc 0 cut) :
    HasDerivAt (cap d P k) (capD P k r) r := by
  have hc := (cosine_positive hr).ne'
  have h1 := ((Real.hasDerivAt_sin r).const_mul k).const_add P
  have hh := (h1.div (Real.hasDerivAt_cos r) hc).const_add d
  convert hh using 1
  · rfl
  · dsimp [capD]
    field_simp [hc]
    linear_combination (-k)*(Real.sin_sq_add_cos_sq r)

theorem Uminus_hasDerivAt (P : ℝ) {r : ℝ} (hr : r∈Icc 0 cut) :
    HasDerivAt (Uminus P) (capD P (-K) r) r := cap_hasDerivAt _ _ _ hr

theorem Uplus_hasDerivAt (P : ℝ) {r : ℝ} (hr : r∈Icc 0 cut) :
    HasDerivAt (Uplus P) (capD P k0 r) r := cap_hasDerivAt _ _ _ hr

theorem Lminus_hasDerivAt (B : ℝ) {r : ℝ} (hr : r∈Icc 0 cut) :
    HasDerivAt (Lminus B) (capD (1/2-B) K r) r := cap_hasDerivAt _ _ _ hr

theorem Lplus_hasDerivAt (B : ℝ) {r : ℝ} (hr : r∈Icc 0 cut) :
    HasDerivAt (Lplus B) (capD (1/2-B) (-k0) r) r := cap_hasDerivAt _ _ _ hr

@[simp] theorem Uminus_zero (P : ℝ) : Uminus P 0=P-1/2 := by norm_num [Uminus,cap]; ring
@[simp] theorem Uplus_zero (P : ℝ) : Uplus P 0=P-1/2 := by norm_num [Uplus,cap]; ring
@[simp] theorem Lminus_zero (B : ℝ) : Lminus B 0=1-B := by norm_num [Lminus,cap]; ring
@[simp] theorem Lplus_zero (B : ℝ) : Lplus B 0=1-B := by norm_num [Lplus,cap]; ring

theorem GA_negative_iff (G : SignedPoint) (b : ℝ) {r : ℝ} (hr : r∈Icc 0 cut) :
    quarterFeasible G (flat b) (-r) 3 ↔ b≤Uminus (G.a-1/2) r := by
  have hc := cosine_positive hr
  rw [quarterFeasible,edgeWidth_negative_formula (angle_domain hr)]
  simp only [quarterProjection,Matrix.cons_val,flat,Real.sin_neg,Real.cos_neg]
  unfold Uminus cap
  rw [← sub_le_iff_le_add',le_div_iff₀ hc]
  simp only [K]
  constructor <;> intro hh <;> linarith only [hh]

theorem GA_positive_iff (G : SignedPoint) (b : ℝ) {r : ℝ} (hr : r∈Icc 0 cut) :
    quarterFeasible G (flat b) r 3 ↔ b≤Uplus (G.a-1/2) r := by
  have hc := cosine_positive hr
  rw [quarterFeasible,edgeWidth_positive_formula (angle_domain hr)]
  simp only [quarterProjection,Matrix.cons_val,flat]
  unfold Uplus cap
  rw [← sub_le_iff_le_add',le_div_iff₀ hc]
  simp only [k0]
  constructor <;> intro hh <;> linarith only [hh]

theorem AB_negative_iff (B : SignedPoint) (b : ℝ) {r : ℝ} (hr : r∈Icc 0 cut) :
    zeroFeasible (flat b) B (-r) 2 ↔ Lminus (-B.y) r≤b := by
  have hc := cosine_positive hr
  rw [zeroFeasible,edgeWidth_negative_formula (angle_domain hr)]
  simp only [zeroProjection,Matrix.cons_val,flat,Real.sin_neg,Real.cos_neg]
  unfold Lminus cap
  rw [← le_sub_iff_add_le',div_le_iff₀ hc]
  simp only [K]
  constructor <;> intro hh <;> linarith only [hh]

theorem AB_positive_iff (B : SignedPoint) (b : ℝ) {r : ℝ} (hr : r∈Icc 0 cut) :
    zeroFeasible (flat b) B r 2 ↔ Lplus (-B.y) r≤b := by
  have hc := cosine_positive hr
  rw [zeroFeasible,edgeWidth_positive_formula (angle_domain hr)]
  simp only [zeroProjection,Matrix.cons_val,flat]
  unfold Lplus cap
  rw [← le_sub_iff_add_le',div_le_iff₀ hc]
  simp only [k0]
  constructor <;> intro hh <;> linarith only [hh]

theorem flat_geometry {b : ℝ} (hb : b∈Ioo 0 (1/2:ℝ)) :
    (flat b).Sorted ∧ (flat b).Core ∧ (flat b).AvoidsCore ∧
      (flat b).circle<313/144 := by
  have habs : |b|=b := abs_of_pos hb.1
  refine ⟨?_,?_,?_,?_⟩
  · simp only [SignedPoint.Sorted,flat,habs]
    exact ⟨by norm_num,by linarith [hb.2]⟩
  · norm_num [SignedPoint.Core,SignedPoint.coreDistance,flat,habs,
      max_eq_right (show b-1/2≤0 by linarith [hb.2])]
  · norm_num [SignedPoint.AvoidsCore,SignedPoint.coreDistance,flat,habs,
      max_eq_right (show b-1/2≤0 by linarith [hb.2])]
  · dsimp [SignedPoint.circle,flat]
    rw [habs]
    nlinarith [hb.1,hb.2]

theorem flat_small_circle {b : ℝ} (hb : b∈Ioo 0 (1/5:ℝ)) :
    (flat b).circle<5989/3600 := by
  dsimp [SignedPoint.circle,flat]
  rw [abs_of_pos hb.1]
  nlinarith [hb.1,hb.2]

end SquaresInCircles.Eight.GlobalGA.MixedNegativeA
end
end
end

section
/-!
## The same derivative reserve for both mixed-sign A motions

All angles stay on the single
interval [0,19/50]. The exact comparison cos² > 43/50 pays both
secant derivatives. The two gap derivatives share the literal reserve
10459/25800 > 2/5; no contact or angle subdivision is introduced.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.MixedNegativeA
open Candidate Secondary

def secSq (r : ℝ) : ℝ := 1/Real.cos r^2
def secTan (r : ℝ) : ℝ := Real.sin r/Real.cos r^2

theorem capD_identity (P k r : ℝ) : capD P k r=P*secTan r+k*secSq r := by
  dsimp [capD,secTan,secSq]
  ring

theorem secant_bounds {r : ℝ} (hr : r∈Icc 0 cut) :
    1≤ secSq r ∧ secSq r<50/43 ∧ 0≤ secTan r ∧ secTan r<19/43 := by
  have hcos := cosine_positive hr
  have hcoslo := Real.one_sub_sq_div_two_le_cos (x:=r)
  have hr2 := pow_le_pow_left₀ hr.1 hr.2 2
  have hcoscut : (4639/5000:ℝ)≤Real.cos r := by simp only [cut] at hr2; nlinarith
  have hcos2 : (43/50:ℝ)<Real.cos r^2 := by nlinarith
  have hcos1 : Real.cos r^2≤1 := by
    nlinarith [Real.sin_sq_add_cos_sq r,sq_nonneg (Real.sin r)]
  have hsin := (transport_trig (angle_domain hr)).2.2.1
  have hsine := (Real.sin_le hr.1).trans hr.2
  refine ⟨?_,?_,?_,?_⟩
  · unfold secSq
    apply (le_div_iff₀ (pow_pos hcos 2)).2
    simpa using hcos1
  · unfold secSq
    apply (div_lt_iff₀ (pow_pos hcos 2)).2
    nlinarith only [hcos2]
  · exact div_nonneg hsin (sq_nonneg _)
  · unfold secTan
    apply (div_lt_iff₀ (pow_pos hcos 2)).2
    simp only [cut] at hsine
    nlinarith only [hcos2,hsine]

theorem upper_negative_slope {P r : ℝ} (hP : P∈Ioo 0 (183/200:ℝ))
    (hr : r∈Icc 0 cut) : capD P (-K) r<0 := by
  have hb := secant_bounds hr
  have hh := mul_le_mul hP.2.le hb.2.2.2.le hb.2.2.1 (by norm_num : (0:ℝ)≤183/200)
  rw [capD_identity]
  simp only [K]
  nlinarith [hb.1]

theorem lower_negative_slope {B r : ℝ} (hB : B<9/10)
    (hr : r∈Icc 0 cut) : 0<capD (1/2-B) K r := by
  have hb := secant_bounds hr
  have hh := mul_le_mul_of_nonneg_right
    (show -(2/5:ℝ)≤1/2-B by linarith) hb.2.2.1
  rw [capD_identity]
  dsimp [K]
  nlinarith [hb.1,hb.2.2.2]

theorem lower_positive_slope {B r : ℝ} (hB : (1/2:ℝ)≤B)
    (hr : r∈Icc 0 cut) : capD (1/2-B) (-k0) r<0 := by
  have hb := secant_bounds hr
  have hh := mul_nonpos_of_nonpos_of_nonneg (by linarith : 1/2-B≤0) hb.2.2.1
  rw [capD_identity]
  dsimp [k0]
  nlinarith [hb.1]

theorem Uminus_antitone {P : ℝ} (hP : P∈Ioo 0 (183/200:ℝ)) :
    AntitoneOn (Uminus P) (Icc 0 cut) :=
  antiOn_of_hasDeriv_nonpos
    (fun _ hr => (Uminus_hasDerivAt P hr).continuousAt.continuousWithinAt)
    (fun _ hr => Uminus_hasDerivAt P (Ioo_subset_Icc_self hr))
    (fun _ hr => (upper_negative_slope hP (Ioo_subset_Icc_self hr)).le)

theorem Lminus_monotone {B : ℝ} (hB : B<9/10) :
    MonotoneOn (Lminus B) (Icc 0 cut) :=
  monoOn_of_hasDeriv_nonneg
    (fun _ hr => (Lminus_hasDerivAt B hr).continuousAt.continuousWithinAt)
    (fun _ hr => Lminus_hasDerivAt B (Ioo_subset_Icc_self hr))
    (fun _ hr => (lower_negative_slope hB (Ioo_subset_Icc_self hr)).le)

theorem Lplus_antitone {B : ℝ} (hB : (1/2:ℝ)≤B) :
    AntitoneOn (Lplus B) (Icc 0 cut) :=
  antiOn_of_hasDeriv_nonpos
    (fun _ hr => (Lplus_hasDerivAt B hr).continuousAt.continuousWithinAt)
    (fun _ hr => Lplus_hasDerivAt B (Ioo_subset_Icc_self hr))
    (fun _ hr => (lower_positive_slope hB (Ioo_subset_Icc_self hr)).le)

theorem Lminus_lower {B r : ℝ} (hB : B<9/10) (hr : r∈Icc 0 cut) :
    (1/10:ℝ)<Lminus B r := by
  have hh := Lminus_monotone hB (show (0:ℝ)∈Icc 0 cut by norm_num [cut]) hr hr.1
  rw [Lminus_zero] at hh
  linarith

theorem common_derivative_reserve {P B x y : ℝ}
    (hP : P∈Ioo 0 (183/200:ℝ)) (hB : B<9/10)
    (hx : x∈Icc 0 cut) (hy : y∈Icc 0 cut) :
    (2/5:ℝ)< -capD P (-K) x+capD (1/2-B) (-k0) y ∧
    (2/5:ℝ)< -capD P k0 y+capD (1/2-B) K x := by
  have hxb := secant_bounds hx
  have hyb := secant_bounds hy
  have hPx := mul_le_mul hP.2.le hxb.2.2.2.le hxb.2.2.1 (by norm_num : (0:ℝ)≤183/200)
  have hPy := mul_le_mul hP.2.le hyb.2.2.2.le hyb.2.2.1 (by norm_num : (0:ℝ)≤183/200)
  have hBx := mul_le_mul_of_nonneg_right
    (show -(2/5:ℝ)≤1/2-B by linarith) hxb.2.2.1
  have hBy := mul_le_mul_of_nonneg_right
    (show -(2/5:ℝ)≤1/2-B by linarith) hyb.2.2.1
  rw [capD_identity,capD_identity,capD_identity,capD_identity]
  dsimp [K,k0]
  constructor <;> nlinarith [hxb.1,hyb.2.1,hxb.2.2.2,hyb.2.2.2]

def gap (negativeGA : Bool) (P B n p τ : ℝ) : ℝ :=
  if negativeGA then Uminus P (n-τ)-Lplus B (p-τ)
  else Uplus P (p-τ)-Lminus B (n-τ)

def gapD (negativeGA : Bool) (P B n p τ : ℝ) : ℝ :=
  if negativeGA then -capD P (-K) (n-τ)+capD (1/2-B) (-k0) (p-τ)
  else -capD P k0 (p-τ)+capD (1/2-B) K (n-τ)

theorem motion_angles {n p τ : ℝ} (hn : n∈Icc 0 cut) (hp : p∈Icc 0 n)
    (hτ : τ∈Icc 0 p) : n-τ∈Icc 0 cut ∧ p-τ∈Icc 0 cut := by
  exact ⟨⟨by linarith [hτ.2,hp.2],by linarith [hn.2,hτ.1]⟩,
    ⟨by linarith [hτ.2],by linarith [hn.2,hp.2,hτ.1]⟩⟩

theorem gap_hasDerivAt (negativeGA : Bool) (P B : ℝ) {n p τ : ℝ}
    (hn : n∈Icc 0 cut) (hp : p∈Icc 0 n) (hτ : τ∈Icc 0 p) :
    HasDerivAt (gap negativeGA P B n p) (gapD negativeGA P B n p τ) τ := by
  have hm := motion_angles hn hp hτ
  cases negativeGA
  · have h1 := (Uplus_hasDerivAt P hm.2).comp τ ((hasDerivAt_id' τ).const_sub p)
    have h2 := (Lminus_hasDerivAt B hm.1).comp τ ((hasDerivAt_id' τ).const_sub n)
    convert h1.sub h2 using 1
    · funext x; simp [gap]
    · simp only [gapD,Bool.false_eq_true,↓reduceIte]; ring
  · have h1 := (Uminus_hasDerivAt P hm.1).comp τ ((hasDerivAt_id' τ).const_sub n)
    have h2 := (Lplus_hasDerivAt B hm.2).comp τ ((hasDerivAt_id' τ).const_sub p)
    convert h1.sub h2 using 1
    · funext x; simp [gap]
    · simp only [gapD,↓reduceIte]; ring

theorem gap_growth (negativeGA : Bool) {P B n p τ : ℝ}
    (hP : P∈Ioo 0 (183/200:ℝ)) (hB : B<9/10)
    (hn : n∈Icc 0 cut) (hp : p∈Icc 0 n) (hτ : τ∈Icc 0 p) :
    gap negativeGA P B n p 0+(2/5)*τ≤gap negativeGA P B n p τ := by
  have hm : MonotoneOn (fun τ => gap negativeGA P B n p τ-(2/5)*τ) (Icc 0 p) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun τ hτ => ((gap_hasDerivAt negativeGA P B hn hp hτ).sub
        ((hasDerivAt_id τ).const_mul (2/5:ℝ))).continuousAt.continuousWithinAt)
      (fun τ hτ => (gap_hasDerivAt negativeGA P B hn hp (Ioo_subset_Icc_self hτ)).sub
        ((hasDerivAt_id τ).const_mul (2/5:ℝ)))
    intro τ hτ
    have hangles := motion_angles hn hp (Ioo_subset_Icc_self hτ)
    have hres := common_derivative_reserve hP hB hangles.1 hangles.2
    cases negativeGA <;> dsimp [gapD] <;> linarith
  have hh := hm ⟨le_rfl,hp.1⟩ hτ hτ.1
  simp only [mul_zero,sub_zero] at hh
  linarith

end SquaresInCircles.Eight.GlobalGA.MixedNegativeA
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.MixedNegativeA
open Candidate Secondary

def tangentGA (B b p τ : ℝ) : ℝ := max b (Lplus B (p-τ))
def tangentAB (P b p τ : ℝ) : ℝ := min b (Uplus P (p-τ))

theorem positive_AB_large_neighbor {B b p : ℝ}
    (hb : b∈Ioo 0 (39/250:ℝ)) (hp : p∈Icc 0 (1/4:ℝ))
    (hAB : Lplus B p≤b) : (4/5:ℝ)<B := by
  have hp' : p∈Icc 0 cut := ⟨hp.1,hp.2.trans (by norm_num [cut])⟩
  have hc := cosine_positive hp'
  have hcos := Real.one_sub_sq_div_two_le_cos (x:=p)
  have hp2 := pow_le_pow_left₀ hp.1 hp.2 2
  have hcoslo : (31/32:ℝ)≤Real.cos p := by nlinarith
  have hs : Real.sin p≤(1/4:ℝ) := (Real.sin_le hp.1).trans hp.2
  have hprod := mul_le_mul
    (show (43/125:ℝ)≤1/2-b by linarith [hb.2]) hcoslo
    (by norm_num : (0:ℝ)≤31/32) (by linarith [hb.2] : 0≤1/2-b)
  have hcap := hAB
  unfold Lplus cap at hcap
  rw [← le_sub_iff_add_le',div_le_iff₀ hc] at hcap
  simp only [k0] at hcap
  linarith only [hcap,hprod,hs]

theorem GA_motion {P B b n p τ : ℝ}
    (hP : P∈Ioo 0 (183/200:ℝ)) (hB : B<9/10)
    (hb : b∈Ioo 0 (39/250:ℝ)) (hn : n∈Ioo 0 (1/4:ℝ))
    (hp : p∈Icc 0 n) (hτ : τ∈Icc 0 p)
    (hGA : b≤Uminus P n) (hAB : Lplus B p≤b) :
    tangentGA B b p τ∈Ioo 0 (1/5:ℝ) ∧
    tangentGA B b p τ≤Uminus P (n-τ) ∧
    Lplus B (p-τ)≤tangentGA B b p τ := by
  have hn' : n∈Icc 0 cut := ⟨hn.1.le,hn.2.le.trans (by norm_num [cut])⟩
  have hp' : p∈Icc 0 cut := ⟨hp.1,hp.2.trans hn'.2⟩
  have hangles := motion_angles hn' hp hτ
  have hlarge := positive_AB_large_neighbor hb ⟨hp.1,hp.2.trans hn.2.le⟩ hAB
  have hU := Uminus_antitone hP hangles.1 hn' (by linarith [hτ.1])
  have hgap := gap_growth true hP hB hn' hp hτ
  have hgap0 : 0≤gap true P B n p 0 := by
    simp only [gap,ite_true,sub_zero]
    linarith
  have hroom : Lplus B (p-τ)≤Uminus P (n-τ) := by
    dsimp [gap] at hgap hgap0
    linarith [hτ.1]
  have hL := Lplus_antitone (B:=B) (by linarith)
    (show (0:ℝ)∈Icc 0 cut by norm_num [cut]) hangles.2 hangles.2.1
  rw [Lplus_zero] at hL
  refine ⟨⟨?_,?_⟩,?_,?_⟩
  · exact hb.1.trans_le (le_max_left _ _)
  · exact max_lt (by linarith [hb.2]) (by linarith)
  · exact max_le (hGA.trans hU) hroom
  · exact le_max_right _ _

theorem AB_motion {P B b n p τ : ℝ}
    (hP : P∈Ioo 0 (183/200:ℝ)) (hB : B<9/10)
    (hb : b∈Ioo 0 (1/2:ℝ)) (hn : n∈Icc 0 cut)
    (hp : p∈Icc 0 n) (hτ : τ∈Icc 0 p)
    (hGA : b≤Uplus P p) (hAB : Lminus B n≤b) :
    tangentAB P b p τ∈Ioo (1/10:ℝ) (1/2:ℝ) ∧
    tangentAB P b p τ≤Uplus P (p-τ) ∧
    Lminus B (n-τ)≤tangentAB P b p τ := by
  have hangles := motion_angles hn hp hτ
  have hL := Lminus_monotone hB hangles.1 hn (by linarith [hτ.1])
  have hgap := gap_growth false hP hB hn hp hτ
  simp only [gap,Bool.false_eq_true,↓reduceIte,sub_zero] at hgap
  have hroom : Lminus B (n-τ)≤Uplus P (p-τ) := by
    linarith [hτ.1]
  have hlow' : Lminus B (n-τ)≤tangentAB P b p τ :=
    le_min (hL.trans hAB) hroom
  exact ⟨⟨(Lminus_lower hB hangles.1).trans_le hlow',
    (min_le_left _ _).trans_lt hb.2⟩,min_le_right _ _,hlow'⟩

theorem GA_original_motion {Q b n p τ : ℝ} {G B : SignedPoint}
    (hQ : (5/2:ℝ)≤Q) (hG : G.a-1/2∈Ioo 0 (183/200:ℝ)) (hB : -B.y<9/10)
    (hb : b∈Ioo 0 (39/250:ℝ)) (hn : n∈Ioo 0 (1/4:ℝ))
    (hp : p∈Icc 0 n) (hτ : τ∈Icc 0 p)
    (hGA : quarterFeasible G (flat b) (-n) 3)
    (hAB : zeroFeasible (flat b) B p 2) :
    let b' := tangentGA (-B.y) b p τ
    (flat b').Sorted ∧ (flat b').Core ∧ (flat b').AvoidsCore ∧
      (flat b').Contained Q ∧ b'∈Ioo 0 (1/5:ℝ) ∧
      quarterFeasible G (flat b') (-(n-τ)) 3 ∧ zeroFeasible (flat b') B (p-τ) 2 := by
  have hn' : n∈Icc 0 cut := ⟨hn.1.le,hn.2.le.trans (by norm_num [cut])⟩
  have hp' : p∈Icc 0 cut := ⟨hp.1,hp.2.trans hn'.2⟩
  have hh := GA_motion hG hB hb hn hp hτ
    ((GA_negative_iff G b hn').1 hGA) ((AB_positive_iff B b hp').1 hAB)
  have hgeom := flat_geometry (show tangentGA (-B.y) b p τ∈Ioo 0 (1/2:ℝ) from
    ⟨hh.1.1,by linarith [hh.1.2]⟩)
  have hang := motion_angles hn' hp hτ
  exact ⟨hgeom.1,hgeom.2.1,hgeom.2.2.1,
    (flat_small_circle hh.1).le.trans (by linarith),hh.1,
    (GA_negative_iff G _ hang.1).2 hh.2.1,(AB_positive_iff B _ hang.2).2 hh.2.2⟩

theorem AB_original_motion {Q b n p τ : ℝ} {G B : SignedPoint}
    (hQ : (5/2:ℝ)≤Q) (hG : G.a-1/2∈Ioo 0 (183/200:ℝ)) (hB : -B.y<9/10)
    (hb : b∈Ioo 0 (1/2:ℝ)) (hn : n∈Icc 0 cut)
    (hp : p∈Icc 0 n) (hτ : τ∈Icc 0 p)
    (hGA : quarterFeasible G (flat b) p 3)
    (hAB : zeroFeasible (flat b) B (-n) 2) :
    let b' := tangentAB (G.a-1/2) b p τ
    (flat b').Sorted ∧ (flat b').Core ∧ (flat b').AvoidsCore ∧
      (flat b').Contained Q ∧ b'∈Ioo (1/10:ℝ) (1/2:ℝ) ∧
      quarterFeasible G (flat b') (p-τ) 3 ∧ zeroFeasible (flat b') B (-(n-τ)) 2 := by
  have hp' : p∈Icc 0 cut := ⟨hp.1,hp.2.trans hn.2⟩
  have hh := AB_motion hG hB hb hn hp hτ
    ((GA_positive_iff G b hp').1 hGA) ((AB_negative_iff B b hn).1 hAB)
  have hgeom := flat_geometry (show tangentAB (G.a-1/2) b p τ∈Ioo 0 (1/2:ℝ) from
    ⟨by linarith [hh.1.1],hh.1.2⟩)
  have hang := motion_angles hn hp hτ
  exact ⟨hgeom.1,hgeom.2.1,hgeom.2.2.1,hgeom.2.2.2.le.trans (by linarith),hh.1,
    (GA_positive_iff G _ hang.2).2 hh.2.1,(AB_negative_iff B _ hang.1).2 hh.2.2⟩

theorem GA_terminal {Q b n p : ℝ} {G B : SignedPoint}
    (hQ : (5/2:ℝ)≤Q) (hG : G.a-1/2∈Ioo 0 (183/200:ℝ)) (hB : -B.y<9/10)
    (hb : b∈Ioo 0 (39/250:ℝ)) (hn : n∈Ioo 0 (1/4:ℝ)) (hp : p∈Icc 0 n)
    (hGA : quarterFeasible G (flat b) (-n) 3) (hAB : zeroFeasible (flat b) B p 2) :
    ∃A' : SignedPoint,A'.Sorted ∧ A'.Core ∧ A'.AvoidsCore ∧ A'.Contained Q ∧
      A'.a=7/12 ∧ A'.y∈Ioo 0 (1/5:ℝ) ∧
      quarterFeasible G A' (-(n-p)) 3 ∧ zeroFeasible A' B 0 0 := by
  have hh := GA_original_motion hQ hG hB hb hn hp ⟨hp.1,le_rfl⟩ hGA hAB
  refine ⟨flat (tangentGA (-B.y) b p p),hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1,rfl,
    hh.2.2.2.2.1,hh.2.2.2.2.2.1,?_⟩
  have hzero : zeroFeasible (flat (tangentGA (-B.y) b p p)) B 0 2 := by
    simpa only [sub_self] using hh.2.2.2.2.2.2
  simpa [zeroFeasible,zeroProjection] using hzero

theorem AB_terminal {Q b n p : ℝ} {G B : SignedPoint}
    (hQ : (5/2:ℝ)≤Q) (hG : G.a-1/2∈Ioo 0 (183/200:ℝ)) (hB : -B.y<9/10)
    (hb : b∈Ioo 0 (1/2:ℝ)) (hn : n∈Icc 0 cut) (hp : p∈Icc 0 n)
    (hGA : quarterFeasible G (flat b) p 3) (hAB : zeroFeasible (flat b) B (-n) 2) :
    ∃A' : SignedPoint,A'.Sorted ∧ A'.Core ∧ A'.AvoidsCore ∧ A'.Contained Q ∧
      A'.a=7/12 ∧ A'.y∈Ioo (1/10:ℝ) (1/2:ℝ) ∧
      quarterFeasible G A' 0 2 ∧ zeroFeasible A' B (-(n-p)) 2 := by
  have hh := AB_original_motion hQ hG hB hb hn hp ⟨hp.1,le_rfl⟩ hGA hAB
  refine ⟨flat (tangentAB (G.a-1/2) b p p),hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1,rfl,
    hh.2.2.2.2.1,?_,hh.2.2.2.2.2.2⟩
  have hzero : quarterFeasible G (flat (tangentAB (G.a-1/2) b p p)) 0 3 := by
    simpa only [sub_self] using hh.2.2.2.2.2.1
  simpa [quarterFeasible,quarterProjection] using hzero

end SquaresInCircles.Eight.GlobalGA.MixedNegativeA
end
end
end

module

public import SquaresInCircles.Eight.Owners.Sole.PositiveTEnvelope
public import SquaresInCircles.Eight.Owners.Sole.NormGain
public import SquaresInCircles.Eight.Owners.Sole.PositiveTSplitSupport

/-!
# Eight squares: every negative sole-E charge pays its own separated positive budget

The full-domain chords already proved for positive
T are stronger than the negative-primary positive budgets. Concavity
allows both endpoints of each chord to be shifted left by the actual
negative primary. Thus no far-angle comparison between different
negative indices, and no additional low-family subdivision, is needed.
-/

section
/-!
## Splitting at fixed coordinates with the negative-T secant

Increasing the weight of the selected negative primary adds one constant residual, `adjustment`,
to the G/E split (`value_eq_stress`). The error of T and the coordinates of every point stay. The
stress is concave in the split (`concave`) and nonpositive by the same weak contact at which the
weight is increased (`necessary`), and positivity at both ends of the split gives positivity on
the whole split (`positive_of_endpoints`).
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.SoleNegativeTSplit
open Candidate SignedStress SoleTScalarModel SolePositiveTSplitModel

def btWeight (f : Family) (td : Bool) (t s : ℝ) : ℝ :=
  if td then c f t 0 else c f t 0/Real.cos s
def tdWeight (f : Family) (td : Bool) (t s : ℝ) : ℝ :=
  if td then c f t 0/Real.cos s else c f t 0

def adjustment (C : SignedCycle) (f : Family) (td : Bool) (t s : ℝ) : ℝ :=
  c f t 0*(1/Real.cos s-1)*
    (if td then edgeWidth (delta C.theta T)-C.edge T 2
     else edgeWidth (delta C.theta B)-C.edge B 3)

def value (C : SignedCycle) (ab : Fin 4) (f : Family) (td : Bool)
    (R M t s x : ℝ) : ℝ :=
  SolePositiveTSplitModel.value C ab f td R M t 0 x+adjustment C f td t s

def forceData (C : SignedCycle) (ab : Fin 4) (f : Family) (td : Bool) (t s x e : ℝ) :
    Vertex → Point :=
  SoleEStress.forces C ab (btOwner td) (tdOwner td) (deOwner f) (ehOwner f)
    (nWeight f t 0 x) (k f t 0) (ell f t 0) (btWeight f td t s) (tdWeight f td t s)
    (deWeight f t e) (ehWeight f)

def variableDemand (C : SignedCycle) (f : Family) (td : Bool) (t s x e : ℝ) : ℝ :=
  nWeight f t 0 x*edgeWidth (delta C.theta H)+k f t 0*edgeWidth x+
    ell f t 0*edgeWidth (delta C.theta A)+btWeight f td t s*edgeWidth (delta C.theta B)+
    tdWeight f td t s*edgeWidth (delta C.theta T)+
    deWeight f t e*edgeWidth (if isDE f then e else delta C.theta D)+
    ehWeight f*edgeWidth (if isDE f then delta C.theta E else e)

def fixedWork (C : SignedCycle) (ab : Fin 4) (f : Family) (td : Bool) (t s x e : ℝ) : ℝ :=
  work (forceData C ab f td t s x e H) (C.point H)+
    work (forceData C ab f td t s x e A) (C.point A)+
    work (forceData C ab f td t s x e B) (C.point B)+
    work (forceData C ab f td t s x e T) (C.point T)+
    work (forceData C ab f td t s x e D) (C.point D)

def stress (C : SignedCycle) (ab : Fin 4) (f : Family) (td : Bool)
    (R M t s x e : ℝ) : ℝ :=
  variableDemand C f td t s x e-fixedWork C ab f td t s x e-
    k f t 0*SoleResiduals.sigma R (g f t)*Real.sin x-eBound C f R M t e

theorem secant_nonneg {s : ℝ} (hs : s∈Icc 0 frameCap) :
    0<1/Real.cos s ∧ 0≤1/Real.cos s-1 := by
  have hc : 0<Real.cos s := by linarith [(transport_trig hs).1]
  refine ⟨by positivity,?_⟩
  have hh : 1≤1/Real.cos s := (le_div_iff₀ hc).2 (by simpa using Real.cos_le_one s)
  linarith

theorem adjustment_nonpos {C : SignedCycle} {f : Family} (td : Bool) {t s : ℝ}
    (ht : t∈domain f) (hs : s∈Icc 0 frameCap)
    (hf : if td then C.Feasible T 2 else C.Feasible B 3) :
    adjustment C f td t s≤0 := by
  have hc := (coefficient_positive ht (show (0:ℝ)∈Icc 0 t from ⟨le_rfl,(angle ht).1⟩)).2.2.1
  have hcoef := mul_nonneg hc.le (secant_nonneg hs).2
  apply mul_nonpos_of_nonneg_of_nonpos hcoef
  cases td
  · change edgeWidth (delta C.theta B)-C.edge B 3≤0
    change 0≤C.edge B 3-edgeWidth (delta C.theta B) at hf
    linarith
  · change edgeWidth (delta C.theta T)-C.edge T 2≤0
    change 0≤C.edge T 2-edgeWidth (delta C.theta T) at hf
    linarith

theorem concave {C : SignedCycle} (ab : Fin 4) {f : Family} (td : Bool) {R M t s : ℝ}
    (hR : 0≤R) (hQ : R^2≤qCap) (hM : M≤283/200) (ht : t∈domain f)
    (hpoints : ∀ i,(C.point i).Sorted) (hcircle : ∀ i,(C.point i).Contained qCap)
    (hangles : ∀ i,|delta C.theta i|≤frameCap) :
    ConcaveOn ℝ (Icc 0 t) (value C ab f td R M t s) := by
  have hc := SolePositiveTSplitModel.concave ab td hR hQ hM ht
    (show (0:ℝ)∈Icc 0 t from ⟨le_rfl,(angle ht).1⟩) hpoints hcircle hangles
  rw [sub_zero] at hc
  refine ⟨hc.1,?_⟩
  intro x hx y hy a b ha hb hab
  have hh := hc.2 hx hy ha hb hab
  have hsum : a*adjustment C f td t s+b*adjustment C f td t s=adjustment C f td t s := by
    rw [← add_mul,hab,one_mul]
  simp only [value,smul_eq_mul] at hh ⊢
  linarith

theorem value_eq_stress {C : SignedCycle} {ab : Fin 4} {f : Family} (td : Bool)
    (R M : ℝ) {t s x : ℝ} (hab : ab=0 ∨ ab=2) (ht : t∈domain f)
    (hx : x∈Icc 0 t) (hn : C.NormalAnchors) :
    value C ab f td R M t s x=stress C ab f td R M t s x (t-x) := by
  unfold value
  rw [SolePositiveTSplitSupport.value_eq_stress td R M hab ht
    (show (0:ℝ)∈Icc 0 t from ⟨le_rfl,(angle ht).1⟩)
    (by simpa only [sub_zero] using hx) hn]
  rcases hab with rfl | rfl <;> cases f <;> cases td <;>
    simp [stress,variableDemand,fixedWork,forceData,btWeight,tdWeight,adjustment,
      SolePositiveTSplitSupport.stress,SolePositiveTSplitSupport.variableDemand,
      SolePositiveTSplitSupport.fixedWork,SolePositiveTSplitSupport.forceData,
      SolePositiveTSplitModel.btWeight,SolePositiveTSplitModel.tdWeight,mWeight,
      SoleEStress.forces,SoleEStress.weights,CoreEStress.owners,force,previous,source,
      target,word,add,scale,work,SignedCycle.edge,zeroProjection,quarterProjection,
      H,A,B,T,D,E,next,btOwner,tdOwner,deOwner,ehOwner] <;> ring

theorem necessary {C : SignedCycle} {ab : Fin 4} {f : Family} (td : Bool) {R M t s : ℝ}
    (hab : ab=0 ∨ ab=2) (hR : 0≤R) (ht : t∈domain f) (hs : s∈Icc 0 frameCap)
    (hG : 0≤delta C.theta G) (hE : 0≤ePrimary C f)
    (htotal : delta C.theta G+ePrimary C f=t)
    (hpoints : ∀ i,(C.point i).Sorted) (hcircle : ∀ i,(C.point i).Contained (R^2))
    (hn : C.NormalAnchors) (ha : (C.point E).a≤M)
    (hsign : isDE f=true → (C.point E).y≤0)
    (hf : ∀ i,C.Feasible i
      (CoreEStress.owners ab (btOwner td) (tdOwner td) (deOwner f) (ehOwner f) i)) :
    value C ab f td R M t s (delta C.theta G)≤0 := by
  have hbase := SolePositiveTSplitSupport.necessary td hab hR ht
    (show (0:ℝ)∈Icc 0 t from ⟨le_rfl,(angle ht).1⟩) hG hE
    (by simpa only [add_zero] using htotal) hpoints hcircle hn ha hsign hf
  have hprimary : if td then C.Feasible T 2 else C.Feasible B 3 := by
    cases td
    · simpa [CoreEStress.owners,btOwner,tdOwner,T,B] using hf B
    · simpa [CoreEStress.owners,btOwner,tdOwner,T,B] using hf T
  have hadj := adjustment_nonpos td ht hs hprimary
  dsimp [value]
  linarith

theorem positive_of_endpoints {C : SignedCycle} {ab : Fin 4} {f : Family} {td : Bool}
    {R M t s x : ℝ} (hconc : ConcaveOn ℝ (Icc 0 t) (value C ab f td R M t s))
    (hx : x∈Icc 0 t) (h0 : 0<value C ab f td R M t s 0)
    (h1 : 0<value C ab f td R M t s t) : 0<value C ab f td R M t s x := by
  exact (lt_min h0 h1).trans_le (hconc.min_le_of_mem_Icc
    (left_mem_Icc.mpr (hx.1.trans hx.2)) (right_mem_Icc.mpr (hx.1.trans hx.2)) hx)

end SquaresInCircles.Eight.SoleNegativeTSplit
end
end
end

section
/-!
## Coefficient domains after a negative T primary

The four unchanged pairs use the sole-E families at `z = 0` (`oldV`, `old_cap`). Only the negative
BT row uses its secant at `9/100` in a positive ordinary coefficient (`changed_B_domain`,
`changed_B_cost`); the weaker scalar enlargement to `3/10` never bounds that changed pair. The gain
slope `21/20` of the negative primary exceeds every such cost (`gain_exceeds_cost`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SoleNegativeTCoefficients
open SoleTScalarModel SolePositiveTOrdinaryData SolePositiveTCoefficients
open PositiveAngularEnvelope SingleAngleConcavity

def face (f : Family) (atG : Bool) : ScalarCase := ⟨f,true,atG,0⟩
def first (f : Family) (atG : Bool) (t : ℝ) (i : Fin 4) : ℝ :=
  SoleTScalarModel.first (face f atG) t 0 i
def second (f : Family) (atG : Bool) (t : ℝ) (i : Fin 4) : ℝ :=
  SoleTScalarModel.second (face f atG) t 0 i
def small (f : Family) (atG : Bool) (t : ℝ) (i : Fin 4) : ℝ :=
  min (first f atG t i) (second f atG t i)
def large (f : Family) (atG : Bool) (t : ℝ) (i : Fin 4) : ℝ :=
  max (first f atG t i) (second f atG t i)
def nu (f : Family) (atG : Bool) (t : ℝ) : Fin 4 → ℝ :=
  ![if isDE f then lambda f else n (face f atG) t 0,
    ell f t 0,c f t 0,max (p (face f atG) t 0) (c f t 0)]
def oldV (f : Family) (atG : Bool) (R t v : ℝ) (i : Fin 4) : ℝ :=
  Vnu R (small f atG t i) (large f atG t i) (nu f atG t i) v
def single (f : Family) (td : Bool) : Fin 4 → Bool := ![!isDE f,true,!td,true]
def gamma : Family → ℝ
  | .ehLow => 2289/4000
  | .ehMiddle => 76/125
  | .ehHigh => 619/1000
  | .deLow | .deHigh => 109/160

theorem zero_mem {f : Family} {t : ℝ} (ht : t∈domain f) : (0:ℝ)∈Icc 0 t :=
  ⟨le_rfl,(angle ht).1⟩

theorem pairs (f : Family) (atG : Bool) (t : ℝ) :
    first f atG t=![lambda f,k f t 0,ell f t 0,p (face f atG) t 0] ∧
    second f atG t=![n (face f atG) t 0,ell f t 0,c f t 0,c f t 0] := by
  have hm : m (face f atG) t 0=c f t 0 := by simp [m,face]
  refine ⟨rfl,?_⟩
  show ![n (face f atG) t 0,ell f t 0,m (face f atG) t 0,c f t 0]=_
  rw [hm]

theorem positive {f : Family} (atG : Bool) {t : ℝ} (ht : t∈domain f) (i : Fin 4) :
    0<first f atG t i ∧ 0<second f atG t i ∧ 0<small f atG t i := by
  have hh := weights_positive (face f atG) ht (zero_mem ht)
  exact ⟨hh.2.2.2.1 i,hh.2.2.2.2 i,lt_min (hh.2.2.2.1 i) (hh.2.2.2.2 i)⟩

theorem half_ratio {f : Family} (atG : Bool) {t : ℝ} (ht : t∈domain f) (i : Fin 4) :
    large f atG t i≤2*small f atG t i :=
  SolePositiveTCoefficients.half_ratio (face f atG) ht (zero_mem ht) i

theorem old_cap {f : Family} (atG : Bool) {t : ℝ} (ht : t∈domain f) (i : Fin 4) :
    large f atG t i≤(SolePositiveTCoefficients.cap f:ℝ) :=
  pair_upper (face f atG) ht (zero_mem ht) i

theorem nu_between (f : Family) (atG : Bool) (t : ℝ) (i : Fin 4) :
    small f atG t i≤nu f atG t i ∧ nu f atG t i≤large f atG t i := by
  fin_cases i <;> cases f <;>
    simp [nu,small,large,first,second,face,SoleTScalarModel.first,SoleTScalarModel.second,
      lambda,isDE,m]

theorem c_ge_ell {f : Family} (atG : Bool) {t : ℝ} (ht : t∈domain f) :
    ell f t 0≤c f t 0 := by
  simpa [face,m] using m_ge_ell (face f atG) ht (zero_mem ht)

theorem B_ratio {f : Family} (atG : Bool) {t : ℝ} (ht : t∈domain f) :
    (117/200)*c f t 0≤ell f t 0 := by
  have hh := ratio_lower (face f atG) ht (zero_mem ht) 2
  have he := c_ge_ell atG ht
  have hc := (coefficient_positive ht (zero_mem ht)).2.2.1
  have ht0 := (angle ht).1
  have hm : m (face f atG) t 0=c f t 0 := by simp [m,face]
  have h1 : SoleTScalarModel.first (face f atG) t 0 2=ell f t 0 := rfl
  have h2 : SoleTScalarModel.second (face f atG) t 0 2=c f t 0 := hm
  rw [h1,h2,max_eq_right he,min_eq_left he] at hh
  have hr : (117/200:ℝ)≤ratio (face f atG).family t 2 := by
    show (117/200:ℝ)≤ratio f t 2
    cases f <;> norm_num [ratio] <;> linarith
  have hp := mul_le_mul_of_nonneg_right hr hc.le
  linarith

theorem p_half_c {f : Family} (atG : Bool) {t : ℝ} (ht : t∈domain f) :
    p (face f atG) t 0≤2*c f t 0 := by
  have hh := half_ratio atG ht 3
  have hlo := le_max_left (p (face f atG) t 0) (c f t 0)
  have hhi := min_le_right (p (face f atG) t 0) (c f t 0)
  change max (p (face f atG) t 0) (c f t 0)≤
    2*min (p (face f atG) t 0) (c f t 0) at hh
  linarith

theorem tilt_ge_one {e ε : ℝ} (he : e∈Icc 0 (7/20:ℝ)) (hε : 1/4≤ε) :
    1≤Real.cos e+ε*Real.sin e := by
  have he' : e∈Icc 0 frameCap := ⟨he.1,by norm_num [frameCap]; linarith [he.2]⟩
  have hsin := (transport_trig he').2.2.1
  have hm := mul_le_mul_of_nonneg_right hε hsin
  have hc := Real.one_sub_sq_div_two_le_cos (x := e)
  have hs := Real.sin_ge_sub_cube he.1
  have he2 : e^2≤(7/20)*e := by nlinarith [he.1,he.2]
  have he3 : e^3≤(49/400)*e := by
    have hh := mul_le_mul_of_nonneg_right he2 he.1
    nlinarith
  linarith

theorem p_ge_one {f : Family} (atG : Bool) {t : ℝ} (ht : t∈domain f) :
    1≤p (face f atG) t 0 := by
  have hb := SolePositiveTSplitModel.bounds ht (zero_mem ht)
  by_cases he : tiltedE f=true
  · have hlen : t≤7/20 := by simpa only [sub_zero] using hb.tilted_length he
    have ht' : t∈Icc 0 (7/20:ℝ) := ⟨(angle ht).1,hlen⟩
    have he' : SoleTScalarModel.e (face f atG) t 0∈Icc 0 (7/20:ℝ) := by
      cases atG
      · simpa [SoleTScalarModel.e,face] using ht'
      · norm_num [SoleTScalarModel.e,face]
    have hh := tilt_ge_one he' (hb.tilted_epsilon he).1
    show 1≤(if tiltedE f then Real.cos (SoleTScalarModel.e (face f atG) t 0)+
      epsilon f t*Real.sin (SoleTScalarModel.e (face f atG) t 0) else 1)
    simp only [he,↓reduceIte]
    exact hh
  · show 1≤(if tiltedE f then Real.cos (SoleTScalarModel.e (face f atG) t 0)+
      epsilon f t*Real.sin (SoleTScalarModel.e (face f atG) t 0) else 1)
    have he' : tiltedE f=false := by simpa using he
    simp only [he',Bool.false_eq_true,↓reduceIte,le_refl]

theorem EH_A_bounds {f : Family} (hEH : isDE f=false) {t : ℝ}
    (ht : t∈domain f) : k f t 0+ell f t 0≤2 ∧ 11*k f t 0+ell f t 0≤12 := by
  have ht' := angle ht
  cases f <;> norm_num [isDE] at hEH <;>
    norm_num [domain,left,right] at ht <;> dsimp [k,ell,K,L] <;>
    constructor <;> nlinarith [ht.1,ht.2,sq_nonneg t,sq_nonneg (t-1/5),
      mul_nonneg (show 0≤t by linarith [ht'.1])
        (show 0≤7/10-t by linarith [ht'.2])]

theorem middle_base {t : ℝ} (ht : t∈domain .ehMiddle) :
    983/1000≤k .ehMiddle t 0 ∧ 209/200≤c .ehMiddle t 0 ∧
      ell .ehMiddle t 0≤k .ehMiddle t 0 ∧
      (2/3)*k .ehMiddle t 0≤ell .ehMiddle t 0 ∧
      (2/3)*c .ehMiddle t 0≤ell .ehMiddle t 0 := by
  have hw : t-1/5∈Icc 0 (3/20:ℝ) := by
    norm_num [domain,left,right] at ht
    constructor <;> linarith [ht.1,ht.2]
  have hw2 : (t-1/5)^2≤(3/20)*(t-1/5) := by nlinarith [hw.1,hw.2]
  dsimp [k,ell,c,K,L,C]
  refine ⟨?_,?_,?_,?_,?_⟩ <;> nlinarith [hw.1,hw.2,sq_nonneg (t-1/5)]

theorem middle_sorted (atG : Bool) {t : ℝ} (ht : t∈domain .ehMiddle) :
    p (face .ehMiddle atG) t 0≤c .ehMiddle t 0 ∧
      p (face .ehMiddle atG) t 0≤53/50 := by
  have ht' : t∈Icc (1/5:ℝ) (7/20) := by
    have h := ht
    norm_num [domain,left,right] at h
    exact h
  have hε : epsilon .ehMiddle t∈Icc 0 (349/1000:ℝ) := by
    dsimp [epsilon]
    constructor <;> linarith [ht'.1,ht'.2]
  have hp0 := (weights_positive (face .ehMiddle atG) ht (zero_mem ht)).2.2.1
  have hpdef : p (face .ehMiddle atG) t 0=Real.cos (SoleTScalarModel.e (face .ehMiddle atG) t 0)+
      epsilon .ehMiddle t*Real.sin (SoleTScalarModel.e (face .ehMiddle atG) t 0) := by
    simp [p,face,tiltedE]
  have hpSquare : (p (face .ehMiddle atG) t 0)^2≤1+(epsilon .ehMiddle t)^2 := by
    have hh := sq_nonneg (epsilon .ehMiddle t*Real.cos (SoleTScalarModel.e (face .ehMiddle atG) t 0)-
      Real.sin (SoleTScalarModel.e (face .ehMiddle atG) t 0))
    have htrig := Real.sin_sq_add_cos_sq (SoleTScalarModel.e (face .ehMiddle atG) t 0)
    rw [hpdef]
    nlinarith
  have hpUpper : p (face .ehMiddle atG) t 0≤53/50 := by
    have hε2 := pow_le_pow_left₀ hε.1 hε.2 2
    nlinarith
  refine ⟨?_,hpUpper⟩
  rw [hpdef]
  cases atG
  · have hc := cos_upper_four (show 0≤t by linarith [ht'.1])
    have hs := mul_le_mul_of_nonneg_left (Real.sin_le (by linarith [ht'.1] : 0≤t)) hε.1
    have ht2 : t^2≤49/400 := by nlinarith [ht'.1,ht'.2]
    have ht4 := mul_le_mul_of_nonneg_right ht2 (sq_nonneg t)
    have hinterval := mul_nonneg (sub_nonneg.mpr ht'.1) (sub_nonneg.mpr ht'.2)
    have hev : SoleTScalarModel.e (face .ehMiddle false) t 0=t := by simp [SoleTScalarModel.e,face]
    rw [hev]
    dsimp [c,C,epsilon]
    dsimp [epsilon] at hs
    nlinarith
  · have hc := (middle_base ht).2.1
    have hev : SoleTScalarModel.e (face .ehMiddle true) t 0=0 := by simp [SoleTScalarModel.e,face]
    rw [hev]
    simp only [Real.cos_zero,Real.sin_zero,mul_zero,add_zero]
    linarith

theorem correction_domain {f : Family} (atG : Bool) {t : ℝ}
    (ht : t∈domain f) (hf : f=.ehMiddle ∨ f=.ehHigh) :
    p (face f atG) t 0≤c f t 0 ∧
      Real.sqrt ((p (face f atG) t 0)^2+(c f t 0)^2)≤307/200 := by
  have hp0 := (weights_positive (face f atG) ht (zero_mem ht)).2.2.1
  have hc0 := (coefficient_positive ht (zero_mem ht)).2.2.1
  have hroot : (307/200:ℝ)=Real.sqrt ((307/200)^2) := by
    rw [Real.sqrt_sq]; norm_num
  rcases hf with rfl | rfl
  · have hp := middle_sorted atG ht
    have hh := old_cap atG ht 3
    have hmax := le_max_right (p (face .ehMiddle atG) t 0) (c .ehMiddle t 0)
    have hpr := pairs .ehMiddle atG t
    simp only [large,hpr.1,hpr.2] at hh
    have hcap' : (cap .ehMiddle:ℝ)=111/100 := by norm_num [cap]
    rw [hcap'] at hh
    have hh' : max (p (face .ehMiddle atG) t 0) (c .ehMiddle t 0)≤111/100 := hh
    have hc : c .ehMiddle t 0≤111/100 := hmax.trans hh'
    have hp2 := pow_le_pow_left₀ hp0.le hp.2 2
    have hc2 := pow_le_pow_left₀ hc0.le hc 2
    refine ⟨hp.1,?_⟩
    rw [hroot]
    exact Real.sqrt_le_sqrt (by linarith)
  · have hpv : p (face .ehHigh atG) t 0=1 := by simp [p,face,tiltedE]
    have hcv : c .ehHigh t 0=113/100 := by simp [c,C]
    rw [hpv,hcv,hroot]
    exact ⟨by norm_num,Real.sqrt_le_sqrt (by norm_num)⟩

theorem secant_upper {s : ℝ} (hs : s∈Icc 0 (9/100:ℝ)) :
    1/Real.cos s≤20000/19919 := by
  have hs2 : s^2≤81/10000 := by nlinarith [hs.1,hs.2]
  have hc : (19919/20000:ℝ)≤Real.cos s := by
    linarith [Real.one_sub_sq_div_two_le_cos (x := s)]
  have hcp : 0<Real.cos s := by linarith
  apply (div_le_iff₀ hcp).2
  linarith

theorem changed_B_domain {f : Family} (atG : Bool) {t s : ℝ}
    (ht : t∈domain f) (hs : s∈Icc 0 (9/100:ℝ)) :
    0<ell f t 0 ∧ ell f t 0≤c f t 0/Real.cos s ∧
      c f t 0/Real.cos s≤2*ell f t 0 := by
  obtain ⟨hk,hl,hc,_,_,_⟩ := coefficient_positive ht (zero_mem ht)
  have hs' : s∈Icc 0 frameCap := ⟨hs.1,by norm_num [frameCap]; linarith [hs.2]⟩
  have hcos : 0<Real.cos s := by linarith [(transport_trig hs').1]
  have hsec := SoleNegativeTSplit.secant_nonneg hs'
  have he : c f t 0/Real.cos s=c f t 0*(1/Real.cos s) := by ring
  have hcsec : c f t 0≤c f t 0/Real.cos s := by
    have hh := mul_nonneg hc.le hsec.2
    rw [he]
    linarith
  have hu := mul_le_mul_of_nonneg_left (secant_upper hs) hc.le
  have hr := B_ratio atG ht
  exact ⟨hl,(c_ge_ell atG ht).trans hcsec,by rw [he]; linarith⟩

theorem gain_exceeds_cost {f : Family} {t : ℝ} (ht : t∈domain f) :
    gamma f<(21/20)*c f t 0 := by
  cases f <;> norm_num [domain,left,right] at ht <;> dsimp [gamma,c,C,K] <;>
    nlinarith [ht.1,ht.2,sq_nonneg t,sq_nonneg (t-1/5),
      mul_nonneg (sub_nonneg.mpr ht.1) (sub_nonneg.mpr ht.2)]

def cUpper : Family → ℝ
  | .ehLow => 209/200
  | .ehMiddle => 111/100
  | .ehHigh | .deHigh => 113/100
  | .deLow => 1131/1000

theorem c_upper {f : Family} {t : ℝ} (ht : t∈domain f) : c f t 0≤cUpper f := by
  cases f <;> norm_num [domain,left,right] at ht <;> dsimp [cUpper,c,C,K] <;>
    nlinarith [ht.1,ht.2,sq_nonneg t,sq_nonneg (t-1/5),
      mul_nonneg (sub_nonneg.mpr ht.1) (sub_nonneg.mpr ht.2)]

theorem old_cost {f : Family} (atG : Bool) {t : ℝ}
    (ht : t∈domain f) (i : Fin 4) : (109/200)*large f atG t i≤gamma f := by
  have hh := mul_le_mul_of_nonneg_left (old_cap atG ht i)
    (by norm_num : (0:ℝ)≤109/200)
  cases f <;> norm_num [cap,gamma] at hh ⊢ <;> linarith

theorem changed_B_cost {f : Family} {t s : ℝ}
    (ht : t∈domain f) (hs : s∈Icc 0 (9/100:ℝ)) :
    (109/200)*(c f t 0/Real.cos s)≤gamma f := by
  have hc := (coefficient_positive ht (zero_mem ht)).2.2.1
  have hs' : s∈Icc 0 frameCap := ⟨hs.1,by norm_num [frameCap]; linarith [hs.2]⟩
  have hcU := c_upper ht
  have hu := mul_le_mul hcU (secant_upper hs)
    (SoleNegativeTSplit.secant_nonneg hs').1.le
    (show 0≤cUpper f by cases f <;> norm_num [cUpper])
  have he : c f t 0*(1/Real.cos s)=c f t 0/Real.cos s := by ring
  rw [he] at hu
  cases f <;> norm_num [cUpper,gamma] at hu ⊢ <;> linarith

theorem D_linear_cost {f : Family} (atG : Bool) {t : ℝ}
    (ht : t∈domain f) : (2/5)*p (face f atG) t 0≤gamma f := by
  have hh := old_cap atG ht 3
  have hp := le_max_left (p (face f atG) t 0) (c f t 0)
  change max (p (face f atG) t 0) (c f t 0)≤(cap f:ℝ) at hh
  have hpu : p (face f atG) t 0≤(cap f:ℝ) := hp.trans hh
  cases f <;> norm_num [cap,gamma] at hpu ⊢ <;> linarith

theorem D_full_cost {f : Family} (atG : Bool) {t : ℝ}
    (ht : t∈domain f) : (109/200)*p (face f atG) t 0≤gamma f := by
  have hh := old_cost atG ht 3
  have hp := mul_le_mul_of_nonneg_left
    (le_max_left (p (face f atG) t 0) (c f t 0))
    (by norm_num : (0:ℝ)≤109/200)
  change (109/200)*max (p (face f atG) t 0) (c f t 0)≤gamma f at hh
  exact hp.trans hh

end SquaresInCircles.Eight.SoleNegativeTCoefficients
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SoleNegativeTGrowth
open SoleTScalarModel SoleNegativeTCoefficients SolePositiveTCoefficients
open PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryNegativeEnvelope
open SingleAngleConcavity SolePositiveTGrowth

theorem old_concave {f : Family} (atG : Bool) {R t : ℝ}
    (hR : 0≤R) (hQ : R^2≤qCap) (ht : t∈domain f) (i : Fin 4) :
    ConcaveOn ℝ (Icc 0 frameCap) (fun v => oldV f atG R t v i) := by
  exact Vnu_concave hR hQ (positive atG ht i).2.2 min_le_max
    (SoleNegativeTCoefficients.half_ratio atG ht i)
    (SoleNegativeTCoefficients.nu_between f atG t i).1

theorem zero (f : Family) (atG : Bool) (R t : ℝ) (i : Fin 4) :
    oldV f atG R t 0 i=0 := by simp [oldV]

theorem chord {f : Family} (atG : Bool) {R t : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (ht : t∈domain f) (i : Fin 4) :
    gamma f*(frameCap-t)≤oldV f atG R t frameCap i-oldV f atG R t t i := by
  have hp := (positive atG ht i).2.2
  have hpq : small f atG t i≤large f atG t i := min_le_max
  have hq := hp.trans_le hpq
  have hnu := (SoleNegativeTCoefficients.nu_between f atG t i).2
  have hr := ratio_lower (face f atG) ht (zero_mem ht) i
  change ratio f t i*large f atG t i≤ small f atG t i at hr
  have hlo := larger_lower (face f atG) ht (zero_mem ht) i
  change (largeFloor f:ℝ)≤large f atG t i at hlo
  have hsmall := smaller_lower (face f atG) ht (zero_mem ht) i
  change (smallFloor f:ℝ)≤ small f atG t i at hsmall
  have ht' := angle ht
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have hlen : 0≤frameCap-t := by linarith [ht'.2]
  change _≤Vnu R (small f atG t i) (large f atG t i) (nu f atG t i) frameCap-
    Vnu R (small f atG t i) (large f atG t i) (nu f atG t i) t
  cases f
  · have hratio : (117/200)*large .ehLow atG t i≤ small .ehLow atG t i := by
      simp only [ratio] at hr
      nlinarith [mul_nonneg ht'.1 hq.le]
    have htg : t∈Icc 0 (1/5:ℝ) := by simpa [domain,left,right] using ht
    have hfloor : 431/500≤large .ehLow atG t i := by simpa [largeFloor] using hlo
    have hg := low_growth hR hQL hp hpq hratio hfloor hnu htg
    have hc : gamma .ehLow≤121/200 := by norm_num [gamma]
    exact (mul_le_mul_of_nonneg_right hc hlen).trans hg
  · have hratio : (13/20)*large .ehMiddle atG t i≤ small .ehMiddle atG t i := by
      simpa [ratio] using hr
    have htg : t∈Icc 0 (7/20:ℝ) := by
      have hu := ht.2
      norm_num [domain,right] at hu
      exact ⟨ht'.1,hu⟩
    have hfloor : 923/1000≤large .ehMiddle atG t i := by simpa [largeFloor] using hlo
    have hg := middle_growth hR hQL hp hpq hratio hfloor hnu htg
    have hc : gamma .ehMiddle≤7/10 := by norm_num [gamma]
    exact (mul_le_mul_of_nonneg_right hc hlen).trans hg
  · have hratio : (18/25)*large .ehHigh atG t i≤ small .ehHigh atG t i := by
      simpa [ratio] using hr
    have hg := high_growth hR hQL hQU hp hpq hratio hnu ht' hh ht'.2
    have hc : gamma .ehHigh≤ small .ehHigh atG t i := by
      norm_num [smallFloor] at hsmall
      norm_num [gamma]
      linarith
    exact (mul_le_mul_of_nonneg_right hc hlen).trans hg
  · have htg : t∈Icc 0 (7/20:ℝ) := by simpa [domain,left,right] using ht
    by_cases hA : i=1
    · subst i
      obtain ⟨hs,hl,hn,hrA⟩ := SolePositiveTOrdinaryData.DE_A_data (face .deLow atG)
        (by simp [face]) ht (zero_mem ht)
      have hd := de_A (face .deLow atG) (by simp [face]) ht (zero_mem ht)
      change small .deLow atG t 1=ell .deLow t 0 at hs
      change large .deLow atG t 1=k .deLow t 0 at hl
      change (113/200:ℝ)≤ell .deLow t 0 ∧ ell .deLow t 0≤(81/100)*k .deLow t 0 at hd
      change ell .deLow t 0/k .deLow t 0∈Icc (533/1000:ℝ) (81/100) at hrA
      have hpq' : ell .deLow t 0≤k .deLow t 0 := by rw [← hs,← hl]; exact hpq
      have hg := DE_A_growth hR hQL hQU hd.1 hpq' hrA ht'
      have hnu1 : nu .deLow atG t 1=ell .deLow t 0 := rfl
      rw [hs,hl,hnu1]
      have hc : gamma .deLow≤18/25 := by norm_num [gamma]
      exact (mul_le_mul_of_nonneg_right hc hlen).trans hg
    · by_cases hB : i=2
      · subst i
        have hratio : (5/8+27/100*t)*large .deLow atG t 2≤ small .deLow atG t 2 := by
          simpa [ratio] using hr
        have hfloor := SolePositiveTOrdinaryData.DE_B_large (face .deLow atG)
          (by simp [face]) ht (zero_mem ht)
        change 903/1000≤large .deLow atG t 2 at hfloor
        have hg := SolePositiveTDEChord.growth hR hQL hp hpq hratio hfloor hnu htg
        have hc : gamma .deLow≤7/10 := by norm_num [gamma]
        exact (mul_le_mul_of_nonneg_right hc hlen).trans hg
      · have hi : i=0 ∨ i=3 := by fin_cases i <;> simp_all
        have hratio : (18/25)*large .deLow atG t i≤ small .deLow atG t i := by
          simpa [ratio,hA,hB] using hr
        have hg := high_growth hR hQL hQU hp hpq hratio hnu ht' hh ht'.2
        have hsmall' := SolePositiveTOrdinaryData.DE_outer_small (face .deLow atG)
          (by simp [face]) ht (zero_mem ht) i hi
        change 18/25≤ small .deLow atG t i at hsmall'
        have hc : gamma .deLow≤ small .deLow atG t i := by norm_num [gamma]; linarith
        exact (mul_le_mul_of_nonneg_right hc hlen).trans hg
  · have hratio : (18/25)*large .deHigh atG t i≤ small .deHigh atG t i := by
      simpa [ratio] using hr
    have hg := high_growth hR hQL hQU hp hpq hratio hnu ht' hh ht'.2
    have hc : gamma .deHigh≤ small .deHigh atG t i := by
      norm_num [smallFloor] at hsmall
      norm_num [gamma]
      linarith
    exact (mul_le_mul_of_nonneg_right hc hlen).trans hg

/-- The equal-length secant is larger after shifting left. The proof
integrates the difference of the two actual derivatives. -/
theorem shifted_secant {R p q ν a b s : ℝ}
    (hR : 0≤R) (hQ : R^2≤qCap) (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p)
    (hν : p≤ν) (hs : 0≤ s) (ha : a∈Icc s frameCap) (hb : b∈Icc s frameCap)
    (hab : a≤b) :
    Vnu R p q ν b-Vnu R p q ν a≤
      Vnu R p q ν (b-s)-Vnu R p q ν (a-s) := by
  have hx (x : ℝ) (hxx : x∈Icc s frameCap) :
      x∈Icc 0 frameCap ∧ x-s∈Icc 0 frameCap :=
    ⟨⟨hs.trans hxx.1,hxx.2⟩,⟨by linarith [hxx.1],by linarith [hxx.2]⟩⟩
  have hd (x : ℝ) (hxx : x∈Icc s frameCap) :
      HasDerivAt (fun x => Vnu R p q ν (x-s)-Vnu R p q ν x)
        (VnuDeriv R p q ν (x-s)-VnuDeriv R p q ν x) x := by
    have hfirst : HasDerivAt (fun x => Vnu R p q ν (x-s)) (VnuDeriv R p q ν (x-s)) x :=
      HasDerivAt.comp_sub_const x s
        (Vnu_hasDerivAt (R := R) (nu := ν) hp (hp.trans_le hpq) (hx x hxx).2)
    exact hfirst.fun_sub
      (Vnu_hasDerivAt (R := R) (nu := ν) hp (hp.trans_le hpq) (hx x hxx).1)
  have hm : MonotoneOn (fun x => Vnu R p q ν (x-s)-Vnu R p q ν x) (Icc s frameCap) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun x hxx => (hd x hxx).continuousAt.continuousWithinAt
    · exact fun x hxx => hd x (Ioo_subset_Icc_self hxx)
    · intro x hxx
      have hxx' := hx x (Ioo_subset_Icc_self hxx)
      exact sub_nonneg.mpr
        ((VnuDeriv_antitone hR hQ hp hpq hqp hν) hxx'.2 hxx'.1 (by linarith))
  have hh := hm ha hb hab
  simp only at hh
  linarith

theorem shifted_chord {f : Family} (atG : Bool) {R t s : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (ht : t∈domain f) (hs : s∈Icc 0 t) (i : Fin 4) :
    gamma f*(frameCap-t)≤oldV f atG R t (frameCap-s) i-oldV f atG R t (t-s) i := by
  have hshift := shifted_secant hR hQU (positive atG ht i).2.2 min_le_max
    (SoleNegativeTCoefficients.half_ratio atG ht i)
    (SoleNegativeTCoefficients.nu_between f atG t i).1 hs.1
    ⟨hs.2,(angle ht).2⟩ ⟨hs.2.trans (angle ht).2,le_rfl⟩ (angle ht).2
  exact (chord atG hR hQL hQU ht i).trans hshift

theorem linear_coefficient {f : Family} (atG : Bool) {t : ℝ}
    (ht : t∈domain f) (i : Fin 4) : gamma f≤(87/70)*small f atG t i := by
  have hr := ratio_lower (face f atG) ht (zero_mem ht) i
  change ratio f t i*large f atG t i≤ small f atG t i at hr
  have hlo := larger_lower (face f atG) ht (zero_mem ht) i
  change (largeFloor f:ℝ)≤large f atG t i at hlo
  have hsmall := smaller_lower (face f atG) ht (zero_mem ht) i
  change (smallFloor f:ℝ)≤ small f atG t i at hsmall
  have hq := (positive atG ht i).2.2.trans_le (min_le_max : small f atG t i≤large f atG t i)
  have ht0 := (angle ht).1
  cases f
  · norm_num [ratio,largeFloor,gamma] at hr hlo ⊢
    nlinarith [mul_nonneg ht0 hq.le]
  · norm_num [ratio,largeFloor,gamma] at hr hlo ⊢
    linarith
  · norm_num [smallFloor,gamma] at hsmall ⊢
    linarith
  · by_cases hA : i=1
    · subst i
      have hd := de_A (face .deLow atG) (by simp [face]) ht (zero_mem ht)
      obtain ⟨hs,hl,hn,hra⟩ := SolePositiveTOrdinaryData.DE_A_data (face .deLow atG)
        (by simp [face]) ht (zero_mem ht)
      change small .deLow atG t 1=ell .deLow t 0 at hs
      change (113/200:ℝ)≤ell .deLow t 0 ∧ ell .deLow t 0≤(81/100)*k .deLow t 0 at hd
      rw [hs]
      norm_num [gamma]
      linarith [hd.1]
    · by_cases hB : i=2
      · subst i
        have hb := SolePositiveTOrdinaryData.DE_B_large (face .deLow atG)
          (by simp [face]) ht (zero_mem ht)
        change 903/1000≤large .deLow atG t 2 at hb
        norm_num [ratio,gamma] at hr ⊢
        nlinarith [mul_nonneg ht0 hq.le]
      · have hi : i=0 ∨ i=3 := by fin_cases i <;> simp_all
        have hh := SolePositiveTOrdinaryData.DE_outer_small (face .deLow atG)
          (by simp [face]) ht (zero_mem ht) i hi
        change 18/25≤ small .deLow atG t i at hh
        norm_num [gamma]
        linarith
  · norm_num [smallFloor,gamma] at hsmall ⊢
    linarith

theorem radius_chord {R p q ν v : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p) (hν : p≤ν) (hνq : ν≤q)
    (hv : v∈Icc 0 frameCap) : (87/70)*p*v≤Vnu R p q ν v := by
  have hh : 0<frameCap := by norm_num [frameCap]
  have hα : 0≤v/frameCap ∧ v/frameCap≤1 :=
    ⟨div_nonneg hv.1 hh.le,(div_le_one hh).2 hv.2⟩
  have hc := Vnu_concave hR hQU hp hpq hqp hν
  have hch := hc.2 ⟨le_rfl,hh.le⟩ ⟨hh.le,le_rfl⟩
    (sub_nonneg.mpr hα.2) hα.1 (by ring)
  have he : v/frameCap*frameCap=v := div_mul_cancel₀ v hh.ne'
  simp only [smul_eq_mul,Vnu_zero,mul_zero,zero_add,he] at hch
  have hend := (V_endpoint_lower (SoleAngleGrowth.radius_lower hR hQL) hp hpq hqp).le.trans
    (Vnu_ge_V hνq)
  have hm := mul_le_mul_of_nonneg_left hend hα.1
  have hid : (v/frameCap)*((87/100)*p)=(87/70)*p*v := by simp only [frameCap]; ring
  rw [hid] at hm
  exact hm.trans hch

theorem linear_lower {f : Family} (atG : Bool) {R t v : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (ht : t∈domain f) (hv : v∈Icc 0 frameCap) (i : Fin 4) :
    gamma f*v≤oldV f atG R t v i := by
  have hbound := radius_chord hR hQL hQU (positive atG ht i).2.2 min_le_max
    (SoleNegativeTCoefficients.half_ratio atG ht i)
    (SoleNegativeTCoefficients.nu_between f atG t i).1
    (SoleNegativeTCoefficients.nu_between f atG t i).2 hv
  exact (mul_le_mul_of_nonneg_right (linear_coefficient atG ht i) hv.1).trans hbound

end SquaresInCircles.Eight.SoleNegativeTGrowth
end
end
end

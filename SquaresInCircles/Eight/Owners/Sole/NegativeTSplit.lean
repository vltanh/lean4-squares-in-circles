module

public import SquaresInCircles.Eight.Owners.Sole.PositiveTSplitSupport

/-!
# Eight squares: splitting at fixed coordinates with the negative-T secant

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

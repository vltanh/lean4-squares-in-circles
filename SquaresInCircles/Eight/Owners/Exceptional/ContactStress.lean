module

public import SquaresInCircles.Eight.Owners.Exceptional.ContactCurvature
public import SquaresInCircles.Eight.Owners.Sole.SplitModel

/-!
# Eight squares: the stress at the exceptional positive E contact

The stress `value` is taken at fixed coordinates: the ordinary angles and the four anchor points
are those of the cycle. The EH0 contact (`Contact`) may have a nonzero signed error; its equality
cancels the varying EH multiplier exactly, with no alignment of the anchor points. The weak owners
and the contact make the stress nonpositive (`necessary`), and it is concave in the G/E split
(`concave`). The same expression serves the rational weights outside the critical strip and the
supporting weights of the sharp family.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.ExceptionalContactStress
open Candidate SignedStress SoleResiduals SecondaryEStress ActualCoreEBlocks

def tilt (eta x : ℝ) : ℝ := Real.cos x+eta*Real.sin x

def Contact (C : SignedCycle) : Prop :=
  edgeWidth (delta C.theta E)=(C.point H).a*Real.cos (delta C.theta E)+
    (C.point H).y*Real.sin (delta C.theta E)+(C.point E).y

def constant (C : SignedCycle) (ab : Fin 4) (k l c : ℝ) : ℝ :=
  l*(edgeWidth (delta C.theta A)-C.edge A ab)+
    c*(edgeWidth (delta C.theta B)-C.edge B 2)+
    c*(edgeWidth (delta C.theta T)-C.edge T 0)-k*(C.point A).a-(C.point D).a

def forces (C : SignedCycle) (ab : Fin 4) (k l c eta x e : ℝ) : Vertex → Point :=
  SoleEStress.forces C ab 2 0 3 0 (k*tilt eta x) k l c c 1 (tilt eta e)

def variableDemand (C : SignedCycle) (k l c eta x e : ℝ) : ℝ :=
  k*tilt eta x*edgeWidth (delta C.theta H)+k*edgeWidth x+
    l*edgeWidth (delta C.theta A)+c*edgeWidth (delta C.theta B)+
    c*edgeWidth (delta C.theta T)+edgeWidth e+tilt eta e*edgeWidth (delta C.theta E)

def anchorWork (C : SignedCycle) (ab : Fin 4) (k l c eta x e : ℝ) : ℝ :=
  work (forces C ab k l c eta x e H) (C.point H)+
    work (forces C ab k l c eta x e A) (C.point A)+
    work (forces C ab k l c eta x e B) (C.point B)+
    work (forces C ab k l c eta x e D) (C.point D)

def eWork (C : SignedCycle) (eta e : ℝ) : ℝ :=
  Real.sin e*((C.point E).a+eta*(C.point E).y)

def stress (C : SignedCycle) (ab : Fin 4) (R k l c eta x e : ℝ) : ℝ :=
  variableDemand C k l c eta x e-anchorWork C ab k l c eta x e-
    k*sigma R eta*Real.sin x-eWork C eta e

def value (C : SignedCycle) (ab : Fin 4) (R k l c eta t x : ℝ) : ℝ :=
  SoleFixedSplit.high (constant C ab k l c+(C.point E).y) (SoleSplitModel.transverse C)
    k eta (sigma R eta) (C.point E).a (C.point E).y t x

theorem tilt_nonneg {eta x : ℝ} (heta : 0≤eta) (hx : x∈Icc 0 frameCap) :
    0≤tilt eta x := by
  obtain ⟨hc,_,hs,_,_⟩ := transport_trig hx
  dsimp [tilt]
  nlinarith [mul_nonneg heta hs]

theorem value_eq_stress {C : SignedCycle} {ab : Fin 4} (R k l c eta : ℝ) {t x : ℝ}
    (hab : ab=0 ∨ ab=2) (ht : t∈Icc 0 frameCap) (hx : x∈Icc 0 t)
    (hn : C.NormalAnchors) (hcontact : Contact C) :
    value C ab R k l c eta t x=stress C ab R k l c eta x (t-x) := by
  have hx' : x∈Icc 0 frameCap := ⟨hx.1,hx.2.trans ht.2⟩
  have he : t-x∈Icc 0 frameCap := ⟨by linarith [hx.2],by linarith [ht.2,hx.1]⟩
  have hH := hn.H_nonneg
  dsimp [Contact] at hcontact
  rw [value,SoleFixedSplit.high_formula]
  rcases hab with rfl | rfl <;>
    simp [stress,variableDemand,anchorWork,eWork,constant,SoleSplitModel.transverse,
      forces,SoleEStress.forces,SoleEStress.weights,CoreEStress.owners,force,previous,
      source,target,word,add,scale,work,SignedCycle.edge,zeroProjection,quarterProjection,
      H,A,B,T,D,E,next,tilt,edgeWidth_positive_formula hx',
      edgeWidth_positive_formula he] at hcontact hH ⊢ <;>
    rw [abs_of_nonneg hH] <;>
    linear_combination (-(Real.cos (t-x)+eta*Real.sin (t-x)))*hcontact

theorem original_demand (C : SignedCycle) (k l c eta : ℝ) :
    variableDemand C k l c eta (delta C.theta G) (delta C.theta D)=
      demand C (SoleEStress.weights (k*tilt eta (delta C.theta G)) k l c c 1
        (tilt eta (delta C.theta D))) := by
  rw [SoleEStress.demand_eq]
  simp [variableDemand]

theorem E_work (C : SignedCycle) (ab : Fin 4) (k l c eta x : ℝ) :
    work (forces C ab k l c eta x (delta C.theta D) E) (C.point E)=
      eWork C eta (delta C.theta D) := by
  unfold forces
  rw [SoleEStress.force_E (Or.inr rfl) (Or.inl rfl)]
  simp [primaryDE,primaryEH,tilt,work,eWork]
  ring

theorem T_force (C : SignedCycle) (ab : Fin 4) (k l c eta x e : ℝ) :
    forces C ab k l c eta x e T=(0,0) := by
  unfold forces
  rw [SoleEStress.force_T,force_T_secondary]
  simp

theorem G_work_le {C : SignedCycle} (ab : Fin 4) {R k eta : ℝ} (l c e : ℝ)
    (hR : 0≤R) (hk : 0≤k) (heta : 0≤eta)
    (hx : delta C.theta G∈Icc 0 frameCap)
    (hs : (C.point G).Sorted) (hc : (C.point G).Contained (R^2)) :
    work (forces C ab k l c eta (delta C.theta G) e G) (C.point G)≤
      k*sigma R eta*Real.sin (delta C.theta G) := by
  have hh := work_le_circleSupport hR hs hc (forces C ab k l c eta (delta C.theta G) e G)
  have hf : forces C ab k l c eta (delta C.theta G) e G=
      SecondaryEStress.forces C ab 2 0 (tiltedWeight k eta (delta C.theta G)) k l c c G := by
    unfold forces; rw [SoleEStress.force_G]; rfl
  have hsup := positive_G_support (R := R) (ab := ab) (bt := 2) (td := 0)
    (l := l) (b := c) (t := c) hk heta hx
  rw [hf] at hh ⊢
  rw [hsup] at hh
  refine hh.trans (le_of_eq ?_)
  unfold primarySupport sigma
  ring

/-- The seven weak owners and the EH contact make the stress nonpositive; no separate support of E
is used and no point moves. -/
theorem necessary {C : SignedCycle} {ab : Fin 4} {R k l c eta t : ℝ}
    (hab : ab=0 ∨ ab=2) (hR : 0≤R) (hk : 0≤k) (hl : 0≤l) (hc0 : 0≤c)
    (heta : 0≤eta) (ht : t∈Icc 0 frameCap)
    (hG : 0≤delta C.theta G) (hD : 0≤delta C.theta D)
    (htotal : delta C.theta G+delta C.theta D=t)
    (hs : ∀ i,(C.point i).Sorted) (hc : ∀ i,(C.point i).Contained (R^2))
    (hn : C.NormalAnchors) (hcontact : Contact C)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 2 0 3 0 i)) :
    value C ab R k l c eta t (delta C.theta G)≤0 := by
  let x := delta C.theta G
  let e := delta C.theta D
  have hx : x∈Icc 0 t := ⟨hG,by dsimp [x,e] at *; linarith⟩
  have he : e∈Icc 0 t := ⟨hD,by dsimp [x,e] at *; linarith⟩
  have hx' : x∈Icc 0 frameCap := ⟨hx.1,hx.2.trans ht.2⟩
  have he' : e∈Icc 0 frameCap := ⟨he.1,he.2.trans ht.2⟩
  have hxe : t-x=e := by dsimp [x,e]; linarith
  have hn0 := mul_nonneg hk (tilt_nonneg heta hx')
  have hp0 := tilt_nonneg heta he'
  have hw : ∀ i,0≤SoleEStress.weights (k*tilt eta x) k l c c 1 (tilt eta e) i := by
    intro i
    fin_cases i <;> simp [SoleEStress.weights,hn0,hk,hl,hc0,hp0]
  let Bnd : Vertex → ℝ := ![
    work (forces C ab k l c eta x e H) (C.point H),k*sigma R eta*Real.sin x,
    work (forces C ab k l c eta x e A) (C.point A),
    work (forces C ab k l c eta x e B) (C.point B),0,
    work (forces C ab k l c eta x e D) (C.point D),eWork C eta e]
  have hb : ∀ i,work (forces C ab k l c eta x e i) (C.point i)≤Bnd i := by
    intro i
    fin_cases i
    · exact le_rfl
    · exact G_work_le ab l c e hR hk heta hx' (hs G) (hc G)
    · exact le_rfl
    · exact le_rfl
    · show work (forces C ab k l c eta x e T) (C.point T)≤Bnd T
      rw [T_force]; simp [work,Bnd,T]
    · exact le_rfl
    · exact (E_work C ab k l c eta x).le
  have hsep := weighted_separation_le hw hf hb
  rw [value_eq_stress R k l c eta hab ht hx hn hcontact,hxe]
  change stress C ab R k l c eta x e≤0
  have hd : variableDemand C k l c eta x e=
      demand C (SoleEStress.weights (k*tilt eta x) k l c c 1 (tilt eta e)) :=
    original_demand C k l c eta
  dsimp only [stress]
  rw [hd]
  simp only [Bnd,Fin.sum_univ_seven,Matrix.cons_val] at hsep
  dsimp only [anchorWork]
  linarith

theorem concave {C : SignedCycle} (ab : Fin 4) {R k l c eta t : ℝ}
    (hR : 0≤R) (hQU : R^2≤qCap) (hk : k∈Icc (431/500:ℝ) 1)
    (heta : eta∈Icc (1/4:ℝ) (327/1000)) (ht : t∈Icc 0 frameCap)
    (hs : ∀ i,(C.point i).Sorted) (hc : ∀ i,(C.point i).Contained qCap)
    (ha : ∀ i,|delta C.theta i|≤frameCap) (hEy : 0≤(C.point E).y) :
    ConcaveOn ℝ (Icc 0 t) (value C ab R k l c eta t) := by
  apply ExceptionalContactCurvature.concave
    (transverse_residual (hs H) (hc H) (ha H)).le hk
    ⟨by linarith [heta.1],heta.2⟩
    (tilt_reserve hR hQU ⟨heta.1,by linarith [heta.2]⟩).le
    (contained_bounds (hs E) (hc E)).1.le hEy ht

end SquaresInCircles.Eight.ExceptionalContactStress

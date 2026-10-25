module

public import SquaresInCircles.Eight.GeometricModel.Basic
public import SquaresInCircles.Eight.TableFree.SignedCoordinates

/-!
# Original centers map directly into the geometric five-corner problem

Uncompiled draft. Once the original physical frames and retained signed
separators have been recovered, the lower bound follows from the definition
of the geometric infimum. No stationary force weights, capture theorem,
terminal theorem, or generated bound is imported.

The five residual identities also pull equality back to the original
anchors and contact gaps. This is an alternative to the weighted dual,
not an assumption that moved intermediate squares equal their ancestors.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree
namespace OriginalFiveCorner
open GeometricModel

/-- The original exterior order remains H,G,A,B,T,D,E. -/
def anchorIndex : Fin 5 → Vertex := ![2,3,5,6,0]

def frameCos (t : ℝ) : Vertex → ℝ :=
  ![Real.sin t,Real.sin t,1,1,0,0,-1]

def frameSin (t : ℝ) : Vertex → ℝ :=
  ![-Real.cos t,-Real.cos t,0,0,1,1,0]

def PhysicalFrames (K : Vertex → UnitSquare) (t : ℝ) : Prop :=
  ∀i, (K i).cosine=frameCos t i ∧ (K i).sine=frameSin t i

def normal (t : ℝ) : Vertex → Point :=
  ![GeometricModel.e t,GeometricModel.e t,(0,1),(-1,0),(-1,0),(0,-1),(- (GeometricModel.f t).1,- (GeometricModel.f t).2)]

def width (t : ℝ) (i : Vertex) : ℝ :=
  if i=1 ∨ i=6 then (1+Real.cos t+Real.sin t)/2 else 1

def gap (K : Vertex → UnitSquare) (t : ℝ) (i : Vertex) : ℝ :=
  projection (normal t i) (sub (K (next i)).center (K i).center)-width t i

def RetainedSeparators (K : Vertex → UnitSquare) (t : ℝ) : Prop :=
  ∀i, 0≤gap K t i

def cornerOffset (t : ℝ) : Fin 5 → Point :=
  ![(1/2,-1/2),(1/2,1/2),(-1/2,1/2),(-1/2,-1/2),
    (-((GeometricModel.e t).1+(GeometricModel.f t).1)/2,-((GeometricModel.e t).2+(GeometricModel.f t).2)/2)]

def chain (K : Vertex → UnitSquare) (t : ℝ) : FiveCorner where
  angle := t
  point i := add (K (anchorIndex i)).center (cornerOffset t i)

def residual (d : FiveCorner) : Fin 5 → ℝ :=
  ![(d.point 1).2-(d.point 0).2-2,
    (d.point 1).1-(d.point 2).1-3,
    (d.point 2).2-(d.point 3).2-2,
    projection (GeometricModel.f d.angle) (sub (d.point 3) (d.point 4))-(1+Real.sin d.angle),
    projection (GeometricModel.e d.angle) (sub (d.point 0) (d.point 4))-(2+Real.cos d.angle)]

theorem spans_iff_residuals (d : FiveCorner) : d.spans ↔
    0≤d.angle ∧ d.angle≤Real.pi/4 ∧ ∀i,0≤residual d i := by
  constructor
  · rintro ⟨h0,h1,h2,h3,h4,h5,h6⟩
    refine ⟨h0,h1,?_⟩
    intro i
    fin_cases i
    · show 0≤(d.point 1).2-(d.point 0).2-2
      linarith
    · show 0≤(d.point 1).1-(d.point 2).1-3
      linarith
    · show 0≤(d.point 2).2-(d.point 3).2-2
      linarith
    · show 0≤projection (GeometricModel.f d.angle) (sub (d.point 3) (d.point 4))-
        (1+Real.sin d.angle)
      rw [GeometricModel.projection_f_sub]
      linarith
    · show 0≤projection (GeometricModel.e d.angle) (sub (d.point 0) (d.point 4))-
        (2+Real.cos d.angle)
      rw [GeometricModel.projection_e_sub]
      linarith
  · rintro ⟨h0,h1,h⟩
    have r0 : 0≤(d.point 1).2-(d.point 0).2-2 := h 0
    have r1 : 0≤(d.point 1).1-(d.point 2).1-3 := h 1
    have r2 : 0≤(d.point 2).2-(d.point 3).2-2 := h 2
    have r3 : 0≤projection (GeometricModel.f d.angle) (sub (d.point 3) (d.point 4))-
        (1+Real.sin d.angle) := h 3
    have r4 : 0≤projection (GeometricModel.e d.angle) (sub (d.point 0) (d.point 4))-
        (2+Real.cos d.angle) := h 4
    rw [GeometricModel.projection_f_sub] at r3
    rw [GeometricModel.projection_e_sub] at r4
    exact ⟨h0,h1,by linarith,by linarith,by linarith,by linarith,by linarith⟩

/-- Each point is an actual vertex of its original square, regardless of
where the original center lies in the later boundary chart. -/
theorem corner_is_original_vertex {K : Vertex → UnitSquare} {t : ℝ}
    (hf : PhysicalFrames K t) (i : Fin 5) :
    closedSquare (K (anchorIndex i)) ((chain K t).point i) := by
  have hc (j : Vertex) := (hf j).1
  have hs (j : Vertex) := (hf j).2
  fin_cases i <;> constructor <;> apply abs_le.mpr <;> constructor <;>
    simp [chain,anchorIndex,cornerOffset,localX,localY,add,
      hc,hs,frameCos,frameSin,GeometricModel.e,GeometricModel.f] <;>
    nlinarith [Real.sin_sq_add_cos_sq t]

/-- Five geometric demands are exact sums of the seven retained gaps. -/
theorem residual_identity (K : Vertex → UnitSquare) (t : ℝ) :
    residual (chain K t)=
      ![gap K t 2,gap K t 3+gap K t 4,gap K t 5,gap K t 6,
        gap K t 0+gap K t 1] := by
  funext i
  fin_cases i <;>
    simp [residual,chain,anchorIndex,cornerOffset,gap,normal,width,next,
      projection,GeometricModel.e,GeometricModel.f,add,sub] <;>
    nlinarith [Real.sin_sq_add_cos_sq t]

theorem chain_spans {K : Vertex → UnitSquare} {t : ℝ}
    (ht : 0≤t ∧ t≤Real.pi/4) (hs : RetainedSeparators K t) :
    (chain K t).spans := by
  apply (spans_iff_residuals _).2
  refine ⟨ht.1,ht.2,?_⟩
  rw [residual_identity]
  intro i
  fin_cases i <;> simp <;>
    first | exact hs _ | exact add_nonneg (hs _) (hs _)

theorem chain_fits {K : Vertex → UnitSquare} {t R : ℝ}
    (hR : 0≤R) (hf : PhysicalFrames K t)
    (hc : ∀i p,closedSquare (K i) p → normSq p≤R^2) :
    (chain K t).fits R := by
  exact ⟨hR,fun i => hc _ _ (corner_is_original_vertex hf i)⟩

/-- The geometric infimum is bounded below independently of attainment. -/
theorem feasible_radii_bounded_below : BddBelow Eight.feasibleRadii := by
  refine ⟨0,?_⟩
  rintro R ⟨d,hd,hfit⟩
  exact hfit.1

/-- A source-level lower bound, using only the definition of the model.
This lemma is independent of every stationary or equality proof. -/
theorem radius_lower_bound {K : Vertex → UnitSquare} {t R : ℝ}
    (ht : 0≤t ∧ t≤Real.pi/4) (hR : 0≤R)
    (hf : PhysicalFrames K t) (hs : RetainedSeparators K t)
    (hc : ∀i p,closedSquare (K i) p → normSq p≤R^2) :
    Eight.radius≤R := by
  exact csInf_le feasible_radii_bounded_below
    ⟨chain K t,chain_spans ht hs,chain_fits hR hf hc⟩

/-- Recover all five original anchor centers from equality of their actual
corner chain with a fixed five-corner configuration. -/
theorem original_anchor_centers {K : Vertex → UnitSquare} {t : ℝ} {d : FiveCorner}
    (h : chain K t=d) :
    t=d.angle ∧ ∀i,(K (anchorIndex i)).center=d.anchorCenter i := by
  subst h
  refine ⟨rfl,?_⟩
  intro i
  fin_cases i <;> apply Prod.ext <;>
    simp [chain,anchorIndex,cornerOffset,FiveCorner.anchorCenter,add,GeometricModel.e,
      GeometricModel.f] <;> ring

/-- Positive sums of the original gaps vanish separately. No weighted dual
or positivity certificate is needed for this step. -/
theorem all_original_contacts_tight {K : Vertex → UnitSquare} {t : ℝ}
    (hs : RetainedSeparators K t)
    (h : ∀i,residual (chain K t) i=0) : ∀i,gap K t i=0 := by
  have hr := residual_identity K t
  have h0 : gap K t 2=0 := by have hh := h 0; rw [hr] at hh; exact hh
  have h1 : gap K t 3+gap K t 4=0 := by have hh := h 1; rw [hr] at hh; exact hh
  have h2 : gap K t 5=0 := by have hh := h 2; rw [hr] at hh; exact hh
  have h3 : gap K t 6=0 := by have hh := h 3; rw [hr] at hh; exact hh
  have h4 : gap K t 0+gap K t 1=0 := by have hh := h 4; rw [hr] at hh; exact hh
  have g0 := hs 0
  have g1 := hs 1
  have g3 := hs 3
  have g4 := hs 4
  intro i
  fin_cases i
  · show gap K t 0=0
    linarith
  · show gap K t 1=0
    linarith
  · exact h0
  · show gap K t 3=0
    linarith
  · show gap K t 4=0
    linarith
  · exact h2
  · exact h3

theorem frame_reconstruction (t : ℝ) (v : Point) :
    v=add (scale (projection (GeometricModel.e t) v) (GeometricModel.e t))
      (scale (projection (GeometricModel.f t) v) (GeometricModel.f t)) := by
  have hu := Real.sin_sq_add_cos_sq t
  apply Prod.ext
  · simp only [GeometricModel.projection,GeometricModel.e,GeometricModel.f,add,scale]
    linear_combination -v.1*hu
  · simp only [GeometricModel.projection,GeometricModel.e,GeometricModel.f,add,scale]
    linear_combination -v.2*hu

/-- The surviving parameters are the actual original centers on the two
contact lines, not comparison coordinates introduced by a transport. -/
theorem original_sliders {K : Vertex → UnitSquare} {t : ℝ} {d : FiveCorner}
    (hchain : chain K t=d) (hgaps : ∀i,gap K t i=0) :
    ∃z η, (K 4).center=d.topCenter z ∧ (K 1).center=d.tiltedCenter η := by
  obtain ⟨-,ha⟩ := original_anchor_centers hchain
  subst hchain
  let z := (K 4).center.2
  let v := sub (K 1).center (K 0).center
  let η := projection (GeometricModel.f t) v
  have hHG : projection (GeometricModel.e t) v=1 := by
    have hh : projection (GeometricModel.e t) (sub (K 1).center (K 0).center)-1=0 := hgaps 0
    linarith
  have hBT : (K 4).center.1=(K 3).center.1-1 := by
    have hh : projection ((-1:ℝ),(0:ℝ)) (sub (K 4).center (K 3).center)-1=0 := hgaps 3
    simp only [GeometricModel.projection,sub] at hh
    linarith
  have hH : (K 0).center=(chain K t).anchorCenter 4 := ha 4
  have hB : (K 3).center=(chain K t).anchorCenter 1 := ha 1
  have hvec := frame_reconstruction t v
  rw [hHG] at hvec
  refine ⟨z,η,?_,?_⟩
  · apply Prod.ext
    · show (K 4).center.1=((chain K t).anchorCenter 1).1-1
      rw [← hB]
      exact hBT
    · rfl
  · apply Prod.ext
    · have hx : (K 1).center.1-(K 0).center.1=1*(GeometricModel.e t).1+
          η*(GeometricModel.f t).1 := congrArg Prod.fst hvec
      show (K 1).center.1=((chain K t).anchorCenter 4).1+Real.cos t-η*Real.sin t
      rw [← hH]
      simp only [GeometricModel.e,GeometricModel.f] at hx
      linarith
    · have hy : (K 1).center.2-(K 0).center.2=1*(GeometricModel.e t).2+
          η*(GeometricModel.f t).2 := congrArg Prod.snd hvec
      show (K 1).center.2=((chain K t).anchorCenter 4).2+Real.sin t+η*Real.cos t
      rw [← hH]
      simp only [GeometricModel.e,GeometricModel.f] at hy
      linarith

/-- The equality transfer isolates exactly the global selection facts used.
This is not advertised as the missing normalization or entry theorem. -/
theorem equality_from_minimizer_uniqueness
    {K : Vertex → UnitSquare} {t : ℝ}
    (ht : 0≤t ∧ t≤Real.pi/4)
    (hR : 0≤Eight.radius)
    (hf : PhysicalFrames K t) (hs : RetainedSeparators K t)
    (hc : ∀i p,closedSquare (K i) p → normSq p≤Eight.radius^2)
    (hunique : ∀d,FiveCorner.IsMinimizer d → d=FiveCorner.selected)
    (htight : ∀i,residual FiveCorner.selected i=0) :
    t=FiveCorner.selected.angle ∧
      (∀i,(K (anchorIndex i)).center=FiveCorner.selected.anchorCenter i) ∧
      (∀i,gap K t i=0) ∧
      ∃z η,(K 4).center=FiveCorner.selected.topCenter z ∧
        (K 1).center=FiveCorner.selected.tiltedCenter η := by
  have hm : FiveCorner.IsMinimizer (chain K t) :=
    ⟨chain_spans ht hs,chain_fits hR hf hc⟩
  have he := hunique _ hm
  obtain ⟨ha,hcenters⟩ := original_anchor_centers he
  have hgaps := all_original_contacts_tight hs (by intro i; rw [he]; exact htight i)
  exact ⟨ha,hcenters,hgaps,original_sliders he hgaps⟩

end OriginalFiveCorner
end SquaresInCircles.Eight.TableFree
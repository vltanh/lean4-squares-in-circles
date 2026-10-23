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
  ![e t,e t,(0,1),(-1,0),(-1,0),(0,-1),(- (f t).1,- (f t).2)]

def width (t : ℝ) (i : Vertex) : ℝ :=
  if i=1 ∨ i=6 then (1+Real.cos t+Real.sin t)/2 else 1

def gap (K : Vertex → UnitSquare) (t : ℝ) (i : Vertex) : ℝ :=
  projection (normal t i) (sub (K (next i)).center (K i).center)-width t i

def RetainedSeparators (K : Vertex → UnitSquare) (t : ℝ) : Prop :=
  ∀i, 0≤gap K t i

def cornerOffset (t : ℝ) : Fin 5 → Point :=
  ![(1/2,-1/2),(1/2,1/2),(-1/2,1/2),(-1/2,-1/2),
    (-((e t).1+(f t).1)/2,-((e t).2+(f t).2)/2)]

def chain (K : Vertex → UnitSquare) (t : ℝ) : FiveCorner where
  angle := t
  point i := add (K (anchorIndex i)).center (cornerOffset t i)

def residual (d : FiveCorner) : Fin 5 → ℝ :=
  ![(d.point 1).2-(d.point 0).2-2,
    (d.point 1).1-(d.point 2).1-3,
    (d.point 2).2-(d.point 3).2-2,
    projection (f d.angle) (sub (d.point 3) (d.point 4))-(1+Real.sin d.angle),
    projection (e d.angle) (sub (d.point 0) (d.point 4))-(2+Real.cos d.angle)]

theorem spans_iff_residuals (d : FiveCorner) : d.spans ↔
    0≤d.angle ∧ d.angle≤Real.pi/4 ∧ ∀i,0≤residual d i := by
  simp only [FiveCorner.spans,residual,Fin.forall_fin_succ]
  constructor <;> intro h <;> rcases h with ⟨h0,h1,h2,h3,h4,h5,h6⟩
  · exact ⟨h0,h1,by linarith,by linarith,by linarith,by linarith,by linarith⟩
  · exact ⟨h0,h1,by linarith,by linarith,by linarith,by linarith,by linarith⟩

/-- Each point is an actual vertex of its original square, regardless of
where the original center lies in the later boundary chart. -/
theorem corner_is_original_vertex {K : Vertex → UnitSquare} {t : ℝ}
    (hf : PhysicalFrames K t) (i : Fin 5) :
    closedSquare (K (anchorIndex i)) ((chain K t).point i) := by
  have hc (j : Vertex) := (hf j).1
  have hs (j : Vertex) := (hf j).2
  fin_cases i <;> constructor <;> apply abs_le.mpr <;> constructor <;>
    simp [chain,anchorIndex,cornerOffset,localX,localY,add,
      hc,hs,frameCos,frameSin,e,f] <;>
    nlinarith [Real.sin_sq_add_cos_sq t]

/-- Five geometric demands are exact sums of the seven retained gaps. -/
theorem residual_identity (K : Vertex → UnitSquare) (t : ℝ) :
    residual (chain K t)=
      ![gap K t 2,gap K t 3+gap K t 4,gap K t 5,gap K t 6,
        gap K t 0+gap K t 1] := by
  funext i
  fin_cases i <;>
    simp [residual,chain,anchorIndex,cornerOffset,gap,normal,width,next,
      projection,e,f,add,sub] <;>
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
theorem feasible_radii_bounded_below : BddBelow FiveCorner.feasibleRadii := by
  refine ⟨0,?_⟩
  rintro R ⟨d,hd,hfit⟩
  exact hfit.1

/-- A source-level lower bound, using only the definition of the model.
This lemma is independent of every stationary or equality proof. -/
theorem radius_lower_bound {K : Vertex → UnitSquare} {t R : ℝ}
    (ht : 0≤t ∧ t≤Real.pi/4) (hR : 0≤R)
    (hf : PhysicalFrames K t) (hs : RetainedSeparators K t)
    (hc : ∀i p,closedSquare (K i) p → normSq p≤R^2) :
    FiveCorner.radius≤R := by
  exact csInf_le feasible_radii_bounded_below
    ⟨chain K t,chain_spans ht hs,chain_fits hR hf hc⟩

/-- Recover all five original anchor centers from equality of their actual
corner chain with a fixed five-corner configuration. -/
theorem original_anchor_centers {K : Vertex → UnitSquare} {t : ℝ} {d : FiveCorner}
    (h : chain K t=d) :
    t=d.angle ∧ ∀i,(K (anchorIndex i)).center=d.anchorCenter i := by
  have ht : t=d.angle := congrArg FiveCorner.angle h
  refine ⟨ht,?_⟩
  intro i
  have hp := congrArg (fun c : FiveCorner => c.point i) h
  fin_cases i <;> apply Prod.ext <;>
    simp [chain,anchorIndex,cornerOffset,FiveCorner.anchorCenter,add,← ht] at hp ⊢ <;>
    first | exact congrArg Prod.fst hp | exact congrArg Prod.snd hp | aesop

/-- Positive sums of the original gaps vanish separately. No weighted dual
or positivity certificate is needed for this step. -/
theorem all_original_contacts_tight {K : Vertex → UnitSquare} {t : ℝ}
    (hs : RetainedSeparators K t)
    (h : ∀i,residual (chain K t) i=0) : ∀i,gap K t i=0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  rw [residual_identity] at h0 h1 h2 h3 h4
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_four] at h0 h1 h2 h3 h4
  intro i
  fin_cases i <;> nlinarith [hs 0,hs 1,hs 2,hs 3,hs 4,hs 5,hs 6]

theorem frame_reconstruction (t : ℝ) (v : Point) :
    v=add (scale (projection (e t) v) (e t))
      (scale (projection (f t) v) (f t)) := by
  ext <;> simp [projection,e,f,add,scale] <;>
    nlinarith [Real.sin_sq_add_cos_sq t]

/-- The surviving parameters are the actual original centers on the two
contact lines, not comparison coordinates introduced by a transport. -/
theorem original_sliders {K : Vertex → UnitSquare} {t : ℝ} {d : FiveCorner}
    (hchain : chain K t=d) (hgaps : ∀i,gap K t i=0) :
    ∃z η, (K 4).center=d.topCenter z ∧ (K 1).center=d.tiltedCenter η := by
  obtain ⟨ht,ha⟩ := original_anchor_centers hchain
  let z := (K 4).center.2
  let v := sub (K 1).center (K 0).center
  let η := projection (f t) v
  have hHG : projection (e t) v=1 := by
    have hh := hgaps 0
    simpa [gap,normal,width,next,v] using hh
  have hBT : (K 4).center.1=(K 3).center.1-1 := by
    have hh := hgaps 3
    simp [gap,normal,width,next,projection,sub] at hh
    linarith
  have hH : (K 0).center=d.anchorCenter 4 := by simpa [anchorIndex] using ha 4
  have hB : (K 3).center=d.anchorCenter 1 := by simpa [anchorIndex] using ha 1
  have hvec := frame_reconstruction t v
  rw [hHG] at hvec
  refine ⟨z,η,?_,?_⟩
  · apply Prod.ext
    · simpa [FiveCorner.topCenter,hB] using hBT
    · rfl
  · apply Prod.ext
    · have hx := congrArg Prod.fst hvec
      simp [v,sub,add,scale,η] at hx
      simp [FiveCorner.tiltedCenter,← ht,← hH]
      linarith
    · have hy := congrArg Prod.snd hvec
      simp [v,sub,add,scale,η] at hy
      simp [FiveCorner.tiltedCenter,← ht,← hH]
      linarith

/-- The equality transfer isolates exactly the global selection facts used.
This is not advertised as the missing normalization or entry theorem. -/
theorem equality_from_minimizer_uniqueness
    {K : Vertex → UnitSquare} {t : ℝ}
    (ht : 0≤t ∧ t≤Real.pi/4)
    (hR : 0≤FiveCorner.radius)
    (hf : PhysicalFrames K t) (hs : RetainedSeparators K t)
    (hc : ∀i p,closedSquare (K i) p → normSq p≤FiveCorner.radius^2)
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
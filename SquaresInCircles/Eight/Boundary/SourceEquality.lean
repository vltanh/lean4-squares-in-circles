module

public import SquaresInCircles.Eight.Boundary.Candidate.Geometry
public import SquaresInCircles.Eight.Boundary.Reduction
public import SquaresInCircles.Eight.Equality.Angles
public import SquaresInCircles.Eight.Model
public import SquaresInCircles.Eight.Owners.Negative.ContactGeometry
public import SquaresInCircles.Eight.Stationary.FixedEval
public import SquaresInCircles.Eight.Words.Outside.EEndpoint

/-!
# Eight squares: strict comparisons of the axes of G–A and of E–H

A sorted square that avoids the core has primary coordinate above `447/800`
(`sorted_core_primary_reserve`, `original_core_primary_reserve`). With `aG > 447/800`,
`bA < 11/25`, `0 ≤ aA + g < 71/50` and `0 ≤ κ < 13/200`, the reserve `aG - bA - (aA + g) κ`
exceeds `529/20000` (`ga_coefficient_reserve`), and when `1 - c = s κ` it is the difference,
divided by `s`, of the projections of G–A on the axes zero and one
(`ga_projection_difference`). So when GA0 is tight, GA1 falls strictly short of the width
(`ga1_strictly_unavailable`), with no upper bound on the radial state of G. In the same way, when
EH1 is tight, EH0 falls strictly short of the width, since `bH < aE` and `aH + bE ≥ 0`
(`eh0_strictly_unavailable`). At a tight contact the witness of G–A or of E–H is therefore the
tight axis.
-/

section
/-!
## E along its own circle

For a sorted point E with `y ≤ 0` and `7/12 < a`, the points `point E b = (primary E b, -b)`,
`0 ≤ b ≤ -E.y`, run along the circle `(a + 1/2)² + (b + 1/2)² = E.circle` of E, from E at
`b = -E.y` (`initial`) to the axis `y = 0`. The circle is that of E itself, which need not be the
level of the cycle nor exceed `qLow`. The points are sorted, avoid the core and have primary
coordinate at least that of E (`geometry`); the primary coordinate has the derivative
`-slope E b`, with `0 ≤ slope E b ≤ 1` (`derivative`), and `b - slope · primary = -(1 - slope)/2`
(`radial_identity`).

The primary margins `eh` of E–H on the axis one and `de` of D–E on the axis three, as functions of
the frame angle `p` of E and of `b` (`eh_actual`, `de_actual`), both increase along the direction
that lowers `p` and moves E along its circle towards `y = 0` at a speed `β > 0` given by the
radial identity (`improving_speed`, `eh_direction_derivative`, `de_direction_derivative`). Hence
two margins at least `η` become strictly larger than `η` after a small move (`improving_shift`).
-/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace SquaresInCircles.Eight.OriginalECircle

def root (E : SignedPoint) (b : ℝ) : ℝ := Real.sqrt (E.circle-(b+1/2)^2)
def primary (E : SignedPoint) (b : ℝ) : ℝ := root E b-1/2
def point (E : SignedPoint) (b : ℝ) : SignedPoint := ⟨primary E b,-b⟩
def slope (E : SignedPoint) (b : ℝ) : ℝ := (b+1/2)/root E b

def eh (E H : SignedPoint) (p b : ℝ) : ℝ :=
  H.a-1/2+(primary E b-1/2)*Real.sin p-(b+1/2)*Real.cos p

def de (E D : SignedPoint) (α p b : ℝ) : ℝ :=
  D.a-1/2-(primary E b+1/2)*Real.sin (p-α)+(b-1/2)*Real.cos (p-α)

theorem root_bounds {E : SignedPoint} {b : ℝ}
    (hEs : E.Sorted) (hEy : E.y≤0) (hb : b∈Icc 0 (-E.y)) :
    0<root E b ∧ E.a+1/2≤root E b ∧
      (root E b)^2=E.circle-(b+1/2)^2 := by
  have hsource : E.circle=(E.a+1/2)^2+(-E.y+1/2)^2 := by
    simp [SignedPoint.circle,abs_of_nonpos hEy]
  have hminor := pow_le_pow_left₀ (show 0≤b+1/2 by linarith [hb.1])
    (show b+1/2≤ -E.y+1/2 by linarith [hb.2]) 2
  have hrad : 0<E.circle-(b+1/2)^2 := by
    rw [hsource]
    nlinarith [hEs.1]
  have hroot : 0<root E b := Real.sqrt_pos.mpr hrad
  have hsq : (root E b)^2=E.circle-(b+1/2)^2 := Real.sq_sqrt hrad.le
  refine ⟨hroot,?_,hsq⟩
  nlinarith [hEs.1]

theorem initial {E : SignedPoint} (hEs : E.Sorted) (hEy : E.y≤0) : point E (-E.y)=E := by
  have heq : E.circle-(-E.y+1/2)^2=(E.a+1/2)^2 := by
    simp [SignedPoint.circle,abs_of_nonpos hEy]
  have ha : primary E (-E.y)=E.a := by
    unfold primary root
    rw [heq,Real.sqrt_sq (show 0≤E.a+1/2 by linarith [hEs.1])]
    ring
  unfold point
  rw [ha,neg_neg]

theorem geometry {E : SignedPoint} {b : ℝ}
    (hEs : E.Sorted) (hEy : E.y≤0) (hEa : 7/12<E.a)
    (hb : b∈Icc 0 (-E.y)) :
    (point E b).Sorted ∧ (point E b).AvoidsCore ∧
      (point E b).circle=E.circle ∧ E.a≤primary E b := by
  have hr := root_bounds hEs hEy hb
  have ha : E.a≤primary E b := by dsimp [primary]; linarith [hr.2.1]
  have hbs : -E.y≤E.a := by simpa [abs_of_nonpos hEy] using hEs.2
  have hsort : b≤primary E b := hb.2.trans (hbs.trans ha)
  have hprimary : 7/12<primary E b := hEa.trans_le ha
  refine ⟨⟨by dsimp [point]; linarith,
    by simpa [point,abs_neg,abs_of_nonneg hb.1] using hsort⟩,?_,?_,ha⟩
  · change (1/12:ℝ)^2≤(max (primary E b-1/2) 0)^2+(max (|-b|-1/2) 0)^2
    rw [max_eq_left (by linarith : 0≤primary E b-1/2)]
    nlinarith [sq_nonneg (max (|-b|-1/2) 0)]
  · have hc : (point E b).circle=(root E b)^2+(b+1/2)^2 := by
      simp only [point,SignedPoint.circle,primary,abs_neg,abs_of_nonneg hb.1]
      ring
    rw [hc,hr.2.2]
    ring

theorem continuous_primary (E : SignedPoint) : Continuous (primary E) := by
  unfold primary root
  fun_prop

theorem derivative {E : SignedPoint} {b : ℝ}
    (hEs : E.Sorted) (hEy : E.y≤0) (hb : b∈Icc 0 (-E.y)) :
    HasDerivAt (primary E) (-slope E b) b ∧ 0≤ slope E b ∧ slope E b≤1 := by
  have hr := root_bounds hEs hEy hb
  have hrad : E.circle-(b+1/2)^2≠0 := by nlinarith [hr.1,hr.2.2]
  have hd := ((hasDerivAt_const b E.circle).sub
    (((hasDerivAt_id b).add_const (1/2)).pow 2)).sqrt hrad
  refine ⟨?_,?_,?_⟩
  · convert hd.sub_const (1/2) using 1
    · rfl
    · dsimp [slope,root]
      field_simp [hr.1.ne']
      ring
  · exact div_nonneg (by linarith [hb.1]) hr.1.le
  · apply (div_le_one hr.1).2
    have hbs : -E.y≤E.a := by simpa [abs_of_nonpos hEy] using hEs.2
    linarith [hb.2,hr.2.1]

theorem radial_identity {E : SignedPoint} {b : ℝ}
    (hEs : E.Sorted) (hEy : E.y≤0) (hb : b∈Icc 0 (-E.y)) :
    b-slope E b*primary E b= -(1-slope E b)/2 := by
  have hr := (root_bounds hEs hEy hb).1
  dsimp [slope,primary]
  field_simp [hr.ne']
  ring

theorem eh_actual (E H : SignedPoint) {p : ℝ} (b : ℝ)
    (hp : p∈Icc 0 (7/10:ℝ)) :
    eh E H p b=quarterProjection (point E b) H p 1-edgeWidth p := by
  rw [edgeWidth_positive_formula hp]
  simp [eh,point,quarterProjection]
  ring

theorem de_actual (E D : SignedPoint) (α : ℝ) {p : ℝ} (b : ℝ)
    (hn : p-α∈Icc 0 (7/10:ℝ)) :
    de E D α p b=quarterProjection D (point E b) (-(p-α)) 3-edgeWidth (-(p-α)) := by
  rw [edgeWidth_negative_formula hn]
  simp only [de,point,quarterProjection,Matrix.cons_val,Real.sin_neg,Real.cos_neg]
  ring

theorem improving_speed {E : SignedPoint} {p n b : ℝ}
    (hEs : E.Sorted) (hEy : E.y≤0) (hEa : 7/12<E.a)
    (hb : b∈Icc 0 (-E.y)) (hp : p∈Icc 0 (7/10:ℝ)) (hn : n∈Icc 0 (7/10:ℝ)) :
    ∃β, 0<β ∧
      0<β*(Real.cos p+slope E b*Real.sin p)-
        ((primary E b-1/2)*Real.cos p+(b+1/2)*Real.sin p) ∧
      0<(primary E b+1/2-β)*Real.cos n+
        (b-1/2-slope E b*β)*Real.sin n := by
  have hg := geometry hEs hEy hEa hb
  have hd := derivative hEs hEy hb
  have ha : 1/2<primary E b := by linarith [hg.2.2.2]
  have hdenβ := OutsideE.contactSpeed_positive ha hb.1 hd.2.1 hp
  have hW := OutsideE.de3_contact_rate_positive (a := primary E b) hb.1 hd.2 hp hn
    (Or.inr (radial_identity hEs hEy hb))
  obtain ⟨β₀,hβ₀⟩ : ∃ β₀,β₀=OutsideE.contactSpeed (primary E b) b (slope E b) p := ⟨_,rfl⟩
  rw [← hβ₀] at hW hdenβ
  obtain ⟨W,hWdef⟩ : ∃ W,W=(primary E b+1/2-β₀)*Real.cos n+
      (b-1/2-slope E b*β₀)*Real.sin n := ⟨_,rfl⟩
  rw [← hWdef] at hW
  obtain ⟨c,hcdef⟩ : ∃ c,c=Real.cos n+slope E b*Real.sin n := ⟨_,rfl⟩
  have hc : 0<c := by
    have ht := transport_trig hn
    rw [hcdef]
    exact add_pos_of_pos_of_nonneg (by linarith [ht.1]) (mul_nonneg hd.2.1 ht.2.2.1)
  obtain ⟨η,hηdef⟩ : ∃ η,η=W/(2*c) := ⟨_,rfl⟩
  have hη : 0<η := by rw [hηdef]; exact div_pos hW (mul_pos (by norm_num) hc)
  have hηc : η*c=W/2 := by rw [hηdef]; field_simp
  refine ⟨β₀+η,add_pos hdenβ.2 hη,?_,?_⟩
  · have hβc : β₀*(Real.cos p+slope E b*Real.sin p)=
        (primary E b-1/2)*Real.cos p+(b+1/2)*Real.sin p := by
      rw [hβ₀,OutsideE.contactSpeed,div_mul_cancel₀ _ hdenβ.1.ne']
    have heq : (β₀+η)*(Real.cos p+slope E b*Real.sin p)-
        ((primary E b-1/2)*Real.cos p+(b+1/2)*Real.sin p)=
        η*(Real.cos p+slope E b*Real.sin p) := by
      rw [add_mul,hβc]
      ring
    rw [heq]
    exact mul_pos hη hdenβ.1
  · have heq : (primary E b+1/2-(β₀+η))*Real.cos n+
        (b-1/2-slope E b*(β₀+η))*Real.sin n=W-η*c := by
      rw [hWdef,hcdef]
      ring
    rw [heq,hηc]
    linarith

theorem eh_direction_derivative {E H : SignedPoint} {p b β : ℝ}
    (hEs : E.Sorted) (hEy : E.y≤0) (hb : b∈Icc 0 (-E.y)) :
    HasDerivAt (fun τ => eh E H (p-τ) (b-β*τ))
      (β*(Real.cos p+slope E b*Real.sin p)-
        ((primary E b-1/2)*Real.cos p+(b+1/2)*Real.sin p)) 0 := by
  have hbder : HasDerivAt (fun τ : ℝ => b-β*τ) (-β) 0 :=
    (((hasDerivAt_id' (0:ℝ)).const_mul β).const_sub b).congr_deriv (by ring)
  have hpder : HasDerivAt (fun τ : ℝ => p-τ) (-1) 0 :=
    (hasDerivAt_id' (0:ℝ)).const_sub p
  have ha0 : HasDerivAt (primary E) (-slope E b) (b-β*0) := by
    simpa using (derivative hEs hEy hb).1
  have hader := ha0.comp 0 hbder
  have hsder := (Real.hasDerivAt_sin (p-0)).comp 0 hpder
  have hcder := (Real.hasDerivAt_cos (p-0)).comp 0 hpder
  have F : HasDerivAt (fun τ => eh E H (p-τ) (b-β*τ))
      (0+(-slope E b*-β*Real.sin (p-0)+(primary E (b-β*0)-1/2)*(Real.cos (p-0)*-1))-
        (-β*Real.cos (p-0)+(b-β*0+1/2)*(-Real.sin (p-0)*-1))) 0 :=
    ((hasDerivAt_const (0:ℝ) (H.a-1/2)).fun_add
      ((hader.sub_const (1/2)).fun_mul hsder)).fun_sub
        ((hbder.add_const (1/2)).fun_mul hcder)
  convert F using 1
  simp only [sub_zero,mul_zero]
  ring

theorem de_direction_derivative {E D : SignedPoint} {α p b β : ℝ}
    (hEs : E.Sorted) (hEy : E.y≤0) (hb : b∈Icc 0 (-E.y)) :
    HasDerivAt (fun τ => de E D α (p-τ) (b-β*τ))
      ((primary E b+1/2-β)*Real.cos (p-α)+
        (b-1/2-slope E b*β)*Real.sin (p-α)) 0 := by
  have hbder : HasDerivAt (fun τ : ℝ => b-β*τ) (-β) 0 :=
    (((hasDerivAt_id' (0:ℝ)).const_mul β).const_sub b).congr_deriv (by ring)
  have hpder : HasDerivAt (fun τ : ℝ => (p-τ)-α) (-1) 0 :=
    ((hasDerivAt_id' (0:ℝ)).const_sub p).sub_const α
  have ha0 : HasDerivAt (primary E) (-slope E b) (b-β*0) := by
    simpa using (derivative hEs hEy hb).1
  have hader := ha0.comp 0 hbder
  have hsder := (Real.hasDerivAt_sin ((p-0)-α)).comp 0 hpder
  have hcder := (Real.hasDerivAt_cos ((p-0)-α)).comp 0 hpder
  have F : HasDerivAt (fun τ => de E D α (p-τ) (b-β*τ))
      (0-((-slope E b*-β)*Real.sin ((p-0)-α)+(primary E (b-β*0)+1/2)*
          (Real.cos ((p-0)-α)*-1))+
        (-β*Real.cos ((p-0)-α)+(b-β*0-1/2)*(-Real.sin ((p-0)-α)*-1))) 0 :=
    ((hasDerivAt_const (0:ℝ) (D.a-1/2)).fun_sub
      ((hader.add_const (1/2)).fun_mul hsder)).fun_add
        ((hbder.sub_const (1/2)).fun_mul hcder)
  convert F using 1
  simp only [sub_zero,mul_zero]
  ring

/-- If `eh` and `de` are at least `η` at `(p, b)`, with `0 ≤ α < p ≤ 7/10` and `0 < b ≤ -E.y`,
both exceed `η` at some `(p', b')` with `α < p' < p` and `0 < b' ≤ -E.y`: lower `p` and move E
along its circle at the speed of `improving_speed`. -/
theorem improving_shift {E D H : SignedPoint} {α p b η : ℝ}
    (hEs : E.Sorted) (hEy : E.y≤0) (hEa : 7/12<E.a)
    (hα : 0≤α) (hp : α<p) (hpu : p≤7/10)
    (hb : b∈Ioc 0 (-E.y)) (hEH : η≤eh E H p b) (hDE : η≤de E D α p b) :
    ∃p' b', p'∈Ioo α p ∧ b'∈Ioc 0 (-E.y) ∧
      η<eh E H p' b' ∧ η<de E D α p' b' := by
  have hbcc : b∈Icc 0 (-E.y) := ⟨hb.1.le,hb.2⟩
  have hpdom : p∈Icc 0 (7/10:ℝ) := ⟨by linarith,hpu⟩
  have hndom : p-α∈Icc 0 (7/10:ℝ) := ⟨by linarith,by linarith⟩
  obtain ⟨β,hβ,hErate,hDrate⟩ := improving_speed hEs hEy hEa hbcc hpdom hndom
  have hEd := eh_direction_derivative (H := H) (p := p) (β := β) hEs hEy hbcc
  have hDd := de_direction_derivative (D := D) (α := α) (p := p) (β := β) hEs hEy hbcc
  have hEevent : ∀ᶠτ in 𝓝[>] (0:ℝ), η<eh E H (p-τ) (b-β*τ) :=
    (NegativeContact.eventually_right_gt hEd hErate).mono (by
      intro τ hτ
      exact hEH.trans_lt (by simpa using hτ))
  have hDevent : ∀ᶠτ in 𝓝[>] (0:ℝ), η<de E D α (p-τ) (b-β*τ) :=
    (NegativeContact.eventually_right_gt hDd hDrate).mono (by
      intro τ hτ
      exact hDE.trans_lt (by simpa using hτ))
  have hangle : ∀ᶠτ in 𝓝[>] (0:ℝ), τ<p-α :=
    (eventually_lt_nhds (sub_pos.mpr hp)).filter_mono nhdsWithin_le_nhds
  have hcb : ContinuousAt (fun τ : ℝ => b-β*τ) 0 := by fun_prop
  have hval : (0:ℝ)<(fun τ : ℝ => b-β*τ) 0 := by simpa using hb.1
  have hfloor : ∀ᶠτ in 𝓝[>] (0:ℝ), 0<b-β*τ :=
    (hcb.tendsto.eventually (eventually_gt_nhds hval)).filter_mono nhdsWithin_le_nhds
  obtain ⟨τ,hτ,hangle,hfloor,hEevent,hDevent⟩ :=
    ((eventually_mem_nhdsWithin (s := Ioi (0:ℝ)) (a := 0)).and
      (hangle.and (hfloor.and (hEevent.and hDevent)))).exists
  have hτ0 : 0<τ := hτ
  have hprod := mul_pos hβ hτ0
  exact ⟨p-τ,b-β*τ,⟨by linarith,by linarith⟩,
    ⟨hfloor,by linarith [hb.2]⟩,hEevent,hDevent⟩

end SquaresInCircles.Eight.OriginalECircle
end
end
end

section
/-!
## The five-corner chain of a ring of squares

Seven squares `K` in the order H, G, A, B, T, D, E, with the frames of the model
(`PhysicalFrames K t`: H and G turned by `t`, the others axis-parallel) and nonnegative gaps
`gap K t i` along the normals of the model (`RetainedSeparators K t`), give five corners
`chain K t`, a vertex of each of the anchors A, B, D, E and H (`anchorIndex`,
`corner_is_original_vertex`). The five residuals of the spans are sums of the seven gaps
(`residual_identity`), so the chain spans for `0 ≤ t ≤ π/4` (`chain_spans`), and squares in the
disk of radius `R` give `Eight.radius ≤ R` (`radius_lower_bound`) by the definition of the radius
as an infimum.

The same identities describe the equality case. If the chain is a given configuration `d`, the
anchors have the centres of `d` (`original_anchor_centers`); if the residuals vanish, so do the
seven gaps (`all_original_contacts_tight`), and the centres of T and G lie on the two contact
lines of `d` (`original_sliders`).
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight
namespace OriginalFiveCorner
open GeometricModel

/-- The anchors A, B, D, E and H among the vertices H, G, A, B, T, D, E of the cycle. -/
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

/-- Each corner of the chain is a vertex of its anchor square. -/
theorem corner_is_original_vertex {K : Vertex → UnitSquare} {t : ℝ}
    (hf : PhysicalFrames K t) (i : Fin 5) :
    closedSquare (K (anchorIndex i)) ((chain K t).point i) := by
  have hc (j : Vertex) := (hf j).1
  have hs (j : Vertex) := (hf j).2
  fin_cases i <;> constructor <;> apply abs_le.mpr <;> constructor <;>
    simp [chain,anchorIndex,cornerOffset,localX,localY,add,
      hc,hs,frameCos,frameSin,GeometricModel.e,GeometricModel.f] <;>
    nlinarith [Real.sin_sq_add_cos_sq t]

/-- The five residuals of the spans are sums of the seven gaps. -/
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

/-- The feasible radii are bounded below, by `0`. -/
theorem feasible_radii_bounded_below : BddBelow Eight.feasibleRadii := by
  refine ⟨0,?_⟩
  rintro R ⟨d,hd,hfit⟩
  exact hfit.1

/-- Seven squares with the frames of the model and nonnegative gaps, in the disk of radius `R`,
give `Eight.radius ≤ R`. -/
theorem radius_lower_bound {K : Vertex → UnitSquare} {t R : ℝ}
    (ht : 0≤t ∧ t≤Real.pi/4) (hR : 0≤R)
    (hf : PhysicalFrames K t) (hs : RetainedSeparators K t)
    (hc : ∀i p,closedSquare (K i) p → normSq p≤R^2) :
    Eight.radius≤R := by
  exact csInf_le feasible_radii_bounded_below
    ⟨chain K t,chain_spans ht hs,chain_fits hR hf hc⟩

/-- If the chain of `K` is `d`, then `t` is the angle of `d` and the anchors have the centres of
`d`. -/
theorem original_anchor_centers {K : Vertex → UnitSquare} {t : ℝ} {d : FiveCorner}
    (h : chain K t=d) :
    t=d.angle ∧ ∀i,(K (anchorIndex i)).center=d.anchorCenter i := by
  subst h
  refine ⟨rfl,?_⟩
  intro i
  fin_cases i <;> apply Prod.ext <;>
    simp [chain,anchorIndex,cornerOffset,FiveCorner.anchorCenter,add,GeometricModel.e,
      GeometricModel.f] <;> ring

/-- If the five residuals vanish, so do the seven nonnegative gaps. -/
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

/-- If the chain of `K` is `d` and all gaps vanish, the centres of T and G lie on the two contact
lines of `d`, at `d.topCenter z` and `d.tiltedCenter η`. -/
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

end OriginalFiveCorner
end SquaresInCircles.Eight
end
end
end

section
/-!
## The stationary witnesses of seven squares

Seven squares `K` in the order H, G, A, B, T, D, E with the frames of a stationary chain `d`
(`StationaryFrames d K`) have the separation thresholds `stationaryWidth d` on their edges
(`threshold_of_stationary_frames`), and every terminal owner of an edge has the stationary
normal (`terminal_owner_normal`). The gaps of the dual of `OriginalDual` at the centres of `K`
are the slacks of the edges along these normals (`dual_gap_as_projection`); they are nonnegative
when the witnesses have the stationary normals (`gaps_of_retained_normals`). The anchor offsets
of `d` give vertices of the anchor squares, wherever their centres lie
(`anchor_offsets_closed`), and these vertices lie in the disk of squared radius `q` when the
squares do (`vertices_at_original_radius`). Normals and frames pass between two cycles of
squares with the same frames, whatever their centres (`normals_of_same_frames`,
`frames_of_same_frames`).
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight
open Stationary Coordinates

/-- The cosines of the stationary frames, as quarter-turn representatives, in the order H, G, A,
B, T, D, E; `canonicalSin` gives the sines. -/
def canonicalCos (d : Coordinates) : Vertex → ℝ :=
  ![d.s,d.s,1,1,0,0,-1]

def canonicalSin (d : Coordinates) : Vertex → ℝ :=
  ![-d.c,-d.c,0,0,1,1,0]

def StationaryFrames (d : Coordinates) (K : Vertex → UnitSquare) : Prop :=
  ∀ i, (K i).cosine=canonicalCos d i ∧ (K i).sine=canonicalSin d i

/-- The forward normals of the edges in the stationary configuration, as vectors. -/
def stationaryNormal (d : Coordinates) : Vertex → Point :=
  ![d.e,d.e,(0,1),(-1,0),(-1,0),(0,-1),(d.s,-d.c)]

def stationaryWidth (d : Coordinates) (i : Vertex) : ℝ :=
  if i=1 ∨ i=6 then (1+d.c+d.s)/2 else 1

/-- The edges A–B, B–T, T–D, D–E, G–A, H–G, E–H of the dual, as edges of the cycle. -/
def dualEdge : Fin 7 → Vertex := ![2,3,4,5,1,0,6]

theorem threshold_of_stationary_frames {d : Coordinates}
    (hw : d.WeightDomain) {K : Vertex → UnitSquare}
    (hf : StationaryFrames d K) (i : Vertex) :
    SAT.threshold (K i) (K (next i))=stationaryWidth d i := by
  have hc (j : Vertex) := (hf j).1
  have hs (j : Vertex) := (hf j).2
  have hu : d.s^2+d.c^2=1 := by linarith [d.unit]
  have hz : d.c*d.s+-(d.s*d.c)=0 := by ring
  fin_cases i <;>
    simp [stationaryWidth,SAT.threshold,relativeC,relativeS,hc,hs,
      canonicalCos,canonicalSin,next,← pow_two,
      abs_of_pos hw.c_pos,abs_of_pos hw.s_pos,abs_neg,hu,hz] <;> ring

/-- With the stationary frames, every terminal owner of an edge has the stationary normal; on
G–A and E–H, between a turned and an axis-parallel square, the terminal owner is unique. -/
theorem terminal_owner_normal {d : Coordinates} {K : Vertex → UnitSquare}
    (hf : StationaryFrames d K) (i : Vertex) (j : Fin 4)
    (hj : j ∈ Candidate.terminalOwners i) :
    (forwardAxis j).normal (K i) (K (next i))=stationaryNormal d i := by
  have hc (k : Vertex) := (hf k).1
  have hs (k : Vertex) := (hf k).2
  fin_cases i <;> fin_cases j <;>
    simp [Candidate.terminalOwners] at hj <;>
    simp [forwardAxis,SignedAxis.normal,AxisOwner.normal,AxisSign.value,
      stationaryNormal,canonicalCos,canonicalSin,next,hc,hs,scale,
      Eight.e,Eight.f,Coordinates.e]

/-- The gaps of the dual at the centres of `K` are the slacks of the seven edges along the
stationary normals. -/
theorem dual_gap_as_projection (d : Coordinates) (K : Vertex → UnitSquare)
    (e : Fin 7) :
    OriginalDual.gap d (OriginalDual.ofCycle (fun i => (K i).center)) e =
      dot (stationaryNormal d (dualEdge e))
        (sub (K (next (dualEdge e))).center (K (dualEdge e)).center) -
      stationaryWidth d (dualEdge e) := by
  fin_cases e <;>
    simp [OriginalDual.gap,OriginalDual.ofCycle,OriginalDual.cycleIndex,
      dualEdge,stationaryNormal,stationaryWidth,next,Coordinates.e,
      Coordinates.f,dot,sub]
  ring

theorem gaps_of_retained_normals {d : Coordinates} (hw : d.WeightDomain)
    {K : Vertex → UnitSquare} (hf : StationaryFrames d K)
    (selected : Vertex → SignedAxis)
    (hfeasible : ∀ i, (selected i).Feasible (K i) (K (next i)))
    (hnormal : ∀ i, (selected i).normal (K i) (K (next i)) =
      stationaryNormal d i) :
    ∀ e : Fin 7, 0 ≤
      OriginalDual.gap d (OriginalDual.ofCycle (fun i => (K i).center)) e := by
  intro e
  rw [dual_gap_as_projection]
  have h := hfeasible (dualEdge e)
  change SAT.threshold (K (dualEdge e)) (K (next (dualEdge e))) ≤
    dot ((selected (dualEdge e)).normal
      (K (dualEdge e)) (K (next (dualEdge e))))
      (sub (K (next (dualEdge e))).center (K (dualEdge e)).center) at h
  rw [threshold_of_stationary_frames hw hf,hnormal] at h
  exact sub_nonneg.mpr h

/-- With the stationary frames, the anchor offsets of `d` give vertices of the anchor squares,
wherever their centres lie. -/
theorem anchor_offsets_closed {d : Coordinates} {K : Vertex → UnitSquare}
    (hf : StationaryFrames d K) (i : Fin 5) :
    closedSquare (K (OriginalDual.cycleIndex i.castSucc.castSucc))
      (add (OriginalDual.ofCycle (fun j => (K j).center) i.castSucc.castSucc)
        (d.anchorOffsets i)) := by
  have hc (j : Vertex) := (hf j).1
  have hs (j : Vertex) := (hf j).2
  fin_cases i <;> constructor <;> apply abs_le.mpr <;> constructor <;>
    simp [localX,localY,OriginalDual.ofCycle,
      OriginalDual.cycleIndex,anchorOffsets,inFrame,add,hc,hs,
      canonicalCos,canonicalSin] <;>
    nlinarith [d.unit]

/-- If the squares lie in the disk of squared radius `q`, so do the anchor vertices. -/
theorem vertices_at_original_radius {d : Coordinates} {q : ℝ}
    {K : Vertex → UnitSquare} (hf : StationaryFrames d K)
    (hc : ∀ i p, closedSquare (K i) p → normSq p ≤ q) :
    ∀ i : Fin 5,
      normSq (add
        (OriginalDual.ofCycle (fun j => (K j).center) i.castSucc.castSucc)
        (d.anchorOffsets i)) ≤ q :=
  fun i => hc _ _ (anchor_offsets_closed hf i)

/-- The stationary normals of the witnesses pass between two cycles of squares with the same
frames; their centres may differ. -/
theorem normals_of_same_frames {d : Coordinates}
    {K L : Vertex → UnitSquare} {a b : Vertex → SignedAxis}
    (hf : ∀ i, SameFrame (K i) (L i)) (ha : a=b)
    (hn : ∀ i, (b i).normal (L i) (L (next i))=stationaryNormal d i) :
    ∀ i, (a i).normal (K i) (K (next i))=stationaryNormal d i := by
  intro i
  rw [ha,signed_normal_same_frames (hf i) (hf (next i))]
  exact hn i

theorem frames_of_same_frames {d : Coordinates} {K L : Vertex → UnitSquare}
    (hKL : ∀ i, SameFrame (K i) (L i))
    (hL : StationaryFrames d L) : StationaryFrames d K :=
  fun i => ⟨(hKL i).1.trans (hL i).1,(hKL i).2.trans (hL i).2⟩

end SquaresInCircles.Eight
end
end
end

section
@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight

/-! ## Core avoidance gives the reserve of G–A -/

theorem sorted_core_primary_reserve {a b : ℝ} (hba : b≤a)
    (hcore : (1/12 : ℝ)^2 ≤
      (max (a-1/2) 0)^2+(max (b-1/2) 0)^2) :
    447/800<a := by
  by_contra! ha
  have hA : max (a-1/2) 0 ≤ 47/800 :=
    max_le (by linarith) (by norm_num)
  have hBA : max (b-1/2) 0 ≤ max (a-1/2) 0 :=
    max_le_max (by linarith) le_rfl
  have hB : max (b-1/2) 0 ≤ 47/800 := hBA.trans hA
  have hA2 := pow_le_pow_left₀ (le_max_right (a-1/2) 0) hA 2
  have hB2 := pow_le_pow_left₀ (le_max_right (b-1/2) 0) hB 2
  norm_num at hA2 hB2
  nlinarith

theorem original_core_primary_reserve {K : UnitSquare} (hc : CoreAvoiding K)
    (hsorted : beta K (0,0) ≤ alpha K (0,0)) :
    447/800 < alpha K (0,0) := by
  apply sorted_core_primary_reserve hsorted
  simpa only [coreDistanceSq,coreRadius] using
    (coreAvoiding_iff_distance K).1 hc

/-- The reserve of the comparison of GA0 with GA1: `aG - bA - A κ > 529/20000`. -/
theorem ga_coefficient_reserve {aG bA A κ : ℝ}
    (haG : 447/800<aG) (hbA : bA<11/25)
    (hA : A<71/50) (_hA0 : 0≤A)
    (hκ : κ<13/200) (hκ0 : 0≤κ) :
    529/20000 < aG-bA-A*κ := by
  have hp : A*κ ≤ (71/50 : ℝ)*(13/200) :=
    mul_le_mul hA.le hκ.le hκ0 (by norm_num)
  linarith

theorem ga_projection_difference {aG aA bA g s c κ : ℝ}
    (hhalf : 1-c=s*κ) :
    (aA*c-bA*s-g)-(aA-aG*s-g*c) =
      s*(aG-bA-(aA+g)*κ) := by
  linear_combination -(aA+g)*hhalf

/-- When GA0 is tight, as on the stationary source, the projection of GA1 is strictly below the
width `W`, so GA1 does not separate; no upper bound on the radial state of G is used. -/
theorem ga1_strictly_unavailable {aG aA bA g s c κ W : ℝ}
    (hs : 0<s) (hhalf : 1-c=s*κ)
    (haG : 447/800<aG) (hbA : bA<11/25)
    (hA : aA+g<71/50) (hA0 : 0≤aA+g)
    (hκ : κ<13/200) (hκ0 : 0≤κ)
    (hcontact : aA*c-bA*s-g=W) :
    aA-aG*s-g*c < W := by
  have hr := ga_coefficient_reserve haG hbA hA hA0 hκ hκ0
  have hr0 : 0<aG-bA-(aA+g)*κ := by linarith
  have hdiff : 0<(aA*c-bA*s-g)-(aA-aG*s-g*c) := by
    rw [ga_projection_difference hhalf]
    exact mul_pos hs hr0
  linarith

theorem eh_projection_difference (aH bH aE bE s c : ℝ) :
    (aH+aE*s-bE*c)-(aH*c+bH*s-bE) =
      (aE-bH)*s+(aH+bE)*(1-c) := by
  ring

/-- When EH1 is tight, as on the stationary source, the projection of EH0 is strictly below the
width `W`, so the witness of E–H has the normal of EH1. -/
theorem eh0_strictly_unavailable {aH bH aE bE s c W : ℝ}
    (hs : 0<s) (hc : c≤1) (hgap : bH<aE)
    (hpositive : 0≤aH+bE) (hcontact : aH+aE*s-bE*c=W) :
    aH*c+bH*s-bE < W := by
  have hfirst : 0<(aE-bH)*s := mul_pos (sub_pos.mpr hgap) hs
  have hsecond : 0≤(aH+bE)*(1-c) :=
    mul_nonneg hpositive (sub_nonneg.mpr hc)
  have hdiff := eh_projection_difference aH bH aE bE s c
  linarith

end SquaresInCircles.Eight
end
end
end

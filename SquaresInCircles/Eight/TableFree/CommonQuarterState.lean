module

public import SquaresInCircles.Eight.TableFree.CoreAngleEndpoint
public import SquaresInCircles.Eight.TableFree.QuarterWordGeometry
public import SquaresInCircles.Eight.Arithmetic.AffineArc

/-!
# Closed core and outer states for the common quarter-word label

Every support estimate is on the complete original boundary curve. The
outer endpoint rule follows from concavity of the positive circle branch;
the diagonal upper rule follows directly from the circle equation and
canonical order. These estimates do not depend on a candidate word.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.CommonQuarter

open CorePairGeometry

def radius : ℝ := Real.sqrt Q0
def outerAxial : ℝ := Real.sqrt (Q0-1/4)-1/2
def outerDiagonal : ℝ := Real.sqrt (Q0/2)-1/2

def OuterState (a b : ℝ) : Prop :=
  0≤b ∧ b≤a ∧ (a+1/2)^2+(b+1/2)^2=Q0

def State (kind : RadialKind) (a b : ℝ) : Prop :=
  if kind=.outer then OuterState a b else CoreState a b

def outerLabel (a b : ℝ) : ℝ := -9/100+(13/200)*a+(203/200)*b

def coreLabel (a b : ℝ) : ℝ := (73/10)*(7/12-a)+(291/250)*b

def label (kind : RadialKind) (a b : ℝ) : ℝ :=
  if kind=.outer then outerLabel a b else coreLabel a b

theorem radius_bounds : 1978/1000<radius ∧ radius<1979/1000 := by
  rw [radius]
  constructor
  · rw [Real.lt_sqrt (by norm_num)]
    norm_num [Q0]
  · rw [Real.sqrt_lt' (by norm_num)]
    norm_num [Q0]

theorem radius_sq : radius^2=Q0 :=
  Real.sq_sqrt (show (0:ℝ)≤Q0 by norm_num [Q0])

theorem outer_endpoint_bounds :
    141/100<outerAxial ∧ outerAxial<283/200 ∧
      89/100<outerDiagonal ∧ outerDiagonal<9/10 := by
  have h₁ : (191/100:ℝ)<Real.sqrt (Q0-1/4) := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num [Q0]
  have h₂ : Real.sqrt (Q0-1/4)<383/200 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num [Q0]
  have h₃ : (139/100:ℝ)<Real.sqrt (Q0/2) := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num [Q0]
  have h₄ : Real.sqrt (Q0/2)<14/10 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num [Q0]
  unfold outerAxial outerDiagonal
  refine ⟨?_,?_,?_,?_⟩ <;> linarith

theorem axial_circle : (outerAxial+1/2)^2+(1/2:ℝ)^2=Q0 := by
  have h := Real.sq_sqrt (show (0:ℝ)≤Q0-1/4 by norm_num [Q0])
  dsimp [outerAxial]
  nlinarith

theorem diagonal_circle : 2*(outerDiagonal+1/2)^2=Q0 := by
  have h := Real.sq_sqrt (show (0:ℝ)≤Q0/2 by norm_num [Q0])
  dsimp [outerDiagonal]
  nlinarith

/-- The complete outer arc lies between its axial and diagonal ends. -/
theorem outer_bounds {a b : ℝ} (h : OuterState a b) :
    outerDiagonal≤a ∧ a≤outerAxial ∧ 0≤b ∧ b≤outerDiagonal ∧
      a+b≤2*outerDiagonal := by
  obtain ⟨hb,hab,hcircle⟩ := h
  have ha0 : 0≤a := hb.trans hab
  have hc0 : 0<outerDiagonal := by linarith [outer_endpoint_bounds.2.2.1]
  have hao : 0<outerAxial := by linarith [outer_endpoint_bounds.1]
  have hsq := pow_le_pow_left₀ (show 0≤b+1/2 by linarith)
    (show b+1/2≤a+1/2 by linarith) 2
  have hac : outerDiagonal≤a := by
    by_contra! hn
    have hp := mul_pos (sub_pos.mpr hn)
      (show 0<(outerDiagonal+1/2)+(a+1/2) by linarith)
    nlinarith [diagonal_circle]
  have hbc : b≤outerDiagonal := by
    by_contra! hn
    have hp := mul_pos (sub_pos.mpr hn)
      (show 0<(b+1/2)+(outerDiagonal+1/2) by linarith)
    nlinarith [diagonal_circle]
  have hau : a≤outerAxial := by
    by_contra! hn
    have hp := mul_pos (sub_pos.mpr hn)
      (show 0<(a+1/2)+(outerAxial+1/2) by linarith)
    nlinarith [axial_circle,sq_nonneg b]
  have hsum : a+b≤2*outerDiagonal := by
    by_contra! hn
    have hp := mul_pos (show 0<a+b-2*outerDiagonal by linarith)
      (show 0<a+b+2*outerDiagonal+2 by linarith)
    nlinarith [diagonal_circle,sq_nonneg (a-b)]
  exact ⟨hac,hau,hb,hbc,hsum⟩

/-- Every increasing transverse linear support is largest at the diagonal. -/
theorem outer_diagonal_upper {a b X Y : ℝ} (h : OuterState a b)
    (hX : 0≤X) (hXY : X≤Y) :
    X*a+Y*b≤(X+Y)*outerDiagonal := by
  obtain ⟨hac,hau,hb,hbc,hsum⟩ := outer_bounds h
  have h₁ := mul_le_mul_of_nonneg_left hsum hX
  have h₂ := mul_le_mul_of_nonneg_left hbc (sub_nonneg.mpr hXY)
  nlinarith

lemma outer_branch {a b : ℝ} (h : OuterState a b) :
    a=Arithmetic.circleX (-1/2) radius b := by
  have ha : 0<a+1/2 := by linarith [(outer_bounds h).1,outer_endpoint_bounds.2.2.1]
  have he : radius^2-(b-(-1/2))^2=(a+1/2)^2 := by
    rw [radius_sq]
    linear_combination -h.2.2
  rw [Arithmetic.circleX,he,Real.sqrt_sq ha.le]
  ring

lemma outer_branch_endpoints :
    Arithmetic.circleX (-1/2) radius 0=outerAxial ∧
      Arithmetic.circleX (-1/2) radius outerDiagonal=outerDiagonal := by
  constructor
  · symm
    apply outer_branch
    exact ⟨le_rfl,by linarith [outer_endpoint_bounds.1],by simpa using axial_circle⟩
  · symm
    apply outer_branch
    exact ⟨by linarith [outer_endpoint_bounds.2.2.1],le_rfl,by nlinarith [diagonal_circle]⟩

lemma outer_radicand_pos {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    0<radius^2-(b-(-1/2))^2 := by
  have hc0 : 0<outerDiagonal+1/2 := by linarith [outer_endpoint_bounds.2.2.1]
  have hs := pow_le_pow_left₀ (show 0≤b+1/2 by linarith [hb.1])
    (show b+1/2≤outerDiagonal+1/2 by linarith [hb.2]) 2
  rw [radius_sq]
  nlinarith [diagonal_circle,sq_pos_of_pos hc0]

/-- A positive primary coefficient gives a concave circle functional.
A negative primary coefficient with nonnegative transverse coefficient is
already bounded by its axial value. Both alternatives are included. -/
theorem outer_endpoints_lower {a b X Y m : ℝ} (h : OuterState a b)
    (hY : 0≤Y) (ha : m≤X*outerAxial) (hd : m≤(X+Y)*outerDiagonal) :
    m≤X*a+Y*b := by
  obtain ⟨hac,hau,hb,hbc,hsum⟩ := outer_bounds h
  by_cases hX : 0≤X
  · have hl : m≤X*Arithmetic.circleX (-1/2) radius 0+Y*0 := by
      rw [outer_branch_endpoints.1]
      linarith
    have hu : m≤X*Arithmetic.circleX (-1/2) radius outerDiagonal+Y*outerDiagonal := by
      rw [outer_branch_endpoints.2]
      linarith
    have hh := Arithmetic.circle_endpoints_lower (X := X) (Y := Y)
      hX (fun z hz => outer_radicand_pos hz) (show b∈Icc 0 outerDiagonal from ⟨hb,hbc⟩) hl hu
    rw [← outer_branch h] at hh
    exact hh
  · have hm := mul_le_mul_of_nonpos_left hau (le_of_not_ge hX)
    have hy := mul_nonneg hY hb
    linarith

/-- The outer marker is positive and uniformly below `.882`. -/
theorem outer_label_bounds {a b : ℝ} (h : OuterState a b) :
    0<outerLabel a b ∧ outerLabel a b<441/500 := by
  have hl := outer_endpoints_lower (X := (13/200:ℝ)) (Y := (203/200:ℝ))
    (m := (183/2000:ℝ)) h (by norm_num)
    (by linarith [outer_endpoint_bounds.1])
    (by linarith [outer_endpoint_bounds.2.2.1])
  have hu := outer_diagonal_upper (X := (13/200:ℝ)) (Y := (203/200:ℝ))
    h (by norm_num) (by norm_num)
  dsimp [outerLabel]
  constructor <;> linarith [outer_endpoint_bounds.2.2.2]

/-- The common outer label differs from the transverse coordinate by less
than two hundredths, with its original primary coordinate retained. -/
theorem outer_label_error {a b : ℝ} (h : OuterState a b) :
    -(19/1000:ℝ)<outerLabel a b-b ∧ outerLabel a b-b<1/500 := by
  obtain ⟨hac,hau,hb,hbc,hsum⟩ := outer_bounds h
  have hl := outer_endpoints_lower (X := (13/200:ℝ)) (Y := (3/200:ℝ))
    (m := (711/10000:ℝ)) h (by norm_num)
    (by linarith [outer_endpoint_bounds.1])
    (by linarith [outer_endpoint_bounds.2.2.1])
  have hid : (outerAxial-a)*(outerAxial+a+1)=b^2+b := by
    nlinarith [h.2.2,axial_circle]
  have hm := mul_nonneg (sub_nonneg.mpr hau)
    (show 0≤4-(outerAxial+a+1) by linarith [outer_endpoint_bounds.2.1])
  have hbcut : b≤4*(outerAxial-a) := by nlinarith [sq_nonneg b]
  dsimp [outerLabel]
  constructor <;> nlinarith [outer_endpoint_bounds.2.1]

/-- The core marker is nonnegative and below `.83`; its two pieces meet
at the same actual label value. -/
theorem core_label_bounds {a b : ℝ} (h : CoreState a b) :
    0≤coreLabel a b ∧ coreLabel a b<83/100 := by
  obtain ⟨ha,hau,hb,hab,hbd⟩ := CoreAngleEndpoint.state_bounds h
  have had : CoreAngleEndpoint.diagonal≤a := by
    rcases h with ⟨rfl,hb,hbu⟩ | ⟨hb,hab,hcircle⟩
    · linarith [CoreAngleEndpoint.diagonal_bounds.2]
    · exact (CoreAngleEndpoint.corner_diagonal hb hab hcircle).2
  dsimp [coreLabel]
  constructor
  · nlinarith
  · nlinarith [CoreAngleEndpoint.diagonal_bounds.1]

theorem core_label_lower {a b : ℝ} (h : CoreState a b) :
    (291/250)*b≤coreLabel a b := by
  have hau := (CoreAngleEndpoint.state_bounds h).2.1
  dsimp [coreLabel]
  linarith

theorem core_small_side {a b : ℝ} (h : CoreState a b) (hb : b<1/2) :
    a=7/12 ∧ coreLabel a b=(291/250)*b := by
  rcases h with ⟨rfl,hb0,hb1⟩ | ⟨hb0,hab,hcircle⟩
  · constructor
    · rfl
    · dsimp [coreLabel]
      ring
  · linarith

theorem state_label_bounds {kind : RadialKind} {a b : ℝ} (h : State kind a b) :
    0≤label kind a b ∧ label kind a b<441/500 := by
  by_cases hk : kind=.outer
  · have hh := outer_label_bounds (by simpa [State,hk] using h)
    simpa [label,hk] using And.intro hh.1.le hh.2
  · have hh := core_label_bounds (by simpa [State,hk] using h)
    simp only [label,if_neg hk]
    exact ⟨hh.1,by linarith [hh.2]⟩

theorem state_bounds {kind : RadialKind} {a b : ℝ} (h : State kind a b) :
    11/20<a ∧ a<283/200 ∧ 0≤b ∧ b≤a ∧ b<9/10 := by
  by_cases hk : kind=.outer
  · have hh : OuterState a b := by simpa [State,hk] using h
    have hd := outer_bounds hh
    exact ⟨by linarith [hd.1,outer_endpoint_bounds.2.2.1],
      hd.2.1.trans_lt outer_endpoint_bounds.2.1,hh.1,hh.2.1,
      hd.2.2.2.1.trans_lt outer_endpoint_bounds.2.2.2⟩
  · have hh : CoreState a b := by simpa [State,hk] using h
    have hd := CoreAngleEndpoint.state_bounds hh
    have hal : 11/20<a := by
      rcases hh with ⟨rfl,_,_⟩ | ⟨hb,hab,hcircle⟩
      · norm_num
      · linarith [(corner_geometry hb hab hcircle).1]
    exact ⟨hal,by linarith [hd.2.1],hd.2.2.1,hd.2.2.2.1,
      by linarith [hd.2.2.2.2,CoreAngleEndpoint.diagonal_bounds.2]⟩

/-- Every actual original radial state satisfies the semantic state above. -/
theorem actual_state (C : BoundaryCycle Q0) (i : Vertex) :
    State (C.kind i) (C.a i) (C.b i) := by
  by_cases hk : C.kind i=.outer
  · simp only [State,if_pos hk]
    refine ⟨C.b_nonneg i,C.b_le_a i,?_⟩
    simpa [BoundaryState,hk,SquaresInCircles.phi] using C.boundary i
  · simpa [State,hk] using boundary_core_state C i hk

theorem commonValue_eq (kind : RadialKind) (σ : Bool) (a b : ℝ) :
    TableFreeWordGeometry.commonValue kind σ a b=(WordProblems.sign σ:ℝ)*label kind a b := by
  rfl

/-- A full-circle support remains valid even when its minimizer leaves the
allowed outer arc. No support-location hypothesis is introduced. -/
theorem outer_circle_lower {a b X Y : ℝ} (h : OuterState a b) :
    -(X+Y)/2-radius*Real.sqrt (X^2+Y^2)≤X*a+Y*b := by
  have hh := Arithmetic.full_circle_lower (v := (-1/2:ℝ))
    (ρ := radius) (a := a) (b := b) (X := X) (Y := Y)
    (by linarith [radius_bounds.1]) (by rw [radius_sq]; linear_combination h.2.2)
  linarith

/-- Positive primary and negative transverse coefficients attain their
core minimum at the diagonal, by the actual canonical coordinate bounds. -/
theorem core_diagonal_lower {a b X Y : ℝ} (h : CoreState a b)
    (hX : 0≤X) (hY : Y≤0) :
    (X+Y)*CoreAngleEndpoint.diagonal≤X*a+Y*b := by
  have hd := CoreAngleEndpoint.state_bounds h
  have ha : CoreAngleEndpoint.diagonal≤a := by
    rcases h with ⟨rfl,hb,hbu⟩ | ⟨hb,hab,hcircle⟩
    · linarith [CoreAngleEndpoint.diagonal_bounds.2]
    · exact (CoreAngleEndpoint.corner_diagonal hb hab hcircle).2
  have h₁ := mul_le_mul_of_nonneg_left ha hX
  have h₂ := mul_le_mul_of_nonpos_left hd.2.2.2.2 hY
  nlinarith

end SquaresInCircles.Eight.CommonQuarter

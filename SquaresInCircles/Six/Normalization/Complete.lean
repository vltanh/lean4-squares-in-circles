module

public import SquaresInCircles.Six.Normalization.WestStress
public import SquaresInCircles.Six.Construction

/-!
# Six squares: normalized packings

A `PinPacking` is a packing about the origin in the frame of its central square,
whose centre lies in the box `[0, c0]²`; the other five squares are labelled E,
N, W, D and S by the pins they hold. Each holds its own pin, has its phase in
the window of its label, and is separated from the central square along an axis
allowed for its label; every packing in a disk of squared radius at most `Q0` is
congruent to one (`pinPacking_of_ceiling`). The reflection in the diagonal maps
a pin packing to a pin packing, with E and N, and W and S, exchanged, and the
phase of D turned to `5π/2 - t`; so every packing is congruent, or congruent
after the reflection, to one with the phase of D at most `5π/4`. A square
separated along a side of C lies in a deep cap beyond it, faces it, and holds
the point half a unit beyond the side; so W and D are not both separated along
the west side, and D is not separated along the south side. Each exterior square
is separated along its own axis or along its matching side
(`PinPacking.two_choice`). W comes before D, so the phases increase in the order
E, N, W, D, S. With the phase of D at most `5π/4`, D is separated along its own
axis: otherwise W would be separated along its own axis, which
`west_cardinal_impossible` excludes. A `NormalizedPacking` records these facts.
-/

@[expose] public section

noncomputable section
namespace SquaresInCircles.Six.Normalization

/-! ### Pin-labelled packings -/

/-- The central square, followed by E, N, W, D and S. -/
def pinModel (c : Point) (t a b : Fin 5 → ℝ) : Fin 6 → UnitSquare :=
  Fin.cases (axisSquare c) (fun i => orientedSquare (t i) (a i) (b i))

@[simp] lemma pinModel_zero (c : Point) (t a b : Fin 5 → ℝ) :
    pinModel c t a b 0 = axisSquare c := rfl

@[simp] lemma pinModel_succ (c : Point) (t a b : Fin 5 → ℝ) (i : Fin 5) :
    pinModel c t a b i.succ = orientedSquare (t i) (a i) (b i) := rfl

/-- The real lift of a direction within `π` of `c`. -/
def liftNear (c : ℝ) (m : Direction) : ℝ := c+(m-(c:Direction)).toReal

lemma liftNear_class (c : ℝ) (m : Direction) : (liftNear c m : Direction) = m := by
  simp only [liftNear,Real.Angle.coe_add,Real.Angle.coe_toReal]
  abel

lemma liftNear_range (c : ℝ) (m : Direction) :
    -Real.pi ≤ liftNear c m-c ∧ liftNear c m-c ≤ Real.pi := by
  dsimp [liftNear]
  exact ⟨by linarith [(m-(c:Direction)).neg_pi_lt_toReal],
    by linarith [(m-(c:Direction)).toReal_le_pi]⟩

/-- A packing about the origin in the frame of its central square `Q(c)`,
`c ∈ [0, c0]²`, whose other squares are labelled E, N, W, D and S by the pins
they hold: each has a contained chart that avoids the core, its phase in the
window of its label, and is separated from C only along an axis allowed for its
label. -/
structure PinPacking (R : ℝ) where
  center : Point
  phase : Fin 5 → ℝ
  radial : Fin 5 → ℝ
  transverse : Fin 5 → ℝ
  packing : Packing (pinModel center phase radial transverse) (0,0) R
  box : (0 ≤ center.1 ∧ center.1 ≤ c0) ∧ (0 ≤ center.2 ∧ center.2 ≤ c0)
  contained : ∀ i, ContainedChart (radial i) |transverse i|
  avoidsCore : ∀ i, AvoidsCore (radial i) |transverse i|
  holds_pin : ∀ i, openSquare (orientedSquare (phase i) (radial i) (transverse i)) (pin i)
  window : ∀ i, (windowLower i : ℝ) < phase i-modelPhase i ∧
    phase i-modelPhase i < (windowUpper i : ℝ)
  separator : ∀ i, ∃ k, 0 ≤ centralMargin k (phase i) (radial i) (transverse i) center.1 center.2
  allowed_separator : ∀ i k,
    0 ≤ centralMargin k (phase i) (radial i) (transverse i) center.1 center.2 → k ∈ allowed i

namespace PinPacking
variable {R : ℝ} (P : PinPacking R)

/-- The six squares of the packing, C first. -/
def model : Fin 6 → UnitSquare := pinModel P.center P.phase P.radial P.transverse

lemma exterior_disjoint : InteriorDisjoint
    (fun i : Fin 5 => orientedSquare (P.phase i) (P.radial i) (P.transverse i)) := by
  intro i j hij
  exact P.packing.disjoint i.succ j.succ ((Fin.succ_injective _).ne hij)

end PinPacking

/-- A packing about the origin whose square `0` is axis-parallel, contains the
origin and has its centre in the closed first quadrant is congruent to a
pin-labelled packing. -/
theorem pinPacking_of_normalized {S : Fin 6 → UnitSquare} {c : Point} {R : ℝ}
    (hp : Packing S (0,0) R) (hQ : R^2 ≤ Q0) (haxis : S 0 = axisSquare c)
    (hinside : openSquare (S 0) (0,0)) (hx0 : 0 ≤ c.1) (hy0 : 0 ≤ c.2) :
    ∃ P : PinPacking R, Congruent S (0,0) P.model := by
  classical
  have hhalf : |c.1| < 1/2 ∧ |c.2| < 1/2 := by
    simpa [haxis,axisSquare_open,openAxisSquare,abs_neg] using hinside
  have hcore := central_box hp hQ (fun p => by rw [haxis]) hx0 hy0
    ((le_abs_self c.1).trans_lt hhalf.1) ((le_abs_self c.2).trans_lt hhalf.2)
  have hCcore : alpha (S 0) (0,0) ≤ c0 ∧ beta (S 0) (0,0) ≤ c0 := by
    simpa [haxis,alpha,beta,localX,localY,axisSquare,abs_neg,
      abs_of_nonneg hx0,abs_of_nonneg hy0] using hcore
  let F : Fin 5 → UnitSquare := fun i => S i.succ
  have hFdisj : InteriorDisjoint F :=
    fun i j hij => hp.disjoint i.succ j.succ ((Fin.succ_injective _).ne hij)
  have hout (i : Fin 5) : ¬ openSquare (F i) (0,0) := by
    intro hi
    exact hp.disjoint i.succ 0 (by intro he; have hh := congrArg Fin.val he; simp at hh)
      (0,0) ⟨hi,hinside⟩
  choose C hsorted using fun i : Fin 5 => sorted_square_chart (F i) (0,0)
  have hc (i : Fin 5) : ContainedChart (C i).a |(C i).signedB| :=
    (C i).exteriorChart_signed (hsorted i) (hout i) ((hp.phi_le i.succ).trans hQ)
  have hav (i : Fin 5) : AvoidsCore (C i).a |(C i).signedB| := by
    rw [signedB_abs]
    apply avoidsCore_of_disjoint (C i) (hsorted i) (hout i) hCcore
    exact hp.disjoint i.succ 0 (by intro he; have hh := congrArg Fin.val he; simp at hh)
  have hsat (i : Fin 5) (t : ℝ) (ht : (t:Direction)=(C i).phase) :
      ∃ k, 0 ≤ centralMargin k t (C i).a (C i).signedB c.1 c.2 := by
    apply central_separators_complete (hc i).half_le hx0 hy0
      (by linarith [hcore.1,c0_bounds.2]) (by linarith [hcore.2,c0_bounds.2])
    intro p hh
    exact hp.disjoint 0 i.succ
      (by intro he; have hh := congrArg Fin.val he; simp at hh) p
      ⟨by simpa [haxis] using hh.1,(chart_same_open_oriented (C i) ht p).mpr hh.2⟩
  have hcover (i : Fin 5) : ∃ j, openSquare (F i) (pin j) := by
    let t := (C i).phase.toReal
    have ht : (t:Direction)=(C i).phase := Real.Angle.coe_toReal _
    obtain ⟨j,hj⟩ := five_pin_cover (hc i) (hav i)
      hx0 hy0 hcore.1 hcore.2 (hsat i t ht)
    exact ⟨j,(chart_same_open_oriented (C i) ht _).mpr hj⟩
  obtain ⟨σ,hσ⟩ := pin_labels_of_covering F pin hFdisj hcover
  let t : Fin 5 → ℝ := fun i => liftNear (modelPhase i) (C (σ i)).phase
  let a : Fin 5 → ℝ := fun i => (C (σ i)).a
  let b : Fin 5 → ℝ := fun i => (C (σ i)).signedB
  have ht (i : Fin 5) : (t i:Direction)=(C (σ i)).phase := liftNear_class _ _
  have hsame (i : Fin 5) (p : Point) :
      openSquare (F (σ i)) p ↔ openSquare (orientedSquare (t i) (a i) (b i)) p :=
    chart_same_open_oriented (C (σ i)) (ht i) p
  have hpin (i : Fin 5) : openSquare (orientedSquare (t i) (a i) (b i)) (pin i) :=
    (hsame i _).mp (hσ i).1
  have huniq (i j : Fin 5)
      (hj : openSquare (orientedSquare (t i) (a i) (b i)) (pin j)) : j=i :=
    (hσ i).2.2 j ((hsame i (pin j)).mpr hj)
  have hwin (i : Fin 5) : (windowLower i:ℝ)<t i-modelPhase i ∧
      t i-modelPhase i<(windowUpper i:ℝ) :=
    labelled_window i (hc (σ i)) (hav (σ i)) hx0 hy0 hcore.1 hcore.2
      (hsat (σ i) (t i) (ht i)) (liftNear_range _ _) (huniq i)
  let τ := extendExteriorPerm σ
  have hmodelopen (i : Fin 6) (p : Point) :
      openSquare (pinModel c t a b i) p ↔ openSquare (S (τ i)) p := by
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [τ,haxis]
    · exact (hsame j p).symm
  have hmodelclosed (i : Fin 6) (p : Point) :
      closedSquare (pinModel c t a b i) p ↔ closedSquare (S (τ i)) p :=
    same_open_same_closed _ _ (hmodelopen i) p
  have hpack : Packing (pinModel c t a b) (0,0) R :=
    packing_of_same_sets (packing_relabel hp τ) hmodelopen hmodelclosed
  let P : PinPacking R := {
    center := c
    phase := t
    radial := a
    transverse := b
    packing := hpack
    box := ⟨⟨hx0,hcore.1⟩,⟨hy0,hcore.2⟩⟩
    contained := fun i => hc (σ i)
    avoidsCore := fun i => hav (σ i)
    holds_pin := hpin
    window := hwin
    separator := fun i => hsat (σ i) (t i) (ht i)
    allowed_separator := fun i k hk =>
      allowed_axis_of_pin i (hc (σ i)) (hav (σ i))
        hx0 hy0 hcore.1 hcore.2 (hpin i) k hk }
  refine ⟨P,?_⟩
  exact congruent_of_origin_sets τ (fun i p => (hmodelopen i p).symm)
    (fun i p => (hmodelclosed i p).symm)

/-- Every packing in a disk of squared radius at most `Q0` is congruent to a
pin-labelled packing. -/
theorem pinPacking_of_ceiling {S : Fin 6 → UnitSquare} {o : Point} {R : ℝ}
    (hp : Packing S o R) (hQ : R^2 ≤ Q0) :
    ∃ P : PinPacking R, Congruent S o P.model := by
  obtain ⟨F⟩ := normalize_frame_of_ceiling hp hQ
  obtain ⟨P,hP⟩ := pinPacking_of_normalized F.packing hQ F.central_eq F.central_inside
    F.cx_nonneg F.cy_nonneg
  exact ⟨P,congruent_trans F.congruent hP⟩

/-! ### The reflection in the diagonal -/

/-- The phase `π/2 - t` of a reflected square, shifted by `2π` for W, D and S so
that it lies in the window of its new label. -/
def mirroredPhase (i : Fin 5) (t : ℝ) : ℝ :=
  Real.pi/2-t + if i=0 ∨ i=1 then 0 else 2*Real.pi

lemma mirroredPhase_class (i : Fin 5) (t : ℝ) :
    (mirroredPhase i t : Direction) = (Real.pi/2-t : ℝ) := by
  unfold mirroredPhase
  split_ifs <;> simp [Real.Angle.coe_add]

lemma mirrored_oriented_open (i : Fin 5) (t a b : ℝ) (p : Point) :
    openSquare (orientedSquare (mirroredPhase i t) a (-b)) p ↔
      openSquare (orientedSquare t a b) (diagonalPoint p) :=
  (square_phase_open (mirroredPhase_class i t) p).trans (square_diagonal_membership t a b p)

lemma mirrored_window {R : ℝ} (P : PinPacking R) (i : Fin 5) :
    (windowLower i : ℝ) < mirroredPhase i (P.phase (mirrorPin i))-modelPhase i ∧
      mirroredPhase i (P.phase (mirrorPin i))-modelPhase i < (windowUpper i : ℝ) := by
  have h := P.window (mirrorPin i)
  fin_cases i <;> norm_num [mirroredPhase,mirrorPin,modelPhase,windowLower,windowUpper] at * <;>
    constructor <;> linarith [h.1,h.2]

/-- The reflection of a pin packing in the diagonal. -/
def PinPacking.mirror {R : ℝ} (P : PinPacking R) : PinPacking R := by
  classical
  let c := diagonalPoint P.center
  let t : Fin 5 → ℝ := fun i => mirroredPhase i (P.phase (mirrorPin i))
  let a : Fin 5 → ℝ := fun i => P.radial (mirrorPin i)
  let b : Fin 5 → ℝ := fun i => -P.transverse (mirrorPin i)
  let τ := extendExteriorPerm mirrorPin
  have hopen (i : Fin 6) (p : Point) :
      openSquare (pinModel c t a b i) p ↔
        openSquare (reflectDiagonalSquare (P.model (τ i))) p := by
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [pinModel_zero,τ,extendExteriorPerm_zero,PinPacking.model,
        reflectDiagonal_open]
      exact (diagonal_axis_open P.center p).symm
    · rw [pinModel_succ,reflectDiagonal_open]
      exact mirrored_oriented_open j _ _ _ p
  have hclosed (i : Fin 6) (p : Point) :
      closedSquare (pinModel c t a b i) p ↔
        closedSquare (reflectDiagonalSquare (P.model (τ i))) p :=
    same_open_same_closed _ _ (hopen i) p
  have hp : Packing (pinModel c t a b) (0,0) R :=
    packing_of_same_sets
      (packing_relabel (packing_reflectDiagonal P.packing) τ) hopen hclosed
  have hbox : (0 ≤ c.1 ∧ c.1 ≤ c0) ∧ (0 ≤ c.2 ∧ c.2 ≤ c0) := ⟨P.box.2,P.box.1⟩
  have hcontained (i : Fin 5) : ContainedChart (a i) |b i| := by
    simpa [a,b,abs_neg] using P.contained (mirrorPin i)
  have havoids (i : Fin 5) : AvoidsCore (a i) |b i| := by
    simpa [a,b,abs_neg] using P.avoidsCore (mirrorPin i)
  have hpin (i : Fin 5) : openSquare (orientedSquare (t i) (a i) (b i)) (pin i) := by
    apply (mirrored_oriented_open i _ _ _ _).mpr
    rw [pin_diagonal]
    exact P.holds_pin (mirrorPin i)
  have hwindow (i : Fin 5) : (windowLower i:ℝ) < t i-modelPhase i ∧
      t i-modelPhase i < (windowUpper i:ℝ) := mirrored_window P i
  have hsat (i : Fin 5) : ∃ k, 0 ≤ centralMargin k (t i) (a i) (b i) c.1 c.2 := by
    apply central_separators_complete (hcontained i).half_le hbox.1.1 hbox.2.1
      (by linarith [hbox.1.2,c0_bounds.2]) (by linarith [hbox.2.2,c0_bounds.2])
    exact hp.disjoint 0 i.succ (by intro he; have hh := congrArg Fin.val he; simp at hh)
  exact {
    center := c, phase := t, radial := a, transverse := b,
    packing := hp, box := hbox, contained := hcontained, avoidsCore := havoids,
    holds_pin := hpin, window := hwindow, separator := hsat,
    allowed_separator := fun i k hk =>
      allowed_axis_of_pin i (hcontained i) (havoids i)
        hbox.1.1 hbox.2.1 hbox.1.2 hbox.2.2 (hpin i) k hk }

lemma PinPacking.mirror_open {R : ℝ} (P : PinPacking R) (i : Fin 6) (p : Point) :
    openSquare (P.mirror.model i) p ↔
      openSquare (reflectDiagonalSquare (P.model (extendExteriorPerm mirrorPin i))) p := by
  refine Fin.cases ?_ (fun j => ?_) i
  · change openSquare (axisSquare (diagonalPoint P.center)) p ↔
      openSquare (reflectDiagonalSquare (axisSquare P.center)) p
    rw [reflectDiagonal_open]
    exact (diagonal_axis_open P.center p).symm
  · change openSquare (orientedSquare (mirroredPhase j (P.phase (mirrorPin j)))
      (P.radial (mirrorPin j)) (-P.transverse (mirrorPin j))) p ↔
      openSquare (reflectDiagonalSquare
        (orientedSquare (P.phase (mirrorPin j)) (P.radial (mirrorPin j))
          (P.transverse (mirrorPin j)))) p
    rw [reflectDiagonal_open]
    exact mirrored_oriented_open j _ _ _ p

/-- Reflecting the model of the reflected packing gives back the model, up to
the relabelling. -/
lemma PinPacking.congruent_reflected_mirror {R : ℝ} (P : PinPacking R) :
    Congruent P.model (0,0) (fun i => reflectDiagonalSquare (P.mirror.model i)) := by
  let τ := extendExteriorPerm mirrorPin
  have ho (i : Fin 6) (p : Point) :
      openSquare (P.model (τ i)) p ↔
        openSquare (reflectDiagonalSquare (P.mirror.model i)) p := by
    rw [reflectDiagonal_open,P.mirror_open,reflectDiagonal_open,
      diagonalPoint_involutive]
  exact congruent_of_origin_sets τ ho
    (fun i => same_open_same_closed _ _ (ho i))

/-- A pin packing is congruent, possibly after the reflection, to one in which
the phase of D is at most `5π/4`. -/
theorem normalize_diagonal_half {R : ℝ} (P : PinPacking R) :
    ∃ Q : PinPacking R, Q.phase 3 ≤ 5*Real.pi/4 ∧ CongruentOrDiagonal P.model (0,0) Q.model := by
  by_cases h : P.phase 3 ≤ 5*Real.pi/4
  · exact ⟨P,h,Or.inl (congruent_refl P.model)⟩
  · refine ⟨P.mirror,?_,Or.inr P.congruent_reflected_mirror⟩
    change mirroredPhase 3 (P.phase (mirrorPin 3)) ≤ 5*Real.pi/4
    norm_num [mirroredPhase,mirrorPin]
    linarith

/-! ### Sides of the central square -/

/-- The direction of a side of the central square. -/
def cardinalCenter : CentralAxis → ℝ
  | .east => 0
  | .north => Real.pi/2
  | .west => Real.pi
  | .south => 3*Real.pi/2
  | _ => 0

/-- The side of the central square matching each exterior square: east for E,
north for N, west for W and D, south for S. -/
def matchingCardinal : Fin 5 → CentralAxis := ![.east,.north,.west,.west,.south]

/-- The four sides of the central square among the seven axes. -/
def IsCardinal (k : CentralAxis) : Prop :=
  k=.east ∨ k=.north ∨ k=.west ∨ k=.south

/-- The distance from the origin to the line of a side of the central square
centred at `c`. -/
def cardinalDepth (c : Point) : CentralAxis → ℝ
  | .east => 1/2+c.1
  | .north => 1/2+c.2
  | .west => 1/2-c.1
  | .south => 1/2-c.2
  | _ => 0

/-- The point of the axis through the origin half a unit beyond a side of the
central square. -/
def cardinalPiercingPoint (c : Point) : CentralAxis → Point
  | .east => (1+c.1,0)
  | .north => (0,1+c.2)
  | .west => (c.1-1,0)
  | .south => (0,c.2-1)
  | _ => (0,0)

lemma matchingCardinal_isCardinal (i : Fin 5) : IsCardinal (matchingCardinal i) := by
  fin_cases i <;> simp [matchingCardinal,IsCardinal]

lemma south_sin : Real.sin (3*Real.pi/2) = -1 := by
  rw [show 3*Real.pi/2=Real.pi+Real.pi/2 by ring,Real.sin_add]
  simp

lemma south_cos : Real.cos (3*Real.pi/2) = 0 := by
  rw [show 3*Real.pi/2=Real.pi+Real.pi/2 by ring,Real.cos_add]
  simp

lemma cardinal_margin_local (k : CentralAxis) (hk : IsCardinal k) (c : Point) (t a b : ℝ) :
    centralMargin k t a b c.1 c.2 =
      centerX (t-cardinalCenter k) a b-angularWidth (t-cardinalCenter k)-cardinalDepth c k := by
  rcases hk with rfl | rfl | rfl | rfl
  all_goals simp only [centralMargin,cardinalCenter,cardinalDepth,centerX,centerY,angularWidth,
    Real.cos_sub,Real.sin_sub,Real.cos_pi,Real.sin_pi,
    Real.cos_pi_div_two,Real.sin_pi_div_two,south_sin,south_cos,abs_neg,
    mul_zero,mul_one,mul_neg_one,zero_add,add_zero,sub_zero,
    zero_sub,neg_neg]
  all_goals ring

lemma cardinal_piercing_coordinates (k : CentralAxis) (hk : IsCardinal k)
    (c : Point) (t a b : ℝ) :
    localX (orientedSquare (t-cardinalCenter k) a b) (cardinalDepth c k+1/2,0) =
        localX (orientedSquare t a b) (cardinalPiercingPoint c k) ∧
      localY (orientedSquare (t-cardinalCenter k) a b) (cardinalDepth c k+1/2,0) =
        localY (orientedSquare t a b) (cardinalPiercingPoint c k) := by
  rcases hk with rfl | rfl | rfl | rfl
  all_goals constructor <;> simp only [orientedSquare_localX,orientedSquare_localY,
    cardinalCenter,cardinalDepth,cardinalPiercingPoint,Real.cos_sub,Real.sin_sub,
    Real.cos_pi,Real.sin_pi,Real.cos_pi_div_two,
    Real.sin_pi_div_two,south_sin,south_cos,mul_zero,mul_one,mul_neg_one,zero_mul,
    zero_add,add_zero,sub_zero,zero_sub,neg_neg]
  all_goals ring

lemma cardinal_depth_bounds {c : Point}
    (hc : (0 ≤ c.1 ∧ c.1 ≤ c0) ∧ (0 ≤ c.2 ∧ c.2 ≤ c0))
    (k : CentralAxis) (hk : IsCardinal k) :
    coreRadius ≤ cardinalDepth c k ∧ cardinalDepth c k ≤ rho0-1/2 := by
  have hid := c0_add_coreRadius
  rcases hk with rfl | rfl | rfl | rfl <;> dsimp [cardinalDepth] <;>
    constructor <;> dsimp [c0,coreRadius] at * <;>
    linarith [hc.1.1,hc.1.2,hc.2.1,hc.2.2,rho0_bounds.1]

/-- A square separated from the central square along a side, with its phase
within `3π/4` of the direction of that side, has its phase within `2/5` of it:
turned to that direction, it lies in a deep cap and faces it. -/
theorem PinPacking.side_angle {R : ℝ} (P : PinPacking R) (i : Fin 5) {k : CentralAxis}
    (hk : IsCardinal k) (hwin : |P.phase i-cardinalCenter k| ≤ 3*Real.pi/4)
    (hm : 0 ≤ centralMargin k (P.phase i) (P.radial i) (P.transverse i) P.center.1 P.center.2) :
    |P.phase i-cardinalCenter k| < 2/5 := by
  rw [cardinal_margin_local k hk] at hm
  exact primary_cap_angle (by linarith [(P.contained i).half_le])
    ((P.contained i).u_lt_half (P.avoidsCore i)) (cardinal_depth_bounds P.box k hk).1 hwin
    (P.contained i).abs_box (by linarith)

/-- A square separated from the central square along the matching side has its
angle within `2/5` of the direction of that side. -/
lemma PinPacking.matching_cardinal_angle {R : ℝ} (P : PinPacking R) (i : Fin 5)
    (hi : 0 ≤ centralMargin (matchingCardinal i) (P.phase i) (P.radial i) (P.transverse i)
      P.center.1 P.center.2) :
    |P.phase i-cardinalCenter (matchingCardinal i)| < 2/5 := by
  refine P.side_angle i (matchingCardinal_isCardinal i) ?_ hi
  have hw := P.window i
  fin_cases i <;> norm_num [matchingCardinal,cardinalCenter,modelPhase,windowLower,
    windowUpper] at hw ⊢ <;> apply abs_le.mpr <;> constructor <;>
    linarith [hw.1,hw.2,Real.pi_gt_d2]

/-- In its half window, D is not separated from the central square along the
south side. -/
theorem PinPacking.diagonal_south_negative {R : ℝ} (P : PinPacking R)
    (hD : P.phase 3 ≤ 5*Real.pi/4) :
    centralMargin .south (P.phase 3) (P.radial 3) (P.transverse 3) P.center.1 P.center.2 < 0 := by
  by_contra! h
  have hw := P.window 3
  norm_num [modelPhase,windowLower,windowUpper] at hw
  have hh := P.side_angle 3 (k := .south) (by simp [IsCardinal]) (by
    norm_num [cardinalCenter]; apply abs_le.mpr; constructor <;>
      linarith [hw.1,hw.2,Real.pi_gt_d2]) h
  have hl := (abs_lt.mp hh).1
  norm_num [cardinalCenter] at hl
  linarith [Real.pi_gt_d2]

/-- Each exterior square is separated from the central square along the
matching side or along its own axis. -/
theorem PinPacking.two_choice {R : ℝ} (P : PinPacking R)
    (hD : P.phase 3 ≤ 5*Real.pi/4) (i : Fin 5) :
    0 ≤ centralMargin (matchingCardinal i) (P.phase i) (P.radial i) (P.transverse i)
        P.center.1 P.center.2 ∨
      0 ≤ centralMargin .own (P.phase i) (P.radial i) (P.transverse i) P.center.1 P.center.2 := by
  obtain ⟨k,hk⟩ := P.separator i
  have ha := P.allowed_separator i k hk
  by_cases hc : k=matchingCardinal i
  · exact Or.inl (by simpa [hc] using hk)
  by_cases ho : k=.own
  · exact Or.inr (by simpa [ho] using hk)
  have hlast : i=3 ∧ k=.south := by
    fin_cases i <;> cases k <;> simp [matchingCardinal,allowed] at *
  rcases hlast with ⟨rfl,rfl⟩
  linarith [P.diagonal_south_negative hD]

/-- Whether square `i` is not separated from the central square along the
matching side, so that it is separated along its own axis
(`PinPacking.own_of_ownAxis`). -/
def PinPacking.ownAxis {R : ℝ} (P : PinPacking R) (i : Fin 5) : Bool :=
  decide (centralMargin (matchingCardinal i) (P.phase i) (P.radial i) (P.transverse i)
    P.center.1 P.center.2 < 0)

lemma PinPacking.ownAxis_eq_true {R : ℝ} (P : PinPacking R) (i : Fin 5) :
    P.ownAxis i = true ↔
      centralMargin (matchingCardinal i) (P.phase i) (P.radial i) (P.transverse i)
        P.center.1 P.center.2 < 0 := by simp [PinPacking.ownAxis]

lemma PinPacking.ownAxis_eq_false {R : ℝ} (P : PinPacking R) (i : Fin 5) :
    P.ownAxis i = false ↔
      0 ≤ centralMargin (matchingCardinal i) (P.phase i) (P.radial i) (P.transverse i)
        P.center.1 P.center.2 := by simp [PinPacking.ownAxis,not_lt]

lemma PinPacking.own_of_ownAxis {R : ℝ} (P : PinPacking R)
    (hD : P.phase 3 ≤ 5*Real.pi/4) (i : Fin 5) (hi : P.ownAxis i = true) :
    0 ≤ centralMargin .own (P.phase i) (P.radial i) (P.transverse i) P.center.1 P.center.2 := by
  have hh := (P.ownAxis_eq_true i).mp hi
  rcases P.two_choice hD i with h | h
  · linarith
  · exact h

/-- A square separated from the central square along the matching side contains
the point half a unit beyond that side. -/
theorem PinPacking.cardinal_piercing {R : ℝ} (P : PinPacking R) (i : Fin 5)
    (hi : 0 ≤ centralMargin (matchingCardinal i) (P.phase i) (P.radial i) (P.transverse i)
      P.center.1 P.center.2) :
    openSquare (orientedSquare (P.phase i) (P.radial i) (P.transverse i))
      (cardinalPiercingPoint P.center (matchingCardinal i)) := by
  let k := matchingCardinal i
  have hk : IsCardinal k := matchingCardinal_isCardinal i
  have ht := P.matching_cardinal_angle i hi
  have hangle : |P.phase i-cardinalCenter k| ≤ Real.pi/4 := by linarith [Real.pi_gt_d2]
  have hh := (cardinal_depth_bounds P.box k hk).1
  have hm := hi
  rw [cardinal_margin_local k hk] at hm
  have hp := cap_piercing hangle hh (P.contained i).abs_box (by linarith)
  have hcoords := cardinal_piercing_coordinates k hk P.center (P.phase i) (P.radial i) (P.transverse i)
  simpa only [openSquare,hcoords.1,hcoords.2] using hp

/-- Two exterior squares with the same matching side, such as W and D, are not
both separated along it. -/
theorem PinPacking.one_per_side {R : ℝ} (P : PinPacking R) (i j : Fin 5)
    (hside : matchingCardinal i=matchingCardinal j)
    (hi : 0 ≤ centralMargin (matchingCardinal i) (P.phase i) (P.radial i) (P.transverse i)
      P.center.1 P.center.2)
    (hj : 0 ≤ centralMargin (matchingCardinal j) (P.phase j) (P.radial j) (P.transverse j)
      P.center.1 P.center.2) : i=j := by
  by_contra hij
  have hpi := P.cardinal_piercing i hi
  have hpj := P.cardinal_piercing j hj
  rw [← hside] at hpj
  exact P.exterior_disjoint i j hij _ ⟨hpi,hpj⟩

/-- The depth of the matching side is at most the cap depth at the angle of the
square. -/
theorem PinPacking.cardinal_cap_depth {R : ℝ} (P : PinPacking R) (i : Fin 5)
    (hi : 0 ≤ centralMargin (matchingCardinal i) (P.phase i) (P.radial i) (P.transverse i)
      P.center.1 P.center.2) :
    cardinalDepth P.center (matchingCardinal i) ≤
      capDepth |P.phase i-cardinalCenter (matchingCardinal i)| := by
  have hangle := P.matching_cardinal_angle i hi
  have hm := hi
  rw [cardinal_margin_local _ (matchingCardinal_isCardinal i)] at hm
  apply cap_support_bound_signed (a := P.radial i) (b := P.transverse i)
    (by linarith [Real.pi_gt_d2])
  · simpa [phi,abs_of_nonneg (show 0 ≤ P.radial i by linarith [(P.contained i).half_le])]
      using (P.contained i).containment
  · dsimp [centerX,angularWidth] at hm
    linarith

/-! ### The order of the exterior squares -/

/-- The angle of W is less than that of D. -/
theorem PinPacking.west_before_diagonal {R : ℝ} (P : PinPacking R)
    (hD : P.phase 3 ≤ 5*Real.pi/4) : P.phase 2 < P.phase 3 := by
  have hw := P.window 2
  have hd := P.window 3
  norm_num [windowLower,windowUpper,modelPhase] at hw hd
  have hpW : openSquare (orientedSquare (P.phase 2) (P.radial 2) (P.transverse 2))
      (polar (9/10) (11*Real.pi/12)) := by
    simpa [pin,polar,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm]
      using P.holds_pin 2
  have hpD : openSquare (orientedSquare (P.phase 3) (P.radial 3) (P.transverse 3))
      (polar (9/10) (5*Real.pi/4)) := by
    simpa [pin,polar,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm]
      using P.holds_pin 3
  exact SquaresInCircles.Six.west_before_diagonal (P.contained 2) (P.contained 3)
    (P.avoidsCore 2) (P.avoidsCore 3)
    ⟨by linarith [hw.1],by linarith [hw.2]⟩
    ⟨by linarith [hd.1,Real.pi_gt_d2],hD⟩ hpW hpD
    (P.exterior_disjoint 2 3 (by decide))

/-- In its half window, D has angle `π + d` with `-2/5 < d ≤ π/4`. -/
lemma PinPacking.diagonal_deviation {R : ℝ} (P : PinPacking R)
    (hD : P.phase 3 ≤ 5*Real.pi/4) :
    -2/5 < P.phase 3-Real.pi ∧ P.phase 3-Real.pi ≤ Real.pi/4 := by
  have h := P.window 3
  norm_num [windowLower,windowUpper,modelPhase] at h
  constructor <;> linarith [h.1,h.2,Real.pi_gt_d2]

/-- The angles of E, N, W, D and S increase, within one turn. -/
theorem PinPacking.cyclic_primary_order {R : ℝ} (P : PinPacking R)
    (hD : P.phase 3 ≤ 5*Real.pi/4) :
    P.phase 0 < P.phase 1 ∧ P.phase 1 < P.phase 2 ∧
      P.phase 2 < P.phase 3 ∧ P.phase 3 < P.phase 4 ∧ P.phase 4 < P.phase 0+2*Real.pi := by
  have he := P.window 0
  have hn := P.window 1
  have hw := P.window 2
  have hs := P.window 4
  norm_num [windowLower,windowUpper,modelPhase] at he hn hw hs
  exact ⟨by linarith [he.2,hn.1,Real.pi_gt_d2],
    by linarith [hn.2,hw.1,Real.pi_gt_d2],P.west_before_diagonal hD,
    by linarith [hs.1,Real.pi_gt_d2],by linarith [hs.2,he.1,Real.pi_gt_d2]⟩

/-! ### Normalized packings -/

/-- With the phase of D at most `5π/4`, D is not separated from C along the west
side of C. -/
theorem PinPacking.diagonal_west_negative {R : ℝ} (P : PinPacking R)
    (hD : P.phase 3 ≤ 5*Real.pi/4) :
    centralMargin .west (P.phase 3) (P.radial 3) (P.transverse 3) P.center.1 P.center.2 < 0 := by
  by_contra! hwestD
  have hwestW : ¬ 0 ≤ centralMargin .west (P.phase 2) (P.radial 2) (P.transverse 2)
      P.center.1 P.center.2 := by
    intro h
    have hi := P.one_per_side 2 3 rfl h hwestD
    norm_num at hi
  have hownW : 0 ≤ centralMargin .own (P.phase 2) (P.radial 2) (P.transverse 2)
      P.center.1 P.center.2 := by
    rcases P.two_choice hD 2 with h | h
    · exact False.elim (hwestW h)
    · exact h
  have hw := P.window 2
  norm_num [windowLower,windowUpper,modelPhase] at hw
  have hu := P.matching_cardinal_angle 3 hwestD
  have h3 : matchingCardinal 3 = .west := rfl
  rw [h3] at hu
  simp only [cardinalCenter] at hu
  have hub := abs_lt.mp hu
  have hord := P.west_before_diagonal hD
  have htEq : Real.pi+(P.phase 2-Real.pi)=P.phase 2 := by ring
  have huEq : Real.pi+(P.phase 3-Real.pi)=P.phase 3 := by ring
  apply west_cardinal_impossible (c := P.center)
    (t := P.phase 2-Real.pi) (u := P.phase 3-Real.pi)
    (a := P.radial 2) (b := P.transverse 2) (A := P.radial 3) (B := P.transverse 3)
    P.box (P.contained 2) (P.contained 3) (P.avoidsCore 2) (P.avoidsCore 3)
    (by linarith [hw.1]) (by linarith [hub.1]) (by linarith [hub.2]) (by linarith)
  · simpa only [htEq] using hownW
  · simpa only [huEq] using hwestD
  · simpa only [htEq,huEq] using P.exterior_disjoint 2 3 (by decide)

/-- With the phase of D at most `5π/4`, D is separated from C along its own
axis. -/
theorem PinPacking.diagonal_own_axis {R : ℝ} (P : PinPacking R)
    (hD : P.phase 3 ≤ 5*Real.pi/4) :
    P.ownAxis 3 = true ∧
      0 ≤ centralMargin .own (P.phase 3) (P.radial 3) (P.transverse 3) P.center.1 P.center.2 := by
  have hneg := P.diagonal_west_negative hD
  have hbit : P.ownAxis 3=true := by
    apply (P.ownAxis_eq_true 3).mpr
    exact hneg
  exact ⟨hbit,P.own_of_ownAxis hD 3 hbit⟩

/-- A pin packing in which the phase of D is at most `5π/4`. -/
structure NormalizedPacking (R : ℝ) extends PinPacking R where
  diagonal_half : phase 3 ≤ 5*Real.pi/4

namespace NormalizedPacking
variable {R : ℝ} (P : NormalizedPacking R)

/-- The angle of an exterior square from the direction of its matching side. -/
def deviation (i : Fin 5) : ℝ := P.phase i-cardinalCenter (matchingCardinal i)

/-- The angle of D from the west direction. -/
def diagonalAngle : ℝ := P.phase 3-Real.pi

lemma primary_order :
    P.phase 0 < P.phase 1 ∧ P.phase 1 < P.phase 2 ∧ P.phase 2 < P.phase 3 ∧
      P.phase 3 < P.phase 4 ∧ P.phase 4 < P.phase 0+2*Real.pi :=
  P.toPinPacking.cyclic_primary_order P.diagonal_half

lemma diagonal_angle_bounds : -2/5 < P.diagonalAngle ∧ P.diagonalAngle ≤ Real.pi/4 :=
  P.toPinPacking.diagonal_deviation P.diagonal_half

lemma two_choice (i : Fin 5) :
    0 ≤ centralMargin (matchingCardinal i) (P.phase i) (P.radial i) (P.transverse i)
      P.center.1 P.center.2 ∨
    0 ≤ centralMargin .own (P.phase i) (P.radial i) (P.transverse i) P.center.1 P.center.2 :=
  P.toPinPacking.two_choice P.diagonal_half i

lemma own_separator (i : Fin 5) (hi : P.ownAxis i=true) :
    0 ≤ centralMargin .own (P.phase i) (P.radial i) (P.transverse i) P.center.1 P.center.2 :=
  P.toPinPacking.own_of_ownAxis P.diagonal_half i hi

lemma cardinal_separator (i : Fin 5) (hi : P.ownAxis i=false) :
    0 ≤ centralMargin (matchingCardinal i) (P.phase i) (P.radial i) (P.transverse i)
      P.center.1 P.center.2 :=
  (P.toPinPacking.ownAxis_eq_false i).mp hi

lemma cardinal_angle (i : Fin 5) (hi : P.ownAxis i=false) : |P.deviation i| < 2/5 :=
  P.toPinPacking.matching_cardinal_angle i (P.cardinal_separator i hi)

lemma diagonal_own : P.ownAxis 3=true := (P.toPinPacking.diagonal_own_axis P.diagonal_half).1

end NormalizedPacking

/-- A packing in a disk of squared radius at most `Q0` is congruent to a
normalized packing or to its reflection in the diagonal. -/
theorem normalize_of_ceiling {S : Fin 6 → UnitSquare} {o : Point} {R : ℝ}
    (hp : Packing S o R) (hQ : R^2 ≤ Q0) :
    ∃ P : NormalizedPacking R, CongruentOrDiagonal S o P.model := by
  obtain ⟨P,hP⟩ := pinPacking_of_ceiling hp hQ
  obtain ⟨Q,hD,hQ'⟩ := normalize_diagonal_half P
  let N : NormalizedPacking R := ⟨Q,hD⟩
  refine ⟨N,?_⟩
  rcases hQ' with h | h
  · exact Or.inl (congruent_trans hP h)
  · exact Or.inr (congruent_trans hP h)

/-- The same for a disk of squared radius at most `qStar`, which is below
`Q0`. -/
theorem normalize {S : Fin 6 → UnitSquare} {o : Point} {R : ℝ}
    (hp : Packing S o R) (hR : R^2 ≤ Six.qStar) :
    ∃ P : NormalizedPacking R, CongruentOrDiagonal S o P.model :=
  normalize_of_ceiling hp (hR.trans Six.qStar_lt_Q0.le)

end SquaresInCircles.Six.Normalization

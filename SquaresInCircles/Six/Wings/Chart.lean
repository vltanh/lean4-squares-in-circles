import SquaresInCircles.Six.Separators.Signs

/-!
# The wings in the frames of the squares

Read W, D and S at the phases `π - v`, `π + d` and `3π/2 + s`, each with the
coordinates `(a, b)` of its centre in its own frame, and the centre of C at
`(cx, cy)`. A separation of C from W, S or D, along an axis of the exterior
square or a side of C, and a separation of D from W or S along a secondary
axis, is then a linear inequality in the coordinates with sinusoids of the
angles as coefficients. In the model W and D are separated along the secondary
axis of W, and D and S along that of S: these are the two wings. The
reflection in the diagonal exchanges W and S: it maps the angles `(v, s, d)` to
`(s, v, π/2 - d)`, negates the transverse coordinates and exchanges `cx` and
`cy`, and it carries the separations of a missing west wing to those of a
missing south wing.
-/

noncomputable section
namespace SquaresInCircles.Six.Wings
open Normalization

/-- W, D and S at the phases `π - v`, `π + d` and `3π/2 + s`, with their centres
at `(aW, bW)`, `(aD, bD)` and `(aS, bS)` in their frames and inside the disk; the
centre `(cx, cy)` of C in the box `[0, c0]²`; and D separated from C along its
own axis. -/
structure Chart where
  v : ℝ
  s : ℝ
  d : ℝ
  aW : ℝ
  bW : ℝ
  aD : ℝ
  bD : ℝ
  aS : ℝ
  bS : ℝ
  cx : ℝ
  cy : ℝ
  west : ContainedChart aW |bW|
  diagonal : ContainedChart aD |bD|
  south : ContainedChart aS |bS|
  box : (0 ≤ cx ∧ cx ≤ c0) ∧ (0 ≤ cy ∧ cy ≤ c0)
  diagonal_own : 1/2+angularWidth d ≤ aD+cx*Real.cos d+cy*Real.sin d

namespace Chart
variable (X : Chart)

/-- C and W are separated along the own axis of W. -/
def WestOwn : Prop := 1/2+angularWidth X.v ≤ X.aW+X.cx*Real.cos X.v-X.cy*Real.sin X.v

/-- C and W are separated along the west side of C. -/
def WestSide : Prop := 1/2+angularWidth X.v ≤ X.aW*Real.cos X.v+X.bW*Real.sin X.v+X.cx

/-- C and S are separated along the own axis of S. -/
def SouthOwn : Prop := 1/2+angularWidth X.s ≤ X.aS-X.cx*Real.sin X.s+X.cy*Real.cos X.s

/-- C and S are separated along the south side of C. -/
def SouthSide : Prop := 1/2+angularWidth X.s ≤ X.aS*Real.cos X.s-X.bS*Real.sin X.s+X.cy

/-- W and D are separated along the secondary axis of W, as in the model. -/
def WestWing : Prop :=
  1/2+angularWidth (X.d+X.v) ≤ X.aD*Real.sin (X.d+X.v)+X.bD*Real.cos (X.d+X.v)-X.bW

/-- W and D are separated along the secondary axis of D. -/
def WestDiagonal : Prop :=
  1/2+angularWidth (X.d+X.v) ≤ X.aW*Real.sin (X.d+X.v)-X.bW*Real.cos (X.d+X.v)+X.bD

/-- D and S are separated along the secondary axis of S, as in the model. -/
def SouthWing : Prop :=
  1/2+angularWidth (X.d-X.s) ≤ X.bS+X.aD*Real.cos (X.d-X.s)-X.bD*Real.sin (X.d-X.s)

/-- D and S are separated along the secondary axis of D. -/
def SouthDiagonal : Prop :=
  1/2+angularWidth (X.d-X.s) ≤ X.aS*Real.cos (X.d-X.s)+X.bS*Real.sin (X.d-X.s)-X.bD

/-- The separations of a missing south wing: W and D along the secondary axis of
W, and D and S along that of D. -/
structure MissingSouth : Prop where
  west : X.WestWing
  south : X.SouthDiagonal

/-- The separations of a missing west wing: W and D along the secondary axis of
D, and D and S along that of S. -/
structure MissingWest : Prop where
  west : X.WestDiagonal
  south : X.SouthWing

/-- The reflection in the diagonal: W and S exchanged, `d` replaced by `π/2 - d`,
the transverse coordinates negated and the coordinates of C exchanged. -/
def reflect : Chart where
  v := X.s
  s := X.v
  d := Real.pi/2-X.d
  aW := X.aS
  bW := -X.bS
  aD := X.aD
  bD := -X.bD
  aS := X.aW
  bS := -X.bW
  cx := X.cy
  cy := X.cx
  west := by simpa only [abs_neg] using X.south
  diagonal := by simpa only [abs_neg] using X.diagonal
  south := by simpa only [abs_neg] using X.west
  box := ⟨X.box.2,X.box.1⟩
  diagonal_own := by
    rw [angularWidth_half_pi_sub,Real.cos_pi_div_two_sub,Real.sin_pi_div_two_sub]
    linarith [X.diagonal_own]

variable {X}

lemma SouthOwn.reflect (h : X.SouthOwn) : X.reflect.WestOwn := by
  simp only [SouthOwn,WestOwn,Chart.reflect] at *
  linarith

lemma WestOwn.reflect (h : X.WestOwn) : X.reflect.SouthOwn := by
  simp only [SouthOwn,WestOwn,Chart.reflect] at *
  linarith

lemma WestSide.reflect (h : X.WestSide) : X.reflect.SouthSide := by
  simp only [SouthSide,WestSide,Chart.reflect] at *
  linarith

/-- A missing west wing is a missing south wing of the reflection. -/
lemma MissingWest.reflect (h : X.MissingWest) : X.reflect.MissingSouth := by
  have hw := h.west
  have hs := h.south
  constructor
  · change 1/2+angularWidth (Real.pi/2-X.d+X.s) ≤
      X.aD*Real.sin (Real.pi/2-X.d+X.s)+(-X.bD)*Real.cos (Real.pi/2-X.d+X.s)-(-X.bS)
    rw [show Real.pi/2-X.d+X.s=Real.pi/2-(X.d-X.s) by ring,angularWidth_half_pi_sub,
      Real.sin_pi_div_two_sub,Real.cos_pi_div_two_sub]
    simp only [SouthWing] at hs
    linarith
  · change 1/2+angularWidth (Real.pi/2-X.d-X.v) ≤
      X.aW*Real.cos (Real.pi/2-X.d-X.v)+(-X.bW)*Real.sin (Real.pi/2-X.d-X.v)-(-X.bD)
    rw [show Real.pi/2-X.d-X.v=Real.pi/2-(X.d+X.v) by ring,angularWidth_half_pi_sub,
      Real.sin_pi_div_two_sub,Real.cos_pi_div_two_sub]
    simp only [WestDiagonal] at hw
    linarith

end Chart

variable {R : ℝ} (P : NormalizedPacking R)

/-- The chart of W, D and S in a normalized packing. -/
def chart : Chart where
  v := -P.deviation 2
  s := P.deviation 4
  d := P.diagonalAngle
  aW := P.radial 2
  bW := P.transverse 2
  aD := P.radial 3
  bD := P.transverse 3
  aS := P.radial 4
  bS := P.transverse 4
  cx := P.center.1
  cy := P.center.2
  west := P.contained 2
  diagonal := P.contained 3
  south := P.contained 4
  box := P.box
  diagonal_own := by
    have h := P.own_separator 3 P.diagonal_own
    rw [show P.phase 3=P.diagonalAngle+Real.pi by
      dsimp [NormalizedPacking.diagonalAngle]; ring] at h
    simp only [centralMargin,centralNormal,angularWidth,Real.cos_add_pi,Real.sin_add_pi,
      abs_neg] at h
    dsimp [angularWidth]
    linarith

lemma west_phase : P.phase 2=Real.pi-(chart P).v := by
  rw [P.phase_from_deviation 2,show cardinalCenter (matchingCardinal 2)=Real.pi from rfl]
  dsimp [chart]
  ring

lemma diagonal_phase : P.phase 3=Real.pi+(chart P).d := by
  dsimp [chart,NormalizedPacking.diagonalAngle]
  ring

lemma south_phase : P.phase 4=3*Real.pi/2+(chart P).s := P.phase_from_deviation 4

variable {P}

lemma west_own (hW : P.ownAxis 2=true) : (chart P).WestOwn := by
  have h := P.own_separator 2 hW
  rw [west_phase] at h
  simp only [centralMargin,centralNormal,angularWidth,Real.cos_pi_sub,Real.sin_pi_sub,
    abs_neg] at h
  simp only [Chart.WestOwn,angularWidth]
  dsimp [chart] at h ⊢
  linarith

lemma west_side (hW : P.ownAxis 2=false) : (chart P).WestSide := by
  have h := P.cardinal_separator 2 hW
  change 0 ≤ centralMargin .west (P.phase 2) (P.radial 2) (P.transverse 2)
    P.center.1 P.center.2 at h
  rw [west_phase] at h
  simp only [centralMargin,centerX,angularWidth,Real.cos_pi_sub,Real.sin_pi_sub,abs_neg] at h
  simp only [Chart.WestSide,angularWidth]
  dsimp [chart] at h ⊢
  linarith

lemma south_own (hS : P.ownAxis 4=true) : (chart P).SouthOwn := by
  have h := P.own_separator 4 hS
  rw [south_phase] at h
  simp only [centralMargin,centralNormal,angularWidth,Real.cos_add,Real.sin_add,
    south_cos,south_sin,zero_mul,neg_one_mul,add_zero,zero_sub,neg_neg,abs_neg] at h
  simp only [Chart.SouthOwn,angularWidth]
  dsimp [chart] at h ⊢
  linarith

lemma south_side (hS : P.ownAxis 4=false) : (chart P).SouthSide := by
  have h := P.cardinal_separator 4 hS
  change 0 ≤ centralMargin .south (P.phase 4) (P.radial 4) (P.transverse 4)
    P.center.1 P.center.2 at h
  rw [south_phase] at h
  simp only [centralMargin,centerY,angularWidth,Real.cos_add,Real.sin_add,south_cos,
    south_sin,zero_mul,neg_one_mul,add_zero,zero_sub,neg_neg,abs_neg] at h
  simp only [Chart.SouthSide,angularWidth]
  dsimp [chart] at h ⊢
  linarith

lemma west_wing (h : SAT.threshold (P.square 2) (P.square 3) ≤
    dot (normalY (P.square 2)) (sub (P.square 3).center (P.square 2).center)) :
    (chart P).WestWing := by
  change SAT.threshold (P.square 2) (P.square 3) ≤
    frameY (P.square 2) (sub (P.square 3).center (P.square 2).center) at h
  rw [P.square_def 2,P.square_def 3,west_phase,diagonal_phase,oriented_pair_threshold,
    pair_frameY_left,show Real.pi+(chart P).d-(Real.pi-(chart P).v)=(chart P).d+(chart P).v by
      ring] at h
  exact h

lemma west_diagonal (h : SAT.threshold (P.square 2) (P.square 3) ≤
    dot (normalY (P.square 3)) (sub (P.square 3).center (P.square 2).center)) :
    (chart P).WestDiagonal := by
  change SAT.threshold (P.square 2) (P.square 3) ≤
    frameY (P.square 3) (sub (P.square 3).center (P.square 2).center) at h
  rw [P.square_def 2,P.square_def 3,west_phase,diagonal_phase,oriented_pair_threshold,
    pair_frameY_right,show Real.pi+(chart P).d-(Real.pi-(chart P).v)=(chart P).d+(chart P).v by
      ring] at h
  simp only [Chart.WestDiagonal]
  dsimp [chart] at h ⊢
  linarith

lemma south_wing (h : SAT.threshold (P.square 3) (P.square 4) ≤
    dot (normalY (P.square 4)) (sub (P.square 4).center (P.square 3).center)) :
    (chart P).SouthWing := by
  change SAT.threshold (P.square 3) (P.square 4) ≤
    frameY (P.square 4) (sub (P.square 4).center (P.square 3).center) at h
  rw [P.square_def 3,P.square_def 4,diagonal_phase,south_phase,oriented_pair_threshold,
    pair_frameY_right,show 3*Real.pi/2+(chart P).s-(Real.pi+(chart P).d)=
      Real.pi/2-((chart P).d-(chart P).s) by ring,
    angularWidth_half_pi_sub,Real.sin_pi_div_two_sub,Real.cos_pi_div_two_sub] at h
  simp only [Chart.SouthWing]
  dsimp [chart] at h ⊢
  linarith

lemma south_diagonal (h : SAT.threshold (P.square 3) (P.square 4) ≤
    dot (normalY (P.square 3)) (sub (P.square 4).center (P.square 3).center)) :
    (chart P).SouthDiagonal := by
  change SAT.threshold (P.square 3) (P.square 4) ≤
    frameY (P.square 3) (sub (P.square 4).center (P.square 3).center) at h
  rw [P.square_def 3,P.square_def 4,diagonal_phase,south_phase,oriented_pair_threshold,
    pair_frameY_left,show 3*Real.pi/2+(chart P).s-(Real.pi+(chart P).d)=
      Real.pi/2-((chart P).d-(chart P).s) by ring,
    angularWidth_half_pi_sub,Real.sin_pi_div_two_sub,Real.cos_pi_div_two_sub] at h
  exact h

lemma missing_south (h : MissingSouthWing P) : (chart P).MissingSouth :=
  ⟨west_wing h.west_wing,south_diagonal h.from_diagonal⟩

lemma missing_west (h : MissingWestWing P) : (chart P).MissingWest :=
  ⟨west_diagonal h.from_diagonal,south_wing h.south_wing⟩

/-! The angles of a normalized packing. -/

lemma diagonal_range : 1/2 < (chart P).d ∧ (chart P).d ≤ Real.pi/4 :=
  ⟨normalized_diagonal_gt_half P,P.diagonal_angle_range.2⟩

lemma west_upper : (chart P).v < 2/3 := by
  have h := P.deviation_windows.2.2.1.1
  dsimp [chart]
  linarith

lemma south_upper : (chart P).s < 2/3 := P.deviation_windows.2.2.2.2

lemma west_own_angle (hW : P.ownAxis 2=true) : 0 < (chart P).v := by
  have h := own_west_negative P hW
  dsimp [chart]
  linarith

lemma south_own_angle (hS : P.ownAxis 4=true) : 0 < (chart P).s :=
  own_south_positive P hS

lemma west_side_angle (hW : P.ownAxis 2=false) : |(chart P).v| < 2/5 := by
  have h := P.cardinal_angle 2 hW
  dsimp [chart]
  rwa [abs_neg]

lemma south_side_angle (hS : P.ownAxis 4=false) : |(chart P).s| < 2/5 :=
  P.cardinal_angle 4 hS

/-- W and S separated from C along their own axes have `v + s < 24/25`. -/
lemma own_angle_sum (hW : P.ownAxis 2=true) (hS : P.ownAxis 4=true) :
    (chart P).v+(chart P).s < 24/25 := by
  have h := normalized_own_wing_angle_sum P hW hS
  dsimp [chart]
  linarith

end SquaresInCircles.Six.Wings

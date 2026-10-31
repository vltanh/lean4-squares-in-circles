module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import SquaresInCircles.Common.Basic
public import SquaresInCircles.Eight.ExactFamily.Envelope
public import SquaresInCircles.Eight.ExactFamily.CentralParameters

/-!
# Eight squares: the angle of the central square and its half-angle coordinate

The parameters of the statement describe the frame of the central square by an angle `θ`
(`Parameters`), those of `ExactFamily/Coordinates.lean` by the half-angle coordinate
`w = tan (θ/2)` (`EqualityParameters`). The maps `angleToHalf θ = sin θ / (1 + cos θ)` and
`halfToAngle w = 2 arctan w` are inverse to each other between the representatives
`-π/4 ≤ θ < π/4` (`Parameters.AngleRepresentative`) and the interval `1 - √2 ≤ w < √2 - 1`
(`angleToHalf_halfToAngle`, `halfToAngle_angleToHalf`, `angleToHalf_mem`, `halfToAngle_mem`);
the half-open interval contains the representative `-π/4` of the diagonal. They carry the
parameters across (`Parameters.toStationary`, `Parameters.ofStationary`) with the same central
square (`ofStationary_centralSquare`, `toStationary_centralSquare`).
-/

section
/-!
## The geometric model: frames, projections and the admissible family

The statement (`Geometry.lean`) gives the eight-square optimum by five corners
and a free central square. This file adds what the proof measures with: the
frame `e t`, `f t` of a turned square and projections onto it, the squared
distance of a square's farthest vertex from the origin, the separating-axis
margin of two squares, and the admissible parameters, whose models are the
optimal packings with the central square around the disk centre.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.GeometricModel

/-- The first axis of the frame turned by `t`. -/
def e (t : ℝ) : Point := (Real.cos t, Real.sin t)
/-- The second axis of the frame turned by `t`. -/
def f (t : ℝ) : Point := (-Real.sin t, Real.cos t)

/-- The projection of `p` on the direction `n`. -/
def projection (n p : Point) : ℝ := n.1 * p.1 + n.2 * p.2

/-- The squared distance from the origin of the farthest vertex of the unit
square centred at `p` and turned by `t`. -/
def containmentCost (p : Point) (t : ℝ) : ℝ :=
  (|projection (e t) p| + 1 / 2) ^ 2 + (|projection (f t) p| + 1 / 2) ^ 2

/-- Half the sum of the widths of two squares turned by `a` and `b`, along any
axis of either. -/
def separationWidth (a b : ℝ) : ℝ :=
  (1 + |Real.cos (a - b)| + |Real.sin (a - b)|) / 2

/-- How far an axis of one of two squares, turned by `a` and `b` with centres
`d` apart, separates them; they do not overlap when it is nonnegative. -/
def separationMargin (a b : ℝ) (d : Point) : ℝ :=
  max (max |projection (e a) d| |projection (f a) d|)
      (max |projection (e b) d| |projection (f b) d|) - separationWidth a b

/-- The squared radius of the two-height chain of upper chord width three. -/
def twoHeightRadiusSq (u v : ℝ) : ℝ :=
  ((9 + (u - v) ^ 2) * (9 + (4 - u - v) ^ 2)) / 36

end SquaresInCircles.Eight.GeometricModel

namespace SquaresInCircles.Eight.FiveCorner
open GeometricModel

/-- The centres of the seven squares of the ring, `H`, `G`, `A`, `B`, `T`, `D`,
`E`, with `T` at height `z` and `G` at offset `η`. -/
def exteriorCenter (d : FiveCorner) (z η : ℝ) : Fin 7 → Point :=
  ![d.anchorCenter 4, d.tiltedCenter η, d.anchorCenter 0, d.anchorCenter 1,
    d.topCenter z, d.anchorCenter 2, d.anchorCenter 3]

/-- The turns of the seven squares of the ring. -/
def exteriorAngle (d : FiveCorner) : Fin 7 → ℝ :=
  ![d.angle, d.angle, 0, 0, 0, 0, 0]

/-- The seven squares of the ring. -/
def exteriorSquare (d : FiveCorner) (z η : ℝ) (i : Fin 7) : UnitSquare :=
  turnedSquare (d.exteriorCenter z η i) (d.exteriorAngle i)

end SquaresInCircles.Eight.FiveCorner

namespace SquaresInCircles.Eight.Parameters
open GeometricModel

/-- The central square. -/
def centralSquare (p : Parameters) : UnitSquare := turnedSquare p.center p.angle

/-- The squares of `p` about the corners `d`, each square of the ring by its
turn: the central square, then `H`, `G`, `A`, `B`, `T`, `D`, `E`. -/
def model (d : FiveCorner) (p : Parameters) : Fin 8 → UnitSquare :=
  Fin.cons p.centralSquare (d.exteriorSquare p.top p.tilted)

/-- A turn in `[-π/4, π/4)`: every square has exactly one. -/
def AngleRepresentative (θ : ℝ) : Prop :=
  -Real.pi / 4 ≤ θ ∧ θ < Real.pi / 4

/-- The admissible parameters: `T` and `G` in the disk, `T` above and `G` below
the axis, the central square around the disk centre and separated from each
square of the ring. -/
structure Admissible (d : FiveCorner) (p : Parameters) : Prop where
  angle_mem : AngleRepresentative p.angle
  top_contained : containmentCost (d.topCenter p.top) 0 ≤ radius ^ 2
  tilted_contained : containmentCost (d.tiltedCenter p.tilted) d.angle ≤ radius ^ 2
  top_above_axis : 1 / 2 ≤ p.top
  tilted_below_axis :
    (d.tiltedCenter p.tilted).2 + (|Real.cos d.angle| + |Real.sin d.angle|) / 2 ≤ 0
  central_first : |projection (GeometricModel.e p.angle) p.center| < 1 / 2
  central_second : |projection (GeometricModel.f p.angle) p.center| < 1 / 2
  central_separated : ∀ i : Fin 7,
    0 ≤ separationMargin p.angle (d.exteriorAngle i)
      (sub (d.exteriorCenter p.top p.tilted i) p.center)

end SquaresInCircles.Eight.Parameters

namespace SquaresInCircles.Eight.GeometricModel

/-- The model of `p`, or its reflection in the diagonal. -/
def reflectedModel (reflected : Bool) (p : Parameters) : Fin 8 → UnitSquare :=
  if reflected then fun i => reflectSquare (p.model FiveCorner.selected i)
  else p.model FiveCorner.selected

/-- The models of admissible parameters and their reflections. -/
def admissibleModels : Set (Fin 8 → UnitSquare) :=
  {M | ∃ reflected : Bool, ∃ p : Parameters,
    p.Admissible FiveCorner.selected ∧ M = reflectedModel reflected p}

/-- The projection on the first axis of the frame turned by `t`, in coordinates. -/
theorem projection_e_sub (t : ℝ) (p q : Point) :
    projection (e t) (sub p q) = Real.cos t * (p.1 - q.1) + Real.sin t * (p.2 - q.2) := rfl

/-- The projection on the second axis of the frame turned by `t`, in coordinates. -/
theorem projection_f_sub (t : ℝ) (p q : Point) :
    projection (f t) (sub p q) = -Real.sin t * (p.1 - q.1) + Real.cos t * (p.2 - q.2) := rfl

@[simp] theorem projection_eq_dot (n p : Point) : projection n p = dot n p := rfl

@[simp] theorem e_unit (t : ℝ) : normSq (e t) = 1 := by
  simp [normSq, e]

@[simp] theorem f_unit (t : ℝ) : normSq (f t) = 1 := by
  simp [normSq, f]

@[simp] theorem e_dot_f (t : ℝ) : dot (e t) (f t) = 0 := by
  dsimp [e, f, dot]
  ring

@[simp] theorem square_zero (p : Point) : turnedSquare p 0 = axisSquare p := by
  simp [turnedSquare, axisSquare]

theorem localX_square_origin (p : Point) (t : ℝ) :
    localX (turnedSquare p t) (0, 0) = -projection (e t) p := by
  dsimp [localX, turnedSquare, projection, dot, e]
  ring

theorem localY_square_origin (p : Point) (t : ℝ) :
    localY (turnedSquare p t) (0, 0) = -projection (f t) p := by
  dsimp [localY, turnedSquare, projection, dot, f]
  ring

theorem origin_interior_iff (p : Point) (t : ℝ) :
    openSquare (turnedSquare p t) (0, 0) ↔
      |projection (e t) p| < 1 / 2 ∧ |projection (f t) p| < 1 / 2 := by
  simp only [openSquare, localX_square_origin, localY_square_origin, abs_neg]

theorem containmentCost_eq_phi (p : Point) (t : ℝ) :
    containmentCost p t = phi (alpha (turnedSquare p t) (0, 0))
      (beta (turnedSquare p t) (0, 0)) := by
  simp [containmentCost, phi, alpha, beta, localX_square_origin,
    localY_square_origin, abs_neg]

end SquaresInCircles.Eight.GeometricModel

namespace SquaresInCircles.Eight.FiveCorner
open GeometricModel

theorem feasibleRadii_nonneg {R : ℝ} (h : R ∈ feasibleRadii) : 0 ≤ R := by
  obtain ⟨d, hd, hR⟩ := h
  exact hR.1

theorem feasibleRadii_bddBelow : BddBelow feasibleRadii :=
  ⟨0, fun _ h => feasibleRadii_nonneg h⟩

/-- The width-three corner span gives an intrinsic radius bound. -/
theorem three_halves_le {d : FiveCorner} {R : ℝ}
    (hd : d.spans) (hR : d.fits R) : 3 / 2 ≤ R := by
  have hB := hR.2 1
  have hD := hR.2 2
  have hspan := hd.2.2.2.1
  have hBx : (d.point 1).1 ≤ R := by
    have hnonneg := sq_nonneg (d.point 1).2
    dsimp [normSq] at hB
    nlinarith [hR.1]
  have hDx : -R ≤ (d.point 2).1 := by
    have hnonneg := sq_nonneg (d.point 2).2
    dsimp [normSq] at hD
    nlinarith [hR.1]
  linarith

end SquaresInCircles.Eight.FiveCorner
end
end
end

section
@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.GeometricModel
open ExactFamily

def angleToHalf (θ : ℝ) : ℝ := Real.sin θ/(1+Real.cos θ)
def halfToAngle (w : ℝ) : ℝ := 2*Real.arctan w

theorem halfToAngle_frame (w : ℝ) :
    Real.cos (halfToAngle w)=halfAngleCos w ∧
      Real.sin (halfToAngle w)=halfAngleSin w := by
  have hp := halfAngle_den_pos w
  have hs := Real.sq_sqrt hp.le
  have hws := congrArg (fun x : ℝ => w*x) hs
  have hn : Real.sqrt (1+w^2)≠0 := ne_of_gt (Real.sqrt_pos.mpr hp)
  constructor
  · rw [halfToAngle,Real.cos_two_mul,Real.cos_arctan]
    dsimp [halfAngleCos]
    field_simp [hn,ne_of_gt hp]
    nlinarith
  · rw [halfToAngle,Real.sin_two_mul,Real.sin_arctan,Real.cos_arctan]
    dsimp [halfAngleSin]
    field_simp [hn,ne_of_gt hp]
    nlinarith

theorem old_frame_abs_lt_one {w : ℝ}
    (hw : 1-Real.sqrt 2≤w ∧ w<Real.sqrt 2-1) : |w|<1 := by
  have hs := Real.sqrt_nonneg (2:ℝ)
  have hsq := Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
  rw [abs_lt]
  constructor <;> nlinarith

theorem halfToAngle_mem {w : ℝ}
    (hw : 1-Real.sqrt 2≤w ∧ w<Real.sqrt 2-1) :
    Parameters.AngleRepresentative (halfToAngle w) := by
  have hsmall := abs_lt.mp (old_frame_abs_lt_one hw)
  have hd : 0<1-w^2 := by nlinarith
  have hr := Real.sqrt_nonneg (2:ℝ)
  have hr2 := Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
  have hlpoly : (w-1)^2≤2 := by
    have hh := mul_nonneg (show 0≤w-1+Real.sqrt 2 by linarith)
      (show 0≤Real.sqrt 2+1-w by linarith)
    nlinarith
  have hupoly : (w+1)^2<2 := by
    have hh := mul_pos (show 0<Real.sqrt 2-1-w by linarith)
      (show 0<Real.sqrt 2+w+1 by nlinarith)
    nlinarith
  have hl : -1≤2*w/(1-w^2) := (le_div_iff₀ hd).mpr (by nlinarith)
  have hu : 2*w/(1-w^2)<1 := (div_lt_iff₀ hd).mpr (by nlinarith)
  have hla := Real.arctan_strictMono.monotone hl
  have hua := Real.arctan_strictMono hu
  rw [Real.arctan_neg,Real.arctan_one] at hla
  rw [Real.arctan_one] at hua
  dsimp [Parameters.AngleRepresentative,halfToAngle]
  rw [Real.two_mul_arctan hsmall.1 hsmall.2]
  exact ⟨by linarith,hua⟩

theorem representative_frame {θ : ℝ} (hθ : Parameters.AngleRepresentative θ) :
    0<Real.cos θ ∧ -Real.cos θ≤Real.sin θ ∧ Real.sin θ<Real.cos θ := by
  have hmem : θ∈Set.Ioo (-(Real.pi/2)) (Real.pi/2) :=
    ⟨by linarith [hθ.1,Real.pi_pos],by linarith [hθ.2,Real.pi_pos]⟩
  have hc := Real.cos_pos_of_mem_Ioo hmem
  have hlo : Real.tan (-Real.pi/4)≤Real.tan θ := by
    apply Real.strictMonoOn_tan.monotoneOn
    · constructor <;> linarith [Real.pi_pos]
    · exact hmem
    · exact hθ.1
  have hhi : Real.tan θ<Real.tan (Real.pi/4) := by
    apply Real.strictMonoOn_tan hmem
      (show Real.pi/4∈Set.Ioo (-(Real.pi/2)) (Real.pi/2) by
        constructor <;> linarith [Real.pi_pos]) hθ.2
  have hl : -1≤Real.sin θ/Real.cos θ := by
    simpa [neg_div,Real.tan_neg,Real.tan_pi_div_four,Real.tan_eq_sin_div_cos] using hlo
  have hu : Real.sin θ/Real.cos θ<1 := by
    simpa [Real.tan_pi_div_four,Real.tan_eq_sin_div_cos] using hhi
  exact ⟨hc,by simpa using (le_div_iff₀ hc).mp hl,
    by simpa using (div_lt_iff₀ hc).mp hu⟩

theorem angleToHalf_mem {θ : ℝ} (hθ : Parameters.AngleRepresentative θ) :
    1-Real.sqrt 2≤angleToHalf θ ∧ angleToHalf θ<Real.sqrt 2-1 := by
  obtain ⟨hc,hl,hu⟩ := representative_frame hθ
  apply halfAngle_halfopen
    (show Real.cos θ^2+Real.sin θ^2=1 by
      nlinarith [Real.sin_sq_add_cos_sq θ]) hc hl hu

theorem angleToHalf_frame {θ : ℝ} (hθ : Parameters.AngleRepresentative θ) :
    halfAngleCos (angleToHalf θ)=Real.cos θ ∧
      halfAngleSin (angleToHalf θ)=Real.sin θ := by
  apply halfAngle_recover
    (show Real.cos θ^2+Real.sin θ^2=1 by
      nlinarith [Real.sin_sq_add_cos_sq θ]) (representative_frame hθ).1

@[simp] theorem angleToHalf_halfToAngle (w : ℝ) :
    angleToHalf (halfToAngle w)=w := by
  obtain ⟨hc,hs⟩ := halfToAngle_frame w
  rw [angleToHalf,hc,hs]
  dsimp [halfAngleCos,halfAngleSin]
  field_simp [ne_of_gt (halfAngle_den_pos w)]
  ring

theorem halfToAngle_angleToHalf {θ : ℝ} (hθ : Parameters.AngleRepresentative θ) :
    halfToAngle (angleToHalf θ)=θ := by
  have hw := abs_lt.mp (old_frame_abs_lt_one (angleToHalf_mem hθ))
  have hd : 1-(angleToHalf θ)^2≠0 := by nlinarith
  obtain ⟨hc,hs⟩ := angleToHalf_frame hθ
  have ht : 2*angleToHalf θ/(1-angleToHalf θ^2)=Real.tan θ := by
    rw [Real.tan_eq_sin_div_cos,← hc,← hs]
    dsimp [halfAngleCos,halfAngleSin]
    field_simp [ne_of_gt (halfAngle_den_pos (angleToHalf θ)),hd]
  rw [halfToAngle,Real.two_mul_arctan hw.1 hw.2,ht]
  exact Real.arctan_tan (by linarith [hθ.1,Real.pi_pos])
    (by linarith [hθ.2,Real.pi_pos])

private theorem unitSquare_eq {K L : UnitSquare} (h1 : K.center=L.center)
    (h2 : K.cosine=L.cosine) (h3 : K.sine=L.sine) : K=L := by
  cases K; cases L
  simp only at h1 h2 h3
  subst h1 h2 h3
  rfl

end SquaresInCircles.Eight.GeometricModel

namespace SquaresInCircles.Eight.Parameters
open GeometricModel ExactFamily

/-- The parameters with the half-angle coordinate `angleToHalf θ` in place of the angle; only the
equivalence of the two families uses it. -/
def toStationary (p : Parameters) : EqualityParameters :=
  ⟨p.center.1,p.center.2,angleToHalf p.angle,p.top,p.tilted⟩

def ofStationary (p : EqualityParameters) : Parameters :=
  ⟨p.center,halfToAngle p.w,p.z,p.eta⟩

@[simp] theorem toStationary_ofStationary (p : EqualityParameters) : (ofStationary p).toStationary=p := by
  cases p
  simp [toStationary,ofStationary,EqualityParameters.center]

theorem ofStationary_toStationary {p : Parameters} (hp : AngleRepresentative p.angle) :
    ofStationary p.toStationary=p := by
  cases p
  simp [toStationary,ofStationary,EqualityParameters.center,halfToAngle_angleToHalf hp]

theorem ofStationary_centralSquare (p : EqualityParameters) :
    (ofStationary p).centralSquare=p.centralSquare := by
  obtain ⟨hc,hs⟩ := halfToAngle_frame p.w
  exact unitSquare_eq rfl hc hs

theorem toStationary_centralSquare {p : Parameters} (hp : AngleRepresentative p.angle) :
    p.toStationary.centralSquare=p.centralSquare := by
  obtain ⟨hc,hs⟩ := angleToHalf_frame hp
  exact unitSquare_eq rfl hc hs

end SquaresInCircles.Eight.Parameters
end
end
end

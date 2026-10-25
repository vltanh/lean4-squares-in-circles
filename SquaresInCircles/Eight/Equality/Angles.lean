module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import SquaresInCircles.Eight.Stationary.CentralParameters
public import SquaresInCircles.Eight.Equality.Basic

/-!
# Eight squares: the angle of the central square and its half-angle coordinate

The parameters of the statement describe the frame of the central square by an angle `θ`
(`Parameters`), those of `Stationary/Coordinates.lean` by the half-angle coordinate
`w = tan (θ/2)` (`EqualityParameters`). The maps `angleToHalf θ = sin θ / (1 + cos θ)` and
`halfToAngle w = 2 arctan w` are inverse to each other between the representatives
`-π/4 ≤ θ < π/4` (`Parameters.AngleRepresentative`) and the interval `1 - √2 ≤ w < √2 - 1`
(`angleToHalf_halfToAngle`, `halfToAngle_angleToHalf`, `angleToHalf_mem`, `halfToAngle_mem`);
the half-open interval contains the representative `-π/4` of the diagonal. They carry the
parameters across (`Parameters.toStationary`, `Parameters.ofStationary`) with the same central
square (`ofStationary_centralSquare`, `toStationary_centralSquare`).
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.GeometricModel
open Stationary

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
open GeometricModel Stationary

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


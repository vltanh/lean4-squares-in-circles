module

public import SquaresInCircles.Eight.GeometricModel.EqualityModel
public import SquaresInCircles.Eight.GeometricModel.SquareGeometry
public import SquaresInCircles.Eight.ExactFamily.CentralParameters
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# Actual central angles and the old rational coordinate

Uncompiled source draft.  The map used only in this proof adapter is
`θ ↦ sin θ / (1 + cos θ)`, with inverse `w ↦ 2 arctan w`.
The half-open interval includes the negative diagonal representative.
-/

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

theorem physicalFrame_symm {K L : UnitSquare} (h : SamePhysicalFrame K L) :
    SamePhysicalFrame L K := by
  rcases h with ⟨hc,hs⟩ | ⟨hc,hs⟩ | ⟨hc,hs⟩ | ⟨hc,hs⟩ <;>
    simp_all [SamePhysicalFrame]

theorem physicalFrame_trans {K L M : UnitSquare}
    (h : SamePhysicalFrame K L) (g : SamePhysicalFrame L M) :
    SamePhysicalFrame K M := by
  rcases h with ⟨hc,hs⟩ | ⟨hc,hs⟩ | ⟨hc,hs⟩ | ⟨hc,hs⟩ <;>
    rcases g with ⟨gc,gs⟩ | ⟨gc,gs⟩ | ⟨gc,gs⟩ | ⟨gc,gs⟩ <;>
    simp_all [SamePhysicalFrame]

theorem representative_unique {θ φ : ℝ} {p q : Point}
    (hθ : Parameters.AngleRepresentative θ) (hφ : Parameters.AngleRepresentative φ)
    (h : SamePhysicalFrame (square p θ) (square q φ)) : θ=φ := by
  obtain ⟨hcθ,hlθ,huθ⟩ := representative_frame hθ
  obtain ⟨hcφ,hlφ,huφ⟩ := representative_frame hφ
  rcases h with h | h | h | h
  · have hhalf : angleToHalf θ=angleToHalf φ := by
      dsimp [SamePhysicalFrame,square] at h
      simp only [angleToHalf,h.1,h.2]
    rw [← halfToAngle_angleToHalf hθ,← halfToAngle_angleToHalf hφ,hhalf]
  all_goals
    dsimp [square] at h
    obtain ⟨he₁,he₂⟩ := h
    linarith

/-- The half-open real interval is exactly a representative system for the
four physical frame rotations of any unit square. -/
theorem physical_angle_existsUnique (K : UnitSquare) :
    ∃! θ : ℝ, Parameters.AngleRepresentative θ ∧
      SamePhysicalFrame (square K.center θ) K := by
  obtain ⟨k,hc,hl,hu⟩ := halfopen_quarter_exists K
  let L := turnSquare k K
  let w := L.sine/(1+L.cosine)
  let θ := halfToAngle w
  have hw : 1-Real.sqrt 2≤w ∧ w<Real.sqrt 2-1 :=
    halfAngle_halfopen L.unit hc hl hu
  have hθ : Parameters.AngleRepresentative θ := halfToAngle_mem hw
  have hframe := halfAngle_recover L.unit hc
  have htrig := halfToAngle_frame w
  have hsquare : square K.center θ=L := by
    ext <;>
      simp [square,θ,w,htrig.1,htrig.2,hframe.1,hframe.2,L,turnSquare]
  have hphysical : SamePhysicalFrame (square K.center θ) K := by
    rw [hsquare]
    exact turnSquare_physical k K
  refine ⟨θ,⟨hθ,hphysical⟩,?_⟩
  intro φ hφ
  exact representative_unique hφ.1 hθ
    (physicalFrame_trans hφ.2 (physicalFrame_symm hphysical))

namespace Parameters

/-- The rational parameter is confined to the equivalence proof. -/
def toOld (p : Parameters) : EqualityParameters :=
  ⟨p.center.1,p.center.2,angleToHalf p.angle,p.top,p.tilted⟩

def fromOld (p : EqualityParameters) : Parameters :=
  ⟨p.center,halfToAngle p.w,p.z,p.eta⟩

@[simp] theorem toOld_fromOld (p : EqualityParameters) : (fromOld p).toOld=p := by
  cases p
  simp [toOld,fromOld,EqualityParameters.center]

theorem fromOld_toOld {p : Parameters} (hp : AngleRepresentative p.angle) :
    fromOld p.toOld=p := by
  cases p
  simp [toOld,fromOld,EqualityParameters.center,halfToAngle_angleToHalf hp]

theorem fromOld_centralSquare (p : EqualityParameters) :
    (fromOld p).centralSquare=p.centralSquare := by
  obtain ⟨hc,hs⟩ := halfToAngle_frame p.w
  ext <;> simp [centralSquare,fromOld,square,EqualityParameters.centralSquare,
    EqualityParameters.C,EqualityParameters.S,hc,hs]

theorem toOld_centralSquare {p : Parameters} (hp : AngleRepresentative p.angle) :
    p.toOld.centralSquare=p.centralSquare := by
  obtain ⟨hc,hs⟩ := angleToHalf_frame hp
  ext <;> simp [centralSquare,toOld,square,EqualityParameters.centralSquare,
    EqualityParameters.center,EqualityParameters.C,EqualityParameters.S,hc,hs]

/-- Every physical square admits an actual-angle representative, including
diagonal frames.  The proof chooses a physical quarter turn before extracting
the angle; no symmetry of the surrounding packing is used. -/
theorem central_angle_exists (K : UnitSquare) (z η : ℝ) :
    ∃ p : Parameters, SameSquare p.centralSquare K ∧
      p.center=K.center ∧ AngleRepresentative p.angle ∧ p.top=z ∧ p.tilted=η := by
  obtain ⟨r,hr,hc,ha,hz,hη⟩ := central_parameters_exist K z η
  refine ⟨fromOld r,?_,?_,halfToAngle_mem ha,hz,hη⟩
  · simpa only [fromOld_centralSquare] using hr
  · exact hc

theorem quarter_turn_sameSquare (p : Point) (θ : ℝ) :
    SameSquare (square p (θ+Real.pi/2)) (square p θ) := by
  constructor
  · intro x
    exact openSquare_quarter_turn p x θ
  · intro x
    exact closedSquare_quarter_turn p x θ

end Parameters

end SquaresInCircles.Eight.GeometricModel

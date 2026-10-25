module

public import SquaresInCircles.Common.Frames
public import SquaresInCircles.Eight.Stationary.EqualityBox

/-!
# Eight squares: the five-parameter family

The models of the admissible parameters `(x, y, w, z, eta)` of the stationary chart and their
mirror images in the diagonal (`stationaryReflectedModel`) form the set `stationaryModels`: each
is a packing in the closed disk of radius `stationaryRadius = √qStar` about the origin
(`model_packing`) that reaches the circle (`model_reaches`). The admissible set contains its weak
contact boundaries, and every point of the rational box `InBox`, of side `0.002` in each
parameter, is admissible (`box_admissible`); the sample parameters give a model
(`models_nonempty`). Conversely, the admissibility conditions are necessary for a packing at the
radius `√qStar` whose exterior squares are those of a model (`admissible_of_original_geometry`).

The mirror image is a separate branch, chosen by a Boolean, because `Congruent` uses positively
oriented frames.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight
open Stationary Coordinates EqualityParameters

theorem box_admissible {p : EqualityParameters} (hp : p.InBox) : p.Admissible sharpData := by
  have b0 : (979/1000:ℝ) ≤ p.C ∧ p.C ≤ 981/1000 := box_data_bounds hp 0
  have b1 : (39/200:ℝ) ≤ p.S ∧ p.S ≤ 201/1000 := box_data_bounds hp 1
  have b2 : (99/100:ℝ) ≤ sharpData.c*p.C+sharpData.s*p.S ∧
      sharpData.c*p.C+sharpData.s*p.S ≤ 1 := box_data_bounds hp 2
  have b3 : (9/125:ℝ) ≤ sharpData.c*p.S-sharpData.s*p.C ∧
      sharpData.c*p.S-sharpData.s*p.C ≤ 2/25 := box_data_bounds hp 3
  have b4 : (-139/1000:ℝ) ≤ p.C*p.x+p.S*p.y ∧ p.C*p.x+p.S*p.y ≤ 139/1000 :=
    box_data_bounds hp 4
  have b5 : (-3/100:ℝ) ≤ -p.S*p.x+p.C*p.y ∧ -p.S*p.x+p.C*p.y ≤ 3/100 :=
    box_data_bounds hp 5
  have b6 : (1/100:ℝ) ≤ (sharpData.pA).1-p.x-(1+p.C+p.S)/2 ∧
      (sharpData.pA).1-p.x-(1+p.C+p.S)/2 ≤ 1 := box_data_bounds hp 6
  have b7 : (1/100:ℝ) ≤ p.C*((sharpData.pB).1-p.x)+p.S*((sharpData.pB).2-p.y)-(1+p.C+p.S)/2 ∧
      p.C*((sharpData.pB).1-p.x)+p.S*((sharpData.pB).2-p.y)-(1+p.C+p.S)/2 ≤ 1 :=
    box_data_bounds hp 7
  have b8 : (1/100:ℝ) ≤ -p.S*((sharpData.pD).1-p.x)+p.C*((sharpData.pD).2-p.y)-(1+p.C+p.S)/2 ∧
      -p.S*((sharpData.pD).1-p.x)+p.C*((sharpData.pD).2-p.y)-(1+p.C+p.S)/2 ≤ 1 :=
    box_data_bounds hp 8
  have b9 : (1/100:ℝ) ≤ -((sharpData.pE).1-p.x)-(1+p.C+p.S)/2 ∧
      -((sharpData.pE).1-p.x)-(1+p.C+p.S)/2 ≤ 1 := box_data_bounds hp 9
  have b10 : (1/100:ℝ) ≤ -p.C*((sharpData.pH).1-p.x)-p.S*((sharpData.pH).2-p.y)-rawTiltWidth p ∧
      -p.C*((sharpData.pH).1-p.x)-p.S*((sharpData.pH).2-p.y)-rawTiltWidth p ≤ 1 :=
    box_data_bounds hp 10
  have b11 : (1/100:ℝ) ≤ sharpData.s*((sharpData.pG p.eta).1-p.x)-
        sharpData.c*((sharpData.pG p.eta).2-p.y)-rawTiltWidth p ∧
      sharpData.s*((sharpData.pG p.eta).1-p.x)-
        sharpData.c*((sharpData.pG p.eta).2-p.y)-rawTiltWidth p ≤ 1 :=
    box_data_bounds hp 11
  have b12 : (1/100:ℝ) ≤ p.z-p.y-(1+p.C+p.S)/2 ∧ p.z-p.y-(1+p.C+p.S)/2 ≤ 1 :=
    box_data_bounds hp 12
  have b13 : (11/200:ℝ) ≤ qStar-((sharpData.x₂-1)^2+(p.z+1/2)^2) ∧
      qStar-((sharpData.x₂-1)^2+(p.z+1/2)^2) ≤ 2/25 := box_data_bounds hp 13
  have b14 : (56/125:ℝ) ≤ qStar-((sharpData.h₁+2)^2+(sharpData.h₂+p.eta)^2) ∧
      qStar-((sharpData.h₁+2)^2+(sharpData.h₂+p.eta)^2) ≤ 12/25 := box_data_bounds hp 14
  have hW0 : p.W₀=(1+p.C+p.S)/2 := by rw [W₀,abs_of_pos (by linarith : 0< p.S)]
  have hWt : p.Wₜ sharpData=rawTiltWidth p := by
    rw [Wₜ,abs_of_pos (by linarith : 0< sharpData.c*p.S-sharpData.s*p.C)]
    dsimp [rawTiltWidth]; ring
  have hsqrt := Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
  have hsqrt0 := Real.sqrt_nonneg (2:ℝ)
  have hh := sharp_coordinates
  have htopRad : 0≤ qStar-(sharpData.x₂-1)^2 := by
    nlinarith only [b13.1,sq_nonneg (p.z+1/2)]
  have htiltRad : 0≤ qStar-(sharpData.h₁+2)^2 := by
    nlinarith only [b14.1,sq_nonneg (sharpData.h₂+p.eta)]
  refine {
    frame_lower := by nlinarith only [hp.2.2.1.1,hsqrt,hsqrt0]
    frame_upper := by nlinarith only [hp.2.2.1.2,hsqrt,hsqrt0]
    top_lower := by linarith [hp.2.2.2.1.1]
    top_upper := ?_
    tilted_lower := ?_
    tilted_upper := ?_
    core_first := by rw [abs_lt]; exact ⟨by linarith,by linarith⟩
    core_second := by rw [abs_lt]; exact ⟨by linarith,by linarith⟩
    A_sep := ?_
    B_sep := ?_
    D_sep := ?_
    E_sep := ?_
    T_sep := ?_
    H_sep := ?_
    G_sep := ?_ }
  · dsimp [zMax]
    change p.z≤ Real.sqrt (qStar-(sharpData.x₂-1)^2)-1/2
    have hz0 : 0 ≤ p.z+1/2 := by linarith [hp.2.2.2.1.1]
    have hle : p.z+1/2 ≤ Real.sqrt (qStar-(sharpData.x₂-1)^2) :=
      Real.le_sqrt_of_sq_le (by nlinarith only [b13.1])
    linarith
  · dsimp [etaMin]
    change -sharpData.h₂-Real.sqrt (qStar-(sharpData.h₁+2)^2)≤ p.eta
    have hle : -(sharpData.h₂+p.eta) ≤ Real.sqrt (qStar-(sharpData.h₁+2)^2) :=
      Real.le_sqrt_of_sq_le (by nlinarith only [b14.1])
    linarith
  · dsimp [etaMax]
    linarith [hp.2.2.2.2.2,hh.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
  · rw [hW0]
    apply le_trans (by linarith : (1+p.C+p.S)/2≤ (sharpData.pA).1-p.x)
    exact (le_abs_self _).trans ((le_max_left _ _).trans (le_max_left _ _))
  · rw [hW0]
    apply le_trans (by linarith : (1+p.C+p.S)/2≤
      p.C*((sharpData.pB).1-p.x)+p.S*((sharpData.pB).2-p.y))
    exact (le_abs_self _).trans ((le_max_left _ _).trans (le_max_right _ _))
  · rw [hW0]
    apply le_trans (by linarith : (1+p.C+p.S)/2≤
      -p.S*((sharpData.pD).1-p.x)+p.C*((sharpData.pD).2-p.y))
    exact (le_abs_self _).trans ((le_max_right _ _).trans (le_max_right _ _))
  · rw [hW0]
    apply le_trans (by linarith : (1+p.C+p.S)/2≤ -((sharpData.pE).1-p.x))
    exact (neg_le_abs _).trans ((le_max_left _ _).trans (le_max_left _ _))
  · rw [hW0]
    apply le_trans (by linarith : (1+p.C+p.S)/2≤ p.z-p.y)
    exact (le_abs_self _).trans ((le_max_right _ _).trans (le_max_left _ _))
  · rw [hWt]
    apply le_trans (by linarith : rawTiltWidth p≤
      -(p.C*((sharpData.pH).1-p.x)+p.S*((sharpData.pH).2-p.y)))
    exact (neg_le_abs _).trans ((le_max_left _ _).trans (le_max_right _ _))
  · rw [hWt]
    apply le_trans (by linarith : rawTiltWidth p≤
      -(-sharpData.s*((sharpData.pG p.eta).1-p.x)+sharpData.c*((sharpData.pG p.eta).2-p.y)))
    exact (neg_le_abs _).trans ((le_max_right _ _).trans (le_max_left _ _))

theorem sample_admissible : sampleParameters.Admissible sharpData :=
  box_admissible sampleParameters_inBox

theorem containsCore_center_bounds {K : UnitSquare} (hc : ContainsCore K) :
    alpha K (0,0)<5/12 ∧ beta K (0,0)<5/12 := by
  have hunit := K.unit
  have hnorm (a b : ℝ) (h : a^2+b^2≤(1/12:ℝ)^2) :
      normSq (rotate K (a,b))≤coreRadius^2 := by
    dsimp [normSq,rotate,coreRadius]
    nlinarith [hunit]
  have hXp := hc (rotate K (1/12,0)) (hnorm _ _ (by norm_num))
  have hXm := hc (rotate K (-1/12,0)) (hnorm _ _ (by norm_num))
  have hYp := hc (rotate K (0,1/12)) (hnorm _ _ (by norm_num))
  have hYm := hc (rotate K (0,-1/12)) (hnorm _ _ (by norm_num))
  have hloc (a b : ℝ) :
      localX K (rotate K (a,b))=a+localX K (0,0) ∧
      localY K (rotate K (a,b))=b+localY K (0,0) := by
    constructor <;> dsimp [localX,localY,rotate] <;>
      first | linear_combination a*K.unit | linear_combination b*K.unit
  rw [openSquare,(hloc _ _).1] at hXp hXm
  rw [openSquare,(hloc _ _).2] at hYp hYm
  have hxp := abs_lt.mp hXp.1
  have hxm := abs_lt.mp hXm.1
  have hyp := abs_lt.mp hYp.2
  have hym := abs_lt.mp hYm.2
  constructor
  · change |localX K (0,0)|<5/12
    exact abs_lt.mpr ⟨by linarith,by linarith⟩
  · change |localY K (0,0)|<5/12
    exact abs_lt.mpr ⟨by linarith,by linarith⟩

/-- The admissibility conditions are necessary: if the model of `p` is a packing at the squared
radius `qStar`, its central square contains the core disk, its frame parameter `w` lies in
`[1 - √2, √2 - 1)`, and the sliders have `7/12 ≤ z` and `eta ≤ etaMax`, then `p` is admissible. It
is applied once the stationary identity on the original centres and the cyclic order have placed
the two sliders. -/
theorem admissible_of_original_geometry {p : EqualityParameters}
    (hp : SqPacking (p.model sharpData) (0,0) qStar)
    (hcore : ContainsCore p.centralSquare)
    (hframe : 1-Real.sqrt 2≤p.w ∧ p.w<Real.sqrt 2-1)
    (hT : 7/12≤p.z) (hG : p.eta≤ sharpData.etaMax) : p.Admissible sharpData := by
  have hcont (i : Fin 8) : SqContained qStar (p.model sharpData i) := by
    apply (SqContained.iff_points hp.1 _).mpr
    intro x hx
    simpa [sub] using hp.2.1 i x hx
  have hTcont := hcont 5
  have hGcont := hcont 2
  have hbounds := sharp_exterior_bounds
  have hcore' := containsCore_center_bounds hcore
  obtain ⟨hcx,hcy⟩ := p.central_core_coordinates
  rw [hcx,hcy] at hcore'
  have hTpoly : (sharpData.x₂-1)^2+(p.z+1/2)^2≤ qStar := by
    change SqContained qStar (axisSquare (sharpData.pT p.z)) at hTcont
    rw [axis_containment] at hTcont
    simp only [pT] at hTcont
    rw [abs_of_pos (by linarith [hbounds.2.2.1] : 0< sharpData.x₂-3/2),
      abs_of_pos (by linarith : 0< p.z),
      show sharpData.x₂-3/2+1/2=sharpData.x₂-1 by ring] at hTcont
    exact hTcont
  have hGneg : sharpData.h₂+1/2+p.eta<0 := by
    dsimp [etaMax] at hG
    linarith
  have hGpoly : (sharpData.h₁+2)^2+(sharpData.h₂+p.eta)^2≤ qStar := by
    change SqContained qStar (sharpData.tiltedSquare (sharpData.pG p.eta)) at hGcont
    rw [pG,tilted_containment] at hGcont
    rw [abs_of_pos hbounds.2.2.2.2.1,abs_of_neg hGneg] at hGcont
    nlinarith
  have hTrad : 0≤ qStar-(sharpData.x₂-1)^2 := by nlinarith [sq_nonneg (p.z+1/2)]
  have hGrad : 0≤ qStar-(sharpData.h₁+2)^2 := by nlinarith [sq_nonneg (sharpData.h₂+p.eta)]
  refine {
    frame_lower := hframe.1
    frame_upper := hframe.2
    top_lower := hT
    top_upper := ?_
    tilted_lower := ?_
    tilted_upper := hG
    core_first := hcore'.1
    core_second := hcore'.2
    A_sep := (central_axis_sat hframe sharpData.pA).1 ?_
    B_sep := (central_axis_sat hframe sharpData.pB).1 ?_
    D_sep := (central_axis_sat hframe sharpData.pD).1 ?_
    E_sep := (central_axis_sat hframe sharpData.pE).1 ?_
    T_sep := (central_axis_sat hframe (sharpData.pT p.z)).1 ?_
    H_sep := (central_tilted_sat hframe sharpData.pH).1 ?_
    G_sep := (central_tilted_sat hframe (sharpData.pG p.eta)).1 ?_ }
  · dsimp [zMax]
    change p.z≤ Real.sqrt (qStar-(sharpData.x₂-1)^2)-1/2
    nlinarith [Real.sq_sqrt hTrad,Real.sqrt_nonneg (qStar-(sharpData.x₂-1)^2)]
  · dsimp [etaMin]
    change -sharpData.h₂-Real.sqrt (qStar-(sharpData.h₁+2)^2)≤ p.eta
    nlinarith [Real.sq_sqrt hGrad,Real.sqrt_nonneg (qStar-(sharpData.h₁+2)^2)]
  · simpa [EqualityParameters.model] using hp.2.2 0 3 (by decide)
  · simpa [EqualityParameters.model] using hp.2.2 0 4 (by decide)
  · simpa [EqualityParameters.model] using hp.2.2 0 6 (by decide)
  · simpa [EqualityParameters.model] using hp.2.2 0 7 (by decide)
  · simpa [EqualityParameters.model] using hp.2.2 0 5 (by decide)
  · simpa [EqualityParameters.model] using hp.2.2 0 1 (by decide)
  · simpa [EqualityParameters.model] using hp.2.2 0 2 (by decide)

def stationaryRadius : ℝ := Real.sqrt qStar
def stationaryReflectedModel (reflected : Bool) (p : EqualityParameters) : Fin 8 → UnitSquare :=
  if reflected then fun i=>reflectDiagonalSquare (p.model sharpData i) else p.model sharpData
def stationaryModels : Set (Fin 8 → UnitSquare) :=
  {M | ∃ reflected : Bool, ∃ p : EqualityParameters,
    p.Admissible sharpData ∧ M=stationaryReflectedModel reflected p}
def attainingModel : Fin 8 → UnitSquare := sampleParameters.model sharpData

theorem models_nonempty : stationaryModels.Nonempty :=
  ⟨attainingModel,false,sampleParameters,sample_admissible,rfl⟩

theorem model_packing (M : Fin 8 → UnitSquare) (hM : M∈stationaryModels) :
    Packing M (0,0) stationaryRadius := by
  obtain ⟨b,p,hp,rfl⟩ := hM
  have h := (sqPacking_iff_packing _ _ (by linarith [qStar_limits.1])).mp (model_sqPacking hp)
  cases b
  · exact h
  · exact packing_reflectDiagonal h

theorem unreflected_model_reaches (p : EqualityParameters) :
    ∃ i x, closedSquare (p.model sharpData i) x ∧ stationaryRadius^2≤normSq x := by
  refine ⟨3,(sharpData.x₁,sharpData.y),?_,?_⟩
  · norm_num [EqualityParameters.model,axisSquare,closedSquare,localX,localY,pA]
  · rw [stationaryRadius,Real.sq_sqrt (by linarith [qStar_limits.1])]
    change qStar≤ sharpData.x₁^2+sharpData.y^2
    exact sharpData_stationary.first_circle.ge

theorem model_reaches (M : Fin 8 → UnitSquare) (hM : M∈stationaryModels) :
    ∃ i x, closedSquare (M i) x ∧ stationaryRadius^2≤normSq x := by
  obtain ⟨b,p,hp,rfl⟩ := hM
  obtain ⟨i,x,hx,hr⟩ := unreflected_model_reaches p
  cases b
  · exact ⟨i,x,hx,hr⟩
  · refine ⟨i,diagonalPoint x,?_,?_⟩
    · simpa [stationaryReflectedModel,reflectDiagonal_closed] using hx
    · simpa [normSq,diagonalPoint,add_comm] using hr

end SquaresInCircles.Eight

module

public import SquaresInCircles.Eight.ExactFamily.EqualityBox
public import SquaresInCircles.Eight.Terminal
public import SquaresInCircles.Common.Optimum
public import SquaresInCircles.Common.Frames

/-!
# The complete five-parameter equality family

Uncompiled draft.  The admissible set contains its weak contact boundaries.
The whole displayed rational parameter box lies inside it.  Reflection is a
separate Boolean branch because the repository's `Congruent` relation uses
positively oriented frames.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight
open ExactFamily Coordinates EqualityParameters

theorem box_admissible {p : EqualityParameters} (hp : p.InBox) : p.Admissible sharpData := by
  have b0 := box_data_bounds hp 0; have b1 := box_data_bounds hp 1
  have b2 := box_data_bounds hp 2; have b3 := box_data_bounds hp 3
  have b4 := box_data_bounds hp 4; have b5 := box_data_bounds hp 5
  have b6 := box_data_bounds hp 6; have b7 := box_data_bounds hp 7
  have b8 := box_data_bounds hp 8; have b9 := box_data_bounds hp 9
  have b10 := box_data_bounds hp 10; have b11 := box_data_bounds hp 11
  have b12 := box_data_bounds hp 12; have b13 := box_data_bounds hp 13
  have b14 := box_data_bounds hp 14
  simp only [boxData,boxLower,boxUpper,Matrix.cons_val_zero,Matrix.cons_val_succ] at
    b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
  have hW0 : p.W₀=(1+p.C+p.S)/2 := by rw [W₀,abs_of_pos (by linarith : 0<p.S)]
  have hWt : p.Wₜ sharpData=rawTiltWidth p := by
    rw [Wₜ,abs_of_pos (by linarith : 0<sharpData.c*p.S-sharpData.s*p.C)]
    dsimp [rawTiltWidth]; ring
  have hsqrt := Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
  have hsqrt0 := Real.sqrt_nonneg (2:ℝ)
  have hh := sharp_coordinates
  have htopRad : 0≤qStar-(sharpData.x₂-1)^2 := by nlinarith [sq_nonneg (p.z+1/2)]
  have htiltRad : 0≤qStar-(sharpData.h₁+2)^2 := by
    nlinarith [sq_nonneg (sharpData.h₂+p.eta)]
  refine {
    frame_lower := by nlinarith [hp.2.2.1.1]
    frame_upper := by nlinarith [hp.2.2.1.2]
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
    change p.z≤Real.sqrt (qStar-(sharpData.x₂-1)^2)-1/2
    nlinarith [Real.sq_sqrt htopRad,Real.sqrt_nonneg (qStar-(sharpData.x₂-1)^2),hp.2.2.2.1.1]
  · dsimp [etaMin]
    change -sharpData.h₂-Real.sqrt (qStar-(sharpData.h₁+2)^2)≤p.eta
    nlinarith [Real.sq_sqrt htiltRad,Real.sqrt_nonneg (qStar-(sharpData.h₁+2)^2)]
  · dsimp [etaMax]
    linarith [hp.2.2.2.2.2,hh.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
  · rw [hW0]
    apply le_trans (by linarith : (1+p.C+p.S)/2≤(sharpData.pA).1-p.x)
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
    apply le_trans (by linarith : (1+p.C+p.S)/2≤p.z-p.y)
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

/-- Necessity of every displayed parameter condition after the original-center
dual and cyclic-order argument have identified the two remaining sliders. -/
theorem admissible_of_original_geometry {p : EqualityParameters}
    (hp : SqPacking (p.model sharpData) (0,0) qStar)
    (hcore : ContainsCore p.centralSquare)
    (hframe : 1-Real.sqrt 2≤p.w ∧ p.w<Real.sqrt 2-1)
    (hT : 7/12≤p.z) (hG : p.eta≤sharpData.etaMax) : p.Admissible sharpData := by
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
  have hTpoly : (sharpData.x₂-1)^2+(p.z+1/2)^2≤qStar := by
    change SqContained qStar (axisSquare (sharpData.pT p.z)) at hTcont
    rw [axis_containment] at hTcont
    simpa [pT,abs_of_pos (by linarith [hbounds.2.2.1] : 0<sharpData.x₂-3/2),
      abs_of_pos (by linarith : 0<p.z)] using hTcont
  have hGneg : sharpData.h₂+1/2+p.eta<0 := by
    dsimp [etaMax] at hG
    linarith
  have hGpoly : (sharpData.h₁+2)^2+(sharpData.h₂+p.eta)^2≤qStar := by
    change SqContained qStar (sharpData.tiltedSquare (sharpData.pG p.eta)) at hGcont
    rw [pG,tilted_containment] at hGcont
    rw [abs_of_pos hbounds.2.2.2.2.1,abs_of_neg hGneg] at hGcont
    nlinarith
  have hTrad : 0≤qStar-(sharpData.x₂-1)^2 := by nlinarith [sq_nonneg (p.z+1/2)]
  have hGrad : 0≤qStar-(sharpData.h₁+2)^2 := by nlinarith [sq_nonneg (sharpData.h₂+p.eta)]
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
    change p.z≤Real.sqrt (qStar-(sharpData.x₂-1)^2)-1/2
    nlinarith [Real.sq_sqrt hTrad,Real.sqrt_nonneg (qStar-(sharpData.x₂-1)^2)]
  · dsimp [etaMin]
    change -sharpData.h₂-Real.sqrt (qStar-(sharpData.h₁+2)^2)≤p.eta
    nlinarith [Real.sq_sqrt hGrad,Real.sqrt_nonneg (qStar-(sharpData.h₁+2)^2)]
  · simpa [model] using hp.2.2 0 3 (by decide)
  · simpa [model] using hp.2.2 0 4 (by decide)
  · simpa [model] using hp.2.2 0 6 (by decide)
  · simpa [model] using hp.2.2 0 7 (by decide)
  · simpa [model] using hp.2.2 0 5 (by decide)
  · simpa [model] using hp.2.2 0 1 (by decide)
  · simpa [model] using hp.2.2 0 2 (by decide)

theorem model_parameter_injective : Function.Injective (fun p : EqualityParameters=>p.model sharpData) := by
  intro p r h
  have h0 := congrFun h 0
  have hT := congrFun h 5
  have hG := congrFun h 2
  have hxy := congrArg UnitSquare.center h0
  have hC := congrArg UnitSquare.cosine h0
  have hS := congrArg UnitSquare.sine h0
  have hZ := congrArg (fun K : UnitSquare=>K.center.2) hT
  have hη := congrArg (fun K : UnitSquare=>dot sharpData.f K.center) hG
  have recover (w : ℝ) : halfAngleSin w/(1+halfAngleCos w)=w := by
    dsimp [halfAngleCos,halfAngleSin]
    field_simp [ne_of_gt (halfAngle_den_pos w)]
    ring
  have hw : p.w=r.w := by
    rw [← recover p.w,← recover r.w]
    simpa [model,centralSquare,C,S] using congrArg₂ (fun c s : ℝ=>s/(1+c)) hC hS
  have heta : p.eta=r.eta := by
    simp [model,tiltedSquare,pG,sharpData.dot_f_inFrame] at hη
    linarith
  have hpx : p.x=r.x := congrArg Prod.fst hxy
  have hpy : p.y=r.y := congrArg Prod.snd hxy
  cases p; cases r
  simp_all [model,centralSquare,center,pT]

def radius : ℝ := Real.sqrt qStar
def reflectedModel (reflected : Bool) (p : EqualityParameters) : Fin 8 → UnitSquare :=
  if reflected then fun i=>reflectDiagonalSquare (p.model sharpData i) else p.model sharpData
def models : Set (Fin 8 → UnitSquare) :=
  {M | ∃ reflected : Bool, ∃ p : EqualityParameters,
    p.Admissible sharpData ∧ M=reflectedModel reflected p}
def attainingModel : Fin 8 → UnitSquare := sampleParameters.model sharpData

theorem models_nonempty : models.Nonempty :=
  ⟨attainingModel,false,sampleParameters,sample_admissible,rfl⟩

theorem model_packing (M : Fin 8 → UnitSquare) (hM : M∈models) :
    Packing M (0,0) radius := by
  obtain ⟨b,p,hp,rfl⟩ := hM
  have h := (sqPacking_iff_packing _ _ (by linarith [qStar_limits.1])).mp (model_sqPacking hp)
  cases b
  · exact h
  · exact packing_reflectDiagonal h

theorem attainingPacking : Packing attainingModel (0,0) radius :=
  model_packing _ ⟨false,sampleParameters,sample_admissible,rfl⟩

theorem unreflected_model_reaches (p : EqualityParameters) :
    ∃ i x, closedSquare (p.model sharpData i) x ∧ radius^2≤normSq x := by
  refine ⟨3,(sharpData.x₁,sharpData.y),?_,?_⟩
  · norm_num [model,axisSquare,closedSquare,localX,localY,pA]
  · rw [radius,Real.sq_sqrt (by linarith [qStar_limits.1])]
    change qStar≤sharpData.x₁^2+sharpData.y^2
    exact sharpData_stationary.first_circle.ge

theorem model_reaches (M : Fin 8 → UnitSquare) (hM : M∈models) :
    ∃ i x, closedSquare (M i) x ∧ radius^2≤normSq x := by
  obtain ⟨b,p,hp,rfl⟩ := hM
  obtain ⟨i,x,hx,hr⟩ := unreflected_model_reaches p
  cases b
  · exact ⟨i,x,hx,hr⟩
  · refine ⟨i,diagonalPoint x,?_,?_⟩
    · simpa [reflectedModel,reflectDiagonal_closed] using hx
    · simpa [normSq,diagonalPoint,add_comm] using hr

theorem whole_box_packing {p : EqualityParameters} (hp : p.InBox) :
    Packing (p.model sharpData) (0,0) radius :=
  model_packing _ ⟨false,p,box_admissible hp,rfl⟩

/-- The five independent closed intervals are all present, not just a single
sample point.  Their coordinate map into the normalized family is injective. -/
theorem five_parameter_box :
    (∀ p : EqualityParameters, p.InBox→Packing (p.model sharpData) (0,0) radius) ∧
      Function.Injective (fun p : EqualityParameters=>p.model sharpData) :=
  ⟨fun _ hp=>whole_box_packing hp,model_parameter_injective⟩

end SquaresInCircles.Eight

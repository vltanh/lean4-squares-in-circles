module

public import SquaresInCircles.Eight.Owners.Direct.NegativeTEndpoint
public import SquaresInCircles.Eight.Words.One.NegativeCoupledStop

/-!
# Eight squares: strict original-D loss at the full coupled hard endpoint

Once BT2 is actual, the proved EH reserve pays for a
small D-primary decrease and an equal E-tangent increase. Both original
DE axes remain aligned contact. E stays on its actual original outer
circle or full true-core arc, and the loss is recorded at D itself.
-/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace SquaresInCircles.Eight
namespace DirectNegativeT
open AlignedNegative PrimaryCap

theorem FullCoupledStop.hard_endpoint {q t h : ℝ} {D T B E H : SignedPoint}
    {kind : FullE.ArcKind} {I : Source q t D T B} {jDE jEH : Fin 4}
    (O : FullCoupledStop I kind E H h jEH) (J : FullE.ArcSource q E kind)
    (hqL : qLow≤q) (hqU : q≤qCap)
    (hjDE : jDE=2 ∨ jDE=3) (hjEH : jEH=0 ∨ jEH=1)
    (hDE : quarterFeasible D E 0 jDE)
    (hhard : quarterFeasible (point (B.a-1/2) O.angle) B.reflect (-O.angle) 0) :
    Nonempty (LocalEndpoint I E H (-t) h jDE jEH) := by
  let D₀ := Dpath D.circle (B.a-1/2) O.angle
  let T₀ := Tpath (B.a-1/2) O.angle
  let b := coupledTangent D.circle (B.a-1/2) O.angle
  have hg := I.path_data hqU O.angle_mem
  have hDEraw : 1≤D.a-E.y := by
    rcases hjDE with rfl | rfl <;>
      simpa [quarterFeasible,quarterProjection,edgeWidth_zero] using hDE
  have hbupper : b< -E.y := by
    have hprim := hg.D_primary
    dsimp [b,coupledTangent,Dpath,SignedPoint.reflect] at *
    linarith
  let cap := min ((D₀.a-|D₀.y|)/2) (min ((D₀.a-7/12)/2) ((-E.y-b)/2))
  have hcap : 0<cap := by
    apply lt_min
    · exact div_pos (sub_pos.mpr hg.D_nondiagonal) (by norm_num)
    · apply lt_min
      · exact div_pos (by linarith [hg.D_primary_high]) (by norm_num)
      · exact div_pos (by linarith) (by norm_num)
  let M : ℝ → ℝ := fun η => quarterProjection (kind.point q (b+η)) H (h+O.angle) jEH-
    edgeWidth (h+O.angle)
  have hprimary := kind.continuous_primary q
  have hM : Continuous M := by
    dsimp [M,quarterProjection,FullE.ArcKind.point]
    fin_cases jEH <;> fun_prop
  have hMzero : 0<M 0 := by
    have hh := O.mixed_strict
    rw [fullCoupledSlack_actual kind H jEH hjEH ⟨O.error_mem.1,by linarith [O.error_mem.2]⟩]
      at hh
    simpa [M,b,fullCoupledPoint] using hh
  have hpositive : ∀ᶠ η in 𝓝[>] (0:ℝ), 0<M η :=
    (hM.continuousAt.tendsto.eventually (eventually_gt_nhds hMzero)).filter_mono
      nhdsWithin_le_nhds
  have hbound : ∀ᶠ η in 𝓝[>] (0:ℝ), η<cap :=
    (eventually_lt_nhds hcap).filter_mono nhdsWithin_le_nhds
  obtain ⟨η,hη,hηcap,hMη⟩ := (eventually_mem_nhdsWithin.and (hbound.and hpositive)).exists
  replace hη : 0<η := hη
  have hηsort : η<(D₀.a-|D₀.y|)/2 := hηcap.trans_le (min_le_left _ _)
  have hηcore : η<(D₀.a-7/12)/2 :=
    hηcap.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hηradial : η<(-E.y-b)/2 :=
    hηcap.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  let D' : SignedPoint := ⟨D₀.a-η,D₀.y⟩
  let E' := kind.point q (b+η)
  have hbη : b+η∈Icc 0 (-E.y) := by
    constructor <;> linarith [O.tangent_mem.1]
  have hEg := J.geometry hqL hbη
  have hDs : D'.Sorted := by
    constructor
    · dsimp [D']; linarith [hg.D_primary_high]
    · dsimp [D']; linarith
  have hDnd : |D'.y|<D'.a := by dsimp [D']; linarith [hg.D_nondiagonal]
  have hDcore : D'.AvoidsCore := by
    have ha : 7/12≤D'.a := by dsimp [D']; linarith
    unfold SignedPoint.AvoidsCore SignedPoint.coreDistance
    rw [max_eq_left (by linarith : 0≤D'.a-1/2)]
    nlinarith [sq_nonneg (max (|D'.y|-1/2) 0)]
  have hDloss : D'.circle<D.circle := by
    rw [← hg.D_circle]
    have hprod := mul_pos hη (show 0<2*(D₀.a+1/2)-η by linarith [hg.D_primary_high])
    show (D₀.a-η+1/2)^2+(|D₀.y|+1/2)^2<(D₀.a+1/2)^2+(|D₀.y|+1/2)^2
    linarith
  have hTD0 : zeroFeasible T₀ D' 0 0 := by
    have h := hg.TD0
    simp only [zeroFeasible,zeroProjection,Matrix.cons_val_zero,Real.sin_zero,Real.cos_zero,
      mul_zero,mul_one,add_zero] at h ⊢
    exact h
  have hBT2 : quarterFeasible B T₀ (-O.angle) 2 := by
    apply (quarterFeasible_reflect B T₀ (-O.angle) 2).1
    simpa [T₀,Tpath,reflectedOwner] using hhard
  have hDEfinal : quarterFeasible D' E' 0 jDE := by
    rcases hjDE with rfl | rfl <;>
      simp [quarterFeasible,quarterProjection,D',E',b,coupledTangent,D₀,Dpath,
        SignedPoint.reflect,FullE.ArcKind.point,edgeWidth_zero] <;> linarith
  have hEHfinal : quarterFeasible E' H (h+O.angle) jEH := sub_nonneg.mp hMη.le
  exact ⟨{
    angle := O.angle
    angle_mem := O.angle_mem
    Dpoint := D'
    Tpoint := T₀
    Epoint := E'
    Etheta := -O.angle
    E_frame := Or.inr ⟨by linarith [O.angle_mem.2],neg_nonpos.mpr O.angle_mem.1⟩
    E_advance := by linarith [O.angle_mem.2]
    D_sorted := hDs
    T_sorted := hg.T_sorted
    E_sorted := hEg.1
    D_core := hDcore
    T_core := hg.T_core
    E_core := hEg.2.2.1
    D_circle_loss := hDloss
    T_inside := hg.T_inside
    E_contained := hEg.2.1
    E_radial := hEg.2.2.2.1
    E_circle_nonincrease := hEg.2.2.2.2.1
    D_negative := hg.D_negative
    T_positive := hg.T_positive
    E_nonpos := by dsimp [E',FullE.ArcKind.point]; linarith [hbη.1]
    D_nondiagonal := hDnd
    T_nondiagonal := hg.T_nondiagonal
    D_tangent_decreases := hg.D_tangent
    TD0 := hTD0
    TD2 := (zero_owner_tie _ _).1 hTD0
    BT2 := hBT2
    DE := by simpa using hDEfinal
    EH := by simpa using hEHfinal }⟩


end DirectNegativeT
end SquaresInCircles.Eight

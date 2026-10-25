module

public import SquaresInCircles.Eight.Owners.Direct.NegativeTCoupledStop

/-!
# Eight squares: strict original-D-circle loss at the direct negative-T endpoints

The positive-DE endpoint spends its actual DE reserve
on a small D-primary decrease. The aligned endpoint instead increases E's
tangent by exactly that decrease; DE remains exact contact and the proved
EH reserve pays for the perturbation. E stays on its original radial arc.
-/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace SquaresInCircles.Eight
namespace DirectNegativeT
open AlignedNegative PrimaryCap OutsideE DirectNegativeE

structure PathData {q t : ℝ} {D T B : SignedPoint} (I : Source q t D T B) (x : ℝ) : Prop where
  D_sorted : (Dpath D.circle (B.a-1/2) x).Sorted
  D_circle : (Dpath D.circle (B.a-1/2) x).circle=D.circle
  D_core : (Dpath D.circle (B.a-1/2) x).AvoidsCore
  D_negative : (Dpath D.circle (B.a-1/2) x).y<0
  D_nondiagonal : |(Dpath D.circle (B.a-1/2) x).y|<(Dpath D.circle (B.a-1/2) x).a
  D_primary : D.a<(Dpath D.circle (B.a-1/2) x).a
  D_primary_high : 211/250<(Dpath D.circle (B.a-1/2) x).a
  D_tangent : |(Dpath D.circle (B.a-1/2) x).y| < |D.y|
  T_sorted : (Tpath (B.a-1/2) x).Sorted
  T_core : (Tpath (B.a-1/2) x).Core
  T_inside : (Tpath (B.a-1/2) x).circle<q
  T_positive : 0<(Tpath (B.a-1/2) x).y
  T_nondiagonal : |(Tpath (B.a-1/2) x).y|<(Tpath (B.a-1/2) x).a
  TD0 : zeroFeasible (Tpath (B.a-1/2) x) (Dpath D.circle (B.a-1/2) x) 0 0
  TD2 : zeroFeasible (Tpath (B.a-1/2) x) (Dpath D.circle (B.a-1/2) x) 0 2

theorem Source.path_data {q t x : ℝ} {D T B : SignedPoint}
    (I : Source q t D T B) (hq : q≤qCap) (hx : x∈Ico 0 t) : PathData I x := by
  let K := movingAnchor D.circle (B.a-1/2) x
  let L := point (B.a-1/2) x
  have hg := I.path_geometry hq ⟨hx.1,hx.2.le⟩
  have hdrop := I.path_tangent_strict hq hx
  have hsource := I.cuts hq
  rw [SignedPoint.reflect_circle] at hg hdrop
  have hDy : D.y<0 := by
    have hh := hsource.2.2.2.1
    change 211/250< -D.y at hh
    linarith
  have hKy : 0<K.y := hg.2.2.2.2.2.1
  have hKdrop : K.y< -D.y := hdrop
  have hKprimary : D.a≤K.a := hg.2.2.1
  have hDsort : -D.y≤D.a := by simpa [SignedPoint.reflect,abs_of_neg hDy] using I.H_sorted.2
  have hKstrict : K.y<K.a := hKdrop.trans_le (hDsort.trans hKprimary)
  have hKhigh : 211/250<K.a := hsource.2.2.2.1.trans_le (hDsort.trans hKprimary)
  have hcircle : (K.a+1/2)^2+(K.y+1/2)^2=(D.a+1/2)^2+(-D.y+1/2)^2 := by
    have h := hg.2.1
    change K.circle=D.circle at h
    unfold SignedPoint.circle at h
    rw [abs_of_pos hKy,abs_of_neg hDy] at h
    exact h
  have hKprimStrict : D.a<K.a := by
    have hprod := mul_pos (show 0< -D.y-K.y by linarith only [hKdrop])
      (show 0< -D.y+K.y+1 by linarith only [hKy,hDy])
    have hsq : (D.a+1/2)^2<(K.a+1/2)^2 := by linarith only [hcircle,hprod]
    have hK0 : 0≤K.a+1/2 := by linarith only [hKhigh]
    linarith only [lt_of_pow_lt_pow_left₀ 2 hK0 hsq]
  obtain ⟨hPlo,hPup,hcap,hDle⟩ := I.cap_data hq
  have hv := I.path_cap hq ⟨hx.1,hx.2.le⟩
  obtain ⟨hLs,hLcore,hLavoid,hLinside⟩ := point_geometric
    ⟨hPlo,hPup⟩ ⟨hx.1,hx.2.le.trans I.tilt_cap⟩ (by linarith only [hv.1])
    hsource.2.2.2.2.2.2.2
  have hv1 : 3/5<value (B.a-1/2) x := hv.1
  have hv2 : value (B.a-1/2) x<183/200 := hv.2.1
  have hLy : L.y<0 := by dsimp only [L,point]; linarith only [hv1]
  have hLnondiag : |L.y|<L.a := by
    rw [abs_of_neg hLy]
    dsimp only [L,point]
    linarith only [hv2]
  have hTD0 : zeroFeasible L.reflect K.reflect 0 0 := by
    simp [zeroFeasible,zeroProjection,K,L,movingAnchor,anchorAt,point,SignedPoint.reflect]
    norm_num
  exact {
    D_sorted := (SignedPoint.reflect_sorted _).2 hg.1
    D_circle := (SignedPoint.reflect_circle _).trans hg.2.1
    D_core := (SignedPoint.reflect_avoidsCore _).2 hg.2.2.2.2.1
    D_negative := by show -K.y<0; linarith only [hKy]
    D_nondiagonal := by show |-K.y|<K.a; rw [abs_neg,abs_of_pos hKy]; exact hKstrict
    D_primary := hKprimStrict
    D_primary_high := hKhigh
    D_tangent := by
      show |-K.y| < |D.y|
      rw [abs_neg,abs_of_pos hKy,abs_of_neg hDy]
      exact hKdrop
    T_sorted := (SignedPoint.reflect_sorted _).2 hLs
    T_core := (SignedPoint.reflect_core _).2 hLcore
    T_inside := (SignedPoint.reflect_circle _).trans_lt hLinside
    T_positive := by show 0< -L.y; linarith only [hLy]
    T_nondiagonal := by show |-L.y|<L.a; rw [abs_neg]; exact hLnondiag
    TD0 := hTD0
    TD2 := (zero_owner_tie _ _).1 hTD0 }

structure LocalEndpoint {q t : ℝ} {D T B : SignedPoint}
    (I : Source q t D T B) (E H : SignedPoint) (e h : ℝ) (jDE jEH : Fin 4) where
  angle : ℝ
  angle_mem : angle∈Ico 0 t
  Dpoint : SignedPoint
  Tpoint : SignedPoint
  Epoint : SignedPoint
  Etheta : ℝ
  E_frame : Etheta=e ∨ Etheta∈Icc (-t) 0
  E_advance : e≤Etheta
  D_sorted : Dpoint.Sorted
  T_sorted : Tpoint.Sorted
  E_sorted : Epoint.Sorted
  D_core : Dpoint.AvoidsCore
  T_core : Tpoint.Core
  E_core : Epoint.AvoidsCore
  D_circle_loss : Dpoint.circle<D.circle
  T_inside : Tpoint.circle<q
  E_contained : Epoint.Contained q
  E_radial : Epoint.Boundary q
  E_circle_nonincrease : Epoint.circle≤E.circle
  D_negative : Dpoint.y<0
  T_positive : 0<Tpoint.y
  E_nonpos : Epoint.y≤0
  D_nondiagonal : |Dpoint.y|<Dpoint.a
  T_nondiagonal : |Tpoint.y|<Tpoint.a
  D_tangent_decreases : |Dpoint.y| < |D.y|
  TD0 : zeroFeasible Tpoint Dpoint 0 0
  TD2 : zeroFeasible Tpoint Dpoint 0 2
  BT2 : quarterFeasible B Tpoint (-angle) 2
  DE : quarterFeasible Dpoint Epoint (Etheta+angle) jDE
  EH : quarterFeasible Epoint H (h-Etheta) jEH

theorem PositiveDEStop.hard_endpoint {q t e h : ℝ} {D T B E H : SignedPoint}
    {I : Source q t D T B} {jDE jEH : Fin 4}
    (O : PositiveDEStop I E e jDE) (hq : q≤qCap)
    (hEs : E.Sorted) (hEc : E.Contained q) (hEcore : E.AvoidsCore)
    (hEr : E.Boundary q) (hEy : E.y≤0)
    (hjDE : jDE=2 ∨ jDE=3)
    (hEH : quarterFeasible E H (h-e) jEH)
    (hhard : quarterFeasible (point (B.a-1/2) O.angle) B.reflect (-O.angle) 0) :
    Nonempty (LocalEndpoint I E H e h jDE jEH) := by
  let D₀ := Dpath D.circle (B.a-1/2) O.angle
  let T₀ := Tpath (B.a-1/2) O.angle
  have hg := I.path_data hq O.angle_mem
  let margin := positiveDESlack D.circle (B.a-1/2) e E jDE O.angle
  let η := min ((D₀.a-|D₀.y|)/2) (min ((D₀.a-7/12)/2) (margin/2))
  have hmargin : 0<margin := O.mixed_strict
  have hη : 0<η := by
    apply lt_min
    · exact div_pos (sub_pos.mpr hg.D_nondiagonal) (by norm_num)
    · apply lt_min
      · exact div_pos (by linarith [hg.D_primary_high]) (by norm_num)
      · exact div_pos hmargin (by norm_num)
  have hηsort : η≤(D₀.a-|D₀.y|)/2 := min_le_left _ _
  have hηcore : η≤(D₀.a-7/12)/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hηslack : η≤margin/2 := (min_le_right _ _).trans (min_le_right _ _)
  let D' : SignedPoint := ⟨D₀.a-η,D₀.y⟩
  have hDs : D'.Sorted := by
    constructor
    · dsimp [D']; linarith [hg.D_primary_high]
    · dsimp [D']; linarith
  have hDnd : |D'.y|<D'.a := by dsimp [D']; linarith [hg.D_nondiagonal]
  have hDcore : D'.AvoidsCore := by
    have ha : 7/12≤D'.a := by dsimp only [D']; linarith only [hηcore,hg.D_primary_high]
    unfold SignedPoint.AvoidsCore SignedPoint.coreDistance
    rw [max_eq_left (by linarith only [ha] : 0≤D'.a-1/2)]
    have h1 : (1/12:ℝ)^2≤(D'.a-1/2)^2 := pow_le_pow_left₀ (by norm_num) (by linarith only [ha]) 2
    linarith only [h1,sq_nonneg (max (|D'.y|-1/2) 0)]
  have hDloss : D'.circle<D.circle := by
    have hc : (D₀.a+1/2)^2+(|D₀.y|+1/2)^2=D.circle := hg.D_circle
    have hprod := mul_pos hη (show 0<2*(D₀.a+1/2)-η by linarith [hg.D_primary_high])
    show (D₀.a-η+1/2)^2+(|D₀.y|+1/2)^2<D.circle
    rw [← hc]
    linarith only [hprod]
  have hTD0 : zeroFeasible T₀ D' 0 0 := by
    have h := hg.TD0
    unfold zeroFeasible at h ⊢
    rw [zeroProjection_aligned] at h ⊢
    simp only [Matrix.cons_val_zero] at h ⊢
    exact h
  have hBT2 : quarterFeasible B T₀ (-O.angle) 2 := by
    apply (quarterFeasible_reflect B T₀ (-O.angle) 2).1
    simpa [T₀,Tpath,reflectedOwner] using hhard
  have hDE : quarterFeasible D' E (e+O.angle) jDE := by
    have hm : margin=quarterProjection D₀ E (e+O.angle) jDE-edgeWidth (e+O.angle) :=
      positiveDESlack_actual E jDE hjDE ⟨O.error_mem.1,by linarith [O.error_mem.2]⟩
    rcases hjDE with rfl | rfl
    · have hcos := mul_le_mul_of_nonneg_left (Real.cos_le_one (e+O.angle)) hη.le
      dsimp [quarterFeasible,quarterProjection,D'] at hm ⊢
      nlinarith
    · dsimp [quarterFeasible,quarterProjection,D'] at hm ⊢
      linarith
  exact ⟨{
    angle := O.angle
    angle_mem := O.angle_mem
    Dpoint := D'
    Tpoint := T₀
    Epoint := E
    Etheta := e
    E_frame := Or.inl rfl
    E_advance := le_rfl
    D_sorted := hDs
    T_sorted := hg.T_sorted
    E_sorted := hEs
    D_core := hDcore
    T_core := hg.T_core
    E_core := hEcore
    D_circle_loss := hDloss
    T_inside := hg.T_inside
    E_contained := hEc
    E_radial := hEr
    E_circle_nonincrease := le_rfl
    D_negative := hg.D_negative
    T_positive := hg.T_positive
    E_nonpos := hEy
    D_nondiagonal := hDnd
    T_nondiagonal := hg.T_nondiagonal
    D_tangent_decreases := hg.D_tangent
    TD0 := hTD0
    TD2 := (zero_owner_tie _ _).1 hTD0
    BT2 := hBT2
    DE := hDE
    EH := hEH }⟩

theorem CoupledStop.hard_endpoint {q t h : ℝ} {D T B E H : SignedPoint} {kind : ArcKind}
    {I : Source q t D T B} {jDE jEH : Fin 4}
    (O : CoupledStop I kind E H h jEH) (J : ArcSource q E kind)
    (hqL : qLow≤q) (hqU : q≤qCap)
    (hjDE : jDE=2 ∨ jDE=3) (hjEH : jEH=0 ∨ jEH=1)
    (hDE : quarterFeasible D E 0 jDE) :
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
    dsimp [M,quarterProjection,ArcKind.point]
    fin_cases jEH <;> simp only [
      ] <;> fun_prop
  have hMzero : 0<M 0 := by
    have hh := O.mixed_strict
    rw [coupledSlack_actual kind H jEH hjEH ⟨O.error_mem.1.le,by linarith [O.error_mem.2]⟩]
      at hh
    simpa [M,b,coupledPoint] using hh
  have hpositive : ∀ᶠ η in 𝓝[>] (0:ℝ), 0<M η :=
    (hM.continuousAt.tendsto.eventually (eventually_gt_nhds hMzero)).filter_mono
      nhdsWithin_le_nhds
  have hbound : ∀ᶠ η in 𝓝[>] (0:ℝ), η<cap :=
    (eventually_lt_nhds hcap).filter_mono nhdsWithin_le_nhds
  obtain ⟨η,hηmem,hηcap,hMη⟩ := (eventually_mem_nhdsWithin.and (hbound.and hpositive)).exists
  have hη : 0<η := hηmem
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
    have ha : 7/12≤D'.a := by dsimp only [D']; linarith only [hηcore,hg.D_primary_high]
    unfold SignedPoint.AvoidsCore SignedPoint.coreDistance
    rw [max_eq_left (by linarith only [ha] : 0≤D'.a-1/2)]
    have h1 : (1/12:ℝ)^2≤(D'.a-1/2)^2 := pow_le_pow_left₀ (by norm_num) (by linarith only [ha]) 2
    linarith only [h1,sq_nonneg (max (|D'.y|-1/2) 0)]
  have hDloss : D'.circle<D.circle := by
    have hc : (D₀.a+1/2)^2+(|D₀.y|+1/2)^2=D.circle := hg.D_circle
    have hprod := mul_pos hη (show 0<2*(D₀.a+1/2)-η by linarith [hg.D_primary_high])
    show (D₀.a-η+1/2)^2+(|D₀.y|+1/2)^2<D.circle
    rw [← hc]
    linarith only [hprod]
  have hTD0 : zeroFeasible T₀ D' 0 0 := by
    have h := hg.TD0
    unfold zeroFeasible at h ⊢
    rw [zeroProjection_aligned] at h ⊢
    simp only [Matrix.cons_val_zero] at h ⊢
    exact h
  have hBT2 : quarterFeasible B T₀ (-O.angle) 2 := by
    apply (quarterFeasible_reflect B T₀ (-O.angle) 2).1
    simpa [T₀,Tpath,reflectedOwner] using O.hard
  have hDEfinal : quarterFeasible D' E' 0 jDE := by
    rcases hjDE with rfl | rfl <;>
      simp [quarterFeasible,quarterProjection,D',E',b,coupledTangent,D₀,Dpath,
        SignedPoint.reflect,ArcKind.point,edgeWidth_zero] <;> ring_nf <;> norm_num
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
    E_nonpos := by dsimp [E',ArcKind.point]; linarith [hbη.1]
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

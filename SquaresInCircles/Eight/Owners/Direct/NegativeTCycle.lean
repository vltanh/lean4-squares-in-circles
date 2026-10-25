module

public import SquaresInCircles.Eight.Frames.Pair.TransportAssembly
public import SquaresInCircles.Eight.Owners.Direct.NegativeTCoupledArc

/-!
# Eight squares: hard entry by the direct negative-T transport

The transport `replaceTDE` changes only D, T and E; H, G, A and B keep their points and frames, so
a loss already spent on the circle of H is kept exactly. The resulting hard input is ordered and
keeps the selected normals of DE, EH and TD (`hardInput`, `direct_negative_t_hard_entry`).
-/

section
/-!
## Reaching BT2 along the aligned D/T/E contact

The compact set of the argument contains the points of the coupled arc, on the same circles, and
their EH margins. Neither a zero tangent of E nor a zero EH error stops a negative primary that
has not reached BT2, so its derivative forces an endpoint where BT2 is available, with a strict
reserve in the original EH witness (`CoupledStop`, `Source.coupled_stop`).
-/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace SquaresInCircles.Eight
namespace DirectNegativeT
open AlignedNegative PrimaryCap OutsideE DirectNegativeE

private theorem exists_left_improvement_with_pos {f g : ℝ → ℝ} {l m d : ℝ}
    (hd : HasDerivAt f d m) (hneg : d<0) (hlm : l< m)
    (hgc : ContinuousAt g m) (hgp : 0<g m) :
    ∃ x, x∈Ioo l m ∧ 0<g x ∧ f m<f x := by
  have hf : HasDerivAt f d (-(-m)) := by simpa using hd
  have hg : HasDerivAt (fun z => f (-z)) (-d) (-m) :=
    (hf.comp (-m) (hasDerivAt_id (-m)).neg).congr_deriv (by ring)
  have hbetter := NegativeContact.eventually_right_gt hg (neg_pos.mpr hneg)
  have hbound : ∀ᶠ z in 𝓝[>] (-m), z< -l :=
    (eventually_lt_nhds (show -m< -l by linarith)).filter_mono nhdsWithin_le_nhds
  have hgc' : ContinuousAt g (-(-m)) := by simpa using hgc
  have hgref : ContinuousAt (fun z => g (-z)) (-m) := hgc'.comp continuous_neg.continuousAt
  have hpos : ∀ᶠ z in 𝓝[>] (-m), 0<g (-z) :=
    (hgref.tendsto.eventually (eventually_gt_nhds (by simpa using hgp))).filter_mono
      nhdsWithin_le_nhds
  obtain ⟨z,hz,hbound,hpos,hbetter⟩ :=
    (eventually_mem_nhdsWithin.and (hbound.and (hpos.and hbetter))).exists
  have hz' : -m<z := hz
  exact ⟨-z,⟨by linarith,by linarith⟩,hpos,by simpa using hbetter⟩

structure CoupledStop {q t : ℝ} {D T B : SignedPoint}
    (I : Source q t D T B) (kind : ArcKind) (E H : SignedPoint) (e : ℝ) (j : Fin 4) where
  angle : ℝ
  angle_mem : angle∈Ico 0 t
  tangent_mem : coupledTangent D.circle (B.a-1/2) angle∈Icc 0 (-E.y)
  error_mem : e+angle∈Ioc 0 (21/100 : ℝ)
  hard : quarterFeasible (point (B.a-1/2) angle) B.reflect (-angle) 0
  mixed_strict : 0<coupledSlack kind q D.circle (B.a-1/2) e H j angle

theorem Source.coupled_stop {q t e : ℝ} {D T B E H : SignedPoint} {kind : ArcKind}
    (I : Source q t D T B) (J : ArcSource q E kind) (hqL : qLow≤q) (hqU : q≤qCap)
    (hHy : 211/250<H.y ∧ H.y<9/10) (hHs : H.Sorted) (hHa : H.a<1)
    (he : e+t∈Ioc 0 (21/100 : ℝ))
    (jDE jEH : Fin 4) (hjDE : jDE=2 ∨ jDE=3) (hjEH : jEH=0 ∨ jEH=1)
    (hDE : quarterFeasible D E 0 jDE) (hEH : quarterFeasible E H (e+t) jEH) :
    Nonempty (CoupledStop I kind E H e jEH) := by
  let P := B.a-1/2
  let b : ℝ → ℝ := coupledTangent D.circle P
  let L : ℝ → ℝ := coupledSlack kind q D.circle P e H jEH
  let l := max 0 (-e)
  let k : ℝ := 1/500
  let F : ℝ → ℝ := fun x => L x-L t-k*(t-x)
  have hlt : l<t := max_lt_iff.mpr ⟨I.tilt_pos,by linarith [he.1]⟩
  have hl0 : 0≤l := le_max_left _ _
  have hlE : -e≤l := le_max_right _ _
  have hDEraw : 1≤D.a-E.y := by
    rcases hjDE with rfl | rfl <;>
      simpa [quarterFeasible,quarterProjection,edgeWidth_zero] using hDE
  have hbupper {x : ℝ} (hx : x∈Icc 0 t) : b x≤ -E.y := by
    have hh := (I.path_geometry hqU hx).2.2.1
    rw [SignedPoint.reflect_circle] at hh
    change D.a≤(movingAnchor D.circle P x).a at hh
    dsimp [b,coupledTangent]
    linarith
  have hbt : 0<b t := by
    have hh := ((I.normalize hqU).source.cuts hqU).2.2.2.2.1
    rw [(I.normalize hqU).H_eq,SignedPoint.reflect_circle] at hh
    exact sub_pos.mpr hh
  have hbtmem : b t∈Icc 0 (-E.y) :=
    ⟨hbt.le,hbupper ⟨I.tilt_pos.le,le_rfl⟩⟩
  have hLstart : 0≤L t := by
    have hm := ArcSource.mixed_projection_mono J (H := H) hqL hbtmem
      ⟨he.1.le,by linarith [he.2]⟩ jEH hjEH
    have hf : quarterFeasible (kind.point q (b t)) H (e+t) jEH := hEH.trans hm
    dsimp [L]
    rw [coupledSlack_actual kind H jEH hjEH ⟨he.1.le,by linarith [he.2]⟩]
    exact sub_nonneg.mpr hf
  let clamp : ℝ → ℝ := fun x => max l (min t x)
  have hclamp (x : ℝ) : clamp x∈Icc l t :=
    ⟨le_max_left _ _,max_le hlt.le (min_le_left _ _)⟩
  have hclamp_eq {x : ℝ} (hx : x∈Icc l t) : clamp x=x := by
    simp [clamp,min_eq_right hx.2,max_eq_right hx.1]
  have hcclamp : Continuous clamp := by dsimp [clamp]; fun_prop
  have hcosclamp (x : ℝ) : Real.cos (clamp x)≠0 := by
    apply (transport_cos_pos (x := clamp x) ?_).ne'
    rw [abs_of_nonneg (hl0.trans (hclamp x).1)]
    exact (hclamp x).2.trans I.tilt_cap
  have hvalue : Continuous (fun x => value P (clamp x)) := by
    unfold value
    exact (continuous_const.sub (continuous_const.mul
      (Real.continuous_sin.comp hcclamp))).div
      (Real.continuous_cos.comp hcclamp) hcosclamp
  have hcb : Continuous (fun x => b (clamp x)) := by
    dsimp [b,coupledTangent,movingAnchor,anchorAt]
    fun_prop
  have hprimary := kind.continuous_primary q
  have hcF : Continuous (fun x => F (clamp x)) := by
    dsimp [F,L,coupledSlack,mixedSlack,lowSlack,ehSlack,b,coupledTangent,movingAnchor,anchorAt]
    split_ifs <;> fun_prop
  let S : Set ℝ := (Icc l t ∩ {x | 0≤b (clamp x)}) ∩ {x | 0≤F (clamp x)}
  have hcompact : IsCompact S :=
    (isCompact_Icc.inter_right (isClosed_le continuous_const hcb)).inter_right
      (isClosed_le continuous_const hcF)
  have htS : t∈S := by
    refine ⟨⟨⟨hlt.le,le_rfl⟩,?_⟩,?_⟩
    · show 0≤b (clamp t)
      rw [hclamp_eq ⟨hlt.le,le_rfl⟩]; exact hbt.le
    · show 0≤F (clamp t)
      rw [hclamp_eq ⟨hlt.le,le_rfl⟩]; simp [F]
  obtain ⟨m,hm,hmin⟩ := hcompact.exists_isMinOn ⟨t,htS⟩ continuous_id.continuousOn
  have hmint : m∈Icc l t := hm.1.1
  have hm0 : 0≤m := hl0.trans hmint.1
  have hbm : 0≤b m := by
    have h2 : 0≤b (clamp m) := hm.1.2
    rwa [hclamp_eq hmint] at h2
  have hbmem : b m∈Icc 0 (-E.y) := ⟨hbm,hbupper ⟨hm0,hmint.2⟩⟩
  have hFm : 0≤F m := by
    have h2 : 0≤F (clamp m) := hm.2
    rwa [hclamp_eq hmint] at h2
  have hLm : 0≤L m := by
    have hh := mul_nonneg (show 0≤k by norm_num [k]) (sub_nonneg.mpr hmint.2)
    dsimp [F] at hFm
    linarith
  have hem : e+m∈Icc 0 (21/100 : ℝ) := by constructor <;> linarith [hmint.1,hmint.2,he.2]
  have heh : quarterFeasible (coupledPoint kind q D.circle P m) H (e+m) jEH := by
    have hh := hLm
    dsimp [L] at hh
    rw [coupledSlack_actual kind H jEH hjEH ⟨hem.1,by linarith [hem.2]⟩] at hh
    exact sub_nonneg.mp hh
  have hep : 0<e+m := by
    apply lt_of_le_of_ne hem.1
    intro hezero
    have hf : quarterFeasible (kind.point q (b m)) H 0 jEH := by
      rw [← hezero] at heh
      exact heh
    exact zero_error_impossible hHa hbm jEH hjEH hf
  have hhard : quarterFeasible (point P m) B.reflect (-m) 0 := by
    by_contra hnot
    have hmpos : 0<m := by
      apply lt_of_le_of_ne hm0
      intro hzero
      have hprimary : quarterFeasible (point P 0) B.reflect 0 1 := by
        have h := (actual_primary_contact
          (show B.reflect.a=P+1/2 by dsimp [P,SignedPoint.reflect]; ring)
          (show (0:ℝ)∈Icc 0 (7/10) by constructor <;> norm_num)).ge
        rw [neg_zero] at h
        exact h
      apply hnot
      rw [← hzero,neg_zero]
      exact (quarter_low_tie (point P 0) B.reflect).2 hprimary
    have hlm : l<m := max_lt_iff.mpr ⟨hmpos,by linarith⟩
    have hgeom := I.path_geometry hqU ⟨hm0,hmint.2⟩
    have hc : Real.cos m≠0 := (transport_cos_pos (by
      rw [abs_of_nonneg hm0]; exact hmint.2.trans I.tilt_cap)).ne'
    have hrad : 0<D.circle-(2-value P m)^2 := by
      have h := hgeom.2.2.2.2.2.2
      rw [SignedPoint.reflect_circle] at h
      exact h
    have hDb := (movingAnchor_derivatives hc hrad).1
    have hbder : HasDerivAt b (primaryGain D.circle P m) m :=
      (hDb.const_sub 1).congr_deriv (neg_neg _)
    have hbpositive : 0<b m := by
      have hh := ((I.atAngle hqU ⟨hmpos,hmint.2⟩ hnot).cuts hqU).2.2.2.2.1
      rw [SignedPoint.reflect_circle] at hh
      exact sub_pos.mpr hh
    have hdL := ArcSource.coupled_hasDerivAt J (e := e) (H := H) hqL hbmem hc hrad jEH
    have hdF : HasDerivAt F (coupledDerivative kind q D.circle P e H jEH m+k) m :=
      ((hdL.sub_const (L t)).sub
        (((hasDerivAt_id m).const_sub t).const_mul k)).congr_deriv (by ring)
    have hneg : coupledDerivative kind q D.circle P e H jEH m+k<0 := by
      have hh := I.coupled_derivative_negative J hqL hqU hHy hHs
        ⟨hmpos,hmint.2⟩ hnot hbmem hem jEH hjEH
      dsimp [P,k]
      linarith
    obtain ⟨x,hx,hbx,hbetter⟩ := exists_left_improvement_with_pos hdF hneg hlm
      hbder.continuousAt hbpositive
    have hxt : x∈Icc l t := ⟨hx.1.le,hx.2.le.trans hmint.2⟩
    have hxS : x∈S := by
      refine ⟨⟨hxt,?_⟩,?_⟩
      · show 0≤b (clamp x)
        rw [hclamp_eq hxt]; exact hbx.le
      · show 0≤F (clamp x)
        rw [hclamp_eq hxt]; exact hFm.trans hbetter.le
    have hh : m≤x := hmin hxS
    linarith [hx.2]
  have hmt : m<t := by
    apply lt_of_le_of_ne hmint.2
    intro hmeq
    have hh := (I.normalize hqU).source.no_hard
    rw [(I.normalize hqU).G_eq] at hh
    rw [hmeq] at hhard
    exact hh hhard
  have hstrict : 0<L m := by
    have hgrowth := mul_pos (show 0<k by norm_num [k]) (sub_pos.mpr hmt)
    dsimp [F] at hFm
    linarith
  exact ⟨⟨m,⟨hm0,hmt⟩,hbmem,⟨hep,hem.2⟩,hhard,hstrict⟩⟩

end DirectNegativeT
end SquaresInCircles.Eight
end
end
end

section
/-!
## Strict original-D-circle loss at the direct negative-T endpoints

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
end
end
end

section
/-!
## Complete direct negative-T local transport with E's original sign

The three actual positions of E relative to D are
exhausted. E below D reaches actual alignment on its radial arc; E above D
reaches BT2 or actual alignment on D's own circle; the aligned contact then
reaches BT2 with a paid strict D-circle loss. H and B are never changed.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
namespace DirectNegativeT
open AlignedNegative PrimaryCap OutsideE DirectNegativeE

theorem original_eh_error_positive {H E : SignedPoint} {p : ℝ} {j : Fin 4}
    (hHs : H.Sorted) (hHy : 0≤H.y) (hHa : H.a<1)
    (hEs : E.Sorted) (hEy : E.y≤0) (hp : |p|≤7/10)
    (hj : j=0 ∨ j=1) (hf : quarterFeasible E H p j) : 0<p := by
  by_contra! hnonpos
  have hn : -p∈Icc 0 (7/10 : ℝ) := by constructor <;> linarith [(abs_le.mp hp).1]
  have hsin : Real.sin p≤0 := by
    have hh := (transport_trig hn).2.2.1
    rwa [Real.sin_neg,neg_nonneg] at hh
  have hcos : 0<Real.cos p := transport_cos_pos hp
  have hwidth := edgeWidth_ge_one p
  rcases hj with rfl | rfl
  · have hc := mul_le_mul_of_nonneg_left (Real.cos_le_one p) hHs.1.le
    have hs := mul_nonpos_of_nonneg_of_nonpos hHy hsin
    simp only [quarterFeasible,quarterProjection,Matrix.cons_val_zero] at hf
    linarith
  · have hs := mul_nonpos_of_nonneg_of_nonpos hEs.1.le hsin
    have hy := mul_nonpos_of_nonpos_of_nonneg hEy hcos.le
    simp [quarterFeasible,quarterProjection] at hf
    linarith

/-- The original E position, either mixed error sign, and all four mixed
owner combinations are included. The near-H cuts and H--D span remain
explicit source hypotheses; no global owner-exclusion theorem is presumed. -/
theorem Source.direct_endpoint {q t e h : ℝ} {D T B E H : SignedPoint}
    (I : Source q t D T B) (hqL : qLow≤q) (hqU : q≤qCap)
    (hHy : 211/250<H.y ∧ H.y<9/10) (hHs : H.Sorted) (hHa : H.a<1)
    (hEs : E.Sorted) (hEc : E.Contained q) (hEcore : E.AvoidsCore)
    (hEr : E.Boundary q) (hEy : E.y≤0)
    (hDEwidth : |e+t|≤7/10) (hEHwidth : |h-e|≤7/10)
    (hspan : h+t<21/100)
    (jDE jEH : Fin 4) (hjDE : jDE=2 ∨ jDE=3) (hjEH : jEH=0 ∨ jEH=1)
    (hDE : quarterFeasible D E (e+t) jDE) (hEH : quarterFeasible E H (h-e) jEH) :
    Nonempty (LocalEndpoint I E H e h jDE jEH) := by
  have hp : 0<h-e := original_eh_error_positive hHs (by linarith [hHy.1]) hHa
    hEs hEy hEHwidth hjEH hEH
  have hpwide : h-e∈Ioc 0 (7/10 : ℝ) := ⟨hp,(abs_le.mp hEHwidth).2⟩
  have hDs : D.Sorted := by simpa using I.H_sorted
  have hcuts := I.cuts hqU
  have hDy : 211/250< -D.y := hcuts.2.2.2.1
  have hDa : D.a<1 := hcuts.2.2.2.2.1
  rcases lt_trichotomy (e+t) 0 with hbelow | haligned | habove
  · let n := -(e+t)
    have hn : n∈Ioc 0 (7/10 : ℝ) := by
      dsimp [n]
      constructor <;> linarith [(abs_le.mp hDEwidth).1]
    obtain ⟨O⟩ := DirectNegativeE.alignment_endpoint hqL hqU hHy hHs hHa hDy hDs hDa
      hEs hEy hEr hn hpwide jDE jEH hjDE hjEH (by simpa [n] using hDE) hEH
    have hα : h+t∈Ioc 0 (21/100 : ℝ) := by
      refine ⟨?_,hspan.le⟩
      have hh := O.positive_span
      dsimp [n] at hh
      linarith
    have hEHaligned : quarterFeasible O.point H (h+t) jEH := by
      have heq : (h-e)-n=h+t := by dsimp [n]; ring
      simpa only [heq] using O.EH
    obtain ⟨kind,J⟩ := arcSource_of_owner O.sorted O.nonpos O.radial hHy hHs hHa hjEH
      ⟨hα.1.le,by linarith [hα.2]⟩ hEHaligned
    obtain ⟨S⟩ := I.coupled_stop J hqL hqU hHy hHs hHa hα jDE jEH hjDE hjEH O.DE hEHaligned
    obtain ⟨K⟩ := S.hard_endpoint J hqL hqU hjDE hjEH O.DE
    exact ⟨{
      angle := K.angle
      angle_mem := K.angle_mem
      Dpoint := K.Dpoint
      Tpoint := K.Tpoint
      Epoint := K.Epoint
      Etheta := K.Etheta
      E_frame := by
        right
        rcases K.E_frame with heq | hrange
        · rw [heq]
          exact ⟨le_rfl,by linarith [I.tilt_pos]⟩
        · exact hrange
      E_advance := (show e≤ -t by linarith).trans K.E_advance
      D_sorted := K.D_sorted
      T_sorted := K.T_sorted
      E_sorted := K.E_sorted
      D_core := K.D_core
      T_core := K.T_core
      E_core := K.E_core
      D_circle_loss := K.D_circle_loss
      T_inside := K.T_inside
      E_contained := K.E_contained
      E_radial := K.E_radial
      E_circle_nonincrease := K.E_circle_nonincrease.trans O.circle_nonincrease
      D_negative := K.D_negative
      T_positive := K.T_positive
      E_nonpos := K.E_nonpos
      D_nondiagonal := K.D_nondiagonal
      T_nondiagonal := K.T_nondiagonal
      D_tangent_decreases := K.D_tangent_decreases
      TD0 := K.TD0
      TD2 := K.TD2
      BT2 := K.BT2
      DE := K.DE
      EH := K.EH }⟩
  · have heq : e= -t := by linarith
    have hα : h+t∈Ioc 0 (21/100 : ℝ) := ⟨by linarith,hspan.le⟩
    obtain ⟨kind,J⟩ := arcSource_of_owner hEs hEy hEr hHy hHs hHa hjEH
      ⟨hp.le,hpwide.2⟩ hEH
    have hDEaligned : quarterFeasible D E 0 jDE := by simpa [haligned] using hDE
    have hEHaligned : quarterFeasible E H (h+t) jEH := by simpa [heq] using hEH
    obtain ⟨O⟩ := I.coupled_stop J hqL hqU hHy hHs hHa hα jDE jEH hjDE hjEH
      hDEaligned hEHaligned
    simpa only [heq] using O.hard_endpoint J hqL hqU hjDE hjEH hDEaligned
  · have hd : e+t∈Ioc 0 (21/100 : ℝ) := ⟨habove,by linarith⟩
    obtain ⟨O⟩ := I.positive_de_stop hqU hEs hEc hEcore hEy hd jDE hjDE hDE
    by_cases hhard : quarterFeasible (point (B.a-1/2) O.angle) B.reflect (-O.angle) 0
    · exact O.hard_endpoint hqU hEs hEc hEcore hEr hEy hjDE hEH hhard
    · have hal : e+O.angle=0 := O.terminal.resolve_left hhard
      have hmpos : 0<O.angle := by
        apply lt_of_le_of_ne O.angle_mem.1
        intro hzero
        have hprimary : quarterFeasible (point (B.a-1/2) 0) B.reflect 0 1 := by
          have h := (actual_primary_contact
            (show B.reflect.a=(B.a-1/2)+1/2 by dsimp [SignedPoint.reflect]; ring)
            (show (0:ℝ)∈Icc 0 (7/10) by constructor <;> norm_num)).ge
          rw [neg_zero] at h
          exact h
        apply hhard
        rw [← hzero,neg_zero]
        exact (quarter_low_tie (point (B.a-1/2) 0) B.reflect).2 hprimary
      let D₁ := Dpath D.circle (B.a-1/2) O.angle
      let T₁ := Tpath (B.a-1/2) O.angle
      have hg := I.path_data hqU O.angle_mem
      have I₁ : Source q O.angle D₁ T₁ B := by
        have h := I.atAngle hqU ⟨hmpos,O.angle_mem.2.le⟩ hhard
        rw [SignedPoint.reflect_circle] at h
        show AlignedNegative.Source q O.angle D₁.reflect T₁.reflect B.reflect
        simp only [D₁,T₁,Dpath,Tpath,SignedPoint.reflect_reflect]
        exact h
      have hDEaligned : quarterFeasible D₁ E 0 jDE := by
        have hh := O.mixed_strict.le
        rw [positiveDESlack_actual E jDE hjDE
          ⟨O.error_mem.1,by linarith [O.error_mem.2]⟩] at hh
        rw [hal] at hh
        exact sub_nonneg.mp hh
      have heq : e= -O.angle := by linarith
      have hα : h+O.angle∈Ioc 0 (21/100 : ℝ) := by
        constructor <;> linarith [O.angle_mem.2]
      have hEHaligned : quarterFeasible E H (h+O.angle) jEH := by simpa [heq] using hEH
      obtain ⟨kind,J⟩ := arcSource_of_owner hEs hEy hEr hHy hHs hHa hjEH
        ⟨hp.le,hpwide.2⟩ hEH
      obtain ⟨S⟩ := I₁.coupled_stop J hqL hqU hHy hHs hHa hα jDE jEH hjDE hjEH
        hDEaligned hEHaligned
      obtain ⟨K⟩ := S.hard_endpoint J hqL hqU hjDE hjEH hDEaligned
      exact ⟨{
        angle := K.angle
        angle_mem := ⟨K.angle_mem.1,K.angle_mem.2.trans O.angle_mem.2⟩
        Dpoint := K.Dpoint
        Tpoint := K.Tpoint
        Epoint := K.Epoint
        Etheta := K.Etheta
        E_frame := by
          rcases K.E_frame with hh | hh
          · exact Or.inl (hh.trans heq.symm)
          · exact Or.inr ⟨by linarith [hh.1,O.angle_mem.2],hh.2⟩
        E_advance := heq.trans_le K.E_advance
        D_sorted := K.D_sorted
        T_sorted := K.T_sorted
        E_sorted := K.E_sorted
        D_core := K.D_core
        T_core := K.T_core
        E_core := K.E_core
        D_circle_loss := K.D_circle_loss.trans_eq hg.D_circle
        T_inside := K.T_inside
        E_contained := K.E_contained
        E_radial := K.E_radial
        E_circle_nonincrease := K.E_circle_nonincrease
        D_negative := K.D_negative
        T_positive := K.T_positive
        E_nonpos := K.E_nonpos
        D_nondiagonal := K.D_nondiagonal
        T_nondiagonal := K.T_nondiagonal
        D_tangent_decreases := K.D_tangent_decreases.trans hg.D_tangent
        TD0 := K.TD0
        TD2 := K.TD2
        BT2 := K.BT2
        DE := K.DE
        EH := K.EH }⟩

end DirectNegativeT
end SquaresInCircles.Eight
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
open Candidate
namespace DirectNegativeT

private theorem feasible_T_iff (C : SignedCycle) (j : Fin 4) :
    C.Feasible T j ↔
      edgeWidth (delta C.theta T)≤zeroProjection (C.point T) (C.point D) (delta C.theta T) j := by
  have hw : Candidate.word T=0 := by decide
  have hn : next T=D := by decide
  simp only [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,hw,↓reduceIte,hn,sub_nonneg]

private theorem feasible_B_iff (C : SignedCycle) (j : Fin 4) :
    C.Feasible B j ↔
      edgeWidth (delta C.theta B)≤quarterProjection (C.point B) (C.point T) (delta C.theta B) j := by
  have hw : Candidate.word B=1 := by decide
  have hn : next B=T := by decide
  simp only [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,hw,one_ne_zero,↓reduceIte,hn,
    sub_nonneg]

/-- The local source of the reflected D/T/B contact, which does not involve E; E and its mixed
witnesses keep their signed coordinates. -/
theorem sourceOfCycle {q : ℝ} {C : SignedCycle}
    (hn : C.Necessary q) (ha : C.NormalAnchors) (w : C.Witnesses)
    (halign : C.theta T=C.theta D) (ht : C.theta D<C.theta B)
    (hy : 0≤(C.point T).y) (hBT : C.Feasible B 3) (hnot : ¬C.Feasible B 2) :
    Source q (C.theta B-C.theta D) (C.point D) (C.point T) (C.point B) := by
  have hδT : delta C.theta T=0 := by
    simpa [delta,next,T,D] using sub_eq_zero.mpr halign.symm
  have hδB : delta C.theta B= -(C.theta B-C.theta D) := by
    simp only [delta,next,B]
    change C.theta T-C.theta B= -(C.theta B-C.theta D)
    rw [halign]
    ring
  have hTD : zeroFeasible (C.point T) (C.point D) 0 (w.owner T) := by
    have h := (feasible_T_iff C _).1 (w.feasible T)
    rw [hδT] at h
    exact h
  have hTD2 : zeroFeasible (C.point T) (C.point D) 0 2 := by
    have hj : w.owner T=0 ∨ w.owner T=2 := by
      simpa [SignedCycle.normalOwners,T] using w.allowed T
    rcases hj with hj | hj
    · exact (zero_owner_tie _ _).1 (by simpa [hj] using hTD)
    · simpa [hj] using hTD
  have hBTr : quarterFeasible (C.point B) (C.point T) (-(C.theta B-C.theta D)) 3 := by
    have h := (feasible_B_iff C _).1 hBT
    rw [hδB] at h
    exact h
  exact {
    H_sorted := by simpa using hn.sorted D
    G_sorted := by simpa using hn.sorted T
    A_sorted := by simpa using hn.sorted B
    H_contained := by simpa using hn.contained D
    G_contained := by simpa using hn.contained T
    A_contained := by simpa using hn.contained B
    H_core := by simpa using hn.core D
    G_core := by simpa using hn.core T
    A_core := by simpa using hn.core B
    H_nonneg := by simpa [SignedPoint.reflect] using neg_nonneg.mpr ha.D_nonpos
    G_nonpos := by simpa [SignedPoint.reflect] using neg_nonpos.mpr hy
    A_nonneg := by simpa [SignedPoint.reflect] using neg_nonneg.mpr ha.B_nonpos
    tilt_pos := sub_pos.mpr ht
    tilt_cap := (le_abs_self _).trans (hn.spread B D)
    HG := by simpa [reflectedOwner] using (zeroFeasible_reflect _ _ 0 2).2 hTD2
    GA := by simpa [reflectedOwner] using (quarterFeasible_reflect _ _ _ 3).2 hBTr
    no_hard := by
      intro hh
      have hf : quarterFeasible (C.point B) (C.point T) (-(C.theta B-C.theta D)) 2 :=
        (quarterFeasible_reflect _ _ _ 2).1 (by simpa [reflectedOwner] using hh)
      apply hnot
      refine (feasible_B_iff C 2).2 ?_
      rw [hδB]
      exact hf }

def replaceTDE (C : SignedCycle) (pD pT pE : SignedPoint) (x ε : ℝ) : SignedCycle :=
  replacePoint (replacePoint (replacePoint C E pE (C.theta B+ε))
    D pD (C.theta B-x)) T pT (C.theta B-x)

theorem replaceTDE_unchanged (C : SignedCycle) (pD pT pE : SignedPoint) (x ε : ℝ)
    (i : Vertex) (hiD : i≠D) (hiT : i≠T) (hiE : i≠E) :
    (replaceTDE C pD pT pE x ε).point i=C.point i ∧
      (replaceTDE C pD pT pE x ε).theta i=C.theta i := by
  simp [replaceTDE,replacePoint,hiD,hiT,hiE]

theorem replaceTDE_BT (C : SignedCycle) (pD pT pE : SignedPoint) (x ε : ℝ)
    (j : Fin 4) : (replaceTDE C pD pT pE x ε).Feasible B j ↔
      quarterFeasible (C.point B) pT (-x) j := by
  have heq : C.theta B-x-C.theta B= -x := by ring
  simp [replaceTDE,replacePoint,SignedCycle.Feasible,SignedCycle.slack,
    SignedCycle.edge,word,delta,next,B,T,D,E,quarterFeasible,sub_nonneg]

theorem replaceTDE_TD (C : SignedCycle) (pD pT pE : SignedPoint) (x ε : ℝ)
    (j : Fin 4) : (replaceTDE C pD pT pE x ε).Feasible T j ↔
      zeroFeasible pT pD 0 j := by
  simp [replaceTDE,replacePoint,SignedCycle.Feasible,SignedCycle.slack,
    SignedCycle.edge,word,delta,next,B,T,D,E,zeroFeasible,sub_nonneg]

theorem replaceTDE_DE (C : SignedCycle) (pD pT pE : SignedPoint) (x ε : ℝ)
    (j : Fin 4) : (replaceTDE C pD pT pE x ε).Feasible D j ↔
      quarterFeasible pD pE (ε+x) j := by
  have heq : C.theta B+ε-(C.theta B-x)=ε+x := by ring
  simp [replaceTDE,replacePoint,SignedCycle.Feasible,SignedCycle.slack,
    SignedCycle.edge,word,delta,next,B,T,D,E,quarterFeasible,sub_nonneg]

theorem replaceTDE_EH (C : SignedCycle) (pD pT pE : SignedPoint) (x ε : ℝ)
    (j : Fin 4) : (replaceTDE C pD pT pE x ε).Feasible E j ↔
      quarterFeasible pE (C.point H) (C.theta H-C.theta B-ε) j := by
  have heq : C.theta 0-(C.theta 3+ε)=C.theta 0-C.theta 3-ε := by ring
  simp [replaceTDE,replacePoint,SignedCycle.Feasible,SignedCycle.slack,
    SignedCycle.edge,word,delta,next,H,B,T,D,E,quarterFeasible,sub_nonneg,heq]

theorem replaceTDE_other_feasible (C : SignedCycle) (pD pT pE : SignedPoint) (x ε : ℝ)
    (i : Vertex) (hi : i=H ∨ i=G ∨ i=A) (j : Fin 4) :
    (replaceTDE C pD pT pE x ε).Feasible i j ↔ C.Feasible i j := by
  have hu : ∀ k : Vertex,k=H ∨ k=G ∨ k=A ∨ k=B →
      (replaceTDE C pD pT pE x ε).point k=C.point k ∧
        (replaceTDE C pD pT pE x ε).theta k=C.theta k := by
    intro k hk
    apply replaceTDE_unchanged <;> rcases hk with rfl | rfl | rfl | rfl <;> decide
  have h1 := hu i (by rcases hi with h | h | h <;> simp [h])
  have h2 := hu (next i) (by rcases hi with rfl | rfl | rfl <;> decide)
  simp only [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,delta,h1.1,h1.2,h2.1,h2.2]

namespace LocalEndpoint

variable {q : ℝ} {C : SignedCycle}
variable {I : Source q (C.theta B-C.theta D) (C.point D) (C.point T) (C.point B)}
variable {jDE jEH : Fin 4}

def cycle (O : LocalEndpoint I (C.point E) (C.point H)
    (C.theta E-C.theta B) (C.theta H-C.theta B) jDE jEH) : SignedCycle :=
  replaceTDE C O.Dpoint O.Tpoint O.Epoint O.angle O.Etheta

theorem unchanged (O : LocalEndpoint I (C.point E) (C.point H)
    (C.theta E-C.theta B) (C.theta H-C.theta B) jDE jEH)
    (i : Vertex) (hiD : i≠D) (hiT : i≠T) (hiE : i≠E) :
    O.cycle.point i=C.point i ∧ O.cycle.theta i=C.theta i :=
  replaceTDE_unchanged C O.Dpoint O.Tpoint O.Epoint O.angle O.Etheta i hiD hiT hiE

theorem necessary (O : LocalEndpoint I (C.point E) (C.point H)
    (C.theta E-C.theta B) (C.theta H-C.theta B) jDE jEH)
    (hn : C.Necessary q) : O.cycle.Necessary q := by
  have hDB : C.theta D≤C.theta B := by linarith [I.tilt_pos]
  have hEframe : C.theta B+O.Etheta=C.theta E ∨
      C.theta B+O.Etheta∈Icc (min (C.theta D) (C.theta B)) (max (C.theta D) (C.theta B)) := by
    rcases O.E_frame with hh | hh
    · left; linarith
    · right
      rw [min_eq_left hDB,max_eq_right hDB]
      constructor <;> linarith [hh.1,hh.2]
  have hnE := SignedCycle.necessary_replace_clamped (v := E) (a := D) (b := B)
    hn O.E_sorted O.E_contained O.E_core hEframe
  have hDframe : C.theta B-O.angle∈
      Icc (min ((replacePoint C E O.Epoint (C.theta B+O.Etheta)).theta D)
        ((replacePoint C E O.Epoint (C.theta B+O.Etheta)).theta B))
      (max ((replacePoint C E O.Epoint (C.theta B+O.Etheta)).theta D)
        ((replacePoint C E O.Epoint (C.theta B+O.Etheta)).theta B)) := by
    simp only [replacePoint,Function.update_of_ne (by decide : D≠E),
      Function.update_of_ne (by decide : B≠E),min_eq_left hDB,max_eq_right hDB,mem_Icc]
    constructor <;> linarith [O.angle_mem.1,O.angle_mem.2]
  have hnD := SignedCycle.necessary_replace_clamped (v := D) (a := D) (b := B)
    hnE O.D_sorted (O.D_circle_loss.le.trans (hn.contained D)) O.D_core (Or.inr hDframe)
  apply SignedCycle.necessary_replace_clamped (v := T) (a := D) (b := D)
    hnD O.T_sorted O.T_inside.le O.T_core.ge
  right
  simp [replacePoint]

theorem normal (O : LocalEndpoint I (C.point E) (C.point H)
    (C.theta E-C.theta B) (C.theta H-C.theta B) jDE jEH)
    (ha : C.NormalAnchors) : O.cycle.NormalAnchors := by
  constructor
  · rw [(O.unchanged H (by decide) (by decide) (by decide)).1]; exact ha.H_nonneg
  · rw [(O.unchanged A (by decide) (by decide) (by decide)).1]; exact ha.A_nonneg
  · rw [(O.unchanged B (by decide) (by decide) (by decide)).1]; exact ha.B_nonpos
  · simpa [cycle,replaceTDE,replacePoint,T,D,E] using O.D_negative.le

def witnesses (w : C.Witnesses)
    (O : LocalEndpoint I (C.point E) (C.point H)
      (C.theta E-C.theta B) (C.theta H-C.theta B) (w.owner D) (w.owner E)) :
    O.cycle.Witnesses where
  owner := ![w.owner H,w.owner G,w.owner A,2,w.owner T,w.owner D,w.owner E]
  feasible i := by
    fin_cases i
    · exact (replaceTDE_other_feasible C O.Dpoint O.Tpoint O.Epoint O.angle O.Etheta H
        (Or.inl rfl) _).2 (w.feasible H)
    · exact (replaceTDE_other_feasible C O.Dpoint O.Tpoint O.Epoint O.angle O.Etheta G
        (Or.inr (Or.inl rfl)) _).2 (w.feasible G)
    · exact (replaceTDE_other_feasible C O.Dpoint O.Tpoint O.Epoint O.angle O.Etheta A
        (Or.inr (Or.inr rfl)) _).2 (w.feasible A)
    · exact (replaceTDE_BT C O.Dpoint O.Tpoint O.Epoint O.angle O.Etheta 2).2 O.BT2
    · apply (replaceTDE_TD C O.Dpoint O.Tpoint O.Epoint O.angle O.Etheta _).2
      have hj : w.owner T=0 ∨ w.owner T=2 := by
        simpa [SignedCycle.normalOwners,T] using w.allowed T
      rcases hj with hj | hj
      · simpa [hj] using O.TD0
      · simpa [hj] using O.TD2
    · exact (replaceTDE_DE C O.Dpoint O.Tpoint O.Epoint O.angle O.Etheta _).2 O.DE
    · exact (replaceTDE_EH C O.Dpoint O.Tpoint O.Epoint O.angle O.Etheta _).2 O.EH
  allowed i := by
    fin_cases i
    · simpa [H] using w.allowed H
    · simpa [G] using w.allowed G
    · simpa [A] using w.allowed A
    · norm_num [SignedCycle.normalOwners,B]
    · simpa [T] using w.allowed T
    · simpa [D] using w.allowed D
    · simpa [E] using w.allowed E

theorem zero_signs (w : C.Witnesses)
    (O : LocalEndpoint I (C.point E) (C.point H)
      (C.theta E-C.theta B) (C.theta H-C.theta B) (w.owner D) (w.owner E))
    (hz : C.ZeroSignImplications w) : O.cycle.ZeroSignImplications (O.witnesses w) := by
  constructor
  · intro hj
    have hj' : w.owner H=2 := by simpa [witnesses,H] using hj
    rw [(O.unchanged G (by decide) (by decide) (by decide)).1]
    exact hz.HG_canceling hj'
  · intro _
    simpa [cycle,replaceTDE,replacePoint] using O.T_positive

theorem ordered (w : C.Witnesses)
    (O : LocalEndpoint I (C.point E) (C.point H)
      (C.theta E-C.theta B) (C.theta H-C.theta B) (w.owner D) (w.owner E))
    (hn : C.Necessary q) (hq : q≤qCap) (ha : C.NormalAnchors)
    (hz : C.ZeroSignImplications w) : O.cycle.Ordered :=
  SignedCycle.normal_necessary_ordered (O.necessary hn) hq (O.normal ha)
    (O.witnesses w) (O.zero_signs w hz)

theorem anchor_nonincrease (O : LocalEndpoint I (C.point E) (C.point H)
    (C.theta E-C.theta B) (C.theta H-C.theta B) jDE jEH) :
    AnchorNonincrease C O.cycle := by
  intro i hi
  by_cases hiD : i=D
  · subst i
    simpa [cycle,replaceTDE,replacePoint,D,T,E] using O.D_circle_loss.le
  · by_cases hiE : i=E
    · subst i
      simpa [cycle,replaceTDE,replacePoint,D,T,E] using O.E_circle_nonincrease
    · have hiT : i≠T := by
        rintro rfl
        revert hi
        decide
      rw [(O.unchanged i hiD hiT hiE).1]

theorem strict_anchor_loss (O : LocalEndpoint I (C.point E) (C.point H)
    (C.theta E-C.theta B) (C.theta H-C.theta B) jDE jEH) :
    StrictAnchorLoss C O.cycle := by
  refine ⟨D,by simp [anchorVertices],?_⟩
  simpa [cycle,replaceTDE,replacePoint,D,T,E] using O.D_circle_loss

def hardInput (w : C.Witnesses)
    (O : LocalEndpoint I (C.point E) (C.point H)
      (C.theta E-C.theta B) (C.theta H-C.theta B) (w.owner D) (w.owner E))
    (hn : C.Necessary q) (ha : C.NormalAnchors) (hz : C.ZeroSignImplications w)
    (hGA : C.Feasible G 0) : SignedCycle.HardInput q where
  cycle := O.cycle
  necessary := O.necessary hn
  anchors_normal := O.normal ha
  E_nonpos := by simpa [cycle,replaceTDE,replacePoint,D,T,E] using O.E_nonpos
  witnesses := O.witnesses w
  GA_hard := (replaceTDE_other_feasible C O.Dpoint O.Tpoint O.Epoint O.angle O.Etheta G
    (Or.inr (Or.inl rfl)) 0).2 hGA
  BT_hard := (replaceTDE_BT C O.Dpoint O.Tpoint O.Epoint O.angle O.Etheta 2).2 O.BT2
  zero_signs := O.zero_signs w hz
  E_radial := by
    have hh := SignedPoint.boundary_radial_alternative O.E_sorted O.E_radial
      (hn.sorted H) O.D_sorted (hn.contained H)
      (O.D_circle_loss.le.trans (hn.contained D))
    simpa [cycle,replaceTDE,replacePoint,H,D,T,E] using hh

end LocalEndpoint

/-- The hard entry at the same `q`, keeping any loss already spent on the circle of H. Its inputs
are the cuts near H and the H–D span `θ_H - θ_D < 21/100`; E may be anywhere in the frame
interval. -/
theorem direct_negative_t_hard_entry {q : ℝ} {C : SignedCycle}
    (hn : C.Necessary q) (hqL : qLow≤q) (hqU : q≤qCap) (ha : C.NormalAnchors)
    (w : C.Witnesses) (hz : C.ZeroSignImplications w)
    (hyE : (C.point E).y≤0) (hrE : (C.point E).Boundary q)
    (hHy : 211/250<(C.point H).y) (hHa : (C.point H).a<1)
    (hspan : C.theta H-C.theta D<21/100)
    (halign : C.theta T=C.theta D) (ht : C.theta D<C.theta B)
    (hyT : 0≤(C.point T).y) (hBT : C.Feasible B 3)
    (hnot : ¬C.Feasible B 2) (hGA : C.Feasible G 0) :
    ∃ J : SignedCycle.HardInput q,
      J.cycle.Ordered ∧ J.cycle.theta D=J.cycle.theta T ∧
      C.theta D<J.cycle.theta D ∧ J.cycle.theta D≤C.theta B ∧
      J.cycle.Feasible T (w.owner T) ∧ J.cycle.Feasible D (w.owner D) ∧
      J.cycle.Feasible E (w.owner E) ∧
      |(J.cycle.point D).y|<(J.cycle.point D).a ∧
      |(J.cycle.point T).y|<(J.cycle.point T).a ∧
      (J.cycle.point D).circle<(C.point D).circle ∧
      AnchorNonincrease C J.cycle ∧ StrictAnchorLoss C J.cycle ∧
      (∀ i, i≠D → i≠T → i≠E →
        J.cycle.point i=C.point i ∧ J.cycle.theta i=C.theta i) := by
  let I := sourceOfCycle hn ha w halign ht hyT hBT hnot
  have hHupper : (C.point H).y<9/10 :=
    (le_abs_self _).trans_lt (SignedPoint.coordinate_bounds
      (hn.sorted H) (hn.core H) (hn.contained H) hqU).2.2
  have hDEwidth : |(C.theta E-C.theta B)+(C.theta B-C.theta D)|≤7/10 := by
    rw [show (C.theta E-C.theta B)+(C.theta B-C.theta D)=C.theta E-C.theta D by ring]
    exact hn.spread E D
  have hEHwidth : |(C.theta H-C.theta B)-(C.theta E-C.theta B)|≤7/10 := by
    rw [show (C.theta H-C.theta B)-(C.theta E-C.theta B)=C.theta H-C.theta E by ring]
    exact hn.spread H E
  have hspan' : (C.theta H-C.theta B)+(C.theta B-C.theta D)<21/100 := by
    rw [show (C.theta H-C.theta B)+(C.theta B-C.theta D)=C.theta H-C.theta D by ring]
    exact hspan
  have hjDE : w.owner D=2 ∨ w.owner D=3 := by
    simpa [SignedCycle.normalOwners,D] using w.allowed D
  have hjEH : w.owner E=0 ∨ w.owner E=1 := by
    simpa [SignedCycle.normalOwners,E] using w.allowed E
  have hDE : quarterFeasible (C.point D) (C.point E)
      ((C.theta E-C.theta B)+(C.theta B-C.theta D)) (w.owner D) := by
    rw [show (C.theta E-C.theta B)+(C.theta B-C.theta D)=C.theta E-C.theta D by ring]
    simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,
      word,delta,next,D,E,quarterFeasible,sub_nonneg] using w.feasible D
  have hEH : quarterFeasible (C.point E) (C.point H)
      ((C.theta H-C.theta B)-(C.theta E-C.theta B)) (w.owner E) := by
    rw [show (C.theta H-C.theta B)-(C.theta E-C.theta B)=C.theta H-C.theta E by ring]
    simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,
      word,delta,next,H,E,quarterFeasible,sub_nonneg] using w.feasible E
  obtain ⟨O⟩ := I.direct_endpoint hqL hqU ⟨hHy,hHupper⟩ (hn.sorted H) hHa
    (hn.sorted E) (hn.contained E) (hn.core E) hrE hyE hDEwidth hEHwidth hspan'
    (w.owner D) (w.owner E) hjDE hjEH hDE hEH
  let J := O.hardInput w hn ha hz hGA
  refine ⟨J,O.ordered w hn hqU ha hz,?_,?_,?_,(O.witnesses w).feasible T,
    (O.witnesses w).feasible D,(O.witnesses w).feasible E,?_,?_,?_,
    O.anchor_nonincrease,O.strict_anchor_loss,?_⟩
  · simp [J,LocalEndpoint.hardInput,LocalEndpoint.cycle,replaceTDE,replacePoint,D,T,E]
  · change C.theta D<O.cycle.theta D
    have hh : C.theta D<C.theta B-O.angle := by linarith [O.angle_mem.2]
    simpa [LocalEndpoint.cycle,replaceTDE,replacePoint,D,T,E] using hh
  · change O.cycle.theta D≤C.theta B
    have hh : C.theta B-O.angle≤C.theta B := by linarith [O.angle_mem.1]
    simpa [LocalEndpoint.cycle,replaceTDE,replacePoint,D,T,E] using hh
  · simpa [J,LocalEndpoint.hardInput,LocalEndpoint.cycle,replaceTDE,replacePoint,D,T,E]
      using O.D_nondiagonal
  · simpa [J,LocalEndpoint.hardInput,LocalEndpoint.cycle,replaceTDE,replacePoint]
      using O.T_nondiagonal
  · simpa [J,LocalEndpoint.hardInput,LocalEndpoint.cycle,replaceTDE,replacePoint,D,T,E]
      using O.D_circle_loss
  · exact O.unchanged

end DirectNegativeT
end SquaresInCircles.Eight
end
end
end

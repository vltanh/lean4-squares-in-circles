module

public import SquaresInCircles.Eight.TableFree.DirectNegativeTCoupledArc

/-!
# Compact attainment of BT2 along the aligned D/T/E contact

Uncompiled source. The compact set contains only explicit same-circle
points and actual retained EH margins. Neither a zero E tangent nor a zero
EH error can stop an unconverted negative primary. Its actual derivative
therefore forces an attained BT2 endpoint with a strict original-EH reserve.
-/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace SquaresInCircles.Eight.TableFree
namespace DirectNegativeT
open AlignedNegative PrimaryCap OutsideE DirectNegativeE

private theorem exists_left_improvement_with_pos {f g : ℝ → ℝ} {l m d : ℝ}
    (hd : HasDerivAt f d m) (hneg : d<0) (hlm : l<m)
    (hgc : ContinuousAt g m) (hgp : 0<g m) :
    ∃ x, x∈Ioo l m ∧ 0<g x ∧ f m<f x := by
  have hf : HasDerivAt f d (-(-m)) := by simpa using hd
  have hg : HasDerivAt (fun z => f (-z)) (-d) (-m) := by
    simpa using hf.comp (-m) (hasDerivAt_id (-m)).neg
  have hbetter := NegativeContact.eventually_right_gt hg (neg_pos.mpr hneg)
  have hbound : ∀ᶠ z in 𝓝[>] (-m), z< -l :=
    (eventually_lt_nhds (show -m< -l by linarith)).filter_mono nhdsWithin_le_nhds
  have hgc' : ContinuousAt g (-(-m)) := by simpa using hgc
  have hgref : ContinuousAt (fun z => g (-z)) (-m) := hgc'.comp continuous_neg.continuousAt
  have hpos : ∀ᶠ z in 𝓝[>] (-m), 0<g (-z) :=
    (hgref.tendsto.eventually (eventually_gt_nhds (by simpa using hgp))).filter_mono
      nhdsWithin_le_nhds
  obtain ⟨z,hz,hbound,hpos,hbetter⟩ :=
    (self_mem_nhdsWithin.and (hbound.and (hpos.and hbetter))).exists
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
    change D.a≤(movingAnchor D.circle P x).a at hh
    dsimp [b,coupledTangent]
    linarith
  have hbt : 0<b t := by
    have hh := ((I.normalize hqU).source.cuts hqU).2.2.2.2.1
    rw [(I.normalize hqU).H_eq] at hh
    dsimp [b,coupledTangent,P]
    simpa using (show 0<1-(movingAnchor D.reflect.circle (B.reflect.a-1/2) t).a by
      linarith)
  have hbtmem : b t∈Icc 0 (-E.y) :=
    ⟨hbt.le,hbupper ⟨I.tilt_pos.le,le_rfl⟩⟩
  have hLstart : 0≤L t := by
    have hm := J.mixed_projection_mono hqL hbtmem
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
    · rw [hclamp_eq ⟨hlt.le,le_rfl⟩]; exact hbt.le
    · rw [hclamp_eq ⟨hlt.le,le_rfl⟩]; simp [F]
  obtain ⟨m,hm,hmin⟩ := hcompact.exists_isMinOn ⟨t,htS⟩ continuous_id.continuousOn
  have hmint : m∈Icc l t := hm.1.1
  have hm0 : 0≤m := hl0.trans hmint.1
  have hbm : 0≤b m := by simpa only [hclamp_eq hmint] using hm.1.2
  have hbmem : b m∈Icc 0 (-E.y) := ⟨hbm,hbupper ⟨hm0,hmint.2⟩⟩
  have hFm : 0≤F m := by simpa only [hclamp_eq hmint] using hm.2
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
      simpa [← hezero,coupledPoint,b] using heh
    exact zero_error_impossible hHa hbm jEH hjEH hf
  have hhard : quarterFeasible (point P m) B.reflect (-m) 0 := by
    by_contra hnot
    have hmpos : 0<m := by
      apply lt_of_le_of_ne hm0
      intro hzero
      have hprimary : quarterFeasible (point P 0) B.reflect 0 1 := by
        simpa using (actual_primary_contact
          (show B.reflect.a=P+1/2 by dsimp [P,SignedPoint.reflect]; ring)
          (show (0:ℝ)∈Icc 0 (7/10) by constructor <;> norm_num)).ge
      exact hnot (by simpa [← hzero] using (quarter_low_tie (point P 0) B.reflect).2 hprimary)
    have hlm : l<m := max_lt_iff.mpr ⟨hmpos,by linarith⟩
    have hgeom := I.path_geometry hqU ⟨hm0,hmint.2⟩
    have hc : Real.cos m≠0 := (transport_cos_pos (by
      rw [abs_of_nonneg hm0]; exact hmint.2.trans I.tilt_cap)).ne'
    have hrad : 0<D.circle-(2-value P m)^2 := by simpa [P] using hgeom.2.2.2.2.2.2
    have hDb := (movingAnchor_derivatives hc hrad).1
    have hbder : HasDerivAt b (primaryGain D.circle P m) m := by
      simpa [b,coupledTangent] using hDb.const_sub 1
    have hbpositive : 0<b m := by
      have hh := ((I.atAngle hqU ⟨hmpos,hmint.2⟩ hnot).cuts hqU).2.2.2.2.1
      dsimp [b,coupledTangent,P]
      simpa using (show 0<1-(movingAnchor D.reflect.circle (B.reflect.a-1/2) m).a by
        linarith)
    have hdL := J.coupled_hasDerivAt (e := e) (H := H) hqL hbmem hc hrad jEH
    have hdF : HasDerivAt F (coupledDerivative kind q D.circle P e H jEH m+k) m := by
      convert (hdL.sub_const (L t)).sub
        (((hasDerivAt_id m).const_sub t).const_mul k) using 1 <;> simp [F,L] <;> ring
    have hneg : coupledDerivative kind q D.circle P e H jEH m+k<0 := by
      have hh := I.coupled_derivative_negative J hqL hqU hHy hHs
        ⟨hmpos,hmint.2⟩ hnot hbmem hem jEH hjEH
      dsimp [P,k]
      linarith
    obtain ⟨x,hx,hbx,hbetter⟩ := exists_left_improvement_with_pos hdF hneg hlm
      hbder.continuousAt hbpositive
    have hxt : x∈Icc l t := ⟨hx.1.le,hx.2.le.trans hmint.2⟩
    have hxS : x∈S := by
      refine ⟨⟨hxt,?_⟩,?_⟩ <;> rw [hclamp_eq hxt]
      · exact hbx.le
      · exact hFm.trans hbetter.le
    have hh : m≤x := hmin hxS
    linarith [hx.2]
  have hmt : m<t := by
    apply lt_of_le_of_ne hmint.2
    intro hmeq
    have hh := (I.normalize hqU).source.no_hard
    rw [(I.normalize hqU).G_eq] at hh
    exact hh (by simpa [P,hmeq] using hhard)
  have hstrict : 0<L m := by
    have hgrowth := mul_pos (show 0<k by norm_num [k]) (sub_pos.mpr hmt)
    dsimp [F] at hFm
    linarith
  exact ⟨⟨m,⟨hm0,hmt⟩,hbmem,⟨hep,hem.2⟩,hhard,hstrict⟩⟩

end DirectNegativeT
end SquaresInCircles.Eight.TableFree

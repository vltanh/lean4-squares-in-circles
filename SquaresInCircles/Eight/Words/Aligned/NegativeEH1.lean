module

public import SquaresInCircles.Eight.Words.Aligned.NegativeEH1Arc
public import SquaresInCircles.Eight.Owners.Negative.ContactScalars

/-!
# Eight squares: a hard endpoint for the short retained-EH1 branch

Compact minimization runs over the H/G circle arc with the positive reserve `(t-x)/4000`
(`Source.eh1_hard_point`). At a minimizing boundary the EH1 slack lies in the strip where its
derivative is negative (`Source.highMixedDerivative_negative`). The strict slack at the GA0
endpoint pays for a contraction on H's own circle (`Source.eh1_hard_endpoint`), which keeps any
earlier anchor loss.
-/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace SquaresInCircles.Eight
namespace AlignedNegative
open PrimaryCap

private theorem high_exists_left_improvement {f : ℝ → ℝ} {l m d : ℝ}
    (hd : HasDerivAt f d m) (hneg : d<0) (hlm : l< m) :
    ∃ x, x∈Ioo l m ∧ f m<f x := by
  have hf : HasDerivAt f d (-(-m)) := by rw [neg_neg]; exact hd
  have hg : HasDerivAt (fun z => f (-z)) (d*(-1)) (-m) :=
    HasDerivAt.comp (-m) hf (hasDerivAt_neg' (x := -m))
  have hbetter := NegativeContact.eventually_right_gt hg (by linarith)
  have hbound : ∀ᶠ z in 𝓝[>] (-m), z< -l :=
    (eventually_lt_nhds (show -m< -l by linarith)).filter_mono nhdsWithin_le_nhds
  obtain ⟨z,hz,hbound,hbetter⟩ :=
    (eventually_mem_nhdsWithin.and (hbound.and hbetter)).exists
  have hz' : -m<z := hz
  refine ⟨-z,⟨by linarith,by linarith⟩,?_⟩
  simpa using hbetter

private theorem exists_left_positive {f : ℝ → ℝ} {l m : ℝ}
    (hc : ContinuousAt f m) (hp : 0<f m) (hlm : l< m) :
    ∃ x, x∈Ioo l m ∧ 0<f x := by
  have hpositive : ∀ᶠ x in 𝓝[<] m, 0<f x :=
    (hc.tendsto.eventually (eventually_gt_nhds hp)).filter_mono nhdsWithin_le_nhds
  have hbound : ∀ᶠ x in 𝓝[<] m, l<x :=
    (eventually_gt_nhds hlm).filter_mono nhdsWithin_le_nhds
  obtain ⟨x,hxm,hlx,hpx⟩ :=
    (eventually_mem_nhdsWithin.and (hbound.and hpositive)).exists
  exact ⟨x,⟨hlx,hxm⟩,hpx⟩

theorem Source.eh1_hard_point {q t e : ℝ} {H G A E : SignedPoint}
    (I : Source q t H G A) (hq : q≤qCap)
    (hEs : E.Sorted) (hEc : E.Contained q) (hEy : E.y≤0)
    (he : |e+t|≤11/50) (hf : quarterFeasible E H (e+t) 1) :
    ∃ x, x∈Ico 0 t ∧ e+x∈Icc 0 (11/50 : ℝ) ∧
      quarterFeasible (point (A.a-1/2) x) A (-x) 0 ∧
      0<highMixedSlack H.circle (A.a-1/2) e E x := by
  let P := A.a-1/2
  let L : ℝ → ℝ := highMixedSlack H.circle P e E
  let l : ℝ := max 0 (-e)
  let k : ℝ := 1/4000
  let F : ℝ → ℝ := fun x => L x-k*(t-x)
  have hewide : |e+t|≤7/10 := by linarith
  have hεpos := I.eh1_error_positive hq hEs hEy hewide hf
  have hlt : l<t := max_lt_iff.mpr ⟨I.tilt_pos,by linarith⟩
  have hl0 : 0≤l := le_max_left _ _
  have hlE : -e≤l := le_max_right _ _
  have hεcap : e+t≤11/50 := (abs_le.mp he).2
  have hL0 : 0≤L t := by
    have hN := (I.normalize hq).retains_mixed hq hewide (Or.inr rfl) hf
    rw [(I.normalize hq).H_eq] at hN
    dsimp [L,P]
    rw [highMixedSlack_actual E ⟨hεpos.le,by linarith⟩]
    exact sub_nonneg.mpr hN
  let clamp : ℝ → ℝ := fun x => max l (min t x)
  have hclamp (x : ℝ) : clamp x∈Icc l t := by
    exact ⟨le_max_left _ _,max_le hlt.le (min_le_left _ _)⟩
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
  have hcF : Continuous (fun x => F (clamp x)) := by
    dsimp [F,L,highMixedSlack,movingAnchor,anchorAt]
    fun_prop
  let S : Set ℝ := Icc l t ∩ {x | 0≤F (clamp x)}
  have hcompact : IsCompact S :=
    isCompact_Icc.inter_right (isClosed_le continuous_const hcF)
  have htS : t∈S := by
    refine ⟨⟨hlt.le,le_rfl⟩,?_⟩
    show 0≤F (clamp t)
    rw [hclamp_eq ⟨hlt.le,le_rfl⟩]
    simpa [F] using hL0
  obtain ⟨m,hm,hmin⟩ := hcompact.exists_isMinOn ⟨t,htS⟩ continuous_id.continuousOn
  have hmint : m∈Icc l t := hm.1
  have hm0 : 0≤m := hl0.trans hmint.1
  have hFm : 0≤F m := by
    have h : 0≤F (clamp m) := hm.2
    rwa [hclamp_eq hmint] at h
  have hLm : 0≤L m := by
    have hh := mul_nonneg (show 0≤k by norm_num [k]) (sub_nonneg.mpr hmint.2)
    dsimp [F] at hFm
    linarith
  have hem : e+m∈Icc 0 (11/50 : ℝ) := by
    constructor <;> linarith [hmint.1,hmint.2]
  have hhard : quarterFeasible (point P m) A (-m) 0 := by
    by_contra hnot
    have hmpos : 0<m := by
      by_contra! hmnonpos
      have hmzero : m=0 := le_antisymm hmnonpos hm0
      have hprimary : quarterFeasible (point P 0) A 0 1 := by
        have h := (actual_primary_contact
          (show A.a=P+1/2 by dsimp [P]; ring)
          (show (0:ℝ)∈Icc 0 (7/10) by constructor <;> norm_num)).ge
        rw [neg_zero] at h
        exact h
      apply hnot
      rw [hmzero,neg_zero]
      exact (quarter_low_tie (point P 0) A).2 hprimary
    have hlm : l<m := by
      by_contra! hml
      have hmeq : m=l := le_antisymm hml hmint.1
      have hezero : e+m=0 := by
        rcases le_total 0 (-e) with he0 | he0
        · have hleq : l= -e := max_eq_right he0
          linarith
        · have hleq : l=0 := max_eq_left he0
          linarith
      let J := I.atAngle hq ⟨hmpos,hmint.2⟩ hnot
      have hHa := (J.cuts hq).2.2.2.2.1
      have hLzero : L m=(movingAnchor H.circle P m).a+E.y-1 := by
        simp [L,highMixedSlack,hezero]
      rw [hLzero] at hLm
      linarith
    have hgeom := I.path_geometry hq ⟨hm0,hmint.2⟩
    have hc : Real.cos m≠0 := (transport_cos_pos (by
      rw [abs_of_nonneg hm0]; exact hmint.2.trans I.tilt_cap)).ne'
    have hdL := highMixedSlack_hasDerivAt (qH := H.circle) (P := P) (e := e) E hc
      hgeom.2.2.2.2.2.2
    have hdF : HasDerivAt F (highMixedDerivative H.circle P e E m+k) m := by
      have h := hdL.fun_sub (((hasDerivAt_id' m).const_sub t).const_mul k)
      convert h using 1
      ring
    have hleft : ∃ x, x∈Ioo l m ∧ 0≤F x := by
      by_cases hFzero : F m=0
      · have hsmall : L m≤1/1000 := by
          dsimp [F,k] at hFzero
          linarith [I.tilt_cap]
        have hnegative : highMixedDerivative H.circle P e E m+k<0 := by
          have hh := I.highMixedDerivative_negative hq hEc hEy
            ⟨hmpos,hmint.2⟩ hnot hem hsmall
          dsimp [k,P]
          linarith
        obtain ⟨x,hx,hbetter⟩ := high_exists_left_improvement hdF hnegative hlm
        exact ⟨x,hx,hFm.trans hbetter.le⟩
      · have hpos : 0<F m := lt_of_le_of_ne hFm (Ne.symm hFzero)
        obtain ⟨x,hx,hposx⟩ := exists_left_positive hdF.continuousAt hpos hlm
        exact ⟨x,hx,hposx.le⟩
    obtain ⟨x,hx,hposx⟩ := hleft
    have hxt : x∈Icc l t := ⟨hx.1.le,hx.2.le.trans hmint.2⟩
    have hxS : x∈S := by
      refine ⟨hxt,?_⟩
      show 0≤F (clamp x)
      rw [hclamp_eq hxt]
      exact hposx
    have hbad : m≤x := hmin hxS
    linarith [hx.2]
  have hmt : m<t := by
    apply lt_of_le_of_ne hmint.2
    intro hmeq
    have hn := (I.normalize hq).source.no_hard
    rw [(I.normalize hq).G_eq] at hn
    exact hn (by simpa [P,hmeq] using hhard)
  have hstrict : 0<L m := by
    have hgrowth := mul_pos (show 0<k by norm_num [k]) (sub_pos.mpr hmt)
    dsimp [F] at hFm
    linarith
  exact ⟨m,⟨hm0,hmt⟩,hem,hhard,hstrict⟩

structure HighMixedEndpoint {q t : ℝ} {H G A : SignedPoint}
    (I : Source q t H G A) (E : SignedPoint) (e : ℝ) where
  angle : ℝ
  angle_mem : angle∈Ico 0 t
  Hpoint : SignedPoint
  Gpoint : SignedPoint
  H_sorted : Hpoint.Sorted
  G_sorted : Gpoint.Sorted
  H_core : Hpoint.AvoidsCore
  G_core : Gpoint.Core
  H_circle_loss : Hpoint.circle<H.circle
  G_inside : Gpoint.circle<q
  H_positive : 0<Hpoint.y
  G_negative : Gpoint.y<0
  H_nondiagonal : |Hpoint.y|<Hpoint.a
  G_nondiagonal : |Gpoint.y|<Gpoint.a
  G_primary : Gpoint.a=7/12
  H_tangent_decreases : Hpoint.y<H.y
  HG0 : zeroFeasible Hpoint Gpoint 0 0
  HG2 : zeroFeasible Hpoint Gpoint 0 2
  GA0 : quarterFeasible Gpoint A (-angle) 0
  EH1 : quarterFeasible E Hpoint (e+angle) 1
  EH_error : e+angle∈Icc 0 (11/50 : ℝ)

theorem Source.eh1_hard_endpoint {q t e : ℝ} {H G A E : SignedPoint}
    (I : Source q t H G A) (hq : q≤qCap)
    (hEs : E.Sorted) (hEc : E.Contained q) (hEy : E.y≤0)
    (he : |e+t|≤11/50) (hf : quarterFeasible E H (e+t) 1) :
    Nonempty (HighMixedEndpoint I E e) := by
  obtain ⟨x,hx,heX,hGA,hL⟩ := I.eh1_hard_point hq hEs hEc hEy he hf
  let P := A.a-1/2
  let H₀ := movingAnchor H.circle P x
  let G₀ := point P x
  obtain ⟨hHs,hHcircle,hHprimary,hHtangent,hHcore,hHy,hHrad⟩ :=
    I.path_geometry hq ⟨hx.1,hx.2.le⟩
  have hHtangentStrict := I.path_tangent_strict hq hx
  have hHsort : H₀.y<H₀.a := by
    have hh := I.H_sorted.2
    rw [abs_of_nonneg I.H_nonneg] at hh
    exact hHtangentStrict.trans_le (hh.trans hHprimary)
  have hHhigh : 211/250<H₀.a := by
    have hh := I.H_sorted.2
    rw [abs_of_nonneg I.H_nonneg] at hh
    exact (I.cuts hq).2.2.2.1.trans_le (hh.trans hHprimary)
  let margin := highMixedSlack H.circle P e E x
  have hmargin : 0<margin := hL
  let η := min ((H₀.a-H₀.y)/2) (min ((H₀.a-7/12)/2) (margin/2))
  have hη : 0<η := by
    apply lt_min
    · exact div_pos (sub_pos.mpr hHsort) (by norm_num)
    · apply lt_min
      · apply div_pos _ (by norm_num)
        linarith
      · exact div_pos hmargin (by norm_num)
  have hηsort : η≤(H₀.a-H₀.y)/2 := min_le_left _ _
  have hηcore : η≤(H₀.a-7/12)/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hηslack : η≤margin/2 := (min_le_right _ _).trans (min_le_right _ _)
  let H' : SignedPoint := ⟨H₀.a-η,H₀.y⟩
  have hHs' : H'.Sorted := by
    constructor
    · dsimp [H']; linarith
    · dsimp [H']; rw [abs_of_pos hHy]; linarith
  have hHcore' : H'.AvoidsCore := by
    have ha : 7/12≤H'.a := by dsimp [H']; linarith
    unfold SignedPoint.AvoidsCore SignedPoint.coreDistance
    rw [max_eq_left (by linarith : 0≤H'.a-1/2)]
    nlinarith [sq_nonneg (max (|H'.y|-1/2) 0)]
  have hHloss : H'.circle<H.circle := by
    have hp : 0<η*(2*(H₀.a+1/2)-η) := by
      apply mul_pos hη
      linarith
    have heq : H₀.circle=H.circle := hHcircle
    rw [← heq]
    dsimp [H',SignedPoint.circle]
    nlinarith
  obtain ⟨hPlo,hPup,hcap,hDle⟩ := I.cap_data hq
  have hD := I.path_cap hq ⟨hx.1,hx.2.le⟩
  obtain ⟨hGs,hGcore,hGavoid,hGinside⟩ := point_geometric
    ⟨hPlo,hPup⟩ ⟨hx.1,hx.2.le.trans I.tilt_cap⟩ (by linarith [hD.1])
    (I.cuts hq).2.2.2.2.2.2.2
  have hGnegative : G₀.y<0 := by dsimp [G₀,point,P]; linarith [hD.1]
  have hHnondiagonal : |H'.y|<H'.a := by
    dsimp [H']; rw [abs_of_pos hHy]; linarith
  have hGnondiagonal : |G₀.y|<G₀.a := by
    rw [abs_of_neg hGnegative]
    dsimp [G₀,point]
    linarith [hD.2.1]
  have hHG0 : zeroFeasible H' G₀ 0 0 := by
    simp only [zeroFeasible,zeroProjection,H',H₀,G₀,movingAnchor,anchorAt,point,edgeWidth_zero,
      Real.sin_zero,Real.cos_zero,Matrix.cons_val_zero]
    linarith
  have hEH : quarterFeasible E H' (e+x) 1 := by
    have hm : margin=quarterProjection E H₀ (e+x) 1-edgeWidth (e+x) :=
      highMixedSlack_actual E ⟨heX.1,by linarith [heX.2]⟩
    change edgeWidth (e+x)≤quarterProjection E H' (e+x) 1
    simp only [quarterProjection,Matrix.cons_val_one,Matrix.cons_val_zero,H'] at hm ⊢
    linarith
  exact ⟨{
    angle := x
    angle_mem := hx
    Hpoint := H'
    Gpoint := G₀
    H_sorted := hHs'
    G_sorted := hGs
    H_core := hHcore'
    G_core := hGcore
    H_circle_loss := hHloss
    G_inside := hGinside
    H_positive := hHy
    G_negative := hGnegative
    H_nondiagonal := hHnondiagonal
    G_nondiagonal := hGnondiagonal
    G_primary := rfl
    H_tangent_decreases := hHtangentStrict
    HG0 := hHG0
    HG2 := (zero_owner_tie _ _).1 hHG0
    GA0 := hGA
    EH1 := hEH
    EH_error := heX }⟩

end AlignedNegative
end SquaresInCircles.Eight

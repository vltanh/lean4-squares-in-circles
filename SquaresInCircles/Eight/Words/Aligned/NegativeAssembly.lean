module

public import SquaresInCircles.Eight.Frames.Pair.TransportAssembly
public import SquaresInCircles.Eight.Owners.Negative.ContactGeometry
public import SquaresInCircles.Eight.Words.Aligned.NegativeEH1Arc

/-!
# Eight squares: seven-cycle assembly of the retained-EH0 negative conversion

`replaceHG` inserts the moved H and G at their physical frames `θA + x`; all other centers and
frames, including E, are unchanged. The weak HG witness of the original cycle is kept, even when
its owner is 2. The moved cycle `LowMixedEndpoint.cycle` is necessary and in physical order, its
two changed centers are strictly nondiagonal, and H has a strict loss on its own original
circle.

A BT2 axis then gives a hard-class descendant (`aligned_negative_eh0_hard_entry`). Earlier
anchor losses do no harm: only containment and the radial alternative of E in the original cycle
are used, and no anchor is lifted to the circle `q`.
-/

section
/-!
## An aligned negative primary reaches GA0 with strict H loss

The endpoint is obtained by minimizing the frame over a compact set on which the physical EH0
margin keeps a reserve (`Source.eh0_hard_point`): there GA0 holds and the EH0 slack is strictly
positive. That slack pays for a contraction of H's primary with a strict loss on H's circle
(`Source.eh0_hard_endpoint`). Only H and G change; A and E, and hence every other anchor, stay
the same.
-/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace SquaresInCircles.Eight
namespace AlignedNegative
open PrimaryCap

private theorem exists_left_improvement {f : ℝ → ℝ} {l m d : ℝ}
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

theorem Source.eh0_error_positive {q t ε : ℝ} {H G A E : SignedPoint}
    (I : Source q t H G A) (hq : q≤qCap)
    (hE : E.y≤0) (hε : |ε|≤7/10) (hf : quarterFeasible E H ε 0) : 0<ε := by
  have hHa := (I.cuts hq).2.2.2.2.1
  have hHpos : 0<H.a := I.H_sorted.1
  by_contra! hnonpos
  have hneg : -ε∈Icc 0 (7/10 : ℝ) := by
    constructor <;> linarith [(abs_le.mp hε).1]
  have hs := (transport_trig hneg).2.2.1
  rw [Real.sin_neg] at hs
  have hcos := mul_le_mul_of_nonneg_left (Real.cos_le_one ε) hHpos.le
  have hsin := mul_nonpos_of_nonneg_of_nonpos I.H_nonneg (by linarith : Real.sin ε≤0)
  have hp : edgeWidth ε≤E.y+H.a*Real.cos ε+H.y*Real.sin ε := hf
  linarith [edgeWidth_ge_one ε]

/-- The selected endpoint is a GA0 contact-or-feasible state, and the positive amount of frame
movement has bought strict EH0 slack. The proof uses a compact minimum and the strict physical
derivative. -/
theorem Source.eh0_hard_point {q t e : ℝ} {H G A E : SignedPoint}
    (I : Source q t H G A) (hq : q≤qCap)
    (hE : E.y≤0) (he : |e+t|≤7/10)
    (hf : quarterFeasible E H (e+t) 0) :
    ∃ x, x∈Ico 0 t ∧ e+x∈Icc 0 (7/10 : ℝ) ∧
      quarterFeasible (point (A.a-1/2) x) A (-x) 0 ∧
      0<lowMixedSlack H.circle (A.a-1/2) e E x := by
  let P := A.a-1/2
  let L : ℝ → ℝ := lowMixedSlack H.circle P e E
  let l : ℝ := max 0 (-e)
  let k : ℝ := 3/100
  let F : ℝ → ℝ := fun x => L x-L t-k*(t-x)
  have hεpos := I.eh0_error_positive hq hE he hf
  have hlt : l<t := by
    exact max_lt_iff.mpr ⟨I.tilt_pos,by linarith⟩
  have hl0 : 0≤l := le_max_left _ _
  have hlE : -e≤l := le_max_right _ _
  have hεcap : e+t≤7/10 := (abs_le.mp he).2
  have hL0 : 0≤L t := by
    have hN := (I.normalize hq).retains_mixed hq he (Or.inl rfl) hf
    have hNeq := (I.normalize hq).H_eq
    rw [hNeq] at hN
    dsimp [L,P]
    rw [lowMixedSlack_actual E ⟨hεpos.le,hεcap⟩]
    exact sub_nonneg.mpr hN
  let clamp : ℝ → ℝ := fun x => max l (min t x)
  have hclamp (x : ℝ) : clamp x∈Icc l t := by
    refine ⟨le_max_left _ _,?_⟩
    exact max_le hlt.le (min_le_left _ _)
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
    dsimp [F,L,lowMixedSlack,movingAnchor,anchorAt]
    fun_prop
  let S : Set ℝ := Icc l t ∩ {x | 0≤F (clamp x)}
  have hcompact : IsCompact S :=
    isCompact_Icc.inter_right (isClosed_le continuous_const hcF)
  have htS : t∈S := by
    refine ⟨⟨hlt.le,le_rfl⟩,?_⟩
    show 0≤F (clamp t)
    rw [hclamp_eq ⟨hlt.le,le_rfl⟩]
    simp [F]
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
  have hem : e+m∈Icc 0 (7/10 : ℝ) := by
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
      have hLzero : L m=E.y+(movingAnchor H.circle P m).a-1 := by
        simp [L,lowMixedSlack,hezero]
      rw [hLzero] at hLm
      linarith
    have hgeom := I.path_geometry hq ⟨hm0,hmint.2⟩
    have hc : Real.cos m≠0 := (transport_cos_pos (by
      rw [abs_of_nonneg hm0]; exact hmint.2.trans I.tilt_cap)).ne'
    have hdL := lowMixedSlack_hasDerivAt (qH := H.circle) (P := P) (e := e) E hc
      hgeom.2.2.2.2.2.2
    have hdF : HasDerivAt F (lowMixedDerivative H.circle P e m+k) m := by
      have h := (hdL.sub_const (L t)).fun_sub (((hasDerivAt_id' m).const_sub t).const_mul k)
      convert h using 1
      ring
    have hnegative : lowMixedDerivative H.circle P e m+k<0 := by
      have hh := I.lowMixedDerivative_negative hq ⟨hmpos,hmint.2⟩ hnot hem
      dsimp [k,P]
      linarith
    obtain ⟨x,hx,hbetter⟩ := exists_left_improvement hdF hnegative hlm
    have hxt : x∈Icc l t := ⟨hx.1.le,hx.2.le.trans hmint.2⟩
    have hxS : x∈S := by
      refine ⟨hxt,?_⟩
      show 0≤F (clamp x)
      rw [hclamp_eq hxt]
      exact hFm.trans hbetter.le
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

structure LowMixedEndpoint {q t : ℝ} {H G A : SignedPoint}
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
  EH0 : quarterFeasible E Hpoint (e+angle) 0
  EH_error : e+angle∈Icc 0 (7/10 : ℝ)

/-- The strict mixed margin pays for a contraction of H's primary. The loss is on the original
H circle, so an earlier loss is kept. -/
theorem Source.eh0_hard_endpoint {q t e : ℝ} {H G A E : SignedPoint}
    (I : Source q t H G A) (hq : q≤qCap)
    (hE : E.y≤0) (he : |e+t|≤7/10)
    (hf : quarterFeasible E H (e+t) 0) : Nonempty (LowMixedEndpoint I E e) := by
  obtain ⟨x,hx,heX,hGA,hL⟩ := I.eh0_hard_point hq hE he hf
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
  let margin := lowMixedSlack H.circle P e E x
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
    · dsimp [H']
      linarith
    · dsimp [H']
      rw [abs_of_pos hHy]
      linarith
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
    dsimp [H']
    rw [abs_of_pos hHy]
    linarith
  have hGnondiagonal : |G₀.y|<G₀.a := by
    rw [abs_of_neg hGnegative]
    dsimp [G₀,point]
    linarith [hD.2.1]
  have hHG0 : zeroFeasible H' G₀ 0 0 := by
    simp only [zeroFeasible,zeroProjection,H',H₀,G₀,movingAnchor,anchorAt,point,edgeWidth_zero,
      Real.sin_zero,Real.cos_zero,Matrix.cons_val_zero]
    linarith
  have hEH : quarterFeasible E H' (e+x) 0 := by
    have hm : margin=quarterProjection E H₀ (e+x) 0-edgeWidth (e+x) :=
      lowMixedSlack_actual E heX
    have hc := mul_le_mul_of_nonneg_left (Real.cos_le_one (e+x)) hη.le
    change edgeWidth (e+x)≤quarterProjection E H' (e+x) 0
    simp only [quarterProjection,Matrix.cons_val_zero,H'] at hm ⊢
    nlinarith
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
    EH0 := hEH
    EH_error := heX }⟩

end AlignedNegative
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
namespace AlignedNegative

/-- Both changed physical frames have tilt x above the retained A frame. -/
def replaceHG (C : SignedCycle) (pH pG : SignedPoint) (x : ℝ) : SignedCycle :=
  replacePoint (replacePoint C H pH (C.theta A+x)) G pG (C.theta A+x)

theorem replaceHG_unchanged (C : SignedCycle) (pH pG : SignedPoint) (x : ℝ)
    (i : Vertex) (hH : i≠H) (hG : i≠G) :
    (replaceHG C pH pG x).point i=C.point i ∧
      (replaceHG C pH pG x).theta i=C.theta i := by
  simp [replaceHG,replacePoint,hH,hG]

theorem replaceHG_HG (C : SignedCycle) (pH pG : SignedPoint) (x : ℝ)
    (j : Fin 4) :
    (replaceHG C pH pG x).Feasible H j ↔ zeroFeasible pH pG 0 j := by
  simp [replaceHG,replacePoint,SignedCycle.Feasible,SignedCycle.slack,
    SignedCycle.edge,word,delta,next,H,G,A,zeroFeasible,sub_nonneg]

theorem replaceHG_GA (C : SignedCycle) (pH pG : SignedPoint) (x : ℝ)
    (j : Fin 4) :
    (replaceHG C pH pG x).Feasible G j ↔
      quarterFeasible pG (C.point A) (-x) j := by
  simp [replaceHG,replacePoint,SignedCycle.Feasible,SignedCycle.slack,
    SignedCycle.edge,word,delta,next,H,G,A,quarterFeasible,sub_nonneg]

theorem replaceHG_EH (C : SignedCycle) (pH pG : SignedPoint) (x : ℝ)
    (j : Fin 4) :
    (replaceHG C pH pG x).Feasible E j ↔
      quarterFeasible (C.point E) pH (C.theta A-C.theta E+x) j := by
  rw [show C.theta A-C.theta E+x=C.theta A+x-C.theta E by ring]
  simp [replaceHG,replacePoint,SignedCycle.Feasible,SignedCycle.slack,
    SignedCycle.edge,word,delta,next,H,G,A,E,quarterFeasible,sub_nonneg]

/-- In particular AB, BT, TD, and DE retain every original weak owner. -/
theorem replaceHG_other_feasible (C : SignedCycle) (pH pG : SignedPoint) (x : ℝ)
    (i : Vertex) (hi : i≠H ∧ i≠G ∧ i≠E) (j : Fin 4) :
    (replaceHG C pH pG x).Feasible i j ↔ C.Feasible i j := by
  have hn : next i≠H ∧ next i≠G := by
    revert hi; fin_cases i <;> decide
  obtain ⟨hnH,hnG⟩ := hn
  simp [replaceHG,replacePoint,SignedCycle.Feasible,SignedCycle.slack,
    SignedCycle.edge,delta,hi.1,hi.2.1,hnH,hnG]

private theorem replacement_frame_range {C : SignedCycle} {x : ℝ}
    (hx : x∈Icc 0 (C.theta H-C.theta A)) :
    C.theta A+x∈Icc (min (C.theta A) (C.theta H))
      (max (C.theta A) (C.theta H)) := by
  have hAH : C.theta A≤C.theta H := by linarith [hx.1,hx.2]
  simp only [min_eq_left hAH,max_eq_right hAH,mem_Icc]
  constructor <;> linarith [hx.1,hx.2]

theorem replaceHG_necessary {q x : ℝ} {C : SignedCycle} {pH pG : SignedPoint}
    (hn : C.Necessary q)
    (hHs : pH.Sorted) (hHc : pH.Contained q) (hHcore : pH.AvoidsCore)
    (hGs : pG.Sorted) (hGc : pG.Contained q) (hGcore : pG.AvoidsCore)
    (hx : x∈Icc 0 (C.theta H-C.theta A)) :
    (replaceHG C pH pG x).Necessary q := by
  have hnH := SignedCycle.necessary_replace_clamped (v := H) (a := A) (b := H)
    hn hHs hHc hHcore (Or.inr (replacement_frame_range hx))
  have hframe : C.theta A+x∈
      Icc (min ((replacePoint C H pH (C.theta A+x)).theta H)
          ((replacePoint C H pH (C.theta A+x)).theta H))
        (max ((replacePoint C H pH (C.theta A+x)).theta H)
          ((replacePoint C H pH (C.theta A+x)).theta H)) := by
    simp [replacePoint]
  exact SignedCycle.necessary_replace_clamped (v := G) (a := H) (b := H)
    hnH hGs hGc hGcore (Or.inr hframe)

theorem replaceHG_strictSpread {x : ℝ} {C : SignedCycle} (pH pG : SignedPoint)
    (hs : C.StrictSpread) (hx : x∈Icc 0 (C.theta H-C.theta A)) :
    (replaceHG C pH pG x).StrictSpread := by
  have hsH := SignedCycle.strictSpread_replace_clamped
    (v := H) (a := A) (b := H) (p := pH) hs
    (Or.inr (replacement_frame_range hx))
  apply SignedCycle.strictSpread_replace_clamped
    (v := G) (a := H) (b := H) (p := pG) hsH
  right
  simp [replacePoint]

/-- The local `Source`, read off the witnesses of the cycle. -/
theorem sourceOfCycle {q : ℝ} {C : SignedCycle}
    (hn : C.Necessary q) (ha : C.NormalAnchors) (w : C.Witnesses)
    (halign : C.theta G=C.theta H) (ht : C.theta A<C.theta H)
    (hy : (C.point G).y≤0) (hGA : C.Feasible G 1)
    (hnot : ¬C.Feasible G 0) :
    Source q (C.theta H-C.theta A) (C.point H) (C.point G) (C.point A) := by
  have hδH : delta C.theta H=0 := by
    simpa [delta,next,H,G] using sub_eq_zero.mpr halign
  have hδG : delta C.theta G= -(C.theta H-C.theta A) := by
    simp only [delta,next,G]
    change C.theta A-C.theta G= -(C.theta H-C.theta A)
    rw [halign]
    ring
  have hHG : zeroFeasible (C.point H) (C.point G) 0 (w.owner H) := by
    have hh := w.feasible H
    have hword : Candidate.word H=0 := by decide
    have hnext : next H=G := rfl
    unfold SignedCycle.Feasible SignedCycle.slack SignedCycle.edge at hh
    rw [ite_eq_left hword,hnext,hδH] at hh
    exact sub_nonneg.mp hh
  have hHG0 : zeroFeasible (C.point H) (C.point G) 0 0 := by
    have hj : w.owner H=0 ∨ w.owner H=2 := by
      simpa [SignedCycle.normalOwners,H] using w.allowed H
    rcases hj with hj | hj
    · simpa [hj] using hHG
    · exact (zero_owner_tie _ _).2 (by simpa [hj] using hHG)
  have hwordG : ¬Candidate.word G=0 := by decide
  have hnextG : next G=A := rfl
  exact {
    H_sorted := hn.sorted H
    G_sorted := hn.sorted G
    A_sorted := hn.sorted A
    H_contained := hn.contained H
    G_contained := hn.contained G
    A_contained := hn.contained A
    H_core := hn.core H
    G_core := hn.core G
    A_core := hn.core A
    H_nonneg := ha.H_nonneg
    G_nonpos := hy
    A_nonneg := ha.A_nonneg
    tilt_pos := sub_pos.mpr ht
    tilt_cap := by
      have hh := hn.spread H A
      dsimp [frameCap] at hh
      exact (le_abs_self _).trans hh
    HG := hHG0
    GA := by
      unfold SignedCycle.Feasible SignedCycle.slack SignedCycle.edge at hGA
      rw [ite_eq_right hwordG,hnextG,hδG] at hGA
      exact sub_nonneg.mp hGA
    no_hard := by
      intro hh
      apply hnot
      unfold SignedCycle.Feasible SignedCycle.slack SignedCycle.edge
      rw [ite_eq_right hwordG,hnextG,hδG]
      exact sub_nonneg.mpr hh }

private theorem r38_positiveVariation_expand (θ : Vertex → ℝ) :
    positiveVariation θ=positivePart (θ G-θ H)+positivePart (θ A-θ G)+
      positivePart (θ B-θ A)+positivePart (θ T-θ B)+positivePart (θ D-θ T)+
      positivePart (θ E-θ D)+positivePart (θ H-θ E) := by
  simp only [positiveVariation,Fin.sum_univ_seven,delta]
  rfl

namespace LowMixedEndpoint

variable {q : ℝ} {C : SignedCycle}
variable {I : Source q (C.theta H-C.theta A) (C.point H) (C.point G) (C.point A)}

def cycle (O : LowMixedEndpoint I (C.point E) (C.theta A-C.theta E)) : SignedCycle :=
  replaceHG C O.Hpoint O.Gpoint O.angle

theorem unchanged (O : LowMixedEndpoint I (C.point E) (C.theta A-C.theta E))
    (i : Vertex) (hiH : i≠H) (hiG : i≠G) :
    O.cycle.point i=C.point i ∧ O.cycle.theta i=C.theta i :=
  replaceHG_unchanged C O.Hpoint O.Gpoint O.angle i hiH hiG

theorem necessary (O : LowMixedEndpoint I (C.point E) (C.theta A-C.theta E))
    (hn : C.Necessary q) : O.cycle.Necessary q :=
  replaceHG_necessary hn O.H_sorted (O.H_circle_loss.le.trans (hn.contained H))
    O.H_core O.G_sorted O.G_inside.le O.G_core.ge
    ⟨O.angle_mem.1,O.angle_mem.2.le⟩

theorem normal (O : LowMixedEndpoint I (C.point E) (C.theta A-C.theta E))
    (ha : C.NormalAnchors) : O.cycle.NormalAnchors := by
  constructor
  · simpa [cycle,replaceHG,replacePoint,H,G] using O.H_positive.le
  · simpa [cycle,replaceHG,replacePoint,H,G,A] using ha.A_nonneg
  · simpa [cycle,replaceHG,replacePoint,H,G,B] using ha.B_nonpos
  · simpa [cycle,replaceHG,replacePoint,H,G,D] using ha.D_nonpos

/-- GA and EH use their new hard and retained axes. Every other selected normal, including the
original weak HG owner, stays available. -/
def witnesses (O : LowMixedEndpoint I (C.point E) (C.theta A-C.theta E))
    (w : C.Witnesses) : O.cycle.Witnesses where
  owner := ![w.owner H,0,w.owner A,w.owner B,w.owner T,w.owner D,0]
  feasible i := by
    fin_cases i
    · apply (replaceHG_HG C O.Hpoint O.Gpoint O.angle _).2
      have hj : w.owner H=0 ∨ w.owner H=2 := by
        simpa [SignedCycle.normalOwners,H] using w.allowed H
      rcases hj with hj | hj
      · simpa [hj] using O.HG0
      · simpa [hj] using O.HG2
    · exact (replaceHG_GA C O.Hpoint O.Gpoint O.angle 0).2 O.GA0
    · exact (replaceHG_other_feasible C O.Hpoint O.Gpoint O.angle A
        (by decide) _).2 (w.feasible A)
    · exact (replaceHG_other_feasible C O.Hpoint O.Gpoint O.angle B
        (by decide) _).2 (w.feasible B)
    · exact (replaceHG_other_feasible C O.Hpoint O.Gpoint O.angle T
        (by decide) _).2 (w.feasible T)
    · exact (replaceHG_other_feasible C O.Hpoint O.Gpoint O.angle D
        (by decide) _).2 (w.feasible D)
    · exact (replaceHG_EH C O.Hpoint O.Gpoint O.angle 0).2 O.EH0
  allowed i := by
    fin_cases i
    · simpa [H] using w.allowed H
    · norm_num [SignedCycle.normalOwners,G]
    · simpa [A] using w.allowed A
    · simpa [B] using w.allowed B
    · simpa [T] using w.allowed T
    · simpa [D] using w.allowed D
    · norm_num [SignedCycle.normalOwners,E]

theorem zero_signs (O : LowMixedEndpoint I (C.point E) (C.theta A-C.theta E))
    (w : C.Witnesses) (hz : C.ZeroSignImplications w) :
    O.cycle.ZeroSignImplications (O.witnesses w) := by
  constructor
  · intro _
    simpa [cycle,replaceHG,replacePoint] using O.G_negative
  · intro hh
    have hj : w.owner T=0 := by simpa [witnesses,T] using hh
    rw [(O.unchanged T (by decide) (by decide)).1]
    exact hz.TD_canceling hj

theorem ordered (O : LowMixedEndpoint I (C.point E) (C.theta A-C.theta E))
    (hn : C.Necessary q) (hq : q≤qCap) (ha : C.NormalAnchors)
    (w : C.Witnesses) (hz : C.ZeroSignImplications w) : O.cycle.Ordered :=
  SignedCycle.normal_necessary_ordered (O.necessary hn) hq (O.normal ha)
    (O.witnesses w) (O.zero_signs w hz)

theorem strict_spread
    (O : LowMixedEndpoint I (C.point E) (C.theta A-C.theta E))
    (hs : C.StrictSpread) : O.cycle.StrictSpread :=
  replaceHG_strictSpread O.Hpoint O.Gpoint hs ⟨O.angle_mem.1,O.angle_mem.2.le⟩

/-- The two signed budgets lose exactly the physical frame movement. The EH error is
nonnegative at the constructed endpoint. -/
theorem variations
    (O : LowMixedEndpoint I (C.point E) (C.theta A-C.theta E))
    (halign : C.theta G=C.theta H) :
    positiveVariation C.theta-positiveVariation O.cycle.theta=
        C.theta H-C.theta A-O.angle ∧
      negativeVariation C.theta-negativeVariation O.cycle.theta=
        C.theta H-C.theta A-O.angle := by
  have hEHnew : 0≤C.theta A+O.angle-C.theta E := by
    linarith [O.EH_error.1]
  have hEHold : 0≤C.theta H-C.theta E := by
    linarith [O.angle_mem.2]
  have hGAold : positivePart (C.theta A-C.theta H)=0 := by
    exact max_eq_right (by linarith [I.tilt_pos])
  have hGAnew : positivePart (C.theta A-(C.theta A+O.angle))=0 := by
    exact max_eq_right (by linarith [O.angle_mem.1])
  have hGAnew' : positivePart (-O.angle)=0 :=
    max_eq_right (neg_nonpos.mpr O.angle_mem.1)
  have hEHold' : positivePart (C.theta H-C.theta E)=C.theta H-C.theta E :=
    max_eq_left hEHold
  have hEHnew' : positivePart (C.theta A+O.angle-C.theta E)=
      C.theta A+O.angle-C.theta E := max_eq_left hEHnew
  have hp : positiveVariation C.theta-positiveVariation O.cycle.theta=
      C.theta H-C.theta A-O.angle := by
    have t0 : O.cycle.theta H=C.theta A+O.angle := by
      simp [cycle,replaceHG,replacePoint,H,G]
    have t1 : O.cycle.theta G=C.theta A+O.angle := by
      simp [cycle,replaceHG,replacePoint]
    have tk : ∀ k : Vertex, k≠H → k≠G → O.cycle.theta k=C.theta k :=
      fun k hH hG => (O.unchanged k hH hG).2
    rw [r38_positiveVariation_expand,r38_positiveVariation_expand]
    change _ - (positivePart (O.cycle.theta G-O.cycle.theta H)+
      positivePart (O.cycle.theta A-O.cycle.theta G)+_+_+_+_+
      positivePart (O.cycle.theta H-O.cycle.theta E))=_
    rw [t0,t1,tk A (by decide) (by decide),tk B (by decide) (by decide),
      tk T (by decide) (by decide),tk D (by decide) (by decide),
      tk E (by decide) (by decide)]
    rw [halign,sub_self,sub_self,positivePart_zero,hGAold,hGAnew,hEHold',hEHnew']
    ring
  constructor
  · exact hp
  · simpa only [← variations_equal C.theta,← variations_equal O.cycle.theta] using hp

theorem anchor_nonincrease
    (O : LowMixedEndpoint I (C.point E) (C.theta A-C.theta E)) :
    AnchorNonincrease C O.cycle := by
  intro i hi
  by_cases hH : i=H
  · subst i
    simpa [cycle,replaceHG,replacePoint,H,G] using O.H_circle_loss.le
  · have hG : i≠G := by
      rintro rfl
      revert hi; decide
    rw [(O.unchanged i hH hG).1]

theorem strict_anchor_loss
    (O : LowMixedEndpoint I (C.point E) (C.theta A-C.theta E)) :
    StrictAnchorLoss C O.cycle := by
  refine ⟨H,by simp [anchorVertices],?_⟩
  simpa [cycle,replaceHG,replacePoint,H,G] using O.H_circle_loss

/-- The E point is unchanged. If its radial alternative holds before the move, decreasing the
positive H tangent keeps it, also when H is strictly inside the circle. -/
theorem radial_alternative
    (O : LowMixedEndpoint I (C.point E) (C.theta A-C.theta E))
    (hr : (C.point E).a≤7/12 ∨
      max |(C.point H).y| |(C.point D).y|≤(C.point E).a) :
    (O.cycle.point E).a≤7/12 ∨
      max |(O.cycle.point H).y| |(O.cycle.point D).y|≤(O.cycle.point E).a := by
  have hHy : |O.Hpoint.y|≤|(C.point H).y| := by
    rw [abs_of_pos O.H_positive,abs_of_nonneg I.H_nonneg]
    exact O.H_tangent_decreases.le
  rcases hr with hr | hr
  · left
    simpa [cycle,replaceHG,replacePoint,H,G,E] using hr
  · right
    have hh : max |O.Hpoint.y| |(C.point D).y|≤(C.point E).a :=
      (max_le_max_right _ hHy).trans hr
    simpa [cycle,replaceHG,replacePoint,H,G,D,E] using hh

def hardInput (O : LowMixedEndpoint I (C.point E) (C.theta A-C.theta E))
    (hn : C.Necessary q) (ha : C.NormalAnchors) (w : C.Witnesses)
    (hz : C.ZeroSignImplications w) (hyE : (C.point E).y≤0)
    (hBT : C.Feasible B 2)
    (hr : (C.point E).a≤7/12 ∨
      max |(C.point H).y| |(C.point D).y|≤(C.point E).a) :
    SignedCycle.HardInput q where
  cycle := O.cycle
  necessary := O.necessary hn
  anchors_normal := O.normal ha
  E_nonpos := by rw [(O.unchanged E (by decide) (by decide)).1]; exact hyE
  witnesses := O.witnesses w
  GA_hard := (replaceHG_GA C O.Hpoint O.Gpoint O.angle 0).2 O.GA0
  BT_hard := (replaceHG_other_feasible C O.Hpoint O.Gpoint O.angle B
    (by decide) 2).2 hBT
  zero_signs := O.zero_signs w hz
  E_radial := O.radial_alternative hr

end LowMixedEndpoint

/-- The retained-EH0 aligned negative branch reaches the hard class at the same q, with a strict
loss on an original anchor and E unchanged. The endpoint and the order follow from the
original inequalities. -/
theorem aligned_negative_eh0_hard_entry {q : ℝ} {C : SignedCycle}
    (hn : C.Necessary q) (hq : q≤qCap) (ha : C.NormalAnchors)
    (w : C.Witnesses) (hz : C.ZeroSignImplications w)
    (hyE : (C.point E).y≤0)
    (hr : (C.point E).a≤7/12 ∨
      max |(C.point H).y| |(C.point D).y|≤(C.point E).a)
    (halign : C.theta G=C.theta H) (ht : C.theta A<C.theta H)
    (hyG : (C.point G).y≤0) (hGA : C.Feasible G 1)
    (hnot : ¬C.Feasible G 0) (hEH : C.Feasible E 0) (hBT : C.Feasible B 2) :
    ∃ J : SignedCycle.HardInput q,
      J.cycle.Ordered ∧ J.cycle.theta H=J.cycle.theta G ∧
      C.theta A≤J.cycle.theta H ∧ J.cycle.theta H<C.theta H ∧
      J.cycle.Feasible H (w.owner H) ∧ J.cycle.Feasible E 0 ∧
      |(J.cycle.point H).y|<(J.cycle.point H).a ∧
      |(J.cycle.point G).y|<(J.cycle.point G).a ∧
      (J.cycle.point H).circle<(C.point H).circle ∧
      AnchorNonincrease C J.cycle ∧ StrictAnchorLoss C J.cycle ∧
      (∀ i, i≠H → i≠G →
        J.cycle.point i=C.point i ∧ J.cycle.theta i=C.theta i) := by
  let I := sourceOfCycle hn ha w halign ht hyG hGA hnot
  have he : |(C.theta A-C.theta E)+(C.theta H-C.theta A)|≤7/10 := by
    rw [show (C.theta A-C.theta E)+(C.theta H-C.theta A)=
      C.theta H-C.theta E by ring]
    simpa [frameCap] using hn.spread H E
  have hf : quarterFeasible (C.point E) (C.point H)
      ((C.theta A-C.theta E)+(C.theta H-C.theta A)) 0 := by
    rw [show (C.theta A-C.theta E)+(C.theta H-C.theta A)=
      C.theta H-C.theta E by ring]
    simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,
      word,delta,next,H,E,quarterFeasible,sub_nonneg] using hEH
  obtain ⟨O⟩ := I.eh0_hard_endpoint hq hyE he hf
  let J := O.hardInput hn ha w hz hyE hBT hr
  refine ⟨J,O.ordered hn hq ha w hz,?_,?_,?_,?_,?_,?_,?_,?_,
    O.anchor_nonincrease,O.strict_anchor_loss,?_⟩
  · simp [J,LowMixedEndpoint.hardInput,LowMixedEndpoint.cycle,replaceHG,replacePoint,H,G]
  · change C.theta A≤(O.cycle.theta H)
    have hh : C.theta A≤C.theta A+O.angle := by linarith [O.angle_mem.1]
    simpa [LowMixedEndpoint.cycle,replaceHG,replacePoint,H,G] using hh
  · change O.cycle.theta H<C.theta H
    have hh := O.angle_mem.2
    simpa [LowMixedEndpoint.cycle,replaceHG,replacePoint,H,G] using
      (show C.theta A+O.angle<C.theta H by linarith)
  · exact (O.witnesses w).feasible H
  · exact (replaceHG_EH C O.Hpoint O.Gpoint O.angle 0).2 O.EH0
  · simpa [J,LowMixedEndpoint.hardInput,LowMixedEndpoint.cycle,
      replaceHG,replacePoint,H,G] using O.H_nondiagonal
  · simpa [J,LowMixedEndpoint.hardInput,LowMixedEndpoint.cycle,
      replaceHG,replacePoint] using O.G_nondiagonal
  · simpa [J,LowMixedEndpoint.hardInput,LowMixedEndpoint.cycle,
      replaceHG,replacePoint,H,G] using O.H_circle_loss
  · exact O.unchanged

end AlignedNegative
end SquaresInCircles.Eight
end
end
end

module

public import SquaresInCircles.Eight.TableFree.AlignedNegativeScalars

/-!
# Actual aligned-negative contact normalization on H's own circle

Uncompiled source. The source hypotheses are the original H/G/A coordinates,
actual containment and core inequalities, aligned HG, and a genuine negative
GA1 witness. H's radius is its own original corner value, even when a prior
move has already made H strictly interior to the common circle ceiling.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
namespace AlignedNegative
open PrimaryCap

structure Source (q t : ℝ) (H G A : SignedPoint) : Prop where
  H_sorted : H.Sorted
  G_sorted : G.Sorted
  A_sorted : A.Sorted
  H_contained : H.Contained q
  G_contained : G.Contained q
  A_contained : A.Contained q
  H_core : H.AvoidsCore
  G_core : G.AvoidsCore
  A_core : A.AvoidsCore
  H_nonneg : 0≤H.y
  G_nonpos : G.y≤0
  A_nonneg : 0≤A.y
  tilt_pos : 0<t
  tilt_cap : t≤7/10
  HG : zeroFeasible H G 0 0
  GA : quarterFeasible G A (-t) 1
  no_hard : ¬quarterFeasible G A (-t) 0

/-- The local cuts do not require an outer H or a radial-boundary G. This
is the domain needed when the opposite negative conversion has spent an
anchor-circle reserve already. -/
theorem Source.cuts {q t : ℝ} {H G A : SignedPoint}
    (I : Source q t H G A) (hq : q≤qCap) :
    7/12≤G.a ∧ 1/10< -G.y ∧ -G.y<39/250 ∧
      211/250<H.y ∧ H.a<1 ∧ t<9/100 ∧
      intrinsic (-G.y+1/2) t<q ∧ 5/2<q := by
  let g := -G.y
  have hg0 : 0≤g := neg_nonneg.mpr I.G_nonpos
  have habs : |G.y|=g := abs_of_nonpos I.G_nonpos
  have hsort : g≤G.a := by simpa [habs] using I.G_sorted.2
  obtain ⟨hvec,hpair⟩ := negative_primary_contact_vector I.G_sorted.1 hg0 hsort
    ⟨I.tilt_pos,I.tilt_cap⟩
    (by simpa [quarterFeasible,quarterProjection,Real.sin_neg,Real.cos_neg,g]
      using I.GA)
    (by simpa [quarterFeasible,quarterProjection,Real.sin_neg,Real.cos_neg,g]
      using lt_of_not_ge I.no_hard)
  have hAc : (A.a+1/2)^2+(A.y+1/2)^2≤q := by
    simpa [SignedPoint.Contained,SignedPoint.circle,abs_of_nonneg I.A_nonneg]
      using I.A_contained
  have hpairq : (G.a+1/2)^2+(g+3/2)^2<q := hpair.trans_le hAc
  have hgsmall : g<1/2 := by
    by_contra! hbad
    have hGa : 1≤G.a+1/2 := by linarith
    have hg : 2≤g+3/2 := by linarith
    have hsGa := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1) hGa 2
    have hsg := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) hg 2
    dsimp [qCap] at hq
    linarith
  have hGhalf := SignedPoint.primary_gt_half I.G_sorted I.G_core
  have hGcore := I.G_core
  simp only [SignedPoint.AvoidsCore,SignedPoint.coreDistance,habs,
    max_eq_left (by linarith : 0≤G.a-1/2),
    max_eq_right (by linarith : g-1/2≤0),zero_pow,add_zero] at hGcore
  have hGa : 7/12≤G.a := by nlinarith
  have hGasq := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤13/12)
    (show 13/12≤G.a+1/2 by linarith) 2
  have hgcut : g<39/250 := by
    by_contra! hbad
    dsimp [qCap] at hq
    nlinarith
  have hHG : 1≤H.y+g := by simpa [zeroFeasible,zeroProjection,g] using I.HG
  have hHhigh : 211/250<H.y := by linarith
  have hHb := (SignedPoint.coordinate_bounds I.H_sorted I.H_core
    I.H_contained hq).2.2
  have hHy : H.y<9/10 := (le_abs_self _).trans_lt hHb
  have hglow : 1/10<g := by linarith
  have hHc : (H.a+1/2)^2+(H.y+1/2)^2≤q := by
    simpa [SignedPoint.Contained,SignedPoint.circle,abs_of_nonneg I.H_nonneg]
      using I.H_contained
  have hHa : H.a<1 := by
    by_contra! hbad
    dsimp [qCap] at hq
    nlinarith
  have hs := (transport_trig_coarse ⟨I.tilt_pos.le,I.tilt_cap⟩).2.1
  have hkmul := mul_le_mul_of_nonneg_right
    (show K≤G.a+1/2 by unfold K; linarith) hs
  have hR : intrinsic (g+1/2) t<q := by
    dsimp [intrinsic,K]
    nlinarith
  have ht := (intrinsic_cuts
    ⟨by linarith,by linarith⟩ ⟨I.tilt_pos.le,I.tilt_cap⟩ (hR.trans_le hq)).2
  have hqL : 5/2<q := by nlinarith
  exact ⟨hGa,hglow,hgcut,hHhigh,hHa,ht,hR,hqL⟩

theorem Source.cap_data {q t : ℝ} {H G A : SignedPoint}
    (I : Source q t H G A) (hq : q≤qCap) :
    1/2<A.a-1/2 ∧ A.a-1/2<183/200 ∧
      -G.y+1/2≤value (A.a-1/2) t ∧
      value (A.a-1/2) t≤A.a-1/2 := by
  obtain ⟨hGa,hglow,hgcut,hHhigh,hHa,ht,hR,hqL⟩ := I.cuts hq
  obtain ⟨hc,hs0,hs⟩ := transport_trig_coarse ⟨I.tilt_pos.le,I.tilt_cap⟩
  have hcp : 0<Real.cos t := by linarith
  have hsp := Real.sin_pos_of_pos_of_lt_pi I.tilt_pos
    (by linarith [I.tilt_cap,Real.pi_gt_three])
  have hGaS := mul_pos I.G_sorted.1 hsp
  have hGyC := mul_nonneg (neg_nonneg.mpr I.G_nonpos) hcp.le
  have hga := I.GA
  simp [quarterFeasible,quarterProjection,Real.sin_neg,Real.cos_neg] at hga
  have hPlo : 1/2<A.a-1/2 := by
    have hw := edgeWidth_ge_one (-t)
    nlinarith
  have hAupper := (SignedPoint.coordinate_bounds I.A_sorted I.A_core
    I.A_contained hq).2.1
  have hPup : A.a-1/2<183/200 := by linarith
  have hcontact := value_contact_identity (A.a-1/2) t hcp.ne'
  have hK : K≤G.a+1/2 := by unfold K; linarith
  have hkmul := mul_le_mul_of_nonneg_right hK hs0
  have hw := edgeWidth_negative_formula ⟨I.tilt_pos.le,I.tilt_cap⟩
  have hcap : -G.y+1/2≤value (A.a-1/2) t := by
    rw [hw] at hga
    apply (mul_le_mul_right hcp).mp
    unfold K at hcontact hkmul
    nlinarith
  exact ⟨hPlo,hPup,hcap,value_le_position
    ⟨by linarith,hPup.le⟩ ⟨I.tilt_pos.le,I.tilt_cap⟩⟩

def anchorAt (qH D : ℝ) : SignedPoint :=
  ⟨Real.sqrt (qH-(2-D)^2)-1/2,3/2-D⟩

/-- Lowering the tangent follows H's own circle. This includes a previously
interior H: there is no lift to the common outer ceiling. -/
theorem anchorAt_geometry {H : SignedPoint} {D : ℝ}
    (hs : H.Sorted) (hH : 211/250<H.y)
    (hD : 3/5<D ∧ D<183/200) (hyle : 3/2-D≤H.y) :
    (anchorAt H.circle D).Sorted ∧
      (anchorAt H.circle D).circle=H.circle ∧
      H.a≤(anchorAt H.circle D).a ∧
      (anchorAt H.circle D).y≤H.y ∧
      (anchorAt H.circle D).AvoidsCore ∧
      0<(anchorAt H.circle D).y ∧
      0<H.circle-(2-D)^2 := by
  have hH0 : 0≤H.y := by linarith
  have hHs : H.y≤H.a := by simpa [abs_of_nonneg hH0] using hs.2
  have hY : 0<2-D := by linarith [hD.2]
  have hYle : 2-D≤H.y+1/2 := by linarith
  have hYsq := pow_le_pow_left₀ hY.le hYle 2
  have hcircle : H.circle=(H.a+1/2)^2+(H.y+1/2)^2 := by
    simp [SignedPoint.circle,abs_of_nonneg hH0]
  have hrad : 0<H.circle-(2-D)^2 := by rw [hcircle]; nlinarith [hs.1]
  have hroot := Real.sqrt_nonneg (H.circle-(2-D)^2)
  have hrootsq := Real.sq_sqrt hrad.le
  have hprimary : H.a≤(anchorAt H.circle D).a := by
    dsimp [anchorAt]
    rw [hcircle] at hrootsq
    nlinarith [hs.1]
  have hpositive : 0<(anchorAt H.circle D).y := by dsimp [anchorAt]; linarith [hD.2]
  have hsorted : (anchorAt H.circle D).Sorted := by
    constructor
    · exact hs.1.trans_le hprimary
    · rw [abs_of_pos hpositive]
      exact hyle.trans (hHs.trans hprimary)
  have hcore : (anchorAt H.circle D).AvoidsCore := by
    have ha : 211/250<(anchorAt H.circle D).a := hH.trans_le (hHs.trans hprimary)
    unfold SignedPoint.AvoidsCore SignedPoint.coreDistance
    rw [max_eq_left (by linarith : 0≤(anchorAt H.circle D).a-1/2)]
    nlinarith [sq_nonneg (max (|(anchorAt H.circle D).y|-1/2) 0)]
  refine ⟨hsorted,?_,hprimary,hyle,hcore,hpositive,hrad⟩
  simp only [SignedPoint.circle,abs_of_pos hpositive,anchorAt]
  nlinarith

structure Normalization {q t : ℝ} {H G A : SignedPoint} (I : Source q t H G A) where
  Hpoint : SignedPoint
  Gpoint : SignedPoint
  H_eq : Hpoint=anchorAt H.circle (value (A.a-1/2) t)
  G_eq : Gpoint=point (A.a-1/2) t
  source : Source q t Hpoint Gpoint A
  H_circle : Hpoint.circle=H.circle
  H_primary : H.a≤Hpoint.a
  H_tangent : Hpoint.y≤H.y
  G_tangent : Gpoint.y≤G.y
  G_core : Gpoint.Core
  G_inside : Gpoint.circle<q
  HG_contact : zeroProjection Hpoint Gpoint 0 0=edgeWidth 0
  GA_contact : quarterProjection Gpoint A (-t) 1=edgeWidth (-t)

/-- The actual same-radius contact normalization, before any frame moves. -/
def Source.normalize {q t : ℝ} {H G A : SignedPoint}
    (I : Source q t H G A) (hq : q≤qCap) : Normalization I := by
  let P := A.a-1/2
  let D := value P t
  let H' := anchorAt H.circle D
  let G' := point P t
  obtain ⟨hGa,hglow,hgcut,hHhigh,hHa,ht,hR,hqL⟩ := I.cuts hq
  obtain ⟨hPlo,hPup,hcap,hDle⟩ := I.cap_data hq
  have hD : 3/5<D ∧ D<183/200 := by
    dsimp [D,P]
    constructor <;> linarith
  have hHG : 1≤H.y-G.y := by simpa [zeroFeasible,zeroProjection] using I.HG
  have hyle : 3/2-D≤H.y := by dsimp [D,P]; linarith
  obtain ⟨hHs,hHcircle,hHprimary,hHtangent,hHcore,hHy,hHrad⟩ :=
    anchorAt_geometry I.H_sorted hHhigh hD hyle
  obtain ⟨hGs,hGcore,hGavoid,hGinside⟩ := point_geometric
    ⟨hPlo,hPup⟩ ⟨I.tilt_pos.le,I.tilt_cap⟩ (by dsimp [D] at hD; linarith [hD.1]) hqL
  have hGyle : G'.y≤G.y := by dsimp [G',point,P]; linarith
  have hHGcontact : zeroProjection H' G' 0 0=edgeWidth 0 := by
    simp [H',G',anchorAt,point,D,zeroProjection,edgeWidth_zero] <;> ring
  have hGAcontact : quarterProjection G' A (-t) 1=edgeWidth (-t) :=
    actual_primary_contact (by dsimp [P]; ring) ⟨I.tilt_pos.le,I.tilt_cap⟩
  have hnoHard : ¬quarterFeasible G' A (-t) 0 := by
    intro hh
    apply I.no_hard
    have hp : quarterProjection G' A (-t) 0≤quarterProjection G A (-t) 0 := by
      simp only [quarterProjection,Matrix.cons_val_zero]
      linarith
    exact hh.trans hp
  refine {
    Hpoint := H'
    Gpoint := G'
    H_eq := rfl
    G_eq := rfl
    source := {
      H_sorted := hHs
      G_sorted := hGs
      A_sorted := I.A_sorted
      H_contained := hHcircle.le.trans I.H_contained
      G_contained := hGinside.le
      A_contained := I.A_contained
      H_core := hHcore
      G_core := hGavoid
      A_core := I.A_core
      H_nonneg := hHy.le
      G_nonpos := by
        change -(value P t-1/2)≤0
        dsimp [D] at hD
        linarith [hD.1]
      A_nonneg := I.A_nonneg
      tilt_pos := I.tilt_pos
      tilt_cap := I.tilt_cap
      HG := hHGcontact.ge
      GA := hGAcontact.ge
      no_hard := hnoHard }
    H_circle := hHcircle
    H_primary := hHprimary
    H_tangent := hHtangent
    G_tangent := hGyle
    G_core := hGcore
    G_inside := hGinside
    HG_contact := hHGcontact
    GA_contact := hGAcontact }

/-- Lowering H's tangent on its retained circle improves either mixed
witness over the complete signed error interval. No E radial or sign
condition is needed for this fixed-frame normalization. -/
theorem Normalization.mixed_projection_mono {q t e : ℝ} {H G A E : SignedPoint}
    {I : Source q t H G A} (N : Normalization I) (hq : q≤qCap)
    (he : |e|≤7/10) {j : Fin 4} (hj : j=0 ∨ j=1) :
    quarterProjection E H e j≤quarterProjection E N.Hpoint e j := by
  have hsource := I.cuts hq
  have htarget := N.source.cuts hq
  have ha : 0≤N.Hpoint.a-H.a := sub_nonneg.mpr N.H_primary
  have hb : 0≤H.y-N.Hpoint.y := sub_nonneg.mpr N.H_tangent
  have hcircle : (N.Hpoint.a+1/2)^2+(N.Hpoint.y+1/2)^2=
      (H.a+1/2)^2+(H.y+1/2)^2 := by
    simpa [SignedPoint.circle,abs_of_nonneg I.H_nonneg,
      abs_of_nonneg N.source.H_nonneg] using N.H_circle
  have hidentity : (N.Hpoint.a-H.a)*(N.Hpoint.a+H.a+1)=
      (H.y-N.Hpoint.y)*(H.y+N.Hpoint.y+1) := by nlinarith
  have hden := mul_le_mul_of_nonneg_left
    (show N.Hpoint.a+H.a+1≤3 by linarith [hsource.2.2.2.2.1,htarget.2.2.2.2.1]) ha
  have hnum := mul_le_mul_of_nonneg_left
    (show 336/125≤H.y+N.Hpoint.y+1 by linarith [hsource.2.2.2.1,htarget.2.2.2.1]) hb
  have hrate : (112/125)*(H.y-N.Hpoint.y)≤N.Hpoint.a-H.a := by nlinarith
  have hc : 7648/10000<Real.cos e := by
    have hh := (transport_trig ⟨abs_nonneg e,he⟩).1
    simpa only [Real.cos_abs] using hh
  have hs : Real.sin e<6443/10000 := by
    by_cases he0 : 0≤e
    · exact (transport_trig ⟨he0,(abs_le.mp he).2⟩).2.2.2.1
    · have heneg : -e∈Icc 0 (7/10 : ℝ) := by
        constructor <;> linarith [(abs_le.mp he).1]
      have hh := (transport_trig heneg).2.2.1
      rw [Real.sin_neg] at hh
      linarith
  rcases hj with rfl | rfl
  · have hcoef : 0≤(112/125)*Real.cos e-Real.sin e := by linarith
    have hp := mul_nonneg (sub_nonneg.mpr hrate)
      (show 0≤Real.cos e by linarith)
    have hn := mul_nonneg hb hcoef
    simp only [quarterProjection,Matrix.cons_val_zero]
    nlinarith
  · simpa [quarterProjection] using N.H_primary

theorem Normalization.retains_mixed {q t e : ℝ} {H G A E : SignedPoint}
    {I : Source q t H G A} (N : Normalization I) (hq : q≤qCap)
    (he : |e|≤7/10) {j : Fin 4} (hj : j=0 ∨ j=1)
    (hf : quarterFeasible E H e j) : quarterFeasible E N.Hpoint e j :=
  hf.trans (N.mixed_projection_mono hq he hj)

end AlignedNegative
end SquaresInCircles.Eight.TableFree

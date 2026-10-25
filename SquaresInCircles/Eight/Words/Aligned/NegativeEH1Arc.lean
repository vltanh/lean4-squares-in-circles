module

public import SquaresInCircles.Eight.Owners.Negative.PrimaryEntry
public import SquaresInCircles.Eight.Owners.Primary.Cap

/-!
# Eight squares: a uniform short-EH1 boundary reserve on the H/G arc

The short mixed angle is at most `11/50`. E's original circle gives the strict derivative bound
`highMixedDerivative < -1/2000` whenever the EH1 slack `highMixedSlack` is at most `1/1000`
(`Source.highMixedDerivative_negative`). This closed strip contains all first feasibility
boundaries and a small positive movement reserve. E need not satisfy a radial equality.
-/

section
/-!
## The aligned negative contact has a strict anchor-circle gain

The intrinsic A-circle inequality `intrinsic D x < qCap` couples the flat-core height `D` and
the angle `x`. One affine bound on that whole domain, `D + (63/100) x < 82/125`
(`intrinsic_affine_cut`), proves the strict H-circle rate (`circle_rate_reserve`,
`circle_primary_gain`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
namespace AlignedNegative
open PrimaryCap

def intrinsic (D x : ℝ) : ℝ :=
  1+D^2+K^2+2*D*Real.cos x+2*K*Real.sin x

def tangentRate (D x : ℝ) : ℝ := K-D*Real.tan x

theorem intrinsic_hasDerivAt (D x : ℝ) :
    HasDerivAt (intrinsic D) (2*K*Real.cos x-2*D*Real.sin x) x := by
  have h := ((hasDerivAt_const x (1+D^2+K^2)).add
    ((Real.hasDerivAt_cos x).const_mul (2*D))).add
    ((Real.hasDerivAt_sin x).const_mul (2*K))
  convert h using 1
  · funext y
    simp only [intrinsic,Pi.add_apply]
  · ring

theorem intrinsic_strictMono {D : ℝ} (hD : 0≤D ∧ D≤82/125) :
    StrictMonoOn (intrinsic D) (Icc 0 (7/10 : ℝ)) := by
  apply strict_increase_of_reserve
    (df := fun x => 2*K*Real.cos x-2*D*Real.sin x) (k := 3/4)
  · exact (continuous_iff_continuousAt.mpr
      fun y => (intrinsic_hasDerivAt D y).continuousAt).continuousOn
  · intro x hx
    exact intrinsic_hasDerivAt D x
  · norm_num
  · intro x hx
    obtain ⟨hc,hs0,hs⟩ := transport_trig_coarse (Ioo_subset_Icc_self hx)
    have hm := mul_le_mul hD.2 hs.le hs0 (by norm_num : (0:ℝ)≤82/125)
    unfold K
    linarith

/-- The exceptional contact lies on one short continuous domain. -/
theorem intrinsic_cuts {D x : ℝ}
    (hD : 3/5<D ∧ D≤183/200) (hx : x∈Icc 0 (7/10 : ℝ))
    (hR : intrinsic D x<qCap) :
    D<82/125 ∧ x<9/100 := by
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hx
  have hsum : 1≤Real.sin x+Real.cos x := by
    have hh := one_le_abs_cos_add_abs_sin x
    rw [abs_of_pos (by linarith : 0<Real.cos x),abs_of_nonneg hs0] at hh
    linarith
  have hsupport : D≤D*Real.cos x+K*Real.sin x := by
    have hp := mul_nonneg (by linarith [hD.1] : 0≤D) (sub_nonneg.mpr hsum)
    have hm := mul_nonneg (show 0≤K-D by unfold K; linarith [hD.2]) hs0
    nlinarith
  have hbase : K^2+(D+1)^2<qCap := by
    dsimp [intrinsic] at hR
    nlinarith
  have hDu : D<82/125 := by
    by_contra! hbad
    dsimp [K,qCap] at hbase
    nlinarith
  refine ⟨hDu,?_⟩
  by_contra! hxlarge
  have hm := (intrinsic_strictMono ⟨by linarith [hD.1],hDu.le⟩).monotoneOn
    (show (9/100 : ℝ)∈Icc 0 (7/10) by constructor <;> norm_num) hx hxlarge
  have hc9 := Real.one_sub_sq_div_two_le_cos (x := (9/100 : ℝ))
  have hs9 := Real.sin_ge_sub_cube (show (0:ℝ)≤9/100 by norm_num)
  have hcmul := mul_le_mul_of_nonneg_right hD.1.le
    (show 0≤Real.cos (9/100 : ℝ) by linarith)
  have hDsq : (3/5 : ℝ)^2≤D^2 :=
    pow_le_pow_left₀ (by norm_num) hD.1.le 2
  dsimp [intrinsic,K,qCap] at hR hm
  nlinarith

/-- One exact affine estimate keeps the height/angle coupling. Its positive reserve is
`781/2250000`. -/
theorem intrinsic_affine_cut {D x : ℝ}
    (hD : 3/5<D ∧ D≤183/200) (hx : x∈Icc 0 (7/10 : ℝ))
    (hR : intrinsic D x<qCap) : D+(63/100)*x<82/125 := by
  obtain ⟨hDu,hxu⟩ := intrinsic_cuts hD hx hR
  have hD0 : 0≤D := by linarith [hD.1]
  have hc := Real.one_sub_sq_div_two_le_cos (x := x)
  have hs := Real.sin_ge_sub_cube hx.1
  have hxc : x^2≤(9/100 : ℝ)^2 :=
    pow_le_pow_left₀ hx.1 hxu.le 2
  have hDx : D*x≤(2/3 : ℝ)*(9/100) :=
    mul_le_mul (by linarith : D≤2/3) hxu.le hx.1 (by norm_num)
  have hcoef : 0≤2*K-21/10-D*x-(K/3)*x^2 := by
    unfold K
    nlinarith
  have hprod := mul_nonneg hx.1 hcoef
  have hcos := mul_le_mul_of_nonneg_left hc (show 0≤2*D by positivity)
  have hsin := mul_le_mul_of_nonneg_left hs (show 0≤2*K by norm_num [K])
  have hlower : (D+1)^2+K^2+(21/10)*x≤ intrinsic D x := by
    unfold intrinsic
    nlinarith
  by_contra! hbad
  have hb0 : 0≤1+82/125-(63/100)*x := by linarith [hx.1,hxu]
  have hbsq := pow_le_pow_left₀ hb0
    (show 1+82/125-(63/100)*x≤D+1 by linarith) 2
  dsimp [K,qCap] at hlower hR
  nlinarith [sq_nonneg x]

theorem short_tangent_linear {x : ℝ} (hx : x∈Icc 0 (9/100 : ℝ)) :
    0≤Real.tan x ∧ Real.tan x≤(101/100)*x := by
  have hc := transport_cos_pos (show |x|≤(7/10 : ℝ) by
    rw [abs_of_nonneg hx.1]; linarith [hx.2])
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi hx.1
    (by linarith [hx.2,Real.pi_gt_three])
  have hsin : Real.sin x≤x :=
    (le_abs_self _).trans (Real.abs_sin_le_abs.trans_eq (abs_of_nonneg hx.1))
  have hcos := Real.one_sub_sq_div_two_le_cos (x := x)
  have hsq := pow_le_pow_left₀ hx.1 hx.2 2
  have hcl : (100/101 : ℝ)≤Real.cos x := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hcl hx.1
  rw [Real.tan_eq_sin_div_cos]
  refine ⟨div_nonneg hs hc.le,?_⟩
  rw [div_le_iff₀ hc]
  nlinarith

/-- The exact scalar reserve for the anchor gain, on the whole intrinsic domain including its
endpoint `x = 0`. -/
theorem circle_rate_reserve {D x : ℝ}
    (hD : 3/5<D ∧ D≤183/200) (hx : x∈Icc 0 (7/10 : ℝ))
    (hR : intrinsic D x<qCap) :
    1<tangentRate D x ∧ tangentRate D x≤K ∧
      qCap<(2-D)^2*(1+tangentRate D x^2) := by
  obtain ⟨hDu,hxu⟩ := intrinsic_cuts hD hx hR
  have hline := intrinsic_affine_cut hD hx hR
  obtain ⟨ht0,htu⟩ := short_tangent_linear ⟨hx.1,hxu.le⟩
  have hD0 : 0≤D := by linarith [hD.1]
  have htan : D*Real.tan x≤(101/150 : ℝ)*x := by
    have hm := mul_le_mul (show D≤2/3 by linarith) htu ht0 (by norm_num)
    linarith
  let r := tangentRate D x
  let Y := 2-D
  have hrlo : K-(101/150)*x≤r := by dsimp [r,tangentRate]; linarith
  have hr : 1<r := by dsimp [K] at hrlo; linarith [hxu]
  have hru : r≤K := by
    have hm := mul_nonneg hD0 ht0
    dsimp [r,tangentRate]
    linarith
  have hY0 : 0≤Y := by dsimp [Y]; linarith
  have hYu : Y<7/5 := by dsimp [Y]; linarith [hD.1]
  have hYline : 168/125+(63/100)*x<Y := by dsimp [Y]; linarith
  have hYsq := pow_lt_pow_left₀ hYline
    (show 0≤168/125+(63/100)*x by linarith [hx.1]) (by decide : (2:ℕ)≠0)
  have hY2 : (168/125 : ℝ)^2+2*(168/125)*(63/100)*x<Y^2 := by
    linarith [sq_nonneg x]
  have hrbase : 0≤K-(101/150)*x := by unfold K; linarith [hxu]
  have hrsq := pow_le_pow_left₀ hrbase hrlo 2
  have hr2 : K^2-2*K*(101/150)*x≤r^2 := by linarith [sq_nonneg x]
  have hmult := mul_le_mul_of_nonneg_left hr2 (sq_nonneg Y)
  have hYbound : Y^2≤(7/5 : ℝ)^2 := pow_le_pow_left₀ hY0 hYu.le 2
  have hcost := mul_le_mul_of_nonneg_left hYbound
    (show 0≤2*K*(101/150)*x by unfold K; linarith [hx.1])
  have hgrowth := mul_lt_mul_of_pos_left hY2 (show 0<1+K^2 by positivity)
  refine ⟨hr,hru,?_⟩
  change qCap<Y^2*(1+r^2)
  dsimp [K,qCap] at hmult hcost hgrowth ⊢
  linarith

/-- On its own circle `qH ≤ qCap`, H's primary gains faster than one when the aligned negative
angle decreases. -/
theorem circle_primary_gain {qH D x : ℝ}
    (hD : 3/5<D ∧ D≤183/200) (hx : x∈Icc 0 (7/10 : ℝ))
    (hR : intrinsic D x<qCap) (hqH : qH≤qCap)
    (hrad : 0<qH-(2-D)^2) :
    1<(2-D)*tangentRate D x/Real.sqrt (qH-(2-D)^2) := by
  obtain ⟨hr,hru,hreserve⟩ := circle_rate_reserve hD hx hR
  have hY : 0<2-D := by linarith [hD.2]
  have hs := Real.sqrt_pos.mpr hrad
  have hs2 := Real.sq_sqrt hrad.le
  rw [lt_div_iff₀ hs]
  have hp := mul_pos hY (show 0<tangentRate D x by linarith)
  nlinarith

end AlignedNegative
end SquaresInCircles.Eight
end
end
end

section
/-!
## Aligned-negative contact normalization on H's own circle

A `Source q t H G A` records the coordinates of H, G and A, their containment and core
inequalities, the aligned HG witness, and a GA1 witness at the negative angle `-t` where GA0
fails. `Source.normalize` moves H along its own circle `H.circle`, lowering its tangent, and G
to the flat core, so that the HG and GA contacts are exact (`Normalization`); `H.circle` may lie
strictly inside the circle `q`. Lowering H's tangent keeps either mixed witness EH0 or EH1
(`Normalization.retains_mixed`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
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

/-- The local cuts hold without an outer H or a radial-boundary G, so they apply also after
the opposite negative conversion has spent an anchor-circle reserve. -/
theorem Source.cuts {q t : ℝ} {H G A : SignedPoint}
    (I : Source q t H G A) (hq : q≤qCap) :
    7/12≤G.a ∧ 1/10< -G.y ∧ -G.y<39/250 ∧
      211/250<H.y ∧ H.a<1 ∧ t<9/100 ∧
      intrinsic (-G.y+1/2) t<q ∧ 5/2<q := by
  let g := -G.y
  have hg0 : 0≤g := neg_nonneg.mpr I.G_nonpos
  have habs : |G.y|=g := abs_of_nonpos I.G_nonpos
  have hsort : g≤G.a := by rw [← habs]; exact I.G_sorted.2
  have hprim : edgeWidth (-t)≤A.a-G.a*Real.sin t-g*Real.cos t := by
    have h := I.GA
    simp only [quarterFeasible,quarterProjection,Matrix.cons_val,Real.sin_neg,
      Real.cos_neg] at h
    dsimp only [g]
    linarith only [h]
  have hsec : A.a*Real.cos t-A.y*Real.sin t-g<edgeWidth (-t) := by
    have h := not_le.mp I.no_hard
    simp only [quarterProjection,Matrix.cons_val,Real.sin_neg,Real.cos_neg] at h
    dsimp only [g]
    linarith only [h]
  obtain ⟨hvec,hpair⟩ := negative_primary_contact_vector I.G_sorted.1 hg0 hsort
    ⟨I.tilt_pos,I.tilt_cap⟩ hprim hsec
  have hAc : (A.a+1/2)^2+(A.y+1/2)^2≤q := by
    simpa [SignedPoint.Contained,SignedPoint.circle,abs_of_nonneg I.A_nonneg]
      using I.A_contained
  have hpairq : (G.a+1/2)^2+(g+3/2)^2<q := hpair.trans_le hAc
  have hgsmall : g<1/2 := by
    by_contra! hbad
    have hGa : 1≤G.a+1/2 := by linarith only [hsort,hbad]
    have hg : 2≤g+3/2 := by linarith only [hbad]
    have hsGa := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1) hGa 2
    have hsg := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) hg 2
    dsimp [qCap] at hq
    linarith only [hsGa,hsg,hpairq,hq]
  have hGhalf := SignedPoint.primary_gt_half I.G_sorted I.G_core
  have hGcore : (1/12:ℝ)^2≤(G.a-1/2)^2 := by
    have h := I.G_core
    simp only [SignedPoint.AvoidsCore,SignedPoint.coreDistance,habs,
      max_eq_left (by linarith only [hGhalf] : 0≤G.a-1/2),
      max_eq_right (by linarith only [hgsmall] : g-1/2≤0)] at h
    linarith only [h]
  have hGa : 7/12≤G.a := by
    by_contra! hlt
    have hp := mul_pos (sub_pos.mpr hlt) (sub_pos.mpr hGhalf)
    linarith only [hp,hGcore,hlt]
  have hGasq := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤13/12)
    (show 13/12≤G.a+1/2 by linarith only [hGa]) 2
  have hgcut : g<39/250 := by
    by_contra! hbad
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤414/250)
      (show 414/250≤g+3/2 by linarith only [hbad]) 2
    dsimp [qCap] at hq
    linarith only [h,hGasq,hpairq,hq]
  have hHG : 1≤H.y+g := by
    have h := I.HG
    simp only [zeroFeasible,zeroProjection_aligned,edgeWidth_zero,Matrix.cons_val] at h
    dsimp only [g]
    linarith only [h]
  have hHhigh : 211/250<H.y := by linarith only [hHG,hgcut]
  have hHb := (SignedPoint.coordinate_bounds I.H_sorted I.H_core
    I.H_contained hq).2.2
  have hHy : H.y<9/10 := (le_abs_self _).trans_lt hHb
  have hglow : 1/10<g := by linarith only [hHG,hHy]
  have hHc : (H.a+1/2)^2+(H.y+1/2)^2≤q := by
    simpa [SignedPoint.Contained,SignedPoint.circle,abs_of_nonneg I.H_nonneg]
      using I.H_contained
  have hHa : H.a<1 := by
    by_contra! hbad
    have h1 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤3/2)
      (show 3/2≤H.a+1/2 by linarith only [hbad]) 2
    have h2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤336/250)
      (show 336/250≤H.y+1/2 by linarith only [hHhigh]) 2
    dsimp [qCap] at hq
    linarith only [h1,h2,hHc,hq]
  have hs := (transport_trig_coarse ⟨I.tilt_pos.le,I.tilt_cap⟩).2.1
  have hkmul := mul_le_mul_of_nonneg_right
    (show (13/12:ℝ)≤G.a+1/2 by linarith only [hGa]) hs
  have hR : intrinsic (g+1/2) t<q := by
    dsimp only [intrinsic,K]
    linarith only [hvec,hAc,hGasq,hkmul]
  have ht := (intrinsic_cuts ⟨by linarith only [hglow],by linarith only [hgcut]⟩
    ⟨I.tilt_pos.le,I.tilt_cap⟩ (hR.trans_le hq)).2
  have hqL : 5/2<q := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤8/5)
      (show 8/5≤g+3/2 by linarith only [hglow]) 2
    linarith only [h,hGasq,hpairq]
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
  simp only [quarterFeasible,quarterProjection,Matrix.cons_val,Real.sin_neg,
    Real.cos_neg] at hga
  have hPlo : 1/2<A.a-1/2 := by
    have hw := edgeWidth_ge_one (-t)
    linarith
  have hAupper := (SignedPoint.coordinate_bounds I.A_sorted I.A_core
    I.A_contained hq).2.1
  have hPup : A.a-1/2<183/200 := by linarith
  have hcontact := value_contact_identity (A.a-1/2) t hcp.ne'
  have hK : K≤G.a+1/2 := by unfold K; linarith
  have hkmul := mul_le_mul_of_nonneg_right hK hs0
  have hw := edgeWidth_negative_formula ⟨I.tilt_pos.le,I.tilt_cap⟩
  have hcap : -G.y+1/2≤value (A.a-1/2) t := by
    rw [hw] at hga
    refine le_of_mul_le_mul_right ?_ hcp
    linarith
  exact ⟨hPlo,hPup,hcap,value_le_position
    ⟨by linarith,hPup.le⟩ ⟨I.tilt_pos.le,I.tilt_cap⟩⟩

def anchorAt (qH D : ℝ) : SignedPoint :=
  ⟨Real.sqrt (qH-(2-D)^2)-1/2,3/2-D⟩

/-- Lowering the tangent follows H's own circle, also when H lies strictly inside the common
circle; H is not lifted to the outer ceiling. -/
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
    have h := Real.le_sqrt_of_sq_le
      (show (H.a+1/2)^2≤H.circle-(2-D)^2 by rw [hcircle]; linarith)
    dsimp only [anchorAt]
    linarith
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
    have h1 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1/12)
      (show 1/12≤(anchorAt H.circle D).a-1/2 by linarith) 2
    linarith [sq_nonneg (max (|(anchorAt H.circle D).y|-1/2) 0)]
  refine ⟨hsorted,?_,hprimary,hyle,hcore,hpositive,hrad⟩
  have hy' : |(anchorAt H.circle D).y|=2-D-1/2 := by
    rw [abs_of_pos hpositive]
    dsimp only [anchorAt]
    ring
  have ha' : (anchorAt H.circle D).a+1/2=Real.sqrt (H.circle-(2-D)^2) := by
    dsimp only [anchorAt]
    ring
  show ((anchorAt H.circle D).a+1/2)^2+(|(anchorAt H.circle D).y|+1/2)^2=H.circle
  rw [hy',ha',hrootsq]
  ring

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

/-- The same-radius contact normalization, before any frame moves. -/
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
    simp [H',G',anchorAt,point,D,zeroProjection,edgeWidth_zero]
    ring
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

/-- Lowering H's tangent on its own circle improves either mixed witness over the signed error
interval `|e| ≤ 7/10`, with no radial or sign condition on E. -/
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
      (H.y-N.Hpoint.y)*(H.y+N.Hpoint.y+1) := by linear_combination hcircle
  have hden := mul_le_mul_of_nonneg_left
    (show N.Hpoint.a+H.a+1≤3 by linarith [hsource.2.2.2.2.1,htarget.2.2.2.2.1]) ha
  have hnum := mul_le_mul_of_nonneg_left
    (show 336/125≤H.y+N.Hpoint.y+1 by linarith [hsource.2.2.2.1,htarget.2.2.2.1]) hb
  have hrate : (112/125)*(H.y-N.Hpoint.y)≤N.Hpoint.a-H.a := by
    linarith only [hidentity,hden,hnum]
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
    linarith only [hp,hn]
  · simpa [quarterProjection] using N.H_primary

theorem Normalization.retains_mixed {q t e : ℝ} {H G A E : SignedPoint}
    {I : Source q t H G A} (N : Normalization I) (hq : q≤qCap)
    (he : |e|≤7/10) {j : Fin 4} (hj : j=0 ∨ j=1)
    (hf : quarterFeasible E H e j) : quarterFeasible E N.Hpoint e j :=
  hf.trans (N.mixed_projection_mono hq he hj)

end AlignedNegative
end SquaresInCircles.Eight
end
end
end

section
/-!
## The H/G circle-contact arc and its retained EH0 derivative

At every angle `x` of the frame interval, `movingAnchor` places H on its own circle and `point`
places G on the flat core (`Source.path_geometry`). The EH0 margin `lowMixedSlack` is the
physical projection (`lowMixedSlack_actual`). Its derivative is below `-3/50` wherever the
negative primary is not converted, that is, where GA0 fails
(`Source.lowMixedDerivative_negative`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
namespace AlignedNegative
open PrimaryCap

def movingAnchor (qH P x : ℝ) : SignedPoint := anchorAt qH (value P x)

def primaryGain (qH P x : ℝ) : ℝ :=
  (2-value P x)*tangentRate (value P x) x/Real.sqrt (qH-(2-value P x)^2)

def lowMixedSlack (qH P e : ℝ) (E : SignedPoint) (x : ℝ) : ℝ :=
  E.y+(movingAnchor qH P x).a*Real.cos (e+x)+
    (movingAnchor qH P x).y*Real.sin (e+x)-
      (1+Real.cos (e+x)+Real.sin (e+x))/2

def lowMixedDerivative (qH P e x : ℝ) : ℝ :=
  ((movingAnchor qH P x).y-1/2)*Real.cos (e+x)-
    primaryGain qH P x*Real.cos (e+x)+
    (tangentRate (value P x) x-(movingAnchor qH P x).a+1/2)*Real.sin (e+x)

theorem Source.path_cap {q t x : ℝ} {H G A : SignedPoint}
    (I : Source q t H G A) (hq : q≤qCap) (hx : x∈Icc 0 t) :
    3/5<value (A.a-1/2) x ∧ value (A.a-1/2) x<183/200 ∧
      3/2-value (A.a-1/2) x≤H.y := by
  obtain ⟨hPlo,hPup,hcap,hDle⟩ := I.cap_data hq
  have hxwide : x∈Icc 0 (7/10 : ℝ) := ⟨hx.1,hx.2.trans I.tilt_cap⟩
  have hanti := value_strictAnti ⟨by linarith,hPup.le⟩
  have hdown := hanti.antitoneOn hxwide ⟨I.tilt_pos.le,I.tilt_cap⟩ hx.2
  have hup := value_le_position ⟨by linarith,hPup.le⟩ hxwide
  have hglow := (I.cuts hq).2.1
  have hHG : 1≤H.y-G.y := by simpa [zeroFeasible,zeroProjection] using I.HG
  constructor
  · linarith
  constructor <;> linarith

theorem Source.path_geometry {q t x : ℝ} {H G A : SignedPoint}
    (I : Source q t H G A) (hq : q≤qCap) (hx : x∈Icc 0 t) :
    (movingAnchor H.circle (A.a-1/2) x).Sorted ∧
      (movingAnchor H.circle (A.a-1/2) x).circle=H.circle ∧
      H.a≤(movingAnchor H.circle (A.a-1/2) x).a ∧
      (movingAnchor H.circle (A.a-1/2) x).y≤H.y ∧
      (movingAnchor H.circle (A.a-1/2) x).AvoidsCore ∧
      0<(movingAnchor H.circle (A.a-1/2) x).y ∧
      0<H.circle-(2-value (A.a-1/2) x)^2 := by
  have hD := I.path_cap hq hx
  exact anchorAt_geometry I.H_sorted (I.cuts hq).2.2.2.1 ⟨hD.1,hD.2.1⟩ hD.2.2

theorem Source.path_tangent_strict {q t x : ℝ} {H G A : SignedPoint}
    (I : Source q t H G A) (hq : q≤qCap) (hx : x∈Ico 0 t) :
    (movingAnchor H.circle (A.a-1/2) x).y<H.y := by
  obtain ⟨hPlo,hPup,hcap,hDle⟩ := I.cap_data hq
  have hm := value_strictAnti ⟨by linarith,hPup.le⟩
    (show x∈Icc 0 (7/10 : ℝ) from ⟨hx.1,hx.2.le.trans I.tilt_cap⟩)
    ⟨I.tilt_pos.le,I.tilt_cap⟩ hx.2
  have hHG : 1≤H.y-G.y := by simpa [zeroFeasible,zeroProjection] using I.HG
  dsimp [movingAnchor,anchorAt]
  linarith

/-- Every point of the arc where GA0 fails is again a `Source`, so the intrinsic cuts and the
circle-rate theorem apply there. -/
theorem Source.atAngle {q t x : ℝ} {H G A : SignedPoint}
    (I : Source q t H G A) (hq : q≤qCap) (hx : x∈Ioc 0 t)
    (hnot : ¬quarterFeasible (point (A.a-1/2) x) A (-x) 0) :
    Source q x (movingAnchor H.circle (A.a-1/2) x) (point (A.a-1/2) x) A := by
  obtain ⟨hPlo,hPup,hcap,hDle⟩ := I.cap_data hq
  have hD := I.path_cap hq ⟨hx.1.le,hx.2⟩
  obtain ⟨hHs,hHcircle,hHprimary,hHtangent,hHcore,hHy,hHrad⟩ :=
    I.path_geometry hq ⟨hx.1.le,hx.2⟩
  obtain ⟨hGs,hGcore,hGavoid,hGinside⟩ := point_geometric
    ⟨hPlo,hPup⟩ ⟨hx.1.le,hx.2.trans I.tilt_cap⟩ (by linarith [hD.1])
    (I.cuts hq).2.2.2.2.2.2.2
  exact {
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
    G_nonpos := by dsimp [point]; linarith [hD.1]
    A_nonneg := I.A_nonneg
    tilt_pos := hx.1
    tilt_cap := hx.2.trans I.tilt_cap
    HG := by simp only [zeroFeasible,zeroProjection,movingAnchor,anchorAt,point,edgeWidth_zero,Real.sin_zero,Real.cos_zero,Matrix.cons_val_zero]; linarith
    GA := (actual_primary_contact (by ring) ⟨hx.1.le,hx.2.trans I.tilt_cap⟩).ge
    no_hard := hnot }

theorem movingAnchor_derivatives {qH P x : ℝ}
    (hc : Real.cos x≠0) (hrad : 0<qH-(2-value P x)^2) :
    HasDerivAt (fun z => (movingAnchor qH P z).a) (-primaryGain qH P x) x ∧
      HasDerivAt (fun z => (movingAnchor qH P z).y) (tangentRate (value P x) x) x := by
  have hD : HasDerivAt (value P) (-tangentRate (value P x) x) x := by
    convert value_hasDerivAt P x hc using 1
    rw [derivative_rewrite P x hc]
    unfold tangentRate
    ring
  have hY : HasDerivAt (fun z => 2-value P z) (tangentRate (value P x) x) x := by
    simpa using hD.const_sub 2
  have hsq : HasDerivAt (fun z => qH-(2-value P z)^2)
      (0-((2:ℕ):ℝ)*(2-value P x)^(2-1)*tangentRate (value P x) x) x :=
    (hasDerivAt_const x qH).sub (hY.pow 2)
  have hroot := hsq.sqrt hrad.ne'
  have hs : Real.sqrt (qH-(2-value P x)^2)≠0 := (Real.sqrt_pos.mpr hrad).ne'
  constructor
  · have h := hroot.sub_const (1/2)
    have hv : (0-((2:ℕ):ℝ)*(2-value P x)^(2-1)*tangentRate (value P x) x)/
        (2*Real.sqrt (qH-(2-value P x)^2))=-primaryGain qH P x := by
      unfold primaryGain
      field_simp
      ring
    rw [hv] at h
    exact h
  · simpa [movingAnchor,anchorAt] using hD.const_sub (3/2)

theorem lowMixedSlack_hasDerivAt {qH P e x : ℝ} (E : SignedPoint)
    (hc : Real.cos x≠0) (hrad : 0<qH-(2-value P x)^2) :
    HasDerivAt (lowMixedSlack qH P e E) (lowMixedDerivative qH P e x) x := by
  obtain ⟨ha,hy⟩ := movingAnchor_derivatives hc hrad
  have he : HasDerivAt (fun z => e+z) 1 x := by simpa using (hasDerivAt_id x).const_add e
  have hcos : HasDerivAt (fun z => Real.cos (e+z)) (-Real.sin (e+x)*1) x :=
    (Real.hasDerivAt_cos (e+x)).comp x he
  have hsin : HasDerivAt (fun z => Real.sin (e+z)) (Real.cos (e+x)*1) x :=
    (Real.hasDerivAt_sin (e+x)).comp x he
  have h := (((hasDerivAt_const x E.y).fun_add (ha.fun_mul hcos)).fun_add
    (hy.fun_mul hsin)).fun_sub
    ((((hasDerivAt_const x (1:ℝ)).fun_add hcos).fun_add hsin).div_const 2)
  convert h using 1
  · rfl
  · unfold lowMixedDerivative
    ring

theorem lowMixedSlack_actual {qH P e x : ℝ} (E : SignedPoint)
    (he : e+x∈Icc 0 (7/10 : ℝ)) :
    lowMixedSlack qH P e E x=
      quarterProjection E (movingAnchor qH P x) (e+x) 0-edgeWidth (e+x) := by
  rw [edgeWidth_positive_formula he]
  simp [lowMixedSlack,quarterProjection]

/-- The scalar derivative inequality, strict over the positive EH0 error interval. All bounds
concern the anchor H and its own circle. -/
theorem low_mixed_rate {X Y r c s : ℝ}
    (hX : 1≤X ∧ X<3/2) (hY : 168/125<Y ∧ Y≤X)
    (hr : 1<r) (hc : 7648/10000<c) (hs : 0≤ s ∧ s<6443/10000) :
    (Y-1)*c-r*Y/X*c+(r-X+1)*s< -(3/50) := by
  have hX0 : 0<X := by linarith
  have hc0 : 0<c := by linarith
  have hlow := mul_le_mul (show (168/125 : ℝ)≤Y by linarith)
    hc.le (by norm_num : (0:ℝ)≤7648/10000) (by linarith : 0≤Y)
  have hupp := mul_le_mul hX.2.le hs.2.le hs.1 (by norm_num : (0:ℝ)≤3/2)
  have hcoef : X*s-Y*c<0 := by nlinarith
  have hstrict := mul_neg_of_pos_of_neg (sub_pos.mpr hr) hcoef
  have hsort := mul_nonneg (sub_nonneg.mpr hY.2)
    (mul_nonneg (sub_nonneg.mpr hX.1) hc0.le)
  have hnum : X*((Y-1)*c+(r-X+1)*s)-r*Y*c<
      X*(X-2)*(c-s) := by nlinarith
  have hcs : 0<c-s := by linarith
  have hshort := mul_lt_mul_of_pos_right hX.2 hcs
  have hbound : (X-2)*(c-s)< -(3/50) := by nlinarith
  have hboundX := mul_lt_mul_of_pos_left hbound hX0
  have hid : ((Y-1)*c-r*Y/X*c+(r-X+1)*s)*X=
      X*((Y-1)*c+(r-X+1)*s)-r*Y*c := by
    field_simp
    ring
  apply lt_of_mul_lt_mul_right _ hX0.le
  rw [hid]
  linarith

theorem Source.lowMixedDerivative_negative {q t e x : ℝ} {H G A : SignedPoint}
    (I : Source q t H G A) (hq : q≤qCap) (hx : x∈Ioc 0 t)
    (hnot : ¬quarterFeasible (point (A.a-1/2) x) A (-x) 0)
    (he : e+x∈Icc 0 (7/10 : ℝ)) :
    lowMixedDerivative H.circle (A.a-1/2) e x< -(3/50) := by
  let J := I.atAngle hq hx hnot
  have hj := J.cuts hq
  have hD := I.path_cap hq ⟨hx.1.le,hx.2⟩
  have hR : intrinsic (value (A.a-1/2) x) x<qCap := by
    have hh := hj.2.2.2.2.2.2.1.trans_le hq
    simpa [point] using hh
  have hr := (circle_rate_reserve ⟨hD.1,hD.2.1.le⟩
    ⟨hx.1.le,hx.2.trans I.tilt_cap⟩ hR).1
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig he
  have hsort : (movingAnchor H.circle (A.a-1/2) x).y≤(movingAnchor H.circle (A.a-1/2) x).a := by
    have hh := J.H_sorted.2
    rwa [abs_of_nonneg J.H_nonneg] at hh
  have h := low_mixed_rate (X := (movingAnchor H.circle (A.a-1/2) x).a+1/2)
    (Y := (movingAnchor H.circle (A.a-1/2) x).y+1/2)
    ⟨by linarith [hj.2.2.2.1],by linarith [hj.2.2.2.2.1]⟩
    ⟨by linarith [hj.2.2.2.1],by linarith⟩ hr hc ⟨hs0,hs⟩
  have hroot : Real.sqrt (H.circle-(2-value (A.a-1/2) x)^2)=
      (movingAnchor H.circle (A.a-1/2) x).a+1/2 := by
    simp [movingAnchor,anchorAt]
  have hheight : 2-value (A.a-1/2) x=
      (movingAnchor H.circle (A.a-1/2) x).y+1/2 := by
    show 2-value (A.a-1/2) x=(3/2-value (A.a-1/2) x)+1/2
    ring
  have hform : lowMixedDerivative H.circle (A.a-1/2) e x=
      ((movingAnchor H.circle (A.a-1/2) x).y+1/2-1)*Real.cos (e+x)-
        tangentRate (value (A.a-1/2) x) x*((movingAnchor H.circle (A.a-1/2) x).y+1/2)/
          ((movingAnchor H.circle (A.a-1/2) x).a+1/2)*Real.cos (e+x)+
        (tangentRate (value (A.a-1/2) x) x-((movingAnchor H.circle (A.a-1/2) x).a+1/2)+1)*
          Real.sin (e+x) := by
    unfold lowMixedDerivative primaryGain
    rw [hroot,hheight]
    ring
  rw [hform]
  exact h

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
namespace AlignedNegative
open PrimaryCap

def highMixedSlack (qH P e : ℝ) (E : SignedPoint) (x : ℝ) : ℝ :=
  (movingAnchor qH P x).a+E.a*Real.sin (e+x)+E.y*Real.cos (e+x)-
    (1+Real.cos (e+x)+Real.sin (e+x))/2

def highMixedDerivative (qH P e : ℝ) (E : SignedPoint) (x : ℝ) : ℝ :=
  -primaryGain qH P x+(E.a-1/2)*Real.cos (e+x)+(1/2-E.y)*Real.sin (e+x)

theorem highMixedSlack_hasDerivAt {qH P e x : ℝ} (E : SignedPoint)
    (hc : Real.cos x≠0) (hrad : 0<qH-(2-value P x)^2) :
    HasDerivAt (highMixedSlack qH P e E) (highMixedDerivative qH P e E x) x := by
  obtain ⟨ha,hy⟩ := movingAnchor_derivatives hc hrad
  have he : HasDerivAt (fun z => e+z) 1 x := by
    simpa using (hasDerivAt_id x).const_add e
  have hcos : HasDerivAt (fun z => Real.cos (e+z)) (-Real.sin (e+x)*1) x :=
    (Real.hasDerivAt_cos (e+x)).comp x he
  have hsin : HasDerivAt (fun z => Real.sin (e+z)) (Real.cos (e+x)*1) x :=
    (Real.hasDerivAt_sin (e+x)).comp x he
  have h := ((ha.fun_add (hsin.const_mul E.a)).fun_add (hcos.const_mul E.y)).fun_sub
    ((((hasDerivAt_const x (1:ℝ)).fun_add hcos).fun_add hsin).div_const 2)
  convert h using 1
  · rfl
  · unfold highMixedDerivative
    ring

theorem highMixedSlack_actual {qH P e x : ℝ} (E : SignedPoint)
    (he : e+x∈Icc 0 (7/10 : ℝ)) :
    highMixedSlack qH P e E x=
      quarterProjection E (movingAnchor qH P x) (e+x) 1-edgeWidth (e+x) := by
  rw [edgeWidth_positive_formula he]
  simp [highMixedSlack,quarterProjection]

theorem Source.eh1_error_positive {q t ε : ℝ} {H G A E : SignedPoint}
    (I : Source q t H G A) (hq : q≤qCap)
    (hEs : E.Sorted) (hE : E.y≤0) (hε : |ε|≤7/10)
    (hf : quarterFeasible E H ε 1) : 0<ε := by
  have hHa := (I.cuts hq).2.2.2.2.1
  by_contra! hnonpos
  have hneg : -ε∈Icc 0 (7/10 : ℝ) := by
    constructor <;> linarith [(abs_le.mp hε).1]
  have hs := (transport_trig hneg).2.2.1
  rw [Real.sin_neg] at hs
  have hcos : 0<Real.cos ε := transport_cos_pos hε
  have hsin := mul_nonpos_of_nonneg_of_nonpos hEs.1.le
    (by linarith : Real.sin ε≤0)
  have htan := mul_nonpos_of_nonpos_of_nonneg hE hcos.le
  have hp : edgeWidth ε≤H.a+E.a*Real.sin ε+E.y*Real.cos ε := by
    simpa [quarterFeasible,quarterProjection] using hf
  linarith [edgeWidth_ge_one ε]

/-- The first-boundary comparison on the whole strip `L ≤ 1/1000`. The two rotated coordinates
keep E's exact shifted-circle norm. -/
theorem short_high_mixed_rate {ε aH L : ℝ} {E : SignedPoint}
    (hEc : E.Contained qCap) (hEy : E.y≤0)
    (hHa : 211/250<aH) (he : ε∈Icc 0 (11/50 : ℝ))
    (hL : L=aH+E.a*Real.sin ε+E.y*Real.cos ε-
      (1+Real.cos ε+Real.sin ε)/2) (hsmall : L≤1/1000) :
    (E.a-1/2)*Real.cos ε+(1/2-E.y)*Real.sin ε<1999/2000 := by
  let X := E.a+1/2
  let Y := 1/2-E.y
  let U := X*Real.cos ε+Y*Real.sin ε
  let V := Y*Real.cos ε-X*Real.sin ε
  have hcircle : X^2+Y^2≤qCap := by
    simpa [X,Y,SignedPoint.Contained,SignedPoint.circle,abs_of_nonpos hEy,
      sub_eq_add_neg,add_comm] using hEc
  have hrot : U^2+V^2=X^2+Y^2 := by
    calc
      U^2+V^2=(X^2+Y^2)*(Real.sin ε^2+Real.cos ε^2) := by
        dsimp [U,V]
        ring
      _=X^2+Y^2 := by rw [Real.sin_sq_add_cos_sq]; ring
  have hsin : Real.sin ε≤11/50 := by
    exact ((le_abs_self _).trans
      (Real.abs_sin_le_abs.trans_eq (abs_of_nonneg he.1))).trans he.2
  have hcos : (4879/5000 : ℝ)≤Real.cos ε := by
    have hh := Real.one_sub_sq_div_two_le_cos (x := ε)
    nlinarith [he.1,he.2]
  have hV : V=aH-1/2-Real.sin ε-L := by
    rw [hL]
    dsimp [V,X,Y]
    ring
  have hVlow : 123/1000<V := by linarith
  have hnorm : U^2+V^2≤qCap := hrot.trans_le hcircle
  by_contra! hbad
  have hU : (19753/10000 : ℝ)≤U := by
    have heq : U=(E.a-1/2)*Real.cos ε+(1/2-E.y)*Real.sin ε+Real.cos ε := by
      dsimp [U,X,Y]
      ring
    rw [heq]
    linarith
  dsimp [qCap] at hnorm
  nlinarith

theorem Source.highMixedDerivative_negative {q t e x : ℝ} {H G A E : SignedPoint}
    (I : Source q t H G A) (hq : q≤qCap)
    (hEc : E.Contained q) (hEy : E.y≤0)
    (hx : x∈Ioc 0 t)
    (hnot : ¬quarterFeasible (point (A.a-1/2) x) A (-x) 0)
    (he : e+x∈Icc 0 (11/50 : ℝ))
    (hsmall : highMixedSlack H.circle (A.a-1/2) e E x≤1/1000) :
    highMixedDerivative H.circle (A.a-1/2) e E x< -(1/2000) := by
  let J := I.atAngle hq hx hnot
  have hj := J.cuts hq
  have hgeom := I.path_geometry hq ⟨hx.1.le,hx.2⟩
  have hD := I.path_cap hq ⟨hx.1.le,hx.2⟩
  have hR : intrinsic (value (A.a-1/2) x) x<qCap := by
    have hh := hj.2.2.2.2.2.2.1.trans_le hq
    simpa [point] using hh
  have hgain : 1<primaryGain H.circle (A.a-1/2) x :=
    circle_primary_gain ⟨hD.1,hD.2.1.le⟩
      ⟨hx.1.le,hx.2.trans I.tilt_cap⟩ hR (I.H_contained.trans hq)
      hgeom.2.2.2.2.2.2
  have hHa : 211/250<(movingAnchor H.circle (A.a-1/2) x).a := by
    have hsort := J.H_sorted.2
    rw [abs_of_nonneg J.H_nonneg] at hsort
    exact hj.2.2.2.1.trans_le hsort
  have hU := short_high_mixed_rate (hEc.trans hq) hEy hHa he rfl hsmall
  unfold highMixedDerivative
  linarith

end AlignedNegative
end SquaresInCircles.Eight
end
end
end

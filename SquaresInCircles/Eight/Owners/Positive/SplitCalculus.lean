module

public import SquaresInCircles.Eight.Owners.CircleGeometry
public import SquaresInCircles.Eight.Owners.Positive.SplitComparison
public import SquaresInCircles.Eight.Owners.TrigonometricReserves
public import SquaresInCircles.Eight.Words.Zero.TangentPrimary

/-!
# Eight squares: calculus of a positive tilted primary and its outer anchor

The derivatives of the norm `norm r k η t` and of the split function `g` (`norm_hasDerivAt`,
`g_hasDerivAt`, `gDeriv_hasDerivAt`). The negative square term of the second derivative is kept
until the final upper estimate (`gSecond_le`); this is the continuous calculation behind the split
of the core-E stress.
-/

section
/-!
## Complete nonnegative-error primary-pair endpoints

The only remaining local exception is an actual positive
nearest-axis tie. The later global word theorem supplies its exclusion.
The zero-tangent join has already been eliminated by an actual same-radius
BT alignment with strict TD slack. There is no root search or interval grid.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
namespace PairedPrimary

structure Endpoint (q B D t : ℝ) where
  point : SignedPoint
  firstError : ℝ
  first_mem : firstError∈Icc 0 t
  sorted : point.Sorted
  outer : point.Outer q
  avoids_core : point.AvoidsCore
  first_feasible : edgeWidth firstError≤
    B+point.a*Real.sin firstError-point.y*Real.cos firstError
  second_feasible : edgeWidth (t-firstError)≤
    point.a*Real.sin (t-firstError)+point.y*Real.cos (t-firstError)+D
  endpoint : firstError=0 ∨ firstError=t ∨ point.y=point.a

/-- The original pair has arbitrary signed tangent and radial kind. Only
its two actual weak inequalities and squared containment are used. -/
theorem nonnegative_pair_endpoint {q B D u v : ℝ} {p : SignedPoint}
    (hqL : qLow≤q) (hqU : q≤qCap)
    (hB : diagonalCoordinate q≤B ∧ B≤axisCoordinate q)
    (hD : D≤diagonalCoordinate q)
    (hu : 0≤u) (hv : 0≤v) (ht0 : 0<u+v) (ht : u+v≤7/10)
    (hs : p.Sorted) (hc : p.Contained q)
    (h₁ : edgeWidth u≤B+p.a*Real.sin u-p.y*Real.cos u)
    (h₂ : edgeWidth v≤p.a*Real.sin v+p.y*Real.cos v+D) :
    Nonempty (Endpoint q B D (u+v)) := by
  obtain ⟨hyp,hcp,hdp⟩ := outerization_preserves_pair hqL hs hc
    ⟨hu,by linarith⟩ ⟨hv,by linarith⟩ h₁ h₂
  obtain ⟨u',y,hu',hy,hf,hg,hcases,hcontact⟩ := intrinsic_endpoint
    hqL hqU hB ⟨ht0,ht⟩ ⟨hu,by linarith⟩ hyp hcp hdp
  obtain ⟨hps,hpo,hpc⟩ := SignedPoint.outerAt_spec hqL hy
  have hfirst : edgeWidth u'≤B+(arc q y).a*Real.sin u'-y*Real.cos u' := by
    dsimp [contact] at hf
    linarith
  have hsecond : edgeWidth (u+v-u')≤
      (arc q y).a*Real.sin (u+v-u')+y*Real.cos (u+v-u')+D := by
    dsimp [required] at hg
    linarith
  by_cases he0 : u'=0
  · exact ⟨⟨arc q y,u',hu',hps,hpo,hpc,hfirst,hsecond,Or.inl he0⟩⟩
  by_cases het : u'=u+v
  · exact ⟨⟨arc q y,u',hu',hps,hpo,hpc,hfirst,hsecond,Or.inr (Or.inl het)⟩⟩
  rcases hcases with h | h | h | h
  · exact (he0 h).elim
  · exact (het h).elim
  · subst y
    have hu0 : 0<u' := lt_of_le_of_ne hu'.1 (Ne.symm he0)
    have hv0 : 0<u+v-u' := by
      have hlt := lt_of_le_of_ne hu'.2 het
      linarith
    have hc0 : contact q B u' 0=0 := by
      rcases hcontact with hh | hh
      · have hd := (uniform_circle_reserves hqL hqU).1
        linarith
      · exact hh
    have hr := zero_tangent_alignment hqL hqU hB.1 hD hu0 hv0
      (by linarith) hc0 (by simpa using hg)
    obtain ⟨hss,hoo,hcc,hyy,hbt,htd⟩ := hr
    refine ⟨⟨arc q (B-1),0,⟨le_rfl,ht0.le⟩,hss,hoo,hcc,?_,?_,Or.inl rfl⟩⟩
    · simpa using hbt.ge
    · simpa using htd.le
  · have ha := (arc_diagonal hqL).1
    refine ⟨⟨arc q y,u',hu',hps,hpo,hpc,hfirst,hsecond,Or.inr (Or.inr ?_)⟩⟩
    simpa [h,arc,SignedPoint.outerAt] using ha.symm

end PairedPrimary
end SquaresInCircles.Eight
end
end
end

section
/-!
## Positive GA1 with nonpositive HG0/GA1 total

The half-angle polynomial is one identity on the whole allowed domain.
The curved-core alternative is kept separate and has a uniform reserve.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight

private theorem half_angle_polynomial_reserve {t w : ℝ}
    (ht : 0≤t ∧ t<1/2) (_hw : 0≤w)
    (hcone : w*(1+2*t-t^2)≤1-2*t-t^2) :
    1/4 < 1-t-w*((13/12)*t+1/2) := by
  let den := 1+2*t-t^2
  let num := 1-2*t-t^2
  have ht2 : t^2≤t/2 := by nlinarith [mul_nonneg ht.1 (by linarith : 0≤1/2-t)]
  have ht3 : 0≤t^3 := pow_nonneg ht.1 _
  have hden0 : 0<den := by dsimp [den]; nlinarith
  have hden2 : den<2 := by dsimp [den]; nlinarith [sq_nonneg t]
  have hcoef : 0≤(13/12)*t+1/2 := by linarith
  have hmul := mul_le_mul_of_nonneg_right hcone hcoef
  have hid : (1-t)*den-((13/12)*t+1/2)*num =
      1/2+(11/12)*t-t^2/3+(25/12)*t^3 := by dsimp [den,num]; ring
  have hpoly : 1/2≤1/2+(11/12)*t-t^2/3+(25/12)*t^3 := by nlinarith
  have hbound : 1/2 ≤ den*(1-t-w*((13/12)*t+1/2)) := by
    dsimp [den,num] at hid ⊢
    nlinarith
  by_contra! h
  have hm := mul_le_mul_of_nonneg_left h hden0.le
  nlinarith

private theorem sum_angle_half_tangent {x s : ℝ}
    (hx : 0<x) (hs : 0≤ s) (htotal : s+x≤7/10) :
    let t := Real.sin x/(1+Real.cos x)
    let w := Real.sin s/Real.cos s
    0≤t ∧ t<1/2 ∧ 0≤w ∧ w*(1+2*t-t^2)≤1-2*t-t^2 := by
  dsimp only
  have hxrange : x∈Icc 0 (7/10 : ℝ) := ⟨hx.le,by linarith⟩
  have hsrange : s∈Icc 0 (7/10 : ℝ) := ⟨hs,by linarith⟩
  obtain ⟨hc,hc1,hsx0,hsx,hsc⟩ := transport_trig hxrange
  obtain ⟨hC,hC1,hSs0,hSs,hSC⟩ := transport_trig hsrange
  obtain ⟨hcc,hcc1,hss0,hss,hcombined⟩ := transport_trig
    (show s+x∈Icc 0 (7/10 : ℝ) by constructor <;> linarith)
  have hcx : 0<1+Real.cos x := by linarith
  have hcs : 0<Real.cos s := by linarith
  refine ⟨div_nonneg hsx0 hcx.le,?_,div_nonneg hSs0 hcs.le,?_⟩
  · rw [div_lt_iff₀ hcx]
    linarith
  · rw [Real.sin_add,Real.cos_add] at hcombined
    apply le_of_lt
    field_simp [hcx.ne',hcs.ne']
    have hu := Real.sin_sq_add_cos_sq x
    have hmul := mul_pos (by linarith : 0<
      Real.cos s*Real.cos x-Real.sin s*Real.sin x-
      (Real.sin s*Real.cos x+Real.cos s*Real.sin x)) hcx
    nlinarith

/-- One full-domain lower bound for the flat-or-outer branch. -/
theorem positive_primary_flat_reserve {a g x s : ℝ}
    (ha : 7/12≤a) (hg : 0≤g)
    (hx : 0<x) (hs : 0≤ s) (htotal : s+x≤7/10) :
    0 < Real.cos s*(Real.sin x+Real.cos x-1)+
      Real.sin s*((a+1/2)*Real.cos x+(g-1/2)*Real.sin x-13/12) := by
  let t := Real.sin x/(1+Real.cos x)
  let w := Real.sin s/Real.cos s
  obtain ⟨ht0,ht,hw,hcone⟩ := sum_angle_half_tangent hx hs htotal
  have hbracket := half_angle_polynomial_reserve ⟨ht0,ht⟩ hw hcone
  have hxrange : x∈Icc 0 (7/10 : ℝ) := ⟨hx.le,by linarith⟩
  have hsrange : s∈Icc 0 (7/10 : ℝ) := ⟨hs,by linarith⟩
  obtain ⟨hc,hsx0,hsx⟩ := transport_trig_coarse hxrange
  obtain ⟨hC,hS0,hS⟩ := transport_trig_coarse hsrange
  have hsxp : 0<Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx
    (by linarith [hxrange.2,Real.pi_gt_three])
  have hcx : 0<1+Real.cos x := by linarith
  have hCs : 0<Real.cos s := by linarith
  have hhalf : 1-Real.cos x=Real.sin x*t := by
    dsimp [t]
    field_simp [hcx.ne']
    nlinarith [Real.sin_sq_add_cos_sq x]
  have hwc : w*Real.cos s=Real.sin s := by dsimp [w]; field_simp [hCs.ne']
  have hid :
      Real.cos s*(Real.sin x+Real.cos x-1)+
        Real.sin s*((13/12)*Real.cos x-(1/2)*Real.sin x-13/12) =
      Real.sin x*Real.cos s*(1-t-w*((13/12)*t+1/2)) := by
    nlinarith [congrArg (fun u : ℝ => Real.cos s*u) hhalf,
      congrArg (fun u : ℝ => (13/12)*Real.sin s*u) hhalf]
  have hpositive : 0 < Real.sin x*Real.cos s*(1-t-w*((13/12)*t+1/2)) := by
    apply mul_pos (mul_pos hsxp hCs)
    exact lt_trans (by norm_num) hbracket
  have hnonneg1 := mul_nonneg
    (mul_nonneg (show 0≤a-7/12 by linarith) (by linarith : 0≤Real.cos x)) hS0
  have hnonneg2 := mul_nonneg (mul_nonneg hg hsx0) hS0
  linarith

/-- The rounded-core branch has a fixed positive reserve. -/
theorem positive_primary_curved_reserve {a g x s : ℝ}
    (ha : 447/800<a) (hg : 1/2<g)
    (hx : 1/4<x) (hs : 0≤ s) (htotal : s+x≤7/10) :
    3/50 < Real.cos s*(Real.sin x+Real.cos x-1)+
      Real.sin s*((a+1/2)*Real.cos x+(g-1/2)*Real.sin x-13/12) := by
  have hxrange : x∈Icc 0 (7/10 : ℝ) := ⟨by linarith,by linarith⟩
  have hsrange : s∈Icc 0 (9/20 : ℝ) := ⟨hs,by linarith⟩
  obtain ⟨hc,hc1,hsx0,hsx,hsc⟩ := transport_trig hxrange
  have hCs : 89/100<Real.cos s := by
    have hb := Real.one_sub_sq_div_two_le_cos (x := s)
    have hs2 := pow_le_pow_left₀ hs hsrange.2 2
    nlinarith
  have hSs0 := Real.sin_nonneg_of_nonneg_of_le_pi hs
    (by linarith [hsrange.2,Real.pi_gt_three])
  have hSs : Real.sin s≤9/20 :=
    (le_abs_self _).trans (Real.abs_sin_le_abs.trans (by
      rw [abs_of_nonneg hs]; exact hsrange.2))
  have hmon := cos_add_sin_mono (x := (1/4 : ℝ)) (y := x)
    (by norm_num) hx.le (by linarith [hxrange.2,Real.pi_gt_three])
  have hcquarter := Real.one_sub_sq_div_two_le_cos (x := (1/4 : ℝ))
  have hsquarter := Real.sin_ge_sub_cube (show (0:ℝ)≤1/4 by norm_num)
  have hsum : 21/100<Real.sin x+Real.cos x-1 := by nlinarith
  have hcoefficient : -(11/40 : ℝ)<(a+1/2)*Real.cos x-13/12 := by
    have hm := mul_nonneg (show 0≤a-447/800 by linarith) (by linarith : 0≤Real.cos x)
    nlinarith
  have hpositive1 := mul_pos (sub_pos.mpr hCs) (sub_pos.mpr hsum)
  have hbound1 : (89/100 : ℝ)*(21/100)<Real.cos s*(Real.sin x+Real.cos x-1) := by
    nlinarith
  have hbound2 : -(11/40 : ℝ)*(9/20)≤Real.sin s*((a+1/2)*Real.cos x-13/12) := by
    have hm := mul_nonneg hSs0 (show 0≤(a+1/2)*Real.cos x-13/12+11/40 by linarith)
    linarith
  have hnonneg := mul_nonneg hSs0
    (mul_nonneg (sub_nonneg.mpr hg.le) hsx0)
  nlinarith

/-- Explicit original-radius hard endpoint. The strict loss is at G, not
at a rigid anchor, and therefore is not itself an equality contradiction. -/
theorem positive_ga1_nonpositive_total_transport
    {q x s : ℝ} {H G A : SignedPoint}
    (hq : q≤qCap)
    (hHs : H.Sorted) (hGs : G.Sorted) (hAs : A.Sorted)
    (hHc : H.Contained q) (hGc : G.Contained q) (hAc : A.Contained q)
    (hHcore : H.AvoidsCore) (hGcore : G.AvoidsCore) (hAcore : A.AvoidsCore)
    (_hHy : 0≤H.y) (hGy : G.y≤0) (_hAy : 0≤A.y)
    (hx : 0<x) (hs : 0≤ s) (htotal : s+x≤7/10)
    (hHG : zeroFeasible H G (-(s+x)) 0)
    (hGA : quarterFeasible G A x 1) :
    let G' := SignedPoint.flat (-(A.a-1))
    G'.Sorted ∧ G'.Core ∧ G'.AvoidsCore ∧ G'.circle<q ∧
      quarterFeasible G' A 0 0 ∧ quarterFeasible G' A 0 1 ∧
      edgeWidth (-s)<zeroProjection H G' (-s) 0 := by
  dsimp only
  have hg : 0≤-G.y := by linarith
  have hxrange : x∈Icc 0 (7/10 : ℝ) := ⟨hx.le,by linarith⟩
  have hsrange : s∈Icc 0 (7/10 : ℝ) := ⟨hs,by linarith⟩
  have htxrange : s+x∈Icc 0 (7/10 : ℝ) := ⟨by linarith,htotal⟩
  obtain ⟨hc,hsx0,hsx⟩ := transport_trig_coarse hxrange
  obtain ⟨hC,hSs0,hSs⟩ := transport_trig_coarse hsrange
  have hcospos : 0<Real.cos s := by linarith
  have hHG' : edgeWidth (s+x)≤H.y-G.a*Real.sin (s+x)-G.y*Real.cos (s+x) := by
    have h := hHG
    simp only [zeroFeasible,zeroProjection,Matrix.cons_val_zero,Real.sin_neg,Real.cos_neg,
      edgeWidth_neg] at h
    linarith
  have hGA' : edgeWidth x≤A.a+G.a*Real.sin x+G.y*Real.cos x := by
    have h := hGA
    simp only [quarterFeasible,quarterProjection,Matrix.cons_val_one,Matrix.cons_val_zero] at h
    linarith
  have hsin := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [hx,Real.pi_pos]) (by linarith [htotal,Real.pi_gt_three])
    (show x≤s+x by linarith)
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi hx.le
    (by linarith [htotal,Real.pi_gt_three]) (show x≤s+x by linarith)
  have hprod1 := mul_nonneg hGs.1.le (sub_nonneg.mpr hsin)
  have hprod2 := mul_nonneg hg (sub_nonneg.mpr hcos)
  have hsum : 2≤H.y+A.a := by
    linarith [edgeWidth_ge_one x,edgeWidth_ge_one (s+x)]
  obtain ⟨hHl,hHu,hHybound⟩ := SignedPoint.coordinate_bounds hHs hHcore hHc hq
  obtain ⟨hAl,hAu,hAybound⟩ := SignedPoint.coordinate_bounds hAs hAcore hAc hq
  obtain ⟨hGl,hGu,hGybound⟩ := SignedPoint.coordinate_bounds hGs hGcore hGc hq
  have haA : 11/10<A.a := by
    have hHupper := (le_abs_self H.y).trans_lt hHybound
    linarith
  have htangent : |-(A.a-1)|≤1/2 := by
    rw [abs_neg,abs_of_nonneg (by linarith : 0≤A.a-1)]
    linarith
  have hsG := SignedPoint.flat_sorted htangent
  have hcG := SignedPoint.flat_on_core htangent
  have hinside : (SignedPoint.flat (-(A.a-1))).circle<q := by
    have hA : (A.a+1/2)^2+(|A.y|+1/2)^2≤q := hAc
    have hAy0 := abs_nonneg A.y
    have habs : |(-(A.a-1))|=A.a-1 := by
      rw [abs_neg,abs_of_nonneg (by linarith : 0≤A.a-1)]
    show (7/12+1/2)^2+(|(-(A.a-1))|+1/2)^2<q
    rw [habs]
    linarith [sq_nonneg |A.y|]
  have hhard0 : quarterFeasible (SignedPoint.flat (-(A.a-1))) A 0 0 := by
    show edgeWidth 0≤quarterProjection (SignedPoint.flat (-(A.a-1))) A 0 0
    simp only [quarterProjection,SignedPoint.flat,Matrix.cons_val_zero,Real.cos_zero,
      Real.sin_zero,edgeWidth_zero]
    linarith
  have hhard1 := (quarter_low_tie _ _).1 hhard0
  have hweighted : edgeWidth (s+x)+edgeWidth x*Real.cos s+
      (G.a*Real.cos x+(-G.y)*Real.sin x)*Real.sin s≤H.y+A.a*Real.cos s := by
    have hm := mul_le_mul_of_nonneg_right hGA' hcospos.le
    rw [Real.sin_add,Real.cos_add] at hHG'
    linarith
  have hslack :
      Real.cos s*(Real.sin x+Real.cos x-1)+
        Real.sin s*((G.a+1/2)*Real.cos x+(-G.y-1/2)*Real.sin x-13/12) ≤
      H.y-(7/12)*Real.sin s+(A.a-1)*Real.cos s-edgeWidth s := by
    rw [edgeWidth_positive_formula htxrange,edgeWidth_positive_formula hxrange,
      Real.sin_add,Real.cos_add] at hweighted
    rw [edgeWidth_positive_formula hsrange]
    linarith
  have hpositive : 0<
      Real.cos s*(Real.sin x+Real.cos x-1)+
        Real.sin s*((G.a+1/2)*Real.cos x+(-G.y-1/2)*Real.sin x-13/12) := by
    by_cases ha : 7/12≤G.a
    · exact positive_primary_flat_reserve ha hg hx hs htotal
    · have hag : G.a<7/12 := lt_of_not_ge ha
      have hGhalf := SignedPoint.primary_gt_half hGs hGcore
      have hgbig : 1/2< -G.y := by
        by_contra! h
        have hnear := hGcore
        unfold SignedPoint.AvoidsCore SignedPoint.coreDistance at hnear
        rw [max_eq_left (by linarith : 0≤G.a-1/2),
          max_eq_right (by rw [abs_of_nonpos hGy]; linarith : |G.y|-1/2≤0)] at hnear
        linarith [mul_pos (sub_pos.mpr hGhalf) (sub_pos.mpr hag)]
      have hxquarter : 1/4<x := by
        by_contra! h
        have hcx := Real.one_sub_sq_div_two_le_cos (x := x)
        have hsxbound : Real.sin x≤1/4 := (Real.sin_lt hx).le.trans h
        have hx2 := pow_le_pow_left₀ hx.le h 2
        rw [edgeWidth_positive_formula hxrange] at hGA'
        have hprod := mul_pos (sub_pos.mpr hgbig) (show 0<Real.cos x by linarith)
        have hprod' := mul_nonneg (show 0≤7/12-G.a by linarith) hsx0
        linarith
      exact lt_trans (by norm_num : (0:ℝ)<3/50)
        (positive_primary_curved_reserve hGl hgbig hxquarter hs htotal)
  refine ⟨hsG,hcG,hcG.ge,hinside,hhard0,hhard1,?_⟩
  simp only [zeroProjection,SignedPoint.flat,Matrix.cons_val_zero,Real.sin_neg,Real.cos_neg,
    edgeWidth_neg]
  linarith

end SquaresInCircles.Eight
end
end
end

section
@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.PositiveSplitCalculus
open PositivePrimaryBaselines

def f (η t : ℝ) : ℝ := Real.cos t+η*Real.sin t
def df (η t : ℝ) : ℝ := -Real.sin t+η*Real.cos t
def beta (R η : ℝ) : ℝ := 1+2*η-R*Real.sqrt (1+η^2)
def radicand (r k η t : ℝ) : ℝ := r^2+(k*f η t)^2
def norm (r k η t : ℝ) : ℝ := Real.sqrt (radicand r k η t)
def normDeriv (r k η t : ℝ) : ℝ := (k*f η t)*(k*df η t)/norm r k η t
def normSecond (r k η t : ℝ) : ℝ :=
  r^2*(k*df η t)^2/(norm r k η t)^3-(k*f η t)^2/norm r k η t

def g (R r k η t : ℝ) : ℝ :=
  k*primaryCoefficient R η t-R*norm r k η t

def gDeriv (R r k η t : ℝ) : ℝ :=
  k*(-2*Real.sin t+beta R η*Real.cos t)-R*normDeriv r k η t

def gSecond (R r k η t : ℝ) : ℝ :=
  k*(-2*Real.cos t-beta R η*Real.sin t)-R*normSecond r k η t

theorem f_hasDerivAt (η t : ℝ) : HasDerivAt (f η) (df η t) t := by
  exact (Real.hasDerivAt_cos t).fun_add ((Real.hasDerivAt_sin t).const_mul η)

theorem df_hasDerivAt (η t : ℝ) : HasDerivAt (df η) (-f η t) t := by
  refine ((Real.hasDerivAt_sin t).fun_neg.fun_add
    ((Real.hasDerivAt_cos t).const_mul η)).congr_deriv ?_
  simp only [f]
  ring

theorem f_energy (η t : ℝ) : (f η t)^2+(df η t)^2=1+η^2 := by
  dsimp [f,df]
  linear_combination (1+η^2)*(Real.sin_sq_add_cos_sq t)

theorem radicand_pos {r : ℝ} (hr : 0<r) (k η t : ℝ) :
    0<radicand r k η t := by unfold radicand; positivity

theorem norm_pos {r : ℝ} (hr : 0<r) (k η t : ℝ) : 0<norm r k η t :=
  Real.sqrt_pos.mpr (radicand_pos hr k η t)

theorem norm_sq {r : ℝ} (hr : 0<r) (k η t : ℝ) :
    (norm r k η t)^2=radicand r k η t := Real.sq_sqrt (radicand_pos hr k η t).le

theorem norm_hasDerivAt {r : ℝ} (hr : 0<r) (k η t : ℝ) :
    HasDerivAt (norm r k η) (normDeriv r k η t) t := by
  have h := ((hasDerivAt_const t (r^2)).add
    (((f_hasDerivAt η t).const_mul k).pow 2)).sqrt (radicand_pos hr k η t).ne'
  convert h using 1
  · rfl
  · dsimp [normDeriv,norm,radicand]
    ring

private theorem quotient_second_identity {r m v L : ℝ}
    (hL : L≠0) (hLsq : L^2=r^2+m^2) :
    ((v^2-m^2)*L-m*v*(m*v/L))/L^2=r^2*v^2/L^3-m^2/L := by
  field_simp [hL]
  nlinarith [congrArg (fun z : ℝ => v^2*z) hLsq]

theorem normDeriv_hasDerivAt {r : ℝ} (hr : 0<r) (k η t : ℝ) :
    HasDerivAt (normDeriv r k η) (normSecond r k η t) t := by
  have hN := norm_pos hr k η t
  have hnum := ((f_hasDerivAt η t).const_mul k).fun_mul ((df_hasDerivAt η t).const_mul k)
  have h := hnum.fun_div (norm_hasDerivAt hr k η t) hN.ne'
  have hid := quotient_second_identity (v := k*df η t) hN.ne' (norm_sq hr k η t)
  refine h.congr_deriv ?_
  have e : normSecond r k η t=(((k*df η t)^2-(k*f η t)^2)*norm r k η t-
      (k*f η t)*(k*df η t)*((k*f η t)*(k*df η t)/norm r k η t))/(norm r k η t)^2 :=
    hid.symm
  rw [e]
  simp only [normDeriv]
  ring

theorem g_hasDerivAt {r : ℝ} (hr : 0<r) (R k η t : ℝ) :
    HasDerivAt (g R r k η) (gDeriv R r k η t) t := by
  have hc := ((hasDerivAt_const t (1:ℝ)).fun_add
    ((Real.hasDerivAt_cos t).const_mul 2)).fun_add
    ((Real.hasDerivAt_sin t).const_mul (beta R η))
  refine ((hc.const_mul k).fun_sub ((norm_hasDerivAt hr k η t).const_mul R)).congr_deriv ?_
  simp only [gDeriv]
  ring

theorem gDeriv_hasDerivAt {r : ℝ} (hr : 0<r) (R k η t : ℝ) :
    HasDerivAt (gDeriv R r k η) (gSecond R r k η t) t := by
  have hc := ((Real.hasDerivAt_sin t).const_mul (-2)).fun_add
    ((Real.hasDerivAt_cos t).const_mul (beta R η))
  refine ((hc.const_mul k).fun_sub
    ((normDeriv_hasDerivAt hr k η t).const_mul R)).congr_deriv ?_
  simp only [gSecond]
  ring

/-- An upper bound for the second derivative of `g`; the only term dropped is a nonnegative
square. -/
theorem gSecond_le {R r k η t a c : ℝ}
    (hR : 0≤R) (hr : 0<r) (hk : 0≤k) (hη : 0≤η)
    (hcos : 0≤Real.cos t) (hsin : 0≤Real.sin t)
    (hratio : R*(k*f η t)/norm r k η t≤a)
    (hbeta : R*Real.sqrt (1+η^2)-1+(a-2)*η≤c) :
    gSecond R r k η t≤k*((a-2)*Real.cos t+c*Real.sin t) := by
  have hN := norm_pos hr k η t
  have hf : 0≤f η t := add_nonneg hcos (mul_nonneg hη hsin)
  have hm := mul_nonneg hk hf
  have hsupport := mul_le_mul_of_nonneg_right hratio hm
  have hcoef := mul_le_mul_of_nonneg_left hbeta (mul_nonneg hk hsin)
  have hterm : 0≤R*(r^2*(k*df η t)^2/(norm r k η t)^3) := by positivity
  have hid : R*((k*f η t)^2/norm r k η t)=
      (R*(k*f η t)/norm r k η t)*(k*f η t) := by ring
  unfold gSecond normSecond
  simp only [mul_sub]
  rw [hid]
  dsimp [f,beta] at *
  nlinarith

end SquaresInCircles.Eight.PositiveSplitCalculus
end
end
end

module

public import SquaresInCircles.Eight.TableFree.NegativeNoncancelingOuter
public import SquaresInCircles.Eight.TableFree.EZeroCapEndpoints

/-!
# Deleting a negative outer error from the original E-zero cap

Uncompiled draft.  The large middle tangent keeps its original circle
and coordinates.  The negative core composite is compared with the
actual radical E-zero cap.  Its strictly larger initial slope and the
strict curvature gap delete the outer error from the E angle.  The only
cut is the intrinsic crossing of that radical with the diagonal cap.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.NegativeOuterEZero
open PositiveCancelingOuter EZeroFunctions EZeroCapped

def demand (C r : ℝ) : ℝ := 1/2+C*Real.cos r+(13/12)*Real.sin r
def demandD (C r : ℝ) : ℝ := (13/12)*Real.cos r-C*Real.sin r

theorem demand_hasDerivAt (C r : ℝ) : HasDerivAt (demand C) (demandD C r) r := by
  convert (((Real.hasDerivAt_cos r).const_mul C).const_add (1/2)).add
    ((Real.hasDerivAt_sin r).const_mul (13/12)) using 1
  · rfl
  · dsimp [demandD]
    ring

theorem demandD_hasDerivAt (C r : ℝ) :
    HasDerivAt (demandD C) (-(demand C r-1/2)) r := by
  convert ((Real.hasDerivAt_cos r).const_mul (13/12)).sub
    ((Real.hasDerivAt_sin r).const_mul C) using 1
  · rfl
  · dsimp [demand]
    ring

theorem demandD_lower {C r : ℝ} (hC : C∈Ioo (0:ℝ) (8/15))
    (hr : r∈Icc 0 (7/10 : ℝ)) : (1/3 : ℝ)<demandD C r := by
  obtain ⟨hc,hs0,hs⟩ := transport_trig_coarse hr
  have hprod := mul_le_mul hC.2.le hs.le hs0 (by norm_num : (0:ℝ)≤8/15)
  dsimp [demandD]
  linarith

theorem demand_growth {C x y : ℝ} (hC : C∈Ioo (0:ℝ) (8/15))
    (hx : x∈Icc 0 (7/10 : ℝ)) (hy : y∈Icc 0 (7/10 : ℝ)) (hxy : x≤y) :
    (y-x)/3≤demand C y-demand C x := by
  have hh := derivative_reserve
    (f := demand C) (df := demandD C) (l := 0) (u := (7/10 : ℝ)) (k := 1/3)
    (fun r _ => (demand_hasDerivAt C r).continuousAt.continuousWithinAt)
    (fun r _ => demand_hasDerivAt C r)
    (fun r hr => (demandD_lower hC (Ioo_subset_Icc_self hr)).le)
    hx hy hxy
  linarith

theorem demand_monotone {C : ℝ} (hC : C∈Ioo (0:ℝ) (8/15)) :
    MonotoneOn (demand C) (Icc 0 (7/10 : ℝ)) := by
  intro x hx y hy hxy
  have hh := demand_growth hC hx hy hxy
  linarith

theorem endpoint_strictMono : StrictMonoOn h (Icc 0 (7/10 : ℝ)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 (7/10 : ℝ))
  · exact fun x hx => (h_hasDerivAt hx).continuousAt.continuousWithinAt
  · intro x hx
    have hx' := interior_subset hx
    rw [(h_hasDerivAt hx').deriv]
    exact hd_pos hx'

theorem endpoint_zero_upper : h 0<(791/1000 : ℝ) := by
  have hr := rho_sq (show (0:ℝ)∈Icc 0 (7/10) by norm_num)
  have hp := rho_pos (show (0:ℝ)∈Icc 0 (7/10) by norm_num)
  norm_num [u,qCap] at hr
  dsimp [h]
  nlinarith

/-- The actual large-tangent A circle places the initial H demand
strictly above the E cap at zero. -/
theorem initial_demand_lower {A : SignedPoint} {t : ℝ}
    (hAa : 1/2<A.a) (hAy : 1/2≤A.y) (hAc : A.Contained qCap)
    (ht : t∈Icc 0 (7/10 : ℝ)) :
    (73/250 : ℝ)<1-V A t ∧ h 0<1/2+(1-V A t) := by
  have hc := hAc
  rw [SignedPoint.Contained,SignedPoint.circle,
    abs_of_nonneg (show 0≤A.y by linarith)] at hc
  have hysq := pow_le_pow_left₀ (show (0:ℝ)≤1 by norm_num)
    (show 1≤A.y+1/2 by linarith) 2
  have hAu : A.a<151/125 := by
    dsimp [qCap] at hc
    nlinarith
  have hV := V_upper hAa (by linarith) ht
  have hzero := endpoint_zero_upper
  constructor <;> linarith

/-- A positive lower bound for the difference from the shifted radical.
The second derivative is positive throughout the complete comparison
interval, so the initial slope reserve persists. -/
theorem comparison_reserve {C z l : ℝ} (hC : C∈Ioo (0:ℝ) (8/15))
    (hz : z∈Icc 0 (11/100 : ℝ)) (hl : l∈Icc 0 (7/10 : ℝ))
    (hzl : z+l≤11/100) (hinit : h z=1/2+C)
    (hupper : demand C l<9/10) :
    l/50≤demand C l-h (z+l) := by
  let f (r : ℝ) := demand C r-h (z+r)
  let df (r : ℝ) := demandD C r-hd (z+r)
  have hdom (r : ℝ) (hr : r∈Icc 0 l) : z+r∈Icc 0 (11/100 : ℝ) :=
    ⟨by linarith [hz.1,hr.1],by linarith [hr.2]⟩
  have hwide (r : ℝ) (hr : r∈Icc 0 l) : z+r∈Icc 0 (7/10 : ℝ) :=
    ⟨(hdom r hr).1,by linarith [(hdom r hr).2]⟩
  have hfd (r : ℝ) (hr : r∈Icc 0 l) : HasDerivAt f (df r) r := by
    have hh := (h_hasDerivAt (hwide r hr)).comp r ((hasDerivAt_id r).const_add z)
    simpa [f,df] using (demand_hasDerivAt C r).sub hh
  have hfdd (r : ℝ) (hr : r∈Icc 0 l) :
      HasDerivAt df (-(demand C r-1/2)-hdd (z+r)) r := by
    have hh := (hd_hasDerivAt (hwide r hr)).comp r ((hasDerivAt_id r).const_add z)
    simpa [df] using (demandD_hasDerivAt C r).sub hh
  have hdm : MonotoneOn df (Icc 0 l) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun r hr => (hfdd r hr).continuousAt.continuousWithinAt
    · exact fun r hr => hfdd r (Ioo_subset_Icc_self hr)
    · intro r hr
      have hr' := Ioo_subset_Icc_self hr
      have hrw : r∈Icc 0 (7/10 : ℝ) := ⟨hr'.1,hr'.2.trans hl.2⟩
      have hru := demand_monotone hC hrw hl hr'.2
      have hcurv := small_hdd (hdom r hr')
      linarith
  have hd0 : (1/50 : ℝ)<df 0 := by
    have hu := (small_hd hz).2
    simp only [df,demandD,Real.cos_zero,Real.sin_zero,mul_one,mul_zero,sub_zero,add_zero]
    linarith
  have hf0 : f 0=0 := by simp [f,demand,hinit]
  have hh := derivative_reserve
    (f := f) (df := df) (l := 0) (u := l) (k := 1/50)
    (fun r hr => (hfd r hr).continuousAt.continuousWithinAt)
    (fun r hr => hfd r (Ioo_subset_Icc_self hr))
    (by
      intro r hr
      have hm := hdm (show (0:ℝ)∈Icc 0 l from ⟨le_rfl,hl.1⟩)
        (Ioo_subset_Icc_self hr) hr.1.le
      linarith)
    (show (0:ℝ)∈Icc 0 l from ⟨le_rfl,hl.1⟩)
    (show l∈Icc 0 l from ⟨hl.1,le_rfl⟩) hl.1
  rw [hf0] at hh
  dsimp [f] at hh
  linarith

/-- Exact deletion for the original A coordinates.  At positive error
the E-angle deletion and the resulting original-A cap both have strict
room.  Neither a replacement A point nor a frontier-circle assumption
is introduced. -/
theorem large_error_deletion {A : SignedPoint} {t e ε : ℝ}
    (hAa : 1/2<A.a) (hAy : 1/2≤A.y) (hAc : A.Contained qCap)
    (ht : t∈Icc 0 (7/10 : ℝ)) (he : e∈Icc 0 (7/10 : ℝ))
    (hε : ε∈Icc 0 (7/10 : ℝ))
    (hsource : demand (1-V A t) e≤capped ε) :
    e≤ε ∧
      1+edgeWidth t≤capped (ε-e)+A.a*Real.cos t-A.y*Real.sin t ∧
      (0<e → e<ε ∧
        1+edgeWidth t<capped (ε-e)+A.a*Real.cos t-A.y*Real.sin t) := by
  let C := 1-V A t
  have hsource' : demand C e≤capped ε := hsource
  have hbase := initial_demand_lower hAa hAy hAc ht
  have hC0 : 0<C := by dsimp [C]; linarith [hbase.1]
  have hCtop : C<8/15 := by
    have hcap := capped_bounds hε
    obtain ⟨hc,hs0,hs⟩ := transport_trig_coarse he
    have hp := mul_le_mul_of_nonneg_left hc.le hC0.le
    dsimp [demand] at hsource'
    nlinarith
  have hC : C∈Ioo (0:ℝ) (8/15) := ⟨hC0,hCtop⟩
  have hidentity : (1/2+C)+A.a*Real.cos t-A.y*Real.sin t=1+edgeWidth t := by
    rw [edgeWidth_positive_formula ht]
    dsimp [C,V]
    ring
  rcases eq_or_lt_of_le he.1 with he0 | hepos
  · have heq : e=0 := he0.symm
    subst e
    have hh : 1/2+C≤capped ε := by simpa [demand] using hsource'
    refine ⟨hε.1,?_,?_⟩
    · simpa only [sub_zero] using (show 1+edgeWidth t≤capped ε+A.a*Real.cos t-A.y*Real.sin t by linarith)
    · intro hh
      linarith
  have hreqgrow := demand_growth hC (show (0:ℝ)∈Icc 0 (7/10) by norm_num) he he.1
  have hdemand0 : demand C 0=1/2+C := by simp [demand]
  rw [hdemand0] at hreqgrow
  have hH0cap : 1/2+C<diagonalCoordinate qCap := by
    have hcap := min_le_left (diagonalCoordinate qCap) (h ε)
    change capped ε≤diagonalCoordinate qCap at hcap
    linarith
  obtain ⟨c,hc,hcross⟩ := crossing
  have hcc : c∈Icc 0 (7/10 : ℝ) := ⟨hc.1.le,by linarith [hc.2]⟩
  have hcont : ContinuousOn h (Icc 0 c) := fun z hz =>
    (h_hasDerivAt ⟨hz.1,hz.2.trans hcc.2⟩).continuousAt.continuousWithinAt
  have hbase' : h 0<1/2+C := hbase.2
  obtain ⟨z,hz,hinit⟩ := intermediate_value_Icc hc.1.le hcont
    (show 1/2+C∈Icc (h 0) (h c) by rw [hcross]; exact ⟨hbase'.le,hH0cap.le⟩)
  have hzpos : 0<z := by
    by_contra! hn
    have heq : z=0 := le_antisymm hn hz.1
    rw [heq] at hinit
    linarith
  have hzc : z<c := by
    by_contra! hn
    have heq : z=c := le_antisymm hz.2 hn
    rw [heq,hcross] at hinit
    linarith
  have hzsmall : z∈Icc 0 (11/100 : ℝ) := ⟨hz.1,hz.2.trans hc.2.le⟩
  have hreqcap : demand C e≤diagonalCoordinate qCap :=
    hsource'.trans (min_le_left _ _)
  have hreqtop : demand C e<9/10 := hreqcap.trans_lt diagonal_bounds.2
  have hecross : e<c-z := by
    by_contra! hn
    have hr : c-z∈Icc 0 (7/10 : ℝ) := ⟨by linarith,by linarith [hc.2]⟩
    have hreq := demand_monotone hC hr he hn
    have hgap := comparison_reserve hC hzsmall hr (by linarith [hc.2]) hinit
      (hreq.trans_lt hreqtop)
    rw [show z+(c-z)=c by ring,hcross] at hgap
    linarith
  have hgap := comparison_reserve hC hzsmall he (by linarith [hc.2]) hinit hreqtop
  have hεlower : z+e<ε := by
    by_contra! hn
    have hze : z+e∈Icc 0 (7/10 : ℝ) :=
      ⟨by linarith,by linarith [hc.2]⟩
    have hm := h_monotone hε hze hn
    have hcap : capped ε≤h ε := min_le_right _ _
    linarith
  have hdeleted : ε-e∈Icc 0 (7/10 : ℝ) :=
    ⟨by linarith,by linarith [hε.2]⟩
  have hstrict := endpoint_strictMono
    (show z∈Icc 0 (7/10 : ℝ) from ⟨hz.1,by linarith [hzsmall.2]⟩)
    hdeleted (by linarith : z<ε-e)
  have hcapstrict : 1/2+C<capped (ε-e) := by
    apply lt_min hH0cap
    rw [←hinit]
    exact hstrict
  refine ⟨by linarith,by linarith,?_⟩
  intro _
  exact ⟨by linarith,by linarith⟩

/-- The small middle tangent absorbs its outer error into the quarter
tilt at the same original H and A coordinates. -/
theorem small_error_absorption {H A : SignedPoint} {t e : ℝ}
    (hHy : H.y<9/10) (hAa : 1/2<A.a) (hAy : A.y∈Icc (0:ℝ) (1/2))
    (hAc : A.Contained qCap) (ht : 0≤t) (he : 0≤e) (hsum : t+e≤7/10)
    (hsource : demand (1-V A t) e≤H.y) :
    1+edgeWidth (t+e)+e/150≤
      H.y+A.a*Real.cos (t+e)-A.y*Real.sin (t+e) := by
  have hΘ : t+e∈Icc 0 (7/10 : ℝ) := ⟨add_nonneg ht he,hsum⟩
  have hf : 0≤NegativeNoncancelingBarrier.F H A (t+e) t := by
    dsimp [NegativeNoncancelingBarrier.F]
    rw [show t+e-t=e by ring]
    dsimp [demand] at hsource
    linarith
  have hh := HardCancelingOuter.feasible_right_reserve
    (f := NegativeNoncancelingBarrier.F H A (t+e))
    (df := NegativeNoncancelingBarrier.Fd A (t+e))
    (l := t) (u := t+e) (b := 0) (k := 1/150) (by linarith) (by norm_num)
    (fun z _ => NegativeNoncancelingBarrier.F_hasDerivAt H A (t+e) z)
    (by
      intro z hz hfeas
      exact (NegativeNoncancelingBarrier.rate_on_feasible hHy hAa hAy hAc
        ⟨ht.trans hz.1,hz.2⟩ hsum hfeas).le)
    hf (t+e) ⟨by linarith,le_rfl⟩
  have hreserve : e/150≤NegativeNoncancelingBarrier.F H A (t+e) (t+e) := by
    linarith [hh.2]
  simp only [NegativeNoncancelingBarrier.F,sub_self,Real.cos_zero,Real.sin_zero,
    mul_one,mul_zero,sub_zero] at hreserve
  rw [edgeWidth_positive_formula hΘ]
  dsimp [V] at hreserve
  linarith

/-- The two actual tangent regimes yield compatible cap data.  The
conserved difference records precisely which part of the outer error
was absorbed into the quarter tilt and which part was deleted from E.
The original A coordinates are used in either branch. -/
theorem side_cap {H A : SignedPoint} {t e ε : ℝ}
    (hHy : H.y<9/10) (hAa : 1/2<A.a) (hAy : 0≤A.y) (hAc : A.Contained qCap)
    (ht : 0≤t) (he : 0≤e) (hsum : t+e≤7/10) (hε : ε∈Icc 0 (7/10 : ℝ))
    (hsource : demand (1-V A t) e≤H.y) (hcap : H.y≤capped ε) :
    ∃τ ε', 0≤τ ∧ 0≤ε' ∧ τ≤t+e ∧ ε'≤ε ∧
      τ-ε'=t+e-ε ∧
      1+edgeWidth τ≤capped ε'+A.a*Real.cos τ-A.y*Real.sin τ := by
  by_cases hsmall : A.y≤1/2
  · have hh := small_error_absorption hHy hAa ⟨hAy,hsmall⟩ hAc ht he hsum hsource
    exact ⟨t+e,ε,add_nonneg ht he,hε.1,le_rfl,le_rfl,rfl,by linarith⟩
  · have hh := large_error_deletion hAa (le_of_not_ge hsmall) hAc
      ⟨ht,by linarith⟩ ⟨he,by linarith⟩ hε (hsource.trans hcap)
    exact ⟨t,ε-e,ht,by linarith [hh.1],by linarith,by linarith,
      by ring,hh.2.1⟩

end SquaresInCircles.Eight.TableFree.NegativeOuterEZero

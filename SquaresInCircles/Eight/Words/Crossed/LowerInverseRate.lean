module

public import SquaresInCircles.Eight.Frames.Signed.OppositeHardSigns
public import SquaresInCircles.Eight.Owners.Positive.CancelingOuter
public import SquaresInCircles.Eight.Words.Crossed.LargeGeometry
public import SquaresInCircles.Eight.Words.Crossed.GACycle
public import SquaresInCircles.Eight.Words.Crossed.WrongEndpointBound

/-!
# Eight squares: inverse-HG rates on the lower active tangent interval

The exact Y derivative is negative on the
whole interval [48/49,1.04], uniformly at the actual q.  Consequently
only two intrinsic transverse endpoints need bounds.  Both endpoint
bounds hold for the complete q interval directly; no q monotonicity or
angular table is assumed.
-/

section
/-!
## Three H captures and the signed opposite hard contact

A contrary H/G tangent order `H.y ≤ g` forces three rational captures (`contrary_captures`). The
unchanged opposite T may have either sign: the one-tenth capture `-1/10 < T.y` suffices to bound
its hard contact on the whole interval `[0,.32]` (`signed_opposite_bound`). The original TD/HDE
budget then contradicts the contrary order (`tangent_order`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CrossedCancelingBounds
open CrossedCancelingScalar EndpointRotationPenalty EndpointBudgetScalars

theorem support_bound {H : SignedPoint} {c k h : ℝ}
    (hHs : H.Sorted) (hHy : 0≤H.y) (hHq : H.Contained qCap)
    (hc : c∈Icc (0:ℝ) (1/4)) (hk : 0≤k) (hy : H.y≤c)
    (hroot : qCap<(k+1)^2+(c+1/2)^2) (hh : h∈Icc 0 frameCap) :
    S H h≤k*Real.sin h+(c-1/2)*Real.cos h := by
  let J := SignedPoint.outerAt qCap c
  have hqL : qLow≤qCap := by norm_num [qLow,qCap]
  have hcdiag : |c|≤diagonalCoordinate qCap := by
    rw [abs_of_nonneg hc.1]
    linarith [(uniform_circle_reserves hqL le_rfl).1,hc.2]
  obtain ⟨hJs,hJq,hJc⟩ := SignedPoint.outerAt_spec hqL hcdiag
  have hJy : J.y=c := rfl
  have hcircle : (J.a+1/2)^2+(c+1/2)^2=qCap := by
    have h1 : (J.a+1/2)^2+(|J.y|+1/2)^2=qCap := hJq
    rwa [hJy,abs_of_nonneg hc.1] at h1
  have hJa : J.a-1/2≤k := by nlinarith [hJs.1]
  have hsupport := PositiveCancelingOuter.sorted_support_mono hHs hJs hHy
    (show 0≤J.y from hc.1) (hHq.trans_eq hJq.symm) hy hh
  have hsin := mul_le_mul_of_nonneg_right hJa (transport_trig hh).2.2.1
  dsimp [S]
  change H.a*Real.sin h+H.y*Real.cos h≤J.a*Real.sin h+c*Real.cos h at hsupport
  nlinarith

/-- These comparisons use H itself, also when it lies strictly inside `qCap`; only the support
upper bound is evaluated on the circle. -/
theorem contrary_captures {H : SignedPoint} {g r : ℝ}
    (hHs : H.Sorted) (hHy : 0≤H.y) (hHq : H.Contained qCap)
    (hg : g∈Icc (0:ℝ) (26/125)) (hr : r∈Icc 0 frameCap)
    (hHG : 1/2≤g+S H r) (hbad : H.y≤g) :
    37/250<H.y ∧ 33/50<r ∧ 37/200<g := by
  have htr := trig_seven_tenths hr
  have hH : 37/250<H.y := by
    by_contra! hn
    have hs := support_bound hHs hHy hHq
      (c := 37/250) (k := 87/100) (by norm_num) (by norm_num) hn
      (by norm_num [qCap]) hr
    nlinarith [hg.2,htr.1,htr.2]
  have hr' : 33/50<r := by
    by_contra! hn
    have hs := support_bound hHs hHy hHq
      (c := 26/125) (k := 106/125) (by norm_num) (by norm_num)
      (hbad.trans hg.2) (by norm_num [qCap]) hr
    have ht := trig_sixty_six (show r∈Icc 0 (33/50:ℝ) from ⟨hr.1,hn⟩)
    nlinarith [hg.2,ht.1,ht.2]
  have hg' : 37/200<g := by
    by_contra! hn
    have hs := support_bound hHs hHy hHq
      (c := 37/200) (k := 857/1000) (by norm_num) (by norm_num)
      (hbad.trans hn) (by norm_num [qCap]) hr
    nlinarith [htr.1,htr.2]
  exact ⟨hH,hr',hg'⟩

/-- The signed opposite estimate needs only `t > -.1`. Its Taylor polynomial on the whole domain
has a negative quadratic part. -/
theorem signed_opposite_bound {t u : ℝ}
    (ht : -(1/10:ℝ)<t) (hu : u∈Icc 0 frameCap)
    (hcontact : t+1/2<(73/100)*Real.cos u-(481/500)*Real.sin u) :
    t+charge*u<47/200 := by
  have he : (8/25:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have href : (73/100)*Real.cos (8/25)-(481/500)*Real.sin (8/25)<(2/5:ℝ) := by
    have hc := cos_upper_four (show (0:ℝ)≤8/25 by norm_num)
    have hs := Real.sin_ge_sub_cube (show (0:ℝ)≤8/25 by norm_num)
    norm_num at hc hs
    nlinarith
  have hshort : u<8/25 := by
    by_contra! hn
    have hc := CorrelatedSameBlock.cos_anti he hu hn
    have hs := CorrelatedSameBlock.sin_mono he hu hn
    nlinarith
  have hc := cos_upper_four hu.1
  have hs := Real.sin_ge_sub_cube hu.1
  have h2 := pow_le_pow_left₀ hu.1 hshort.le 2
  have h3 := mul_le_mul_of_nonneg_right hshort.le (sq_nonneg u)
  have h4 := mul_le_mul_of_nonneg_right h2 (sq_nonneg u)
  have hpoly : t+charge*u<23/100+(1431/24500)*u-(3/10)*u^2 := by
    dsimp [charge]
    nlinarith
  have hsq := sq_nonneg (u-477/4900)
  nlinarith

theorem opposite_contact_from_circles {A B T : SignedPoint} {g u : ℝ}
    (hAy : 0≤A.y) (hBy : B.y≤0) (hBa : 0<B.a)
    (hAq : A.Contained qCap) (hBq : B.Contained qCap)
    (hsum : A.y-B.y=1) (hg : 37/200<g) (hGA : g+1≤A.a)
    (hu : u∈Icc 0 frameCap) (hBT : quarterFeasible B T (-u) 2) :
    T.y+1/2<(73/100)*Real.cos u-(481/500)*Real.sin u := by
  have hAc : (A.a+1/2)^2+(A.y+1/2)^2≤qCap := by
    simpa [SignedPoint.Contained,SignedPoint.circle,abs_of_nonneg hAy] using hAq
  have hBc : (B.a+1/2)^2+(-B.y+1/2)^2≤qCap := by
    simpa [SignedPoint.Contained,SignedPoint.circle,abs_of_nonpos hBy] using hBq
  have hAyU : A.y<269/500 := by
    dsimp [qCap] at hAc
    nlinarith
  have hByL : 481/500< -B.y+1/2 := by linarith
  have hBaU : B.a-1/2<73/100 := by
    dsimp [qCap] at hBc
    nlinarith
  have hBTref : quarterFeasible T.reflect B.reflect (-u) 0 := by
    simpa [reflectedOwner] using (quarterFeasible_reflect B T (-u) 2).2 hBT
  have hbound := SignedOppositeHardEnvelope.negative_hard_contact hu hBTref
  simp only [SignedPoint.reflect,neg_neg] at hbound
  have ht := transport_trig hu
  have hp := mul_lt_mul_of_pos_right hBaU (show 0<Real.cos u by linarith [ht.1])
  have hY := mul_le_mul_of_nonneg_right hByL.le ht.2.2.1
  nlinarith

/-- The unchanged opposite budget rules out `H.y ≤ g`. The opposite T needs no normal sign. -/
theorem tangent_order {H A B T : SignedPoint} {g r u : ℝ}
    (hHs : H.Sorted) (hHy : 0≤H.y) (hHq : H.Contained qCap)
    (hAy : 0≤A.y) (hBy : B.y≤0) (hBa : 0<B.a)
    (hAq : A.Contained qCap) (hBq : B.Contained qCap)
    (hsum : A.y-B.y=1) (hg : g∈Icc (0:ℝ) (26/125))
    (hr : r∈Icc 0 frameCap) (hu : u∈Icc 0 frameCap)
    (hHG : 1/2≤g+S H r) (hGA : g+1≤A.a)
    (hBT : quarterFeasible B T (-u) 2) (hT : -(1/10:ℝ)<T.y)
    (hbudget : H.y-T.y+charge*(r-u)<1-S0) : g<H.y := by
  by_contra! hbad
  obtain ⟨hH,hr',hg'⟩ := contrary_captures hHs hHy hHq hg hr hHG hbad
  have hc := opposite_contact_from_circles hAy hBy hBa hAq hBq hsum hg' hGA hu hBT
  have hb := signed_opposite_bound hT hu hc
  have hreserve := SignedOppositeHardEnvelope.budget_reserve
  dsimp [charge] at *
  nlinarith

end SquaresInCircles.Eight.CrossedCancelingBounds
end
end
end

section
/-!
## An actual same-q HG2-to-HG0 descendant at the common middle frame

The composite continuation determines the new
G tangent.  The unchanged opposite budget proves it is below H's actual
tangent, so lifting G to its original q-circle supplies an actual HG0
witness.  A positive frame motion gives strict slack at aligned GA; a
decrease of the original A primary retains that slack and makes the
original A circle strictly smaller.  The free G loss is never used.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CrossedCancelingConstruction
open PositiveSmallScalar CrossedCancelingScalar CrossedCancelingBounds
open EndpointRotationPenalty EndpointBudgetScalars

theorem actual_cap {q z : ℝ} {G A : SignedPoint}
    (hq : q≤qCap) (hAs : A.Sorted) (hAc : A.AvoidsCore)
    (hAq : A.Contained q) (hAy : 1/2≤A.y) (hGy : G.y≤0)
    (hz : z∈Icc 0 frameCap) (hGA : quarterFeasible G A (-z) 0) :
    CrossedCancelingScalar.CapData q (A.a-1/2) (A.y+1/2) ∧
      1/2≤V (A.a-1/2) (A.y+1/2) z := by
  have ha := SignedPoint.primary_gt_half hAs hAc
  have hb := SignedOppositeHardEnvelope.negative_hard_contact hz hGA
  have ht := transport_trig hz
  have hp := mul_le_mul_of_nonneg_left ht.2.1 (show 0≤A.a-1/2 by linarith)
  have hy := mul_nonneg (show 0≤A.y+1/2 by linarith) ht.2.2.1
  have ha1 : 1≤A.a := by nlinarith
  have hcircle : (A.a-1/2+1)^2+(A.y+1/2)^2≤q := by
    have h : (A.a+1/2)^2+(A.y+1/2)^2≤q := by
      simpa [SignedPoint.Contained,SignedPoint.circle,
        abs_of_nonneg (show 0≤A.y by linarith)] using hAq
    rw [show A.a-1/2+1=A.a+1/2 by ring]
    exact h
  have hupper : A.a-1/2≤177/250 := by
    have hc := hcircle.trans hq
    dsimp [qCap] at hc
    nlinarith
  exact ⟨⟨⟨by linarith,hupper⟩,by linarith,hcircle,hq⟩,by dsimp [V]; linarith⟩

theorem actual_output {q r z u : ℝ} {H G A B T : SignedPoint}
    (hqL : qLow≤q) (hq : q≤qCap)
    (hHs : H.Sorted) (hAs : A.Sorted) (hBs : B.Sorted)
    (hAc : A.AvoidsCore) (hHq : H.Contained q) (hAq : A.Contained q)
    (hBq : B.Contained q) (hHy : 0≤H.y) (hAy : 1/2≤A.y) (hBy : B.y≤0)
    (hGy : G.y≤0) (hT : -(1/10:ℝ)<T.y) (hsum : A.y-B.y=1)
    (hr : r∈Ioc 0 frameCap) (hz : z∈Icc 0 frameCap)
    (hu : u∈Icc 0 frameCap) (hspan : z+r≤frameCap)
    (hHG : zeroFeasible H G (z+r) 2) (hGA : quarterFeasible G A (-z) 0)
    (hBT : quarterFeasible B T (-u) 2)
    (hbudget : H.y-T.y+charge*(r-u)<1-S0) :
    Nonempty (CrossedGAData q H G A r z) := by
  obtain ⟨C,hV⟩ := actual_cap hq hAs hAc hAq hAy hGy hz hGA
  have hpair := original_pair hr.1.le hz.1 hspan hHG hGA
  have hreserve := alignment_reserve C hHy hHq hr.1.le hz.1 hspan hV hpair
    0 ⟨le_rfl,hz.1⟩
  have hzero : 1≤A.a-1/2+S H r := by
    simpa [composite,V] using hreserve.1
  obtain ⟨g,hgdef⟩ : ∃ g,g=max 0 (1/2-S H r) := ⟨_,rfl⟩
  have hg0 : 0≤g := by rw [hgdef]; exact le_max_left _ _
  have hga : g+1≤A.a := by
    have hh : g≤A.a-1 := by
      rw [hgdef]
      exact max_le (by linarith [C.P_mem.1]) (by linarith)
    linarith
  have hg : g∈Icc (0:ℝ) (26/125) := ⟨hg0,by linarith [C.P_mem.2]⟩
  have hhg : 1/2≤g+S H r := by
    have hh := le_max_right 0 (1/2-S H r); rw [← hgdef] at hh; linarith
  have horder : g<H.y := tangent_order hHs hHy (hHq.trans hq)
    (by linarith) hBy hBs.1 (hAq.trans hq) (hBq.trans hq) hsum hg
    ⟨hr.1.le,hr.2⟩ hu hhg hga hBT hT hbudget
  have hdiag : |-g|≤diagonalCoordinate q := by
    rw [abs_neg,abs_of_nonneg hg0]
    linarith [hg.2,(uniform_circle_reserves hqL hq).1]
  obtain ⟨hGs,hGq,hGc⟩ := SignedPoint.outerAt_spec hqL hdiag
  obtain ⟨G',hG'def⟩ : ∃ G',G'=SignedPoint.outerAt q (-g) := ⟨_,rfl⟩
  rw [← hG'def] at hGs hGq hGc
  have hGyEq : G'.y= -g := by rw [hG'def]; rfl
  have hGcircle : (G'.a+1/2)^2+(g+1/2)^2=q := by
    have h1 : (G'.a+1/2)^2+(|G'.y|+1/2)^2=q := hGq
    rwa [hGyEq,abs_neg,abs_of_nonneg hg0] at h1
  have hHcircle : (H.a+1/2)^2+(H.y+1/2)^2≤q := by
    simpa [SignedPoint.Contained,SignedPoint.circle,abs_of_nonneg hHy] using hHq
  have hminor := pow_lt_pow_left₀ (show g+1/2<H.y+1/2 by linarith)
    (show 0≤g+1/2 by linarith) (by decide : (2:ℕ)≠0)
  have hprimary : H.a<G'.a := by
    have hsq : (H.a+1/2)^2<(G'.a+1/2)^2 := by linarith only [hHcircle,hGcircle,hminor]
    have h := lt_of_pow_lt_pow_left₀ 2 (by linarith only [hGs.1]) hsq
    linarith only [h]
  have hsin : 0<Real.sin r := Real.sin_pos_of_pos_of_lt_pi hr.1
    (by dsimp [frameCap] at hr; linarith [hr.2,Real.pi_gt_three])
  have hpositive := mul_pos (sub_pos.mpr hprimary) hsin
  have hnonneg := mul_nonneg (sub_nonneg.mpr horder.le)
    (sub_nonneg.mpr (Real.cos_le_one r))
  have hHGzero : zeroFeasible H G' r 0 := by
    rw [zeroFeasible,edgeWidth_positive_formula ⟨hr.1.le,hr.2⟩]
    simp only [zeroProjection,Matrix.cons_val_zero,hGyEq]
    dsimp [S] at hhg
    linarith only [hhg,hpositive,hnonneg]
  have hstrictGA : 0<z → g+1<A.a := by
    intro hzpos
    have ht := transport_trig hz
    have hsinz : 0<Real.sin z := Real.sin_pos_of_pos_of_lt_pi hzpos
      (by dsimp [frameCap] at hz; linarith [hz.2,Real.pi_gt_three])
    have hp := mul_le_mul_of_nonneg_left ht.2.1
      (show 0≤A.a-1/2 by linarith [C.P_mem.1])
    have hys := mul_pos (show 0<A.y+1/2 by linarith) hsinz
    have ha1 : 1<A.a := by dsimp [V] at hV; linarith only [hV,hp,hys]
    have hf0 : 1<A.a-1/2+S H r := by
      have hh := hreserve.2
      rw [show composite H (A.a-1/2) (A.y+1/2) r 0=A.a-1/2+S H r by
        simp [composite,V],sub_zero] at hh
      linarith only [hh,hpair,hzpos]
    by_cases hs : 0≤1/2-S H r
    · rw [hgdef,max_eq_right hs]
      linarith
    · have heq : g=0 := by rw [hgdef]; exact max_eq_left (le_of_not_ge hs)
      rw [heq]
      linarith
  have hAout : ∃ A' : SignedPoint, A'.Sorted ∧ A'.AvoidsCore ∧
      A'.Contained q ∧ A'.y=A.y ∧ g+1≤A'.a ∧
      (0<z → A'.circle<q) ∧ (A.circle<q → A'.circle<q) := by
    by_cases hz0 : z=0
    · exact ⟨A,hAs,hAc,hAq,rfl,hga,by intro h; linarith only [h,hz0],fun h => h⟩
    · have hzpos : 0<z := lt_of_le_of_ne hz.1 (Ne.symm hz0)
      have hstrict := hstrictGA hzpos
      obtain ⟨a',ha'def⟩ : ∃ a' : ℝ,a'=(A.a+g+1)/2 := ⟨_,rfl⟩
      have ha' : g+1<a' ∧ a'<A.a := by
        constructor <;> linarith only [ha'def,hstrict]
      have hAy0 : 0≤A.y := by linarith only [hAy]
      have hAs' : (⟨a',A.y⟩ : SignedPoint).Sorted := by
        refine ⟨by linarith only [ha'.1,hg0],?_⟩
        change |A.y|≤a'
        rw [abs_of_nonneg hAy0]
        have hh := (SignedPoint.coordinate_bounds hAs hAc hAq hq).2.2
        rw [abs_of_nonneg hAy0] at hh
        linarith only [ha'.1,hg0,hh]
      have hAc' : (⟨a',A.y⟩ : SignedPoint).AvoidsCore := by
        change (1/12:ℝ)^2≤(max (a'-1/2) 0)^2+(max (|A.y|-1/2) 0)^2
        have h1 : 1/2≤a'-1/2 := by linarith only [ha'.1,hg0]
        rw [max_eq_left (by linarith only [h1] : 0≤a'-1/2)]
        nlinarith only [h1,sq_nonneg (max (|A.y|-1/2) 0)]
      have hsq := pow_lt_pow_left₀ (show a'+1/2<A.a+1/2 by linarith only [ha'.2])
        (show 0≤a'+1/2 by linarith only [ha'.1,hg0]) (by decide : (2:ℕ)≠0)
      have hloss : (⟨a',A.y⟩ : SignedPoint).circle<A.circle := by
        change (a'+1/2)^2+(|A.y|+1/2)^2<
          (A.a+1/2)^2+(|A.y|+1/2)^2
        linarith only [hsq]
      have hstrictq : (⟨a',A.y⟩ : SignedPoint).circle<q := hloss.trans_le hAq
      exact ⟨⟨a',A.y⟩,hAs',hAc',hstrictq.le,rfl,ha'.1.le,fun _ => hstrictq,
        fun h => hloss.trans h⟩
  obtain ⟨A',hAs',hAc',hAq',hAy',hga',hstrict',hloss'⟩ := hAout
  exact ⟨{
    pointG := G'
    pointA := A'
    G_sorted := hGs
    G_avoids := hGc
    G_contained := hGq.le
    G_nonpos := by rw [hGyEq]; linarith only [hg0]
    A_sorted := hAs'
    A_avoids := hAc'
    A_contained := hAq'
    A_tangent := hAy'
    HG_zero := hHGzero
    GA_hard := by
      simpa [quarterFeasible,quarterProjection,hGyEq] using
        (show (1:ℝ)≤ -g+A'.a by linarith only [hga'])
    A_strict := hstrict'
    A_loss := hloss' }⟩

end SquaresInCircles.Eight.CrossedCancelingConstruction
end
end
end

section
/-!
## The inverse-HG rate decreases on the full upper tangent interval

Every radical uses the actual q.  The exact
Y derivative is bounded above by -.9 on the entire feasible transverse
interval, uniformly in tan r <= .0401.  One rational endpoint bounds the
initial inverse rate by 1.43.  No scalar subdivision is used.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CrossedUpperRate
open CrossedClampRates EndpointRotationPenalty

def inverseE (q Y t : ℝ) : ℝ := adjacent q Y-1+
  t*(adjacent q Y-transverse q Y)/(adjacent q Y-transverse q Y*t)
def inverseDPart (q Y t : ℝ) : ℝ := transverse q Y/adjacent q Y+
  q*t*(1-t)/(adjacent q Y*(adjacent q Y-transverse q Y*t)^2)
def inverseRateD (q Y t : ℝ) : ℝ :=
  -q*inverseE q Y t/(CrossedClampRates.radius q Y*Y^2)+inverseDPart q Y t

structure InverseDomain (q Y t : ℝ) : Prop where
  floor : qLow≤q
  ceiling : q≤qCap
  Y_mem : Y∈Icc (26/25 : ℝ) (Real.sqrt (q-9/4))
  t_mem : t∈Icc (0 : ℝ) (401/10000)

theorem inverse_radicals {q Y t : ℝ} (C : InverseDomain q Y t) :
    Y<1291/1000 ∧ 0<q-Y^2 ∧ CrossedClampRates.radius q Y∈Ico (3/2 : ℝ) (427/250) ∧
      transverse q Y∈Ico (1/2 : ℝ) (177/250) ∧
      0<q-(transverse q Y)^2 ∧ adjacent q Y∈Ioo (1847/1000 : ℝ) (383/200) ∧
      (CrossedClampRates.radius q Y)^2+Y^2=q ∧ (adjacent q Y)^2+(transverse q Y)^2=q := by
  have hqL := C.floor
  have hq := C.ceiling
  dsimp [qLow,qCap] at hqL hq
  have hY0 : 0≤Y := by linarith [C.Y_mem.1]
  have htop : 0≤q-9/4 := by linarith
  have htop2 := Real.sq_sqrt htop
  have hY2 := pow_le_pow_left₀ hY0 C.Y_mem.2 2
  have hfloor2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤26/25) C.Y_mem.1 2
  have hYmax : Y<1291/1000 := by nlinarith
  have hr : 0<q-Y^2 := by nlinarith
  have hR0 : 0≤CrossedClampRates.radius q Y := Real.sqrt_nonneg _
  have hR2 : (CrossedClampRates.radius q Y)^2=q-Y^2 := Real.sq_sqrt hr.le
  have hR : CrossedClampRates.radius q Y∈Ico (3/2 : ℝ) (427/250) := by constructor <;> nlinarith
  have hD : transverse q Y∈Ico (1/2 : ℝ) (177/250) := by
    dsimp [transverse]
    constructor <;> linarith [hR.1,hR.2]
  have hD2 := pow_le_pow_left₀ (show 0≤transverse q Y by linarith [hD.1]) hD.2.le 2
  have hx : 0<q-(transverse q Y)^2 := by nlinarith
  have hX0 : 0≤adjacent q Y := Real.sqrt_nonneg _
  have hX2 : (adjacent q Y)^2=q-(transverse q Y)^2 := Real.sq_sqrt hx.le
  have hX : adjacent q Y∈Ioo (1847/1000 : ℝ) (383/200) := by
    constructor <;> nlinarith [hD.1,sq_nonneg (transverse q Y-1/2)]
  exact ⟨hYmax,hr,hR,hD,hx,hX,by nlinarith,by nlinarith⟩

theorem inverse_denominator {q Y t : ℝ} (C : InverseDomain q Y t) :
    (1847/1000-(177/250)*(401/10000) : ℝ)<
      adjacent q Y-transverse q Y*t := by
  obtain ⟨_,_,_,hD,_,hX,_,_⟩ := inverse_radicals C
  have hDt := mul_le_mul hD.2.le C.t_mem.2 C.t_mem.1
    (by norm_num : (0:ℝ)≤177/250)
  linarith [hX.1]

theorem inverse_E_lower {q Y t : ℝ} (C : InverseDomain q Y t) :
    847/1000< inverseE q Y t := by
  obtain ⟨_,_,_,hD,_,hX,_,_⟩ := inverse_radicals C
  have hd := inverse_denominator C
  have hfrac : 0≤t*(adjacent q Y-transverse q Y)/
      (adjacent q Y-transverse q Y*t) := by
    apply div_nonneg
    · exact mul_nonneg C.t_mem.1 (by linarith [hX.1,hD.2])
    · linarith
  dsimp [inverseE]
  linarith [hX.1]

theorem inverse_D_part_upper {q Y t : ℝ} (C : InverseDomain q Y t) :
    inverseDPart q Y t<5/12 := by
  obtain ⟨_,_,_,hD,_,hX,_,_⟩ := inverse_radicals C
  have hX0 : 0<adjacent q Y := by linarith [hX.1]
  have hden := inverse_denominator C
  let d : ℝ := 1847/1000-(177/250)*(401/10000)
  have hd0 : 0<d := by norm_num [d]
  have hden0 : 0<adjacent q Y-transverse q Y*t := lt_trans hd0 hden
  have hk : transverse q Y/adjacent q Y<48/125 := by
    apply (div_lt_iff₀ hX0).2
    nlinarith [hD.2,hX.1]
  have hq0 : 0≤q := by have hh := C.floor; dsimp [qLow] at hh; linarith
  have hqt : q*t≤qCap*(401/10000) :=
    mul_le_mul C.ceiling C.t_mem.2 C.t_mem.1 (by norm_num [qCap])
  have hnum : q*t*(1-t)≤qCap*(401/10000) := by
    have hh := mul_le_mul_of_nonneg_left (show 1-t≤1 by linarith [C.t_mem.1])
      (mul_nonneg hq0 C.t_mem.1)
    nlinarith
  have hd2 := pow_lt_pow_left₀ hden hd0.le (by decide : (2:ℕ)≠0)
  have hbigden := (mul_lt_mul_of_pos_left hd2
      (by norm_num : (0:ℝ)<1847/1000)).trans
    (mul_lt_mul_of_pos_right hX.1 (sq_pos_of_pos hden0))
  let M : ℝ := qCap*(401/10000)/((1847/1000)*d^2)
  have hM : 0<M := by norm_num [M,d,qCap]
  have hsecond : q*t*(1-t)/(adjacent q Y*(adjacent q Y-transverse q Y*t)^2)<M := by
    apply (div_lt_iff₀ (mul_pos hX0 (sq_pos_of_pos hden0))).2
    have hm := mul_lt_mul_of_pos_left hbigden hM
    have hcancel : M*((1847/1000)*d^2)=qCap*(401/10000) := by
      dsimp [M]
      field_simp [hd0.ne']
    rw [hcancel] at hm
    exact hnum.trans_lt hm
  have hscalar : 48/125+M<5/12 := by norm_num [M,d,qCap]
  dsimp [inverseDPart]
  linarith

/-- The sharp monotone factor is a cubic with a factor R-3/2.
The actual-q term has the same favorable sign as qCap-q. -/
theorem inverse_radial_factor {q Y t : ℝ} (C : InverseDomain q Y t) :
    3263/2082≤q/(CrossedClampRates.radius q Y*Y^2) := by
  obtain ⟨_,_,hR,_,_,_,hcircle,_⟩ := inverse_radicals C
  have hY0 : 0<Y := by linarith [C.Y_mem.1]
  have hR0 : 0<CrossedClampRates.radius q Y := by linarith [hR.1]
  have hden : 0<CrossedClampRates.radius q Y*Y^2 := mul_pos hR0 (sq_pos_of_pos hY0)
  apply (le_div_iff₀ hden).2
  have hc : 0≤(CrossedClampRates.radius q Y)^2+(3/2)*CrossedClampRates.radius q Y+9/4-qCap := by
    dsimp [qCap]
    nlinarith [hR.1]
  have hfactor := mul_nonneg (show 0≤CrossedClampRates.radius q Y-3/2 by linarith [hR.1]) hc
  have hqterm := mul_nonneg (sub_nonneg.mpr C.ceiling)
    (show 0≤(3263/2082)*CrossedClampRates.radius q Y-1 by linarith [hR.1])
  have hid : q-(3263/2082)*CrossedClampRates.radius q Y*Y^2=
      (3263/2082)*(CrossedClampRates.radius q Y-3/2)*
        ((CrossedClampRates.radius q Y)^2+(3/2)*CrossedClampRates.radius q Y+9/4-qCap)+
      (qCap-q)*((3263/2082)*CrossedClampRates.radius q Y-1) := by
    dsimp [qCap]
    linear_combination -((3263/2082)*CrossedClampRates.radius q Y)*hcircle
  nlinarith

theorem inverse_rate_derivative_upper {q Y t : ℝ} (C : InverseDomain q Y t) :
    inverseRateD q Y t< -(9/10 : ℝ) := by
  have hE := inverse_E_lower C
  have hR := inverse_radial_factor C
  have hD := inverse_D_part_upper C
  have hR0 : 0<q/(CrossedClampRates.radius q Y*Y^2) := by linarith
  have hproduct := (mul_le_mul_of_nonneg_right hR
      (by norm_num : (0:ℝ)≤847/1000)).trans_lt
    (mul_lt_mul_of_pos_left hE hR0)
  have hid : -q*inverseE q Y t/(CrossedClampRates.radius q Y*Y^2)=
      -((q/(CrossedClampRates.radius q Y*Y^2))*inverseE q Y t) := by ring
  dsimp [inverseRateD]
  rw [hid]
  nlinarith

theorem adjacent_hasDerivAt {q Y t : ℝ} (C : InverseDomain q Y t) :
    HasDerivAt (adjacent q)
      (transverse q Y*Y/(CrossedClampRates.radius q Y*adjacent q Y)) Y := by
  obtain ⟨_,hr,hR,_,hx,hX,_,_⟩ := inverse_radicals C
  have hR0 : CrossedClampRates.radius q Y≠0 := (by linarith [hR.1] : 0<CrossedClampRates.radius q Y).ne'
  have hX0 : adjacent q Y≠0 := (by linarith [hX.1] : 0<adjacent q Y).ne'
  have hd : HasDerivAt (transverse q) (-Y/CrossedClampRates.radius q Y) Y :=
    (radius_hasDerivAt hr).sub_const 1
  have hh := ((hd.pow 2).const_sub q).sqrt hx.ne'
  convert hh using 1
  · rfl
  · dsimp [adjacent]
    field_simp [hR0,show Real.sqrt (q-(transverse q Y)^2)≠0 from hX0]

private theorem inverse_E_derivative_algebra {q R X D Y t : ℝ}
    (hR : R≠0) (hX : X≠0) (hden : X-D*t≠0) (hcircle : X^2+D^2=q) :
    D*Y/(R*X)+t*((D*Y/(R*X)+Y/R)*(X-D*t)-
        (X-D)*(D*Y/(R*X)+t*Y/R))/(X-D*t)^2=
      (Y/R)*(D/X+q*t*(1-t)/(X*(X-D*t)^2)) := by
  have hid : Y*t*((D+X)*(X-D*t)-(X-D)*(D+t*X)-q*(1-t))=0 := by
    linear_combination Y*t*(1-t)*hcircle
  field_simp [hR,hX,hden]
  nlinarith

theorem inverseE_hasDerivAt {q Y t : ℝ} (C : InverseDomain q Y t) :
    HasDerivAt (fun y => inverseE q y t)
      ((Y/CrossedClampRates.radius q Y)*inverseDPart q Y t) Y := by
  obtain ⟨_,hr,hR,_,_,hX,_,hcircle⟩ := inverse_radicals C
  have hR0 : CrossedClampRates.radius q Y≠0 := (by linarith [hR.1] : 0<CrossedClampRates.radius q Y).ne'
  have hX0 : adjacent q Y≠0 := (by linarith [hX.1] : 0<adjacent q Y).ne'
  have hd0 : adjacent q Y-transverse q Y*t≠0 :=
    (by linarith [inverse_denominator C] : 0<adjacent q Y-transverse q Y*t).ne'
  have hd : HasDerivAt (transverse q) (-Y/CrossedClampRates.radius q Y) Y :=
    (radius_hasDerivAt hr).sub_const 1
  have hx := adjacent_hasDerivAt C
  have hh := (hx.sub_const 1).add (((hx.sub hd).div (hx.sub (hd.mul_const t)) hd0).const_mul t)
  convert hh using 1
  · funext y
    dsimp [inverseE]
    ring
  · dsimp [inverseDPart]
    have ha := inverse_E_derivative_algebra (q := q) (R := CrossedClampRates.radius q Y) (X := adjacent q Y)
      (D := transverse q Y) (Y := Y) (t := t) hR0 hX0 hd0 hcircle
    convert ha.symm using 1
    ring

theorem inverseRate_hasDerivAt {q Y t : ℝ} (C : InverseDomain q Y t) :
    HasDerivAt (fun y => inverseRate q y t) (inverseRateD q Y t) Y := by
  obtain ⟨_,hr,hR,_,_,_,hcircle,_⟩ := inverse_radicals C
  have hR0 : CrossedClampRates.radius q Y≠0 := (by linarith [hR.1] : 0<CrossedClampRates.radius q Y).ne'
  have hY0 : Y≠0 := (by linarith [C.Y_mem.1] : 0<Y).ne'
  have hh := ((radius_hasDerivAt hr).div (hasDerivAt_id Y) hY0).mul (inverseE_hasDerivAt C)
  convert hh using 1
  · rfl
  · dsimp [inverseRateD]
    field_simp [hR0,hY0]
    nlinarith [congrArg (fun x : ℝ => inverseE q Y t*x) hcircle]

theorem base_inverse_domain {q t : ℝ} (hqL : qLow≤q) (hq : q≤qCap)
    (ht : t∈Icc (0 : ℝ) (401/10000)) : InverseDomain q (26/25) t := by
  refine ⟨hqL,hq,⟨le_rfl,?_⟩,ht⟩
  have hqL' := hqL
  dsimp [qLow] at hqL'
  have hr : 0≤q-9/4 := by linarith
  have hR0 := Real.sqrt_nonneg (q-9/4)
  have hR2 := Real.sq_sqrt hr
  nlinarith

theorem base_inverse_upper {q t : ℝ} (hqL : qLow≤q) (hq : q≤qCap)
    (ht : t∈Icc (0 : ℝ) (401/10000)) : inverseRate q (26/25) t<143/100 := by
  let C := base_inverse_domain hqL hq ht
  obtain ⟨_,_,hR,hD,_,hX,hR2,hX2⟩ := inverse_radicals C
  have hqL' := hqL
  have hq' := hq
  dsimp [qLow,qCap] at hqL' hq'
  have hRsharp : CrossedClampRates.radius q (26/25)∈Ioo (16833/10000 : ℝ) (3367/2000) := by
    constructor <;> nlinarith [hR.1]
  have hDsharp : 6833/10000<transverse q (26/25) := by
    dsimp [transverse]
    linarith [hRsharp.1]
  have hXsharp : adjacent q (26/25)<18571/10000 := by
    nlinarith [hX.1]
  let d : ℝ := 1847/1000-(177/250)*(401/10000)
  let N : ℝ := (401/10000)*(18571/10000-6833/10000)
  let M : ℝ := 18571/10000-1+N/d
  have hd0 : 0<d := by norm_num [d]
  have hden := inverse_denominator C
  have hden0 : 0<adjacent q (26/25)-transverse q (26/25)*t := lt_trans hd0 hden
  have hdiff : 0≤adjacent q (26/25)-transverse q (26/25) := by linarith [hX.1,hD.2]
  have hn1 := mul_le_mul_of_nonneg_right ht.2 hdiff
  have hn2 := mul_lt_mul_of_pos_left
    (show adjacent q (26/25)-transverse q (26/25)<18571/10000-6833/10000 by linarith)
    (by norm_num : (0:ℝ)<401/10000)
  have hnum : t*(adjacent q (26/25)-transverse q (26/25))<N := by dsimp [N]; linarith
  have hf : t*(adjacent q (26/25)-transverse q (26/25))/
      (adjacent q (26/25)-transverse q (26/25)*t)<N/d := by
    apply (div_lt_iff₀ hden0).2
    have hm := mul_lt_mul_of_pos_left hden (show 0<N/d by norm_num [N,d])
    have hid : (N/d)*d=N := by field_simp [hd0.ne']
    rw [hid] at hm
    linarith
  have hE : inverseE q (26/25) t<M := by dsimp [inverseE,M]; linarith
  have hE0 : 0< inverseE q (26/25) t := by linarith [inverse_E_lower C]
  have hM0 : 0<M := by norm_num [M,N,d]
  have hratio : CrossedClampRates.radius q (26/25)/(26/25)<(3367/2000)/(26/25) := by
    exact div_lt_div_of_pos_right hRsharp.2 (by norm_num)
  have hprod := (mul_lt_mul_of_pos_right hratio hE0).trans
    (mul_lt_mul_of_pos_left hE (by norm_num : (0:ℝ)<(3367/2000)/(26/25)))
  have hconst : ((3367/2000)/(26/25))*M<143/100 := by norm_num [M,N,d]
  change (CrossedClampRates.radius q (26/25)/(26/25))*inverseE q (26/25) t<143/100
  exact hprod.trans hconst

theorem tangent_short {r : ℝ} (hr : r∈Icc (0 : ℝ) (1/25)) :
    Real.tan r∈Icc (0 : ℝ) (401/10000) := by
  have hi : r∈Icc 0 frameCap := ⟨hr.1,by dsimp [frameCap]; linarith [hr.2]⟩
  have he : (1/25 : ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have ht := transport_trig hi
  have hcos : 0<Real.cos r := by linarith [ht.1]
  have hs := CorrelatedSameBlock.sin_mono hi he hr.2
  have hc := CorrelatedSameBlock.cos_anti hi he hr.2
  have hsU := sin_upper_five (show (0:ℝ)≤1/25 by norm_num)
  have hcL := cos_lower_six (show (0:ℝ)≤1/25 by norm_num)
  constructor
  · rw [Real.tan_eq_sin_div_cos]
    exact div_nonneg ht.2.2.1 hcos.le
  · rw [Real.tan_eq_sin_div_cos,div_le_iff₀ hcos]
    norm_num at hsU hcL
    linarith

end SquaresInCircles.Eight.CrossedUpperRate
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CrossedLowerRate
open CrossedClampRates
open CrossedUpperRate (inverseE inverseDPart inverseRateD radius_hasDerivAt)

def shortTangent : ℝ := 20011/500000

structure InverseDomain (q Y t : ℝ) : Prop where
  floor : qLow≤q
  ceiling : q≤qCap
  Y_mem : Y∈Icc (48/49 : ℝ) (26/25)
  t_mem : t∈Icc 0 shortTangent

theorem inverse_radicals {q Y t : ℝ} (C : InverseDomain q Y t) :
    0<q-Y^2 ∧ CrossedClampRates.radius q Y∈Ioo (42/25 : ℝ) (43/25) ∧
      transverse q Y∈Ioo (17/25 : ℝ) (18/25) ∧
      0<q-(transverse q Y)^2 ∧ adjacent q Y∈Ioo (46/25 : ℝ) (93/50) ∧
      (CrossedClampRates.radius q Y)^2+Y^2=q ∧ (adjacent q Y)^2+(transverse q Y)^2=q := by
  have hqL := C.floor
  have hq := C.ceiling
  dsimp [qLow,qCap] at hqL hq
  have hY0 : 0≤Y := by linarith [C.Y_mem.1]
  have hY2 := pow_le_pow_left₀ hY0 C.Y_mem.2 2
  have hYlo2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤48/49) C.Y_mem.1 2
  have hr : 0<q-Y^2 := by nlinarith
  have hR0 : 0≤CrossedClampRates.radius q Y := Real.sqrt_nonneg _
  have hR2 : (CrossedClampRates.radius q Y)^2=q-Y^2 := Real.sq_sqrt hr.le
  have hR : CrossedClampRates.radius q Y∈Ioo (42/25 : ℝ) (43/25) := by constructor <;> nlinarith
  have hD : transverse q Y∈Ioo (17/25 : ℝ) (18/25) := by
    dsimp [transverse]
    constructor <;> linarith [hR.1,hR.2]
  have hD2 := pow_le_pow_left₀ (show 0≤transverse q Y by linarith [hD.1]) hD.2.le 2
  have hx : 0<q-(transverse q Y)^2 := by nlinarith
  have hX0 : 0≤adjacent q Y := Real.sqrt_nonneg _
  have hX2 : (adjacent q Y)^2=q-(transverse q Y)^2 := Real.sq_sqrt hx.le
  have hX : adjacent q Y∈Ioo (46/25 : ℝ) (93/50) := by
    constructor <;> nlinarith [hD.1,sq_nonneg (transverse q Y-17/25)]
  exact ⟨hr,hR,hD,hx,hX,by nlinarith,by nlinarith⟩

theorem inverse_denominator {q Y t : ℝ} (C : InverseDomain q Y t) :
    181/100<adjacent q Y-transverse q Y*t := by
  obtain ⟨_,_,hD,_,hX,_,_⟩ := inverse_radicals C
  have ht : t≤41/1000 := by have hh := C.t_mem.2; dsimp [shortTangent] at hh; linarith
  have hm := mul_le_mul hD.2.le ht C.t_mem.1 (by norm_num : (0:ℝ)≤18/25)
  linarith [hX.1]

theorem inverse_E_lower {q Y t : ℝ} (C : InverseDomain q Y t) :
    21/25< inverseE q Y t := by
  obtain ⟨_,_,hD,_,hX,_,_⟩ := inverse_radicals C
  have hd := inverse_denominator C
  have hf : 0≤t*(adjacent q Y-transverse q Y)/(adjacent q Y-transverse q Y*t) :=
    div_nonneg (mul_nonneg C.t_mem.1 (by linarith [hX.1,hD.2])) (by linarith)
  dsimp [inverseE]
  linarith [hX.1]

theorem inverse_D_part_upper {q Y t : ℝ} (C : InverseDomain q Y t) :
    inverseDPart q Y t<1/2 := by
  obtain ⟨_,_,hD,_,hX,_,_⟩ := inverse_radicals C
  have hX0 : 0<adjacent q Y := by linarith [hX.1]
  have hd := inverse_denominator C
  have hd0 : 0<adjacent q Y-transverse q Y*t := by linarith
  have hfirst : transverse q Y/adjacent q Y<2/5 := by
    apply (div_lt_iff₀ hX0).2
    nlinarith [hD.2,hX.1]
  have hq0 : 0≤q := by have hh := C.floor; dsimp [qLow] at hh; linarith
  have ht : t≤41/1000 := by have hh := C.t_mem.2; dsimp [shortTangent] at hh; linarith
  have hnum1 := mul_le_mul C.ceiling ht C.t_mem.1 (by norm_num [qCap] : (0:ℝ)≤qCap)
  have hnum2 := mul_le_mul_of_nonneg_left (show 1-t≤1 by linarith [C.t_mem.1])
    (mul_nonneg hq0 C.t_mem.1)
  have hnum : q*t*(1-t)≤qCap*(41/1000) := by nlinarith
  have hd2 := pow_lt_pow_left₀ hd (by norm_num : (0:ℝ)≤181/100) (by decide : (2:ℕ)≠0)
  have hden := (mul_lt_mul_of_pos_left hd2 (by norm_num : (0:ℝ)<46/25)).trans
    (mul_lt_mul_of_pos_right hX.1 (sq_pos_of_pos hd0))
  have hsecond : q*t*(1-t)/(adjacent q Y*(adjacent q Y-transverse q Y*t)^2)<1/10 := by
    apply (div_lt_iff₀ (mul_pos hX0 (sq_pos_of_pos hd0))).2
    dsimp [qCap] at hnum
    nlinarith
  dsimp [inverseDPart]
  linarith

theorem inverse_radial_factor {q Y t : ℝ} (C : InverseDomain q Y t) :
    2<q/(CrossedClampRates.radius q Y*Y^2) := by
  obtain ⟨_,hR,_,_,_,_,_⟩ := inverse_radicals C
  have hY0 : 0<Y := by linarith [C.Y_mem.1]
  have hR0 : 0<CrossedClampRates.radius q Y := by linarith [hR.1]
  have hY2 := pow_le_pow_left₀ hY0.le C.Y_mem.2 2
  have hprod := mul_le_mul hR.2.le hY2 (sq_nonneg Y) (by norm_num : (0:ℝ)≤43/25)
  apply (lt_div_iff₀ (mul_pos hR0 (sq_pos_of_pos hY0))).2
  have hqL := C.floor
  dsimp [qLow] at hqL
  nlinarith

theorem inverse_rate_derivative_negative {q Y t : ℝ} (C : InverseDomain q Y t) :
    inverseRateD q Y t< -1 := by
  have hE := inverse_E_lower C
  have hR := inverse_radial_factor C
  have hD := inverse_D_part_upper C
  have hm1 := mul_lt_mul_of_pos_right hR (by norm_num : (0:ℝ)<21/25)
  have hm2 := mul_lt_mul_of_pos_left hE (by linarith : 0<q/(CrossedClampRates.radius q Y*Y^2))
  have hid : -q*inverseE q Y t/(CrossedClampRates.radius q Y*Y^2)=
      -((q/(CrossedClampRates.radius q Y*Y^2))*inverseE q Y t) := by ring
  dsimp [inverseRateD]
  rw [hid]
  nlinarith

theorem adjacent_hasDerivAt {q Y t : ℝ} (C : InverseDomain q Y t) :
    HasDerivAt (adjacent q) (transverse q Y*Y/(CrossedClampRates.radius q Y*adjacent q Y)) Y := by
  obtain ⟨hr,hR,_,hx,hX,_,_⟩ := inverse_radicals C
  have hR0 : CrossedClampRates.radius q Y≠0 := (by linarith [hR.1] : 0<CrossedClampRates.radius q Y).ne'
  have hX0 : adjacent q Y≠0 := (by linarith [hX.1] : 0<adjacent q Y).ne'
  have hd : HasDerivAt (transverse q) (-Y/CrossedClampRates.radius q Y) Y := (radius_hasDerivAt hr).sub_const 1
  have hh := ((hd.pow 2).const_sub q).sqrt hx.ne'
  convert hh using 1
  · rfl
  · dsimp [adjacent]
    field_simp [hR0,show Real.sqrt (q-(transverse q Y)^2)≠0 from hX0]

private theorem inverse_E_derivative_algebra {q R X D Y t : ℝ}
    (hR : R≠0) (hX : X≠0) (hden : X-D*t≠0) (hcircle : X^2+D^2=q) :
    D*Y/(R*X)+t*((D*Y/(R*X)+Y/R)*(X-D*t)-
        (X-D)*(D*Y/(R*X)+t*Y/R))/(X-D*t)^2=
      (Y/R)*(D/X+q*t*(1-t)/(X*(X-D*t)^2)) := by
  have hid : Y*t*((D+X)*(X-D*t)-(X-D)*(D+t*X)-q*(1-t))=0 := by
    linear_combination Y*t*(1-t)*hcircle
  field_simp [hR,hX,hden]
  nlinarith

theorem inverseE_hasDerivAt {q Y t : ℝ} (C : InverseDomain q Y t) :
    HasDerivAt (fun y => inverseE q y t) ((Y/CrossedClampRates.radius q Y)*inverseDPart q Y t) Y := by
  obtain ⟨hr,hR,_,_,hX,_,hcircle⟩ := inverse_radicals C
  have hR0 : CrossedClampRates.radius q Y≠0 := (by linarith [hR.1] : 0<CrossedClampRates.radius q Y).ne'
  have hX0 : adjacent q Y≠0 := (by linarith [hX.1] : 0<adjacent q Y).ne'
  have hd0 : adjacent q Y-transverse q Y*t≠0 :=
    (by linarith [inverse_denominator C] : 0<adjacent q Y-transverse q Y*t).ne'
  have hd : HasDerivAt (transverse q) (-Y/CrossedClampRates.radius q Y) Y := (radius_hasDerivAt hr).sub_const 1
  have hx := adjacent_hasDerivAt C
  have hh := (hx.sub_const 1).add (((hx.sub hd).div (hx.sub (hd.mul_const t)) hd0).const_mul t)
  convert hh using 1
  · funext y
    dsimp [inverseE]
    ring
  · dsimp [inverseDPart]
    have ha := inverse_E_derivative_algebra (q := q) (R := CrossedClampRates.radius q Y) (X := adjacent q Y)
      (D := transverse q Y) (Y := Y) (t := t) hR0 hX0 hd0 hcircle
    convert ha.symm using 1
    ring

theorem inverseRate_hasDerivAt {q Y t : ℝ} (C : InverseDomain q Y t) :
    HasDerivAt (fun y => inverseRate q y t) (inverseRateD q Y t) Y := by
  obtain ⟨hr,hR,_,_,_,hcircle,_⟩ := inverse_radicals C
  have hR0 : CrossedClampRates.radius q Y≠0 := (by linarith [hR.1] : 0<CrossedClampRates.radius q Y).ne'
  have hY0 : Y≠0 := (by linarith [C.Y_mem.1] : 0<Y).ne'
  have hh := ((radius_hasDerivAt hr).div (hasDerivAt_id Y) hY0).mul (inverseE_hasDerivAt C)
  convert hh using 1
  · rfl
  · dsimp [inverseRateD]
    field_simp [hR0,hY0]
    nlinarith [congrArg (fun x : ℝ => inverseE q Y t*x) hcircle]

theorem inverse_antitone {q t : ℝ} (hqL : qLow≤q) (hq : q≤qCap)
    (ht : t∈Icc 0 shortTangent) :
    AntitoneOn (fun Y => inverseRate q Y t) (Icc (48/49:ℝ) (26/25)) := by
  apply antiOn_of_hasDeriv_nonpos
  · intro y hy
    exact (inverseRate_hasDerivAt ⟨hqL,hq,hy,ht⟩).continuousAt.continuousWithinAt
  · intro y hy
    exact inverseRate_hasDerivAt ⟨hqL,hq,Ioo_subset_Icc_self hy,ht⟩
  · intro y hy
    exact (inverse_rate_derivative_negative ⟨hqL,hq,Ioo_subset_Icc_self hy,ht⟩).le.trans (by norm_num)

theorem inverse_upper_box {q Y t Rmax Xmin Xmax Dmin Dmax : ℝ}
    (C : InverseDomain q Y t)
    (hR : CrossedClampRates.radius q Y<Rmax) (hXlo : Xmin<adjacent q Y) (hXhi : adjacent q Y<Xmax)
    (hDlo : Dmin<transverse q Y) (hDhi : transverse q Y<Dmax)
    (hDmax : 0≤Dmax) (hden : 0<Xmin-Dmax*shortTangent) :
    inverseRate q Y t<(Rmax/Y)*(Xmax-1+
      shortTangent*(Xmax-Dmin)/(Xmin-Dmax*shortTangent)) := by
  obtain ⟨_,hRi,hDi,_,hXi,_,_⟩ := inverse_radicals C
  have hY0 : 0<Y := by linarith [C.Y_mem.1]
  have hRmax : 0<Rmax := by linarith [hRi.1]
  let d := Xmin-Dmax*shortTangent
  let N := shortTangent*(Xmax-Dmin)
  have ht0 : 0<shortTangent := by norm_num [shortTangent]
  have hN0 : 0<N := by
    dsimp [N]
    apply mul_pos ht0
    linarith [hXi.1,hDi.2]
  have hDt := mul_le_mul hDhi.le C.t_mem.2 C.t_mem.1 hDmax
  have hd : d<adjacent q Y-transverse q Y*t := by dsimp [d]; linarith
  have hd0 : 0<adjacent q Y-transverse q Y*t := lt_trans hden hd
  have hdiff : 0≤adjacent q Y-transverse q Y := by linarith [hXi.1,hDi.2]
  have hn1 := mul_le_mul_of_nonneg_right C.t_mem.2 hdiff
  have hn2 := mul_lt_mul_of_pos_left
    (show adjacent q Y-transverse q Y<Xmax-Dmin by linarith) ht0
  have hnum : t*(adjacent q Y-transverse q Y)<N := by dsimp [N]; linarith
  have hf : t*(adjacent q Y-transverse q Y)/(adjacent q Y-transverse q Y*t)<N/d := by
    apply (div_lt_iff₀ hd0).2
    have hm := mul_lt_mul_of_pos_left hd (div_pos hN0 hden)
    have he : (N/d)*d=N := div_mul_cancel₀ N (show d≠0 from hden.ne')
    rw [he] at hm
    linarith
  have hE : inverseE q Y t<Xmax-1+N/d := by dsimp [inverseE]; linarith
  have hE0 : 0< inverseE q Y t := by linarith [inverse_E_lower C]
  have hratio := div_lt_div_of_pos_right hR hY0
  have hm := (mul_lt_mul_of_pos_right hratio hE0).trans
    (mul_lt_mul_of_pos_left hE (div_pos hRmax hY0))
  exact hm

theorem inverse_at_one_upper {q t : ℝ} (hqL : qLow≤q) (hq : q≤qCap)
    (ht : t∈Icc 0 shortTangent) : inverseRate q 1 t<1491/1000 := by
  let C : InverseDomain q 1 t := ⟨hqL,hq,by norm_num,ht⟩
  obtain ⟨_,hR,_,_,hX,hR2,hX2⟩ := inverse_radicals C
  have hqL' := hqL
  have hq' := hq
  dsimp [qLow,qCap] at hqL' hq'
  have hRs : CrossedClampRates.radius q 1∈Ioo (8537/5000 : ℝ) (10672/6250) := by
    constructor <;> nlinarith [hR.1]
  have hDs : transverse q 1∈Ioo (3537/5000 : ℝ) (4422/6250) := by
    dsimp [transverse]
    constructor <;> linarith [hRs.1,hRs.2]
  have hXrel : (adjacent q 1)^2=2*CrossedClampRates.radius q 1 := by
    dsimp [transverse] at hX2
    nlinarith
  have hXs : adjacent q 1∈Ioo (18479/10000 : ℝ) (184799/100000) := by
    constructor <;> nlinarith [hX.1,hRs.1,hRs.2]
  have hb := inverse_upper_box C hRs.2 hXs.1 hXs.2 hDs.1 hDs.2
    (by norm_num : (0:ℝ)≤4422/6250)
    (by norm_num [shortTangent] : 0<(18479/10000:ℝ)-(4422/6250)*shortTangent)
  have hk : ((10672/6250:ℝ)/1)*(184799/100000-1+
      shortTangent*(184799/100000-3537/5000)/(18479/10000-(4422/6250)*shortTangent))<1491/1000 := by
    norm_num [shortTangent]
  exact hb.trans hk

theorem inverse_at_floor_upper {q t : ℝ} (hqL : qLow≤q) (hq : q≤qCap)
    (ht : t∈Icc 0 shortTangent) : inverseRate q (48/49) t<153/100 := by
  let C : InverseDomain q (48/49) t := ⟨hqL,hq,by norm_num,ht⟩
  obtain ⟨_,hR,hD,_,hX,hR2,hX2⟩ := inverse_radicals C
  have hqL' := hqL
  have hq' := hq
  dsimp [qLow,qCap] at hqL' hq'
  have hRs : 1719/1000<CrossedClampRates.radius q (48/49) := by nlinarith [hR.1]
  have hDs : 719/1000<transverse q (48/49) := by dsimp [transverse]; linarith
  have hXs : adjacent q (48/49)<461/250 := by
    dsimp [transverse] at hX2
    nlinarith [hR.2,hX.1]
  have hb := inverse_upper_box C hR.2 hX.1 hXs hDs hD.2
    (by norm_num : (0:ℝ)≤18/25)
    (by norm_num [shortTangent] : 0<(46/25:ℝ)-(18/25)*shortTangent)
  have hk : ((43/25:ℝ)/(48/49))*(461/250-1+
      shortTangent*(461/250-719/1000)/(46/25-(18/25)*shortTangent))<153/100 := by
    norm_num [shortTangent]
  exact hb.trans hk

theorem tangent_short {r : ℝ} (hr : r∈Icc (0:ℝ) (1/25)) :
    Real.tan r∈Icc 0 shortTangent := by
  have hi : r∈Icc 0 frameCap := ⟨hr.1,by dsimp [frameCap]; linarith [hr.2]⟩
  have he : (1/25:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have ht := transport_trig hi
  have hc0 : 0<Real.cos r := by linarith [ht.1]
  have hs := CorrelatedSameBlock.sin_mono hi he hr.2
  have hc := CorrelatedSameBlock.cos_anti hi he hr.2
  have hsU := sin_upper_five (show (0:ℝ)≤1/25 by norm_num)
  have hcL := cos_lower_six (show (0:ℝ)≤1/25 by norm_num)
  constructor
  · rw [Real.tan_eq_sin_div_cos]
    exact div_nonneg ht.2.2.1 hc0.le
  · rw [Real.tan_eq_sin_div_cos]
    apply (div_le_iff₀ hc0).2
    dsimp [shortTangent]
    nlinarith

theorem angular_inverse_medium {q Y r : ℝ} (hqL : qLow≤q) (hq : q≤qCap)
    (hY : Y∈Icc (1:ℝ) (26/25)) (hr : r∈Icc (0:ℝ) (1/25)) :
    angularInverseRate q Y r<1491/1000 := by
  have ht := tangent_short hr
  have hm := inverse_antitone hqL hq ht
    (show (1:ℝ)∈Icc (48/49) (26/25) by norm_num)
    (show Y∈Icc (48/49:ℝ) (26/25) from ⟨by linarith [hY.1],hY.2⟩) hY.1
  exact hm.trans_lt (inverse_at_one_upper hqL hq ht)

theorem angular_inverse_small {q Y r : ℝ} (hqL : qLow≤q) (hq : q≤qCap)
    (hY : Y∈Icc (48/49:ℝ) 1) (hr : r∈Icc (0:ℝ) (1/25)) :
    angularInverseRate q Y r<153/100 := by
  have ht := tangent_short hr
  have hm := inverse_antitone hqL hq ht
    (show (48/49:ℝ)∈Icc (48/49) (26/25) by norm_num)
    (show Y∈Icc (48/49:ℝ) (26/25) from ⟨hY.1,by linarith [hY.2]⟩) hY.1
  exact hm.trans_lt (inverse_at_floor_upper hqL hq ht)

end SquaresInCircles.Eight.CrossedLowerRate
end
end
end

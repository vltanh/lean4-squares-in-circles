module

public import SquaresInCircles.Eight.TableFree.CrossedSmallWrongScalar
public import SquaresInCircles.Eight.TableFree.WideSmallPositiveZeroEndpoint

/-!
# The ordered wrong-sign exclusion on the full small interval

Uncompiled source draft.  The middle primary is lifted only to its
actual q-circle, keeping its original tangent.  The wrong intermediate
is optimized on that same circle.  Its intrinsic cap either already
allows tangent zero or reaches zero by the proved monotone demand.
The unchanged source H/D/E/T budget excludes that concrete endpoint.
No conclusion about equality of lifted and original points is used.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
open Candidate
namespace SignedCycle

theorem HardOuterGeometry.wide_small_wrong_G_impossible {q : ℝ}
    (I : HardOuterGeometry q) (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hsmall : (I.cycle.point A).y∈Icc (7/25 : ℝ) (1/2))
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAH : I.cycle.theta A≤I.cycle.theta H)
    (hTy : 0≤(I.cycle.point T).y)
    (hGy : 0≤(I.cycle.point G).y) (hGsmall : (I.cycle.point G).y<1/10) : False := by
  have hHupper : (I.cycle.point H).y<9/10 :=
    (le_abs_self _).trans_lt (SignedPoint.coordinate_bounds
      (I.necessary.sorted H) (I.necessary.core H) (I.necessary.contained H) hq).2.2
  have hcharge := (signed_outer_charges hq I.necessary I.anchors_normal
    I.witnesses I.zero_signs).1
  have hHGorder : I.cycle.theta H<I.cycle.theta G := by
    simp only [EndpointRotationPenalty.charge] at hcharge
    linarith
  have hHG : I.cycle.Feasible H 0 := by
    have ho : I.witnesses.owner H=0 ∨ I.witnesses.owner H=2 := by
      simpa [normalOwners,H] using I.witnesses.allowed H
    rcases ho with ho | ho
    · simpa [ho] using I.witnesses.feasible H
    · exact False.elim (not_lt_of_ge hGy (I.zero_signs.HG_canceling ho))
  obtain ⟨Θ,hΘdef⟩ : ∃ Θ,Θ=I.cycle.theta H-I.cycle.theta A := ⟨_,rfl⟩
  obtain ⟨e,hedef⟩ : ∃ e,e=I.cycle.theta G-I.cycle.theta H := ⟨_,rfl⟩
  have hΘ : 0≤Θ := by rw [hΘdef]; exact sub_nonneg.mpr hAH
  have he : 0<e := by rw [hedef]; exact sub_pos.mpr hHGorder
  have hz : Θ+e∈Icc 0 frameCap := by
    refine ⟨by linarith,?_⟩
    have hspread := (le_abs_self _).trans (I.necessary.spread G A)
    rw [hΘdef,hedef]
    linarith
  have hei : e∈Icc 0 frameCap := ⟨he.le,by linarith [hz.2]⟩
  let P := SignedPoint.outerAt q (I.cycle.point A).y
  obtain ⟨hPs,hPo,hPc⟩ := SignedPoint.outerAt_spec hqL
    (SignedPoint.contained_minor_le_diagonal (I.necessary.sorted A) (I.necessary.contained A))
  have hPy : P.y=(I.cycle.point A).y := rfl
  have hPa : (I.cycle.point A).a≤P.a := by
    have hsource := I.necessary.contained A
    have htarget := hPo
    change ((I.cycle.point A).a+1/2)^2+(|(I.cycle.point A).y|+1/2)^2≤q at hsource
    change (P.a+1/2)^2+(|P.y|+1/2)^2=q at htarget
    rw [hPy] at htarget
    have h2 : ((I.cycle.point A).a+1/2)^2≤(P.a+1/2)^2 := by linarith
    have h3 := le_of_pow_le_pow_left₀ two_ne_zero (by linarith [hPs.1]) h2
    linarith
  obtain ⟨p,hpdef⟩ : ∃ p,p=P.a-1/2 := ⟨_,rfl⟩
  obtain ⟨Y,hYdef⟩ : ∃ Y,Y=(I.cycle.point A).y+1/2 := ⟨_,rfl⟩
  have hY : Y∈Icc (39/50 : ℝ) 1 := by
    rw [hYdef]
    constructor <;> linarith [hsmall.1,hsmall.2]
  have hcircle : (p+1)^2+Y^2=q := by
    have hc := hPo
    change (P.a+1/2)^2+(|P.y|+1/2)^2=q at hc
    rw [hPy,abs_of_nonneg I.anchors_normal.A_nonneg] at hc
    rw [hpdef,hYdef]
    linarith
  have hp : p∈Icc (1/2 : ℝ) (819/1000) := by
    have hqL' := hqL
    have hq' := hq
    dsimp [qLow,qCap] at hqL' hq'
    have hPpos : 0<p := by
      have hh := SignedPoint.primary_gt_half hPs hPc
      rw [hpdef]
      linarith
    constructor
    · have hy2 := pow_le_pow_left₀ (show 0≤Y by linarith [hY.1]) hY.2 2
      by_contra! hlt
      have h3 := pow_lt_pow_left₀ (show p+1<3/2 by linarith) (by linarith) two_ne_zero
      linarith
    · have hy2 := pow_le_pow_left₀ (show (0:ℝ)≤39/50 by norm_num) hY.1 2
      by_contra! hlt
      have h3 := pow_lt_pow_left₀ (show (1819/1000:ℝ)<p+1 by linarith) (by norm_num) two_ne_zero
      linarith
  have S : CrossedSmallWrongScalar.CapData q p Y := {
    P_mem := hp
    Y_mem := hY
    circle := hcircle
    floor := hqL
    ceiling := hq }
  have hGA : -(I.cycle.point G).y+1/2≤PositiveSmallScalar.V p Y (Θ+e) := by
    have hf : quarterFeasible (I.cycle.point G) (I.cycle.point A) (-(Θ+e)) 0 := by
      have hd : I.cycle.theta 2-I.cycle.theta 1= -(Θ+e) := by
        change I.cycle.theta A-I.cycle.theta G= -(Θ+e)
        rw [hΘdef,hedef]; ring
      simpa [Feasible,slack,edge,word,delta,next,G,A,quarterFeasible,sub_nonneg,hd]
        using I.GA_hard
    rw [quarterFeasible,edgeWidth_negative_formula hz] at hf
    simp only [quarterProjection,Matrix.cons_val_zero,Real.cos_neg,Real.sin_neg] at hf
    have hmul := mul_le_mul_of_nonneg_right hPa (show 0≤Real.cos (Θ+e) by
      linarith [(transport_trig hz).1])
    simp only [PositiveSmallScalar.V]
    rw [hpdef,hYdef]
    linarith
  have hVlower : 2/5<PositiveSmallScalar.V p Y (Θ+e) := by linarith
  have hHG' : zeroFeasible (I.cycle.point H) (I.cycle.point G) e 0 := by
    have hd : I.cycle.theta 1-I.cycle.theta 0=e := by
      change I.cycle.theta G-I.cycle.theta H=e
      rw [hedef]
    simpa [Feasible,slack,edge,word,delta,next,H,G,zeroFeasible,sub_nonneg,hd] using hHG
  let Q := SignedPoint.outerAt q 0
  have hQbound : |(0:ℝ)|≤diagonalCoordinate q := by
    have hh := (uniform_circle_reserves hqL hq).1
    rw [abs_zero]
    linarith
  obtain ⟨hQs,hQo,hQc⟩ := SignedPoint.outerAt_spec hqL hQbound
  have hQy : Q.y=0 := rfl
  have hGAzero {s : ℝ} (hs : s∈Ioc 0 e)
      (hV : 1/2≤PositiveSmallScalar.V p Y (Θ+s)) :
      quarterFeasible Q P (-(Θ+s)) 0 := by
    have hi : Θ+s∈Icc 0 frameCap :=
      ⟨by linarith [hs.1],by linarith [hs.2,hz.2]⟩
    rw [quarterFeasible,edgeWidth_negative_formula hi]
    simp only [quarterProjection,Matrix.cons_val_zero,Real.cos_neg,Real.sin_neg,hQy,hPy]
    simp only [PositiveSmallScalar.V] at hV
    rw [hpdef,hYdef] at hV
    linarith
  have hcandidate : ∃s,s∈Ioc 0 e ∧
      zeroFeasible (I.cycle.point H) Q s 0 ∧ quarterFeasible Q P (-(Θ+s)) 0 := by
    by_cases hcap : 1/2≤PositiveSmallScalar.V p Y (Θ+e)
    · have hQa : (I.cycle.point G).a≤Q.a := by
        have hGc := I.necessary.contained G
        have hQcircle := hQo
        change ((I.cycle.point G).a+1/2)^2+(|(I.cycle.point G).y|+1/2)^2≤q at hGc
        change (Q.a+1/2)^2+(|Q.y|+1/2)^2=q at hQcircle
        rw [abs_of_nonneg hGy] at hGc
        rw [hQy,abs_zero] at hQcircle
        have hy2 := pow_le_pow_left₀ (show (0:ℝ)≤1/2 by norm_num)
          (show (1/2:ℝ)≤(I.cycle.point G).y+1/2 by linarith) 2
        have h2 : ((I.cycle.point G).a+1/2)^2≤(Q.a+1/2)^2 := by linarith
        have h3 := le_of_pow_le_pow_left₀ two_ne_zero (by linarith [hQs.1]) h2
        linarith
      have hg : zeroFeasible (I.cycle.point H) Q e 0 := by
        have hh := hHG'
        unfold zeroFeasible at hh ⊢
        simp only [zeroProjection,Matrix.cons_val_zero,hQy] at hh ⊢
        have ha := mul_le_mul_of_nonneg_right hQa (transport_trig hei).2.2.1
        have hy := mul_nonneg hGy (show 0≤Real.cos e by linarith [(transport_trig hei).1])
        linarith
      exact ⟨e,⟨he,le_rfl⟩,hg,hGAzero ⟨he,le_rfl⟩ hcap⟩
    · have hv : PositiveSmallScalar.V p Y (Θ+e)∈Ioo (2/5 : ℝ) (1/2) :=
        ⟨hVlower,lt_of_not_ge hcap⟩
      have hb := CrossedSmallWrongScalar.root_bounds S hz
        ⟨hv.1.le,hv.2.le⟩
      have hW2 : (SmallWrongScalar.W q p Y (Θ+e))^2=
          q-(1-PositiveSmallScalar.V p Y (Θ+e))^2 := Real.sq_sqrt hb.1.le
      have hGa : (I.cycle.point G).a≤SmallWrongScalar.W q p Y (Θ+e)-1/2 := by
        have hGc := I.necessary.contained G
        change ((I.cycle.point G).a+1/2)^2+(|(I.cycle.point G).y|+1/2)^2≤q at hGc
        rw [abs_of_nonneg hGy] at hGc
        have hy2 := pow_le_pow_left₀
          (show 0≤1-PositiveSmallScalar.V p Y (Θ+e) by linarith [hv.2])
          (show 1-PositiveSmallScalar.V p Y (Θ+e)≤(I.cycle.point G).y+1/2 by linarith) 2
        have h2 : ((I.cycle.point G).a+1/2)^2≤(SmallWrongScalar.W q p Y (Θ+e))^2 := by
          rw [hW2]; linarith
        have h3 := le_of_pow_le_pow_left₀ two_ne_zero
          (show 0≤SmallWrongScalar.W q p Y (Θ+e) from Real.sqrt_nonneg _) h2
        linarith
      have hsource : SmallWrongScalar.demand q p Y Θ e≤(I.cycle.point H).y := by
        have hh := hHG'
        rw [zeroFeasible,edgeWidth_positive_formula hei] at hh
        simp only [zeroProjection,Matrix.cons_val_zero] at hh
        have ha := mul_le_mul_of_nonneg_right hGa (transport_trig hei).2.2.1
        have hy := mul_le_mul_of_nonneg_right
          (show 1/2-PositiveSmallScalar.V p Y (Θ+e)≤(I.cycle.point G).y by linarith)
          (show 0≤Real.cos e by linarith [(transport_trig hei).1])
        simp only [SmallWrongScalar.demand]
        linarith
      obtain ⟨s,hs,hzero,hdemand⟩ := CrossedSmallWrongScalar.zero_contact S
        hΘ he hz hv hHupper hsource
      have hi : s∈Icc 0 frameCap := ⟨hs.1.le,hs.2.trans hei.2⟩
      have hW : SmallWrongScalar.W q p Y (Θ+s)=Real.sqrt (q-1/4) := by
        simp only [SmallWrongScalar.W,hzero]
        norm_num
      have hQa : Q.a=Real.sqrt (q-1/4)-1/2 := by
        simp only [Q,SignedPoint.outerAt,abs_zero]
        norm_num
      have hg : zeroFeasible (I.cycle.point H) Q s 0 := by
        simp only [SmallWrongScalar.demand] at hdemand
        rw [hzero,hW] at hdemand
        rw [zeroFeasible,edgeWidth_positive_formula hi]
        simp only [zeroProjection,Matrix.cons_val_zero,hQy,hQa]
        linarith
      exact ⟨s,hs,hg,hGAzero hs hzero.ge⟩
  obtain ⟨s,hs,hHGQ,hGAQ⟩ := hcandidate
  apply I.wide_small_positive_G_zero_impossible (θ := I.cycle.theta H+s)
    hq hAB hnorm hsmall hTA hAH hTy P Q hPs hPc hPo.le hPy hQo.le hQy
    (by linarith [hs.1])
    (by rw [hΘdef] at hz; linarith [hs.2,hz.2])
  · have hd : I.cycle.theta H+s-I.cycle.theta H=s := by ring
    rw [hd]
    exact hHGQ
  · have hd : I.cycle.theta A-(I.cycle.theta H+s)= -(Θ+s) := by rw [hΘdef]; ring
    rw [hd]
    exact hGAQ

end SignedCycle
end SquaresInCircles.Eight.TableFree

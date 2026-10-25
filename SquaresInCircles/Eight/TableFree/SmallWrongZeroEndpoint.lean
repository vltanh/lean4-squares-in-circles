module

public import SquaresInCircles.Eight.TableFree.SmallWrongScalar
public import SquaresInCircles.Eight.TableFree.SmallPositiveZeroEndpoint

/-!
# A small wrong sign reaches an impossible actual zero endpoint

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

theorem HardOuterGeometry.small_wrong_G_impossible {q : ℝ}
    (I : HardOuterGeometry q) (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hsmall : (I.cycle.point A).y∈Icc (67/200 : ℝ) (1/2))
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
    linarith only [hcharge,hHupper,hGy]
  have hHG : I.cycle.Feasible H 0 := by
    have ho : I.witnesses.owner H=0 ∨ I.witnesses.owner H=2 := by
      simpa [normalOwners,H] using I.witnesses.allowed H
    rcases ho with ho | ho
    · simpa [ho] using I.witnesses.feasible H
    · exact False.elim (not_lt_of_ge hGy (I.zero_signs.HG_canceling ho))
  obtain ⟨Θ,hΘ_def⟩ : ∃ Θ, Θ=I.cycle.theta H-I.cycle.theta A := ⟨_,rfl⟩
  obtain ⟨e,he_def⟩ : ∃ e, e=I.cycle.theta G-I.cycle.theta H := ⟨_,rfl⟩
  have hΘ : 0≤Θ := by rw [hΘ_def]; exact sub_nonneg.mpr hAH
  have he : 0<e := by rw [he_def]; exact sub_pos.mpr hHGorder
  have hz : Θ+e∈Icc 0 frameCap := by
    refine ⟨by linarith only [hΘ,he],?_⟩
    have hspread := (le_abs_self _).trans (I.necessary.spread G A)
    rw [hΘ_def,he_def]
    linarith only [hspread]
  have hei : e∈Icc 0 frameCap := ⟨he.le,by linarith only [hz.2,hΘ]⟩
  obtain ⟨hPs,hPo,hPc⟩ := SignedPoint.outerAt_spec hqL
    (SignedPoint.contained_minor_le_diagonal (I.necessary.sorted A) (I.necessary.contained A))
  obtain ⟨P,hP⟩ : ∃ P, P=SignedPoint.outerAt q (I.cycle.point A).y := ⟨_,rfl⟩
  rw [← hP] at hPs hPo hPc
  have hPy : P.y=(I.cycle.point A).y := by rw [hP]; rfl
  have hAy0 := I.anchors_normal.A_nonneg
  have hPcirc : (P.a+1/2)^2+((I.cycle.point A).y+1/2)^2=q := by
    have h : P.circle=q := hPo
    simp only [SignedPoint.circle,hPy,abs_of_nonneg hAy0] at h
    exact h
  have hPa : (I.cycle.point A).a≤P.a := by
    have hAc : (I.cycle.point A).circle≤q := I.necessary.contained A
    simp only [SignedPoint.circle,abs_of_nonneg hAy0] at hAc
    by_contra! hlt
    have h2 := pow_lt_pow_left₀ (show P.a+1/2<(I.cycle.point A).a+1/2 by linarith only [hlt])
      (show 0≤P.a+1/2 by linarith only [hPs.1]) (by decide : (2:ℕ)≠0)
    linarith only [h2,hAc,hPcirc]
  obtain ⟨p,hp_def⟩ : ∃ p, p=P.a-1/2 := ⟨_,rfl⟩
  obtain ⟨Y,hY_def⟩ : ∃ Y, Y=(I.cycle.point A).y+1/2 := ⟨_,rfl⟩
  have hY : Y∈Icc (167/200 : ℝ) 1 := by
    rw [hY_def]
    constructor <;> linarith only [hsmall.1,hsmall.2]
  have hcircle : (p+1)^2+Y^2=q := by
    rw [hp_def,hY_def]
    linear_combination hPcirc
  have hp : p∈Icc (1/2 : ℝ) (397/500) := by
    have hqL' := hqL
    have hq' := hq
    simp only [qLow,qCap] at hqL' hq'
    have hp1 : 0<p+1 := by
      have := SignedPoint.primary_gt_half hPs hPc
      rw [hp_def]
      linarith only [this]
    constructor
    · have hYsq := pow_le_pow_left₀ (show 0≤Y by linarith only [hY.1]) hY.2 2
      by_contra! hlt
      have := pow_lt_pow_left₀ (show p+1<3/2 by linarith only [hlt]) hp1.le
        (by decide : (2:ℕ)≠0)
      linarith only [this,hYsq,hcircle,hqL']
    · have hYsq := pow_le_pow_left₀ (show (0:ℝ)≤167/200 by norm_num) hY.1 2
      by_contra! hlt
      have := pow_lt_pow_left₀ (show (397/500:ℝ)+1<p+1 by linarith only [hlt])
        (by norm_num) (by decide : (2:ℕ)≠0)
      linarith only [this,hYsq,hcircle,hq']
  have S : PositiveSmallScalar.CapData q p Y := {
    P_mem := hp
    Y_mem := hY
    circle := hcircle.le
    ceiling := hq }
  have hGA : -(I.cycle.point G).y+1/2≤PositiveSmallScalar.V p Y (Θ+e) := by
    have hf : edgeWidth (I.cycle.theta A-I.cycle.theta G)≤
        quarterProjection (I.cycle.point G) (I.cycle.point A)
          (I.cycle.theta A-I.cycle.theta G) 0 := by
      simpa [Feasible,slack,edge,word,delta,next,G,A,sub_nonneg] using I.GA_hard
    have hd : I.cycle.theta A-I.cycle.theta G= -(Θ+e) := by rw [hΘ_def,he_def]; ring
    rw [hd,edgeWidth_negative_formula hz] at hf
    simp only [quarterProjection,Matrix.cons_val_zero,Real.cos_neg,Real.sin_neg] at hf
    have hmul := mul_le_mul_of_nonneg_right hPa (show 0≤Real.cos (Θ+e) by
      linarith [(transport_trig hz).1])
    simp only [PositiveSmallScalar.V]
    rw [hp_def,hY_def]
    linarith only [hf,hmul]
  have hVlower : 2/5<PositiveSmallScalar.V p Y (Θ+e) := by linarith only [hGA,hGsmall]
  have hHG' : zeroFeasible (I.cycle.point H) (I.cycle.point G) e 0 := by
    rw [he_def]
    simpa [Feasible,slack,edge,word,delta,next,H,G,zeroFeasible,sub_nonneg] using hHG
  have hQbound : |(0:ℝ)|≤diagonalCoordinate q := by
    rw [abs_zero]
    linarith only [(uniform_circle_reserves hqL hq).1]
  obtain ⟨hQs,hQo,hQc⟩ := SignedPoint.outerAt_spec hqL hQbound
  obtain ⟨Q,hQ⟩ : ∃ Q, Q=SignedPoint.outerAt q 0 := ⟨_,rfl⟩
  rw [← hQ] at hQs hQo hQc
  have hQy : Q.y=0 := by rw [hQ]; rfl
  have hQa : Q.a=Real.sqrt (q-1/4)-1/2 := by
    rw [hQ]
    simp only [SignedPoint.outerAt,abs_zero,zero_add]
    norm_num
  have hGAzero {s : ℝ} (hs : s∈Ioc 0 e)
      (hV : 1/2≤PositiveSmallScalar.V p Y (Θ+s)) :
      quarterFeasible Q P (-(Θ+s)) 0 := by
    have hi : Θ+s∈Icc 0 frameCap :=
      ⟨by linarith only [hs.1,hΘ],by linarith only [hs.2,hz.2]⟩
    rw [quarterFeasible,edgeWidth_negative_formula hi]
    simp only [quarterProjection,Matrix.cons_val_zero,Real.cos_neg,Real.sin_neg,hQy,hPy]
    simp only [PositiveSmallScalar.V] at hV
    rw [hp_def,hY_def] at hV
    linarith only [hV]
  have hcandidate : ∃s,s∈Ioc 0 e ∧
      zeroFeasible (I.cycle.point H) Q s 0 ∧ quarterFeasible Q P (-(Θ+s)) 0 := by
    by_cases hcap : 1/2≤PositiveSmallScalar.V p Y (Θ+e)
    · have hQa' : (I.cycle.point G).a≤Q.a := by
        have hGc : (I.cycle.point G).circle≤q := I.necessary.contained G
        have hQcircle : Q.circle=q := hQo
        simp only [SignedPoint.circle,abs_of_nonneg hGy,hQy,abs_zero] at hGc hQcircle
        by_contra! hlt
        have h2 := pow_lt_pow_left₀ (show Q.a+1/2<(I.cycle.point G).a+1/2 by linarith only [hlt])
          (show 0≤Q.a+1/2 by linarith only [hQs.1]) (by decide : (2:ℕ)≠0)
        have h3 : (1/2:ℝ)^2≤((I.cycle.point G).y+1/2)^2 :=
          pow_le_pow_left₀ (by norm_num) (by linarith only [hGy]) 2
        linarith only [h2,h3,hGc,hQcircle]
      have hg : zeroFeasible (I.cycle.point H) Q e 0 := by
        have hh := hHG'
        rw [zeroFeasible,edgeWidth_positive_formula hei] at hh ⊢
        simp only [zeroProjection,Matrix.cons_val_zero,hQy,zero_mul,sub_zero] at hh ⊢
        have ha := mul_le_mul_of_nonneg_right hQa' (transport_trig hei).2.2.1
        have hy := mul_nonneg hGy (show 0≤Real.cos e by linarith [(transport_trig hei).1])
        linarith only [hh,ha,hy]
      exact ⟨e,⟨he,le_rfl⟩,hg,hGAzero ⟨he,le_rfl⟩ hcap⟩
    · have hv : PositiveSmallScalar.V p Y (Θ+e)∈Ioo (2/5 : ℝ) (1/2) :=
        ⟨hVlower,lt_of_not_ge hcap⟩
      have hb := SmallWrongScalar.root_bounds S hqL hcircle hz ⟨hv.1.le,hv.2.le⟩
      have hW2 : (SmallWrongScalar.W q p Y (Θ+e))^2=
          q-(1-PositiveSmallScalar.V p Y (Θ+e))^2 := Real.sq_sqrt hb.1.le
      have hGa : (I.cycle.point G).a≤SmallWrongScalar.W q p Y (Θ+e)-1/2 := by
        have hGc : (I.cycle.point G).circle≤q := I.necessary.contained G
        simp only [SignedPoint.circle,abs_of_nonneg hGy] at hGc
        have hy2 := pow_le_pow_left₀
          (show 0≤1-PositiveSmallScalar.V p Y (Θ+e) by linarith only [hv.2])
          (show 1-PositiveSmallScalar.V p Y (Θ+e)≤(I.cycle.point G).y+1/2 by
            linarith only [hGA]) 2
        by_contra! hlt
        have h2 := pow_lt_pow_left₀
          (show SmallWrongScalar.W q p Y (Θ+e)<(I.cycle.point G).a+1/2 by linarith only [hlt])
          (show 0≤SmallWrongScalar.W q p Y (Θ+e) by linarith only [hb.2.1])
          (by decide : (2:ℕ)≠0)
        linarith only [h2,hy2,hGc,hW2]
      have hsource : SmallWrongScalar.demand q p Y Θ e≤(I.cycle.point H).y := by
        have hh := hHG'
        rw [zeroFeasible,edgeWidth_positive_formula hei] at hh
        simp only [zeroProjection,Matrix.cons_val_zero] at hh
        have ha := mul_le_mul_of_nonneg_right hGa (transport_trig hei).2.2.1
        have hy := mul_le_mul_of_nonneg_right
          (show 1/2-PositiveSmallScalar.V p Y (Θ+e)≤(I.cycle.point G).y by linarith only [hGA])
          (show 0≤Real.cos e by linarith [(transport_trig hei).1])
        simp only [SmallWrongScalar.demand]
        linarith only [hh,ha,hy]
      obtain ⟨s,hs,hzero,hdemand⟩ := SmallWrongScalar.zero_contact S hqL hcircle
        hΘ he hz hv hHupper hsource
      have hi : s∈Icc 0 frameCap := ⟨hs.1.le,hs.2.trans hei.2⟩
      have hW : SmallWrongScalar.W q p Y (Θ+s)=Real.sqrt (q-1/4) := by
        simp only [SmallWrongScalar.W,hzero]
        norm_num
      have hg : zeroFeasible (I.cycle.point H) Q s 0 := by
        simp only [SmallWrongScalar.demand] at hdemand
        rw [hzero,hW] at hdemand
        rw [zeroFeasible,edgeWidth_positive_formula hi]
        simp only [zeroProjection,Matrix.cons_val_zero,hQy,zero_mul,sub_zero,hQa]
        linarith only [hdemand]
      exact ⟨s,hs,hg,hGAzero hs hzero.ge⟩
  obtain ⟨s,hs,hHGQ,hGAQ⟩ := hcandidate
  apply I.small_positive_G_zero_impossible (θ := I.cycle.theta H+s)
    hq hAB hnorm hsmall hTA hAH hTy P Q hPs hPc hPo.le hPy hQo.le hQy
    (by linarith only [hs.1])
    (by linarith only [hs.2,hz.2,hΘ_def])
  · rw [show I.cycle.theta H+s-I.cycle.theta H=s by ring]
    exact hHGQ
  · rw [show I.cycle.theta A-(I.cycle.theta H+s)= -(Θ+s) by rw [hΘ_def]; ring]
    exact hGAQ

end SignedCycle
end SquaresInCircles.Eight.TableFree

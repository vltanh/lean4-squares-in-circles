module

public import SquaresInCircles.Eight.Corners.GeometricStationaryExistence
public import SquaresInCircles.Eight.Owners.Canonical.NominalFlux
public import SquaresInCircles.Eight.Owners.Stationary.CanonicalRigidity

/-!
# Eight squares: the complete canonical five-anchor sharp theorem

The original inequalities first localize
the tilt.  The geometric existence theorem supplies the stationary
radius bounds.  Thus neither a local stationary enclosure nor an
assumed terminal tilt interval remains in these exports.
-/

section
/-!
## The nominal two-error remainder on both complete tilt tails

The original nominal weights retain the
first-order gains of both nonnegative errors.  Above sine 3/50 the
whole correction is nonnegative.  Below that cut its possible loss is
at most 3/2 times the squared total error.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CanonicalNominal
open CanonicalNegativeStress CanonicalNegativeCorrection

theorem ordinary_short_lower {b k t : ℝ}
    (hb : b∈Icc 0 (1:ℝ)) (hk : k∈Icc 0 (6/5:ℝ))
    (ht : t∈Icc 0 (3/200:ℝ)) :
    k*t-(51/100)*t^2≤b*(Real.cos t-1)+k*Real.sin t := by
  have hh := ordinary_turn_lower ht.1 hb hk
  have ht3 : t^3≤(3/200)*t^2 := by
    have hp := mul_le_mul_of_nonneg_right ht.2 (sq_nonneg t)
    nlinarith
  nlinarith [sq_nonneg t]

theorem secant_short_lower {b γ e : ℝ}
    (hb : b∈Icc 0 (1:ℝ)) (hγ : γ∈Icc 0 (3/2:ℝ))
    (he : e∈Icc 0 (3/200:ℝ)) :
    b*(13/12)*e-(77/100)*e^2≤
      b*(1/Real.cos e-1)+b*(13/12)*Real.tan e-
        (γ/2)*((1/Real.cos e)^2-1) := by
  obtain ⟨hc,hv,hvu,hd,hdu,hv2,hv2u,htan⟩ := short_secant_bounds he
  have hsec := mul_nonneg hb.1 hd
  have htan' := mul_le_mul_of_nonneg_left htan
    (mul_nonneg hb.1 (by norm_num : (0:ℝ)≤13/12))
  have hlast := mul_le_mul hγ.2 hv2u hv2 (by norm_num : (0:ℝ)≤3/2)
  have hb3 := mul_le_mul_of_nonneg_right hb.2 (pow_nonneg he.1 3)
  have he3 : e^3≤(3/200)*e^2 := by
    have hp := mul_le_mul_of_nonneg_right he.2 (sq_nonneg e)
    nlinarith
  nlinarith [sq_nonneg e]

theorem correction_lower {α t e : ℝ}
    (hα : α∈Icc 0 (27/100:ℝ))
    (ht : 0≤t) (he : 0≤e) (hr : t+e≤3/200) :
    (Real.sin α/2)*t+(1/25)*e-(7/10)*(t+e)^2-
      (51/100)*t^2-(77/100)*e^2≤correction (atTilt α) α t e := by
  have hs := (short_trig hα).1
  have hb := beta_bounds hs
  have hb' : (atTilt α).beta∈Icc 0 (1:ℝ) := ⟨le_trans (by norm_num) hb.1,hb.2⟩
  have hk : KB (atTilt α)∈Icc (0:ℝ) (6/5) := KB_bounds hs
  have hγ : (atTilt α).beta^2/(2*(atTilt α).mu 2)∈Icc (0:ℝ) (3/2) := gamma_bounds hs
  have hflux := (flux_bounds hα).1
  have hamp := amplitude_bounds hα
  have hA := mixed_turn_lower (omega:=1) (k:=KA (atTilt α)) (α:=α) (L:=7/5)
    (show 0≤t+e by linarith) hflux
    (by simpa only [one_mul] using hamp.1)
    (by simpa only [one_mul] using hamp.2)
  have hB := ordinary_short_lower hb' hk (show t∈Icc 0 (3/200:ℝ) from ⟨ht,by linarith⟩)
  have hD := secant_short_lower hb' hγ (show e∈Icc 0 (3/200:ℝ) from ⟨he,by linarith⟩)
  have hDcoef : ((atTilt α).beta^2/(2*(atTilt α).mu 2))/2=
      (atTilt α).beta^2/(4*(atTilt α).mu 2) := by
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [hDcoef] at hD
  have hsmall := mul_le_mul_of_nonneg_right (small_error_reserve hα) ht
  have hsecant := mul_le_mul_of_nonneg_right (secant_error_reserve hα) he
  rw [show α-(t+e)=α-t-e by ring] at hA
  have homega : (atTilt α).omega=1 := rfl
  dsimp only [flux] at hsmall hsecant
  rw [homega] at hsmall hsecant
  dsimp only [correction]
  rw [homega]
  linarith

theorem correction_nonneg {α t e : ℝ}
    (hα : α∈Icc 0 (27/100:ℝ)) (hs : 3/50≤Real.sin α)
    (ht : 0≤t) (he : 0≤e) (hr : t+e≤3/200) :
    0≤correction (atTilt α) α t e := by
  have hb := correction_lower hα ht he hr
  have hs' := mul_le_mul_of_nonneg_right hs ht
  have hte := mul_nonneg ht he
  have htt : t^2≤(t+e)*t := by nlinarith
  have hee : e^2≤(t+e)*e := by nlinarith
  have hrt := mul_le_mul_of_nonneg_right hr ht
  have hre := mul_le_mul_of_nonneg_right hr he
  nlinarith

theorem correction_rough_lower {α t e : ℝ}
    (hα : α∈Icc 0 (27/100:ℝ))
    (ht : 0≤t) (he : 0≤e) (hr : t+e≤3/200) :
    -(3/2)*(t+e)^2≤correction (atTilt α) α t e := by
  have hb := correction_lower hα ht he hr
  have hsin := mul_nonneg (div_nonneg (short_trig hα).1.1 (by norm_num : (0:ℝ)≤2)) ht
  have hte := mul_nonneg ht he
  nlinarith [sq_nonneg t,sq_nonneg e,sq_nonneg (t+e)]

end SquaresInCircles.Eight.CanonicalNominal
end
end
end

section
/-!
## The two canonical tilt tails are impossible

The five weak contacts make the nominal two-error scalar nonpositive, while the polynomial on the
whole arc and the error gains make it positive on either tail (`polynomial_small_lower`,
`tail_defect_positive`). So the tilt of a five-anchor system with errors `t + e ≤ 3/200` lies in
the terminal strip `(1/10, 4/25)` (`five_anchor_tilt_range`); only the circle inequalities of the
five anchors are used.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CanonicalNominal
open Eight.FiveCorner CanonicalNegativeStress

theorem polynomial_small_lower {s : ℝ} (hs : s∈Icc 0 (3/50:ℝ)) :
    1/1000<Nominal.polynomial s := by
  have hmono : AntitoneOn Nominal.polynomial (Icc 0 (3/50)) :=
    antiOn_of_hasDeriv_nonpos
      (fun x _ => (Nominal.polynomial_derivative x).continuousAt.continuousWithinAt)
      (fun x _ => Nominal.polynomial_derivative x) (fun x hx => by
        dsimp [Nominal.polynomialD]
        nlinarith [hx.2,sq_nonneg x,pow_nonneg hx.1.le 3,pow_nonneg hx.1.le 4])
  have hp : (1/1000:ℝ)<Nominal.polynomial (3/50) := by norm_num [Nominal.polynomial]
  exact hp.trans_le (hmono hs (by norm_num) hs.2)

theorem tail_defect_positive {q α t e : ℝ}
    (hq : q≤Nominal.ceiling) (hα : α∈Icc 0 (27/100:ℝ)) (hαpos : 0<α)
    (ht : 0≤t) (he : 0≤e) (hr : t+e≤3/200)
    (htail : Real.sin α≤1/10 ∨ 79/500≤Real.sin α) :
    0<CanonicalNegativeStress.defect q (atTilt α) α t (α-t-e) e := by
  have hs := (short_trig hα).1
  have hspos := Real.sin_pos_of_pos_of_lt_pi hαpos
    (by linarith [hα.2,Real.pi_gt_three])
  have hw := positive hs hspos
  have hm : ∀i,(atTilt α).mu i≠0 := fun i => (hw.2.2.2.2.2 i).ne'
  have hquarter : α∈Icc 0 (Real.pi/4) :=
    ⟨hα.1,by linarith [hα.2,Real.pi_gt_three]⟩
  have hgap := Nominal.gap_ge_polynomial hq hquarter hs
  rw [defect_difference hm,baseline_gap]
  by_cases hsmall : Real.sin α≤3/50
  · have hp := polynomial_small_lower ⟨hs.1,hsmall⟩
    have hc := correction_rough_lower hα ht he hr
    have hr2 := pow_le_pow_left₀ (show 0≤t+e by linarith) hr 2
    nlinarith
  · have hc := correction_nonneg hα (by linarith) ht he hr
    have hp : 0<Nominal.polynomial (Real.sin α) := by
      rcases htail with hleft | hright
      · exact Nominal.polynomial_left_positive ⟨hs.1,hleft⟩
      · exact Nominal.polynomial_right_positive ⟨hright,hs.2⟩
    linarith

/-- The necessary five-anchor system forces its tilt `α` into the terminal strip
`1/10 < α < 4/25`. -/
theorem five_anchor_tilt_range {H A B D E : SignedPoint} {q α t e : ℝ}
    (hq : q≤Nominal.ceiling) (hα : α∈Icc 0 (27/100:ℝ)) (hαpos : 0<α)
    (ht : 0≤t) (he : 0≤e) (hr : t+e≤3/200)
    (hyH : 0≤H.y) (hyA : 0≤A.y) (hyB : 0≤B.y) (hyD : 0≤D.y) (hyE : 0≤E.y)
    (hc : ∀i : Fin 5,(![A,B,D,E,H] i).Contained q)
    (hHA : 1+W (α-t-e)≤H.y+A.a*Real.cos (α-t-e)-A.y*Real.sin (α-t-e))
    (hAB : 1≤A.y+B.y)
    (hBD : W t+1/2+1/(2*Real.cos e)+(13/12)*Real.tan e≤
      D.y/Real.cos e+B.a*Real.cos t-B.y*Real.sin t)
    (hDE : 1≤D.a+E.y)
    (hEH : W α≤H.a+E.a*Real.sin α-E.y*Real.cos α) :
    α∈Ioo (1/10:ℝ) (4/25) := by
  have hs := (short_trig hα).1
  have hspos := Real.sin_pos_of_pos_of_lt_pi hαpos
    (by linarith [hα.2,Real.pi_gt_three])
  have hw : (atTilt α).Positive := positive hs hspos
  have hsource := original_circle_inequality (q:=q) hw
    hyH hyA hyB hyD hyE hHA hAB hBD hDE hEH
  have hcenter := centerLoss_nonneg hw ![A,B,D,E,H] α t (α-t-e) e
  have hcircle := circleLoss_nonneg hw hc
  have hnonpos : CanonicalNegativeStress.defect q (atTilt α) α t (α-t-e) e≤0 := by
    linarith
  have hslow : 1/10<Real.sin α := by
    by_contra! hbad
    have hp := tail_defect_positive hq hα hαpos ht he hr (Or.inl hbad)
    linarith
  have hsup : Real.sin α<79/500 := by
    by_contra! hbad
    have hp := tail_defect_positive hq hα hαpos ht he hr (Or.inr hbad)
    linarith
  constructor
  · linarith [Real.sin_le hα.1]
  · by_contra! hbad
    have hmono : Real.sin (4/25:ℝ)≤Real.sin α :=
      Real.sin_le_sin_of_le_of_le_pi_div_two
        (by linarith [Real.pi_pos]) (by linarith [hα.2,Real.pi_gt_three]) hbad
    have hsin := Real.sin_ge_sub_cube (by norm_num : (0:ℝ)≤4/25)
    nlinarith

end SquaresInCircles.Eight.CanonicalNominal
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CanonicalNegativeSharp
open Stationary.FiveCornerGeometry CanonicalNegativeStress StationaryTerminal

theorem five_anchor_rigidity {d : Stationary.Coordinates} (hd : d.IsStationary)
    {H A B D E : SignedPoint} {q α t e : ℝ}
    (hqq : q≤d.q) (hαpos : 0<α) (hαmax : α≤27/100)
    (ht : 0≤t) (he : 0≤e) (hr : t+e≤3/200) (hu : t+e≤α)
    (hyH : 0≤H.y) (hyA : 0≤A.y) (hyB : 0≤B.y) (hyD : 0≤D.y) (hyE : 0≤E.y)
    (hc : ∀i : Fin 5,(![A,B,D,E,H] i).Contained q)
    (hHA : 1+W (α-t-e)≤H.y+A.a*Real.cos (α-t-e)-A.y*Real.sin (α-t-e))
    (hAB : 1≤A.y+B.y)
    (hBD : W t+1/2+1/(2*Real.cos e)+(13/12)*Real.tan e≤
      D.y/Real.cos e+B.a*Real.cos t-B.y*Real.sin t)
    (hDE : 1≤D.a+E.y)
    (hEH : W α≤H.a+E.a*Real.sin α-E.y*Real.cos α) :
    q=d.q ∧ t=0 ∧ e=0 ∧ α=coordinateAngle d ∧
      (∀i : Fin 5,(![A,B,D,E,H] i).circle=d.q) ∧
      ![A,B,D,E,H]=nominalPoints d.q (-d.y) (Real.tan (coordinateAngle d)) := by
  have hq : q≤qTrial := hqq.trans (GeometricExistence.stationary_radius_ceiling hd).le
  have htilt := CanonicalNominal.five_anchor_tilt_range hq ⟨hαpos.le,hαmax⟩ hαpos
    ht he hr hyH hyA hyB hyD hyE hc hHA hAB hBD hDE hEH
  exact stationary_rigidity hd (GeometricExistence.stationary_radius_strip hd)
    hqq ⟨htilt.1.le,htilt.2.le⟩ ht he hr hu hyH hyA hyB hyD hyE hc hHA hAB hBD hDE hEH

end SquaresInCircles.Eight.CanonicalNegativeSharp
end
end
end

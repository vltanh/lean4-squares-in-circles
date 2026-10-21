module

public import SquaresInCircles.Eight.TableFree.CanonicalNominalCorrection

/-!
# Both complete canonical tilt tails are impossible

Uncompiled reconstruction.  The original five weak contacts make the
same nominal two-error scalar nonpositive.  The whole-arc polynomial
and the retained error gains make it strictly positive on either tail.
Only the five original anchor circle inequalities are used.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.CanonicalNominal
open GeometricModel.FiveCorner CanonicalNegativeStress

theorem polynomial_small_lower {s : ℝ} (hs : s∈Icc 0 (3/50:ℝ)) :
    1/1000<Nominal.polynomial s := by
  have hmono : AntitoneOn Nominal.polynomial (Icc 0 (3/50)) :=
    antiOn_of_hasDeriv_nonpos (by dsimp [Nominal.polynomial]; fun_prop)
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

/-- The complete necessary five-anchor system forces the original tilt
into the terminal strip.  No point is moved in this statement. -/
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
  have hw := positive hs hspos
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

end SquaresInCircles.Eight.TableFree.CanonicalNominal

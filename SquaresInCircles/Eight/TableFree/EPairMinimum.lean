module

public import SquaresInCircles.Eight.TableFree.CoreECharge

/-!
# The original E-pair minimum for nonnegative total error

Uncompiled source draft. The E frame may lie between or outside the two
endpoint frames, and its signed tangent may have either sign. The same
first-harmonic calculation applies to every actual sorted E point under
the coarse circle cap, including outer and core points.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.EPairMinimum
open CoreECharge

def J (a b e : ℝ) : ℝ :=
  (a-1/2)*Real.sin e+(|b|+1/2)*(1-Real.cos e)

theorem coefficients {a b e : ℝ} (ha : 1/2≤a ∧ a≤283/200)
    (hb : 0≤b ∧ b≤9/10) (he : e∈Icc 0 frameCap) :
    0≤cosineCoefficient a b e ∧ cosineCoefficient a b e≤1 ∧
    0≤ sameSineCoefficient a b e ∧
    (11/20)*(frameCap-e)≤oppositeSineCoefficient a b e := by
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig he
  have hloss := sub_nonneg.mpr hc1
  have h1 := mul_le_mul_of_nonneg_right (show b+1/2≤(7/5 : ℝ) by linarith) hloss
  have h2 := mul_le_mul_of_nonneg_right (show a-1/2≤(183/200 : ℝ) by linarith) hs0
  have h3 := mul_nonneg (show 0≤1/2+b by linarith) hloss
  have h4 := mul_nonneg (show 0≤a-1/2 by linarith) hs0
  have he' : 0≤e ∧ e≤4/5 := ⟨he.1,by dsimp [frameCap] at he; linarith [he.2]⟩
  have hhalf := halfRatio_upper he'
  have hhalf' : halfRatio e≤77/200 := by dsimp [frameCap] at he; linarith [he.2]
  have hhalfprod := mul_le_mul_of_nonneg_right hhalf' hs0
  rw [(halfRatio_identities he').2] at hhalfprod
  have h5 := mul_le_mul_of_nonneg_right (show a-1/2≤(183/200 : ℝ) by linarith) hloss
  have h6 := mul_le_mul_of_nonneg_right (show (1/2 : ℝ)≤1/2+b by linarith) hs0
  have h7 := mul_le_mul_of_nonneg_right (show 1/2+b≤(7/5 : ℝ) by linarith) hs0
  have h8 := mul_nonneg (show 0≤a-1/2 by linarith) hloss
  have hsin := Real.sin_le he.1
  dsimp [cosineCoefficient,sameSineCoefficient,oppositeSineCoefficient,frameCap]
  exact ⟨by nlinarith,by nlinarith,by nlinarith,by nlinarith [he.2]⟩

theorem same_sign_minimum {a b e u : ℝ} (ha : 1/2≤a ∧ a≤283/200)
    (hb : 0≤b ∧ b≤9/10) (he : e∈Icc 0 frameCap) (hu : u∈Icc 0 e) :
    ehCharge a b e≤pairDeficit a b u (e-u) := by
  have hc := coefficients ha hb he
  have he2 : e≤7/10 := he.2
  have hconc : ConcaveOn ℝ (Icc 0 e)
      (harmonic (cosineCoefficient a b e) (sameSineCoefficient a b e)) := by
    apply harmonic_concave
    intro t ht
    exact harmonic_nonneg hc.1 hc.2.2.1
      ⟨ht.1,by linarith [ht.2,Real.pi_gt_three]⟩
  have hmin := hconc.min_le_of_mem_Icc (left_mem_Icc.mpr he.1)
    (right_mem_Icc.mpr he.1) hu
  have hend := same_endpoint_comparison (a := a) (e := e) hb.1
  have h0 : harmonic (cosineCoefficient a b e) (sameSineCoefficient a b e) 0=
      cosineCoefficient a b e := by simp [harmonic]
  rw [h0,min_eq_left hend] at hmin
  rw [same_harmonic_identity he hu]
  have hq : ehCharge a b e=cosineCoefficient a b e-1 := by
    dsimp [ehCharge,cosineCoefficient]; ring
  linarith

theorem opposite_endpoint {a b e : ℝ} (ha : 1/2≤a ∧ a≤283/200)
    (hb : 0≤b ∧ b≤9/10) (he : e∈Icc 0 frameCap) :
    cosineCoefficient a b e≤
      harmonic (cosineCoefficient a b e) (oppositeSineCoefficient a b e) (frameCap-e) := by
  have hc := coefficients ha hb he
  have hw : frameCap-e∈Icc 0 frameCap := ⟨by linarith [he.2],by linarith [he.1]⟩
  have hangle : 0≤frameCap-e ∧ frameCap-e≤4/5 := by
    constructor <;> dsimp [frameCap] at * <;> linarith [hw.1,hw.2]
  have hratio := halfRatio_upper hangle
  have hid := (halfRatio_identities hangle).2
  have hs := (transport_trig hw).2.2.1
  have h1 := mul_le_mul_of_nonneg_right hratio hs
  have h2 := mul_le_mul_of_nonneg_right hc.2.2.2 hs
  have h3 := mul_le_mul_of_nonpos_right hc.2.1
    (show Real.cos (frameCap-e)-1≤0 by linarith [Real.cos_le_one (frameCap-e)])
  dsimp [harmonic]
  nlinarith

theorem opposite_minimum {a b e n : ℝ} (ha : 1/2≤a ∧ a≤283/200)
    (hb : 0≤b ∧ b≤9/10) (he : e∈Icc 0 frameCap)
    (hn : n∈Icc 0 (frameCap-e)) :
    ehCharge a b e≤pairDeficit a b (-n) (e+n) := by
  have hc := coefficients ha hb he
  have hlen : 0≤frameCap-e := by linarith [he.2]
  have hB : 0≤oppositeSineCoefficient a b e := by
    have hh : 0≤(11/20 : ℝ)*(frameCap-e) := mul_nonneg (by norm_num) hlen
    exact hh.trans hc.2.2.2
  have he1 : 0≤e := he.1
  have hn2 : n≤7/10-e := hn.2
  have hconc : ConcaveOn ℝ (Icc 0 (frameCap-e))
      (harmonic (cosineCoefficient a b e) (oppositeSineCoefficient a b e)) := by
    apply harmonic_concave
    intro t ht
    have ht2 : t≤7/10-e := ht.2
    exact harmonic_nonneg hc.1 hB
      ⟨ht.1,by linarith [Real.pi_gt_three]⟩
  have hmin := hconc.min_le_of_mem_Icc (left_mem_Icc.mpr hlen)
    (right_mem_Icc.mpr hlen) hn
  have hend := opposite_endpoint ha hb he
  have h0 : harmonic (cosineCoefficient a b e) (oppositeSineCoefficient a b e) 0=
      cosineCoefficient a b e := by simp [harmonic]
  rw [h0,min_eq_left hend] at hmin
  rw [opposite_harmonic_identity he hn]
  have hq : ehCharge a b e=cosineCoefficient a b e-1 := by
    dsimp [ehCharge,cosineCoefficient]; ring
  linarith

theorem nonnegative_tangent_minimum {a b u v : ℝ} (ha : 1/2≤a ∧ a≤283/200)
    (hb : 0≤b ∧ b≤9/10) (hu : |u|≤frameCap) (hv : |v|≤frameCap)
    (he : u+v∈Icc 0 frameCap) : ehCharge a b (u+v)≤pairDeficit a b u v := by
  by_cases hu0 : 0≤u
  · by_cases hv0 : 0≤v
    · simpa using same_sign_minimum ha hb he (show u∈Icc 0 (u+v) by constructor <;> linarith)
    · have hn : -v∈Icc 0 (frameCap-(u+v)) := by
        constructor
        · linarith
        · linarith [(le_abs_self u).trans hu]
      have hh := opposite_minimum ha hb he hn
      have hs := pair_swap_comparison (a := a) hb.1 he hn
      have h1 : -(-v)=v := by ring
      have h2 : u+v+-v=u := by ring
      simpa only [h1,h2] using hh.trans hs
  · have hn : -u∈Icc 0 (frameCap-(u+v)) := by
      constructor
      · linarith
      · linarith [(le_abs_self v).trans hv]
    have hh := opposite_minimum ha hb he hn
    have h1 : -(-u)=u := by ring
    have h2 : u+v+-u=v := by ring
    simpa only [h1,h2] using hh

theorem signed_minimum {a b u v : ℝ} (ha : 1/2≤a ∧ a≤283/200)
    (hb : |b|≤9/10) (hu : |u|≤frameCap) (hv : |v|≤frameCap)
    (he : u+v∈Icc 0 frameCap) : -J a b (u+v)≤pairDeficit a b u v := by
  by_cases hb0 : 0≤b
  · have hh := nonnegative_tangent_minimum ha ⟨hb0,by simpa [abs_of_nonneg hb0] using hb⟩ hu hv he
    dsimp [J,ehCharge] at *
    rw [abs_of_nonneg hb0]
    linarith
  · have hb0' : b≤0 := (lt_of_not_ge hb0).le
    have hh := nonnegative_tangent_minimum (b := -b) ha
      ⟨by linarith,by simpa [abs_of_nonpos hb0'] using hb⟩ hv hu
      (show v+u∈Icc 0 frameCap by simpa [add_comm] using he)
    have heq : pairDeficit a (-b) v u=pairDeficit a b u v := by dsimp [pairDeficit]; ring
    rw [heq] at hh
    dsimp [J,ehCharge] at *
    rw [abs_of_nonpos hb0']
    simp only [add_comm v u] at hh
    linarith

theorem actual_positive_total {q u v : ℝ} {H D E : SignedPoint}
    (hEs : E.Sorted) (hEc : E.AvoidsCore) (hEcont : E.Contained q) (hq : q≤qCap)
    (hu : |u|≤frameCap) (hv : |v|≤frameCap) (he : u+v∈Icc 0 frameCap)
    (hDE : quarterFeasible D E u 3) (hEH : quarterFeasible E H v 1) :
    2-J E.a E.y (u+v)≤H.a+D.a := by
  have hb := SignedPoint.coordinate_bounds hEs hEc hEcont hq
  have ha := SignedPoint.primary_gt_half hEs hEc
  have hmin := signed_minimum ⟨ha.le,hb.2.1.le⟩
    (show |-E.y|≤9/10 by simpa using hb.2.2.le) hu hv he
  have hDE' : edgeWidth u≤D.a+E.a*Real.sin u-E.y*Real.cos u := by
    simpa [quarterFeasible,quarterProjection] using hDE
  have hEH' : edgeWidth v≤H.a+E.a*Real.sin v+E.y*Real.cos v := by
    simpa [quarterFeasible,quarterProjection] using hEH
  dsimp [J,pairDeficit] at *
  simp only [abs_neg] at hmin
  linarith

end SquaresInCircles.Eight.TableFree.EPairMinimum

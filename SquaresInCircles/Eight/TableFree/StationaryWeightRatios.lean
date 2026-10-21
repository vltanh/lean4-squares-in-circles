module

public import SquaresInCircles.Eight.TableFree.StationaryBetaBounds

/-!
# Exact force ratios and the first strict terminal reserve

Uncompiled reconstruction.  The normalized masses cancel in the three
quadratic coefficients.  Their bounds and the small-error flux reserve
then follow from the actual circle rectangle and the position equation.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.StationaryTerminal
open ExactFamily.FiveCornerGeometry StationaryPrimitives CanonicalNegativeStress

theorem coefficient_identities {q u h : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hu : u∈Icc (179/200:ℝ) (47/50))
    (hh : h∈Icc (1/10:ℝ) (41/250)) :
    (weights q u h).a=(weights q u h).beta*(2-u)/topRight q u ∧
    KA (weights q u h)=(weights q u h).a*lowerRight q u/cosine h ∧
    KB (weights q u h)=(weights q u h).beta*(2-u) ∧
    (weights q u h).beta^2/(2*(weights q u h).mu 2)=
      (weights q u h).beta*topLeft q u := by
  have hr := radical_bounds hq hu
  have hf := force_bounds hq hu hh
  have hL : 2-u≠0 := ne_of_gt (by linarith [hu.2])
  have hR : lowerRight q u≠0 := ne_of_gt (by linarith [hr.r_lower])
  have hU : topRight q u≠0 := ne_of_gt (by linarith [hr.U_lower])
  have hV : topLeft q u≠0 := ne_of_gt (by linarith [hr.V_lower])
  have hC : cosine h≠0 := (cosine_pos h).ne'
  have hA : rawAlpha q u h≠0 := ne_of_gt (by dsimp [rawAlpha]; linarith [hf.a_lower])
  have hB : rawBeta q u h≠0 := (rawBeta_pos hq hu hh).ne'
  have hO : omega q u h≠0 := ne_of_gt (by linarith [(omega_bounds hq hu hh).1])
  refine ⟨?_,?_,?_,?_⟩
  · dsimp [weights,rawBeta]
    field_simp [hL,hU]
    ring
  · dsimp [KA,weights,rawMass]
    field_simp [hO,hR,hC]
    ring
  · dsimp [KB,weights,rawMass]
    field_simp [hO,hA,hL]
    ring
  · dsimp [weights,rawMass]
    field_simp [hO,hB,hV]
    ring

theorem alpha_bound {q u h : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hu : u∈Icc (179/200:ℝ) (47/50))
    (hh : h∈Icc (1/10:ℝ) (41/250))
    (hz : positionHalf q (cosine h) (sine h) u=0) :
    0≤(weights q u h).a ∧ (weights q u h).a<263/500 := by
  have hr := radical_bounds hq hu
  have hl : 2-u∈Icc (53/50:ℝ) (221/200) := ⟨by linarith [hu.2],by linarith [hu.1]⟩
  have hratio := quotient_bounds hl hr.U (by norm_num) (by norm_num)
  have hratio' : (2-u)/topRight q u∈Icc 0 (337/500:ℝ) :=
    ⟨by linarith [hratio.1],by linarith [hratio.2]⟩
  have hb := beta_bounds hq hu hh hz
  have hp := product_bounds ⟨by linarith [hb.1],hb.2.le⟩ hratio' (by norm_num) (by norm_num)
  rw [(coefficient_identities hq hu hh).1]
  constructor <;> nlinarith [hp.1,hp.2]

theorem correction_coefficients {q u h : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hu : u∈Icc (179/200:ℝ) (47/50))
    (hh : h∈Icc (1/10:ℝ) (41/250))
    (hz : positionHalf q (cosine h) (sine h) u=0) :
    (weights q u h).omega∈Icc 0 (4/5:ℝ) ∧
    KA (weights q u h)∈Icc 0 (471/500:ℝ) ∧
    (weights q u h).beta∈Icc 0 (39/50:ℝ) ∧
    KB (weights q u h)∈Icc 0 (431/500:ℝ) ∧
    (weights q u h).beta^2/(2*(weights q u h).mu 2)∈Icc 0 (6/5:ℝ) := by
  have hr := radical_bounds hq hu
  have ht := trig_bounds hh
  have ho := omega_bounds hq hu hh
  have ha := alpha_bound hq hu hh hz
  have hb := beta_bounds hq hu hh hz
  have hbc : (weights q u h).beta∈Icc 0 (39/50:ℝ) := ⟨by linarith [hb.1],hb.2.le⟩
  have hl : 2-u∈Icc (53/50:ℝ) (221/200) := ⟨by linarith [hu.2],by linarith [hu.1]⟩
  obtain ⟨_,hKA,hKB,hgamma⟩ := coefficient_identities hq hu hh
  have hrc := quotient_bounds hr.r ht.c (by norm_num) (by norm_num)
  have hA := product_bounds ⟨ha.1,ha.2.le⟩ hrc (by norm_num) (by norm_num)
  have hB := product_bounds hbc hl (by norm_num) (by norm_num)
  have hD := product_bounds hbc hr.V (by norm_num) (by norm_num)
  refine ⟨⟨by change 0≤omega q u h; linarith [ho.1],ho.2.le⟩,?_,hbc,?_,?_⟩
  · rw [hKA]
    constructor <;> nlinarith [hA.1,hA.2]
  · rw [hKB]
    exact ⟨by linarith [hB.1],by linarith [hB.2]⟩
  · rw [hgamma]
    exact ⟨by linarith [hD.1],by linarith [hD.2]⟩

theorem flux_formula {q u h : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hu : u∈Icc (179/200:ℝ) (47/50))
    (hh : h∈Icc (1/10:ℝ) (41/250)) :
    flux (weights q u h) (Real.arctan h)=
      omega q u h*(cosine h*u+sine h*(lowerRight q u-1)) := by
  have hr := radical_bounds hq hu
  have hR : lowerRight q u≠0 := ne_of_gt (by linarith [hr.r_lower])
  have hC : cosine h≠0 := (cosine_pos h).ne'
  rw [flux,(coefficient_identities hq hu hh).2.1]
  change (omega q u h*rawAlpha q u h*lowerRight q u/cosine h)*cosine h-
    omega q u h*sine h=_
  dsimp [rawAlpha,positionA]
  field_simp [hR,hC]
  ring

theorem flux_pos {q u h : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hu : u∈Icc (179/200:ℝ) (47/50))
    (hh : h∈Icc (1/10:ℝ) (41/250)) :
    0<flux (weights q u h) (Real.arctan h) := by
  have hr := radical_bounds hq hu
  have ht := trig_bounds hh
  rw [flux_formula hq hu hh]
  apply mul_pos (by linarith [(omega_bounds hq hu hh).1])
  exact add_pos (mul_pos (cosine_pos h) (by linarith [hu.1]))
    (mul_pos (by linarith [ht.s_lower]) (by linarith [hr.r_lower]))

theorem small_reserve_identity {q u h : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hu : u∈Icc (179/200:ℝ) (47/50))
    (hh : h∈Icc (1/10:ℝ) (41/250)) :
    KB (weights q u h)-flux (weights q u h) (Real.arctan h)=
      omega q u h*(sine h-rawAlpha q u h*(lowerRight q u-topRight q u)) := by
  have hr := radical_bounds hq hu
  have hL : 2-u≠0 := ne_of_gt (by linarith [hu.2])
  have hR : lowerRight q u≠0 := ne_of_gt (by linarith [hr.r_lower])
  rw [(coefficient_identities hq hu hh).2.2.1,flux_formula hq hu hh]
  dsimp [weights,rawBeta,rawAlpha,positionA]
  field_simp [hL,hR]
  ring

/-- This reserve uses the whole rectangle only; it remains strict even
before imposing the narrower affine strip. -/
theorem small_reserve {q u h : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hu : u∈Icc (179/200:ℝ) (47/50))
    (hh : h∈Icc (1/10:ℝ) (41/250)) :
    3367/250000<KB (weights q u h)-flux (weights q u h) (Real.arctan h) := by
  have hr := radical_bounds hq hu
  have ht := trig_bounds hh
  have hf := force_bounds hq hu hh
  have hcur := quotient_bounds (product_bounds ht.c hu (by norm_num) (by norm_num)) hr.r
    (by norm_num) (by norm_num)
  have hcurU : cosine h*u/lowerRight q u<27/50 := by linarith [hcur.2]
  have hdelta : lowerRight q u-topRight q u<31/250 := by linarith [hr.r_upper,hr.U_lower]
  have ha : 0<rawAlpha q u h := by dsimp [rawAlpha]; linarith [hf.a_lower]
  have hp := mul_lt_mul_of_pos_left hdelta ha
  have hbase : 10101/500000<sine h-(31/250)*rawAlpha q u h := by
    dsimp [rawAlpha,positionA]
    linarith [ht.s_lower]
  have hinner : 10101/500000<
      sine h-rawAlpha q u h*(lowerRight q u-topRight q u) := by linarith
  have ho := (omega_bounds hq hu hh).1
  have hprod := mul_lt_mul_of_pos_left hinner (by linarith : 0<omega q u h)
  rw [small_reserve_identity hq hu hh]
  nlinarith

end SquaresInCircles.Eight.TableFree.StationaryTerminal

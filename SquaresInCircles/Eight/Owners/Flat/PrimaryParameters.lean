module

public import SquaresInCircles.Eight.Owners.Flat.PrimaryEnvelope

/-!
# Eight squares: actual coefficient families for the flat-primary angular envelope

Every coefficient condition in the joint envelope
is proved here for the existing positive and negative T weights. The
total removed mass may include either or both negative E primaries;
the short negative T angle remains its original independent summand.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FlatPrimaryParameters
open PositiveAngularEnvelope PositivePrimaryBaselines PositiveStressCoefficients
open PositiveOrdinaryEnvelope FlatPrimaryEnvelope

theorem secant_mono {u s : ℝ} (hs : s∈Icc 0 frameCap) (hu : u∈Icc 0 s) :
    (2069/2000)/Real.cos u≤(2069/2000)/Real.cos s := by
  have hu' : u∈Icc 0 frameCap := ⟨hu.1,hu.2.trans hs.2⟩
  have hcU : 0<Real.cos u := by linarith [(transport_trig hu').1]
  have hcS : 0<Real.cos s := by linarith [(transport_trig hs).1]
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi hu.1
    (by norm_num [frameCap] at hs; linarith [hs.2,Real.pi_gt_three]) hu.2
  exact (div_le_div_iff₀ hcU hcS).2 (by linarith)

theorem positive {d s l n b t : ℝ}
    (h : PositiveOrdinaryParameters.Bounds d l n b t)
    (hs : s∈Icc 0 frameCap) : Domain d s l (ps n l t) (qs b t) := by
  have hd := PositiveOrdinaryEnvelope.domains h
  have hsec : (2069/2000 : ℝ)≤(2069/2000)/Real.cos s := by
    simpa using secant_mono hs (show (0:ℝ)∈Icc 0 s from ⟨le_rfl,hs.1⟩)
  refine ⟨h.angle,hs,h.ell_lower,h.ell_upper.le,
    (fun i => (hd i).1),(fun i => (hd i).2.1),(fun i => (hd i).2.2.1),
    (fun i => (hd i).2.2.2.2.1),
    (fun i => (hd i).2.2.2.2.2.trans hsec),?_,?_,?_,
    PositiveOrdinaryEnvelope.high_domains h,?_,(fun hz => (h.low hz).2.2.2)⟩
  · intro i
    have hq0 := ((hd i).1.trans_le (hd i).2.1).le
    have hh := mul_le_mul_of_nonneg_right
      (show ratio d-31/10000≤ratio d by linarith) hq0
    exact hh.trans (hd i).2.2.2.1
  · intro i
    have hDlo : k≤ min 1 t := le_min (by norm_num [k]) h.D_lower
    have hDup : max 1 t≤109/100 := max_le (by norm_num) (by linarith [h.D_upper])
    fin_cases i
    · right; simpa [ps,qs] using And.intro h.H_lower (by norm_num : (1:ℝ)≤109/100)
    · left; simp [ps]
    · left; simp [ps]
    · right; simpa [ps,qs] using And.intro hDlo hDup
  · intro i hi _
    have hq0 := ((hd i).1.trans_le (hd i).2.1).le
    have hr : ratio (d-s)≤ratio d := by dsimp [ratio]; linarith [hs.1]
    have hh := (mul_le_mul_of_nonneg_right hr hq0).trans (hd i).2.2.2.1
    simpa [hi] using hh
  · intro hz i
    have hh := PositiveOrdinaryEnvelope.low_domains h hz i
    exact ⟨hh.1,fun _ => hh.2⟩

theorem negative {d u s b t : ℝ}
    (h : NegativeOrdinaryParameters.Bounds d u b t)
    (hs : s∈Icc 0 frameCap) (hus : u≤ s)
    (hblow : d≤3/10 → b≤1) :
    Domain d s (lN d) (ps (SecondaryEStress.tiltedWeight k (19/50) d) (lN d) t) (qs b t) := by
  have hb := PositiveOrdinaryParameters.familyN h.angle
  have hd := NegativeOrdinaryParameters.domains h
  have hsec := secant_mono hs ⟨h.short.1,hus⟩
  have hDlo : k≤ min 1 t := le_min (by norm_num [k]) h.D_lower
  have hDup : max 1 t≤109/100 :=
    max_le (by norm_num) (NegativeOrdinaryParameters.coefficient_ranges h).2.1
  refine ⟨h.angle,hs,hb.ell_lower,hb.ell_upper.le,
    (fun i => (hd i).1),(fun i => (hd i).2.1),(fun i => (hd i).2.2.1),
    (fun i => (hd i).2.2.2.2.1),
    (fun i => (hd i).2.2.2.2.2.1.trans hsec),
    (fun i => (hd i).2.2.2.1),?_,?_,NegativeOrdinaryParameters.high_domains h,?_,
    (fun hz => (hb.low hz).2.2.2)⟩
  · intro i
    fin_cases i
    · right; simpa [ps,qs] using And.intro hb.H_lower (by norm_num : (1:ℝ)≤109/100)
    · left; simp [ps]
    · left; simp [ps]
    · right; simpa [ps,qs] using And.intro hDlo hDup
  · intro i hi hsd
    have hr : ratio (d-s)≤ratio (d-u) := by dsimp [ratio]; linarith
    have hB0 : 0≤b := (by norm_num [k] : (0:ℝ)≤k).trans h.B_lower
    have hB := (mul_le_mul_of_nonneg_right hr hB0).trans
      (h.shortened (hus.trans hsd))
    have hr' : ratio (d-s)≤ratio d := by dsimp [ratio]; linarith [hs.1]
    have hA : ratio (d-s)*k≤lN d := by
      have hh := (mul_le_mul_of_nonneg_left hb.B_lower
        (show 0≤ratio d by dsimp [ratio]; linarith [h.angle.1])).trans hb.correlated
      exact (mul_le_mul_of_nonneg_right hr' (by norm_num [k] : 0≤k)).trans hh
    fin_cases i
    · change SecondaryEStress.tiltedWeight k (19/50) d=lN d at hi
      exact False.elim (by linarith [hb.H_lower,hb.ell_upper])
    · simpa [ps,qs] using hA
    · simpa [ps,qs] using hB
    · simp [ps] at hi
      exact False.elim (by linarith [hDlo,hb.ell_upper])
  · intro hz i
    refine ⟨(NegativeOrdinaryParameters.low_domains h hz i).1,?_⟩
    intro hi
    fin_cases i
    · simp [qs]
    · norm_num [qs,k]
    · simpa [qs] using hblow hz
    · simp [ps] at hi
      exact False.elim (by linarith [hDlo,hb.ell_upper])

theorem low_cN {d : ℝ} (hd : d∈Icc 0 (3/10)) : cN d≤1909/2000 := by
  have hm := mul_nonneg (show 0≤3/10-d by linarith [hd.2])
    (show 0≤7/20-(3/20)*(d+3/10) by linarith [hd.1,hd.2])
  dsimp [cN]
  nlinarith

theorem low_secant_cN {d u : ℝ} (hd : d∈Icc 0 (3/10))
    (hu : u∈Icc 0 (3/10)) : cN d/Real.cos u≤1 := by
  have hc := NegativeOrdinaryParameters.short_cos hu
  exact (div_le_one hc.2.1).2 (by linarith [low_cN hd,hc.1])

theorem negativeTD {d u s : ℝ} (hd : d∈Icc 0 frameCap)
    (hu : u∈Icc 0 (3/10)) (hs : s∈Icc 0 frameCap) (hus : u≤ s) :
    Domain d s (lN d)
      (ps (SecondaryEStress.tiltedWeight k (19/50) d) (lN d) (cN d/Real.cos u))
      (qs (cN d) (cN d/Real.cos u)) := by
  apply negative (NegativeOrdinaryParameters.familyTD hd hu) hs hus
  intro hz
  linarith [low_cN ⟨hd.1,hz⟩]

theorem negativeBT {d u s : ℝ} (hd : d∈Icc 0 frameCap)
    (hu : u∈Icc 0 (9/100)) (hs : s∈Icc 0 frameCap) (hus : u≤ s) :
    Domain d s (lN d)
      (ps (SecondaryEStress.tiltedWeight k (19/50) d) (lN d) (cN d))
      (qs (cN d/Real.cos u) (cN d)) := by
  apply negative (NegativeOrdinaryParameters.familyBT hd hu) hs hus
  intro hz
  exact low_secant_cN ⟨hd.1,hz⟩ ⟨hu.1,by linarith [hu.2]⟩

end SquaresInCircles.Eight.FlatPrimaryParameters

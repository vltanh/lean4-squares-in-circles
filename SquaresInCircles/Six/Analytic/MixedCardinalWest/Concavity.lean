import SquaresInCircles.Six.Analytic.RadicalTrigConcavity
import SquaresInCircles.Six.Normalization.CapBounds
import SquaresInCircles.Six.Normalization.SecondarySeparation
import SquaresInCircles.Seven.Analysis

/-!
# One analytic stress for the cardinal/cardinal mixed west-wing case

Use weights 2,4,0,3,3 on C--W,C--S,C--D,W--D,D--S, with the last two
normals D-secondary and S-secondary. The universal far-vertex support has the
following signed-projection minorant. Its only nonsmooth wall is s=0.

The two equal outer weights give the radical sqrt(18-18 sin(d-s)). Its
concavity criterion factors as (1-sin x)(144(1+sin x)-18 Q0)>=0, so there
is no subdivision near a support switch. Coordinate concavity reduces the
whole physical box to its twelve geometrically forced vertices. This file
proves concavity; endpoint positivity and actual packing transport are separate.
Compilation remains deferred.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.MixedCardinalWest
open Normalization

def southTerm (s : ℝ) : ℝ :=
  4*Real.cos s+4*max (-Real.sin s) 0-R0*Real.sqrt (25-24*Real.sin s)

def diagonalTerm (x : ℝ) : ℝ :=
  3*Real.cos x-R0*Real.sqrt (18-18*Real.sin x)

def westTerm (w d : ℝ) : ℝ :=
  3*(Real.cos (d-w)+Real.sin (d-w))-R0*Real.sqrt (13+12*Real.sin d)

def gap (w s d : ℝ) : ℝ :=
  9-6*c0+2*Real.cos w+southTerm s+diagonalTerm (d-s)+westTerm w d

private lemma concave_congr_on {f g : ℝ → ℝ} {l u : ℝ}
    (hf : ConcaveOn ℝ (Set.Icc l u) f)
    (he : ∀ x ∈ Set.Icc l u, f x=g x) : ConcaveOn ℝ (Set.Icc l u) g := by
  refine ⟨convex_Icc l u,?_⟩
  intro x hx y hy a b ha hb hab
  have hz := (convex_Icc l u) hx hy ha hb hab
  rw [← he x hx,← he y hy,← he _ hz]
  exact hf.2 hx hy ha hb hab

private lemma cos_small {x : ℝ} (hx : -(2/5) ≤ x ∧ x ≤ 2/5) :
    23/25 ≤ Real.cos x := by
  have hp := mul_nonneg (show 0 ≤ x+2/5 by linarith [hx.1])
    (show 0 ≤ 2/5-x by linarith [hx.2])
  nlinarith [Real.one_sub_sq_div_two_le_cos (x := x)]

private lemma offset_range {d t : ℝ}
    (hd : 1/2 ≤ d ∧ d ≤ Real.pi/4) (ht : -(2/5) ≤ t ∧ t ≤ 2/5) :
    0 ≤ d-t ∧ d-t ≤ 6/5 := by
  constructor <;> linarith [hd.1,hd.2,ht.1,ht.2,Real.pi_lt_d2]

private lemma first_quadrant_trig {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 6/5) :
    0 < Real.cos x ∧ 0 ≤ Real.sin x ∧ Real.sin x < 1 ∧
      1 ≤ Real.cos x+Real.sin x := by
  have hc : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hx.1,Real.pi_pos],by linarith [hx.2,Real.pi_gt_d2]⟩
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi hx.1
    (by linarith [hx.2,Real.pi_gt_d2])
  have hs1 : Real.sin x < 1 := by
    have hc2 := pow_pos hc 2
    nlinarith [Real.sin_sq_add_cos_sq x]
  have hw := one_le_abs_cos_add_abs_sin x
  rw [abs_of_pos hc,abs_of_nonneg hs] at hw
  exact ⟨hc,hs,hs1,hw⟩

/-- Equal outer weights make the entire D-resultant curvature elementary. -/
lemma diagonalTerm_concave :
    ConcaveOn ℝ (Set.Icc 0 (6/5)) diagonalTerm := by
  have hh : ConcaveOn ℝ (Set.Icc 0 (6/5)) (radicalTrig 3 0 18 (-18) R0) := by
    apply radicalTrig_concave R0_nonneg (by norm_num)
    · intro x hx
      have ht := first_quadrant_trig hx
      linarith [ht.2.2.1]
    · intro x hx
      have ht := first_quadrant_trig hx
      have hr : 0 ≤ 18-18*Real.sin x := by linarith [ht.2.2.1]
      have hs := Real.sq_sqrt hr
      have hfactor := mul_nonneg
        (show 0 ≤ 1-Real.sin x by linarith [ht.2.2.1])
        (show 0 ≤ 144*(1+Real.sin x)-18*Q0 by
          norm_num [Q0]; linarith [ht.2.1])
      have hmul := congrArg (fun z : ℝ => Q0*z) hs
      have hsq : (R0*Real.sqrt (18-18*Real.sin x))^2 ≤ (12*Real.cos x)^2 := by
        rw [mul_pow,R0_sq]
        nlinarith [Real.sin_sq_add_cos_sq x]
      have hleft : 0 ≤ R0*Real.sqrt (18-18*Real.sin x) :=
        mul_nonneg R0_nonneg (Real.sqrt_nonneg _)
      have hright : 0 ≤ 12*Real.cos x := by linarith [ht.1]
      have hbound : R0*Real.sqrt (18-18*Real.sin x) ≤ 12*Real.cos x := by
        by_contra! h
        have hp := mul_pos (sub_pos.mpr h)
          (show 0 < R0*Real.sqrt (18-18*Real.sin x)+12*Real.cos x by linarith)
        nlinarith
      have e : (18:ℝ) + -18*Real.sin x = 18-18*Real.sin x := by ring
      rw [e]
      linarith [hbound]
  apply concave_congr_on hh
  intro x _
  have e : (18:ℝ) + -18*Real.sin x = 18-18*Real.sin x := by ring
  simp only [radicalTrig,diagonalTerm,e]
  ring

private lemma south_radical_concave {B l u : ℝ}
    (hl : -(2/5) ≤ l) (hu : u ≤ 2/5)
    (hB : ∀ x ∈ Set.Icc l u, 0 ≤ B*Real.sin x) :
    ConcaveOn ℝ (Set.Icc l u) (radicalTrig 4 B 25 (-24) R0) := by
  apply radicalTrig_concave R0_nonneg (by norm_num)
  · intro x _
    linarith [Real.sin_le_one x]
  · intro x hx
    have hr : 0 ≤ 25-24*Real.sin x := by linarith [Real.sin_le_one x]
    have hs := Real.sq_sqrt hr
    have hroot : Real.sqrt (25-24*Real.sin x) ≤ 7 := by
      nlinarith [Real.neg_one_le_sin x,Real.sqrt_nonneg (25-24*Real.sin x)]
    have hprod := mul_le_mul_of_nonneg_left hroot R0_nonneg
    have hc := cos_small ⟨hl.trans hx.1,hx.2.trans hu⟩
    have hb := hB x hx
    have e : (25:ℝ) + -24*Real.sin x = 25-24*Real.sin x := by ring
    rw [e]
    linarith [R0_lt_1689_1000]

lemma southTerm_negative_concave :
    ConcaveOn ℝ (Set.Icc (-(2/5)) 0) southTerm := by
  have hsin (x : ℝ) (hx : x ∈ Set.Icc (-(2/5)) 0) : Real.sin x ≤ 0 := by
    have h := Real.sin_nonneg_of_nonneg_of_le_pi (x := -x)
      (by linarith [hx.2]) (by linarith [hx.1,Real.pi_gt_d2])
    rw [Real.sin_neg] at h
    linarith
  have hh := south_radical_concave (B := -4) (l := -(2/5)) (u := 0)
    le_rfl (by norm_num) (fun x hx => by linarith [hsin x hx])
  apply concave_congr_on hh
  intro x hx
  dsimp [radicalTrig,southTerm]
  rw [max_eq_left (show 0 ≤ -Real.sin x by linarith [hsin x hx])]
  ring

lemma southTerm_positive_concave :
    ConcaveOn ℝ (Set.Icc 0 (2/5)) southTerm := by
  have hh := south_radical_concave (B := 0) (l := 0) (u := 2/5)
    (by norm_num) le_rfl (fun _ _ => by simp)
  apply concave_congr_on hh
  intro x hx
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi hx.1
    (by linarith [hx.2,Real.pi_gt_d2])
  dsimp [radicalTrig,southTerm]
  rw [max_eq_right (show -Real.sin x ≤ 0 by linarith)]
  ring

lemma westTerm_diagonal_concave {w : ℝ} (hw : -(2/5) ≤ w ∧ w ≤ 0) :
    ConcaveOn ℝ (Set.Icc (1/2) (Real.pi/4)) (westTerm w) := by
  let A := 3*(Real.cos w-Real.sin w)
  let B := 3*(Real.cos w+Real.sin w)
  have he (d : ℝ) : A*Real.cos d+B*Real.sin d=
      3*(Real.cos (d-w)+Real.sin (d-w)) := by
    dsimp [A,B]
    rw [Real.cos_sub,Real.sin_sub]
    ring
  have hh : ConcaveOn ℝ (Set.Icc (1/2) (Real.pi/4)) (radicalTrig A B 13 12 R0) := by
    apply radicalTrig_concave R0_nonneg (by norm_num)
    · intro d _
      linarith [Real.neg_one_le_sin d]
    · intro d hd
      have hr : 0 ≤ 13+12*Real.sin d := by linarith [Real.neg_one_le_sin d]
      have hs := Real.sq_sqrt hr
      have hroot : Real.sqrt (13+12*Real.sin d) ≤ 5 := by
        nlinarith [Real.sin_le_one d,Real.sqrt_nonneg (13+12*Real.sin d)]
      have hmul := mul_le_mul_of_nonneg_left hroot R0_nonneg
      have ht := first_quadrant_trig (offset_range hd ⟨hw.1,by linarith [hw.2]⟩)
      rw [he]
      nlinarith [ht.2.2.2,R0_lt_1689_1000]
  apply concave_congr_on hh
  intro d _
  simp only [radicalTrig,westTerm,he]

lemma gap_diagonal_concave {w s : ℝ}
    (hw : -(2/5) ≤ w ∧ w ≤ 0) (hs : -(2/5) ≤ s ∧ s ≤ 2/5) :
    ConcaveOn ℝ (Set.Icc (1/2) (Real.pi/4)) (fun d => gap w s d) := by
  have hd := concave_affine_argument (a := 1) (b := -s) diagonalTerm_concave
    (fun d hd => by
      obtain ⟨h1,h2⟩ := offset_range hd hs
      exact ⟨by linarith,by linarith⟩)
  have h := ((concave_constant (9-6*c0+2*Real.cos w+southTerm s) (1/2) (Real.pi/4)).add hd).add
    (westTerm_diagonal_concave hw)
  apply concave_congr_on h
  intro d _
  have e : 1*d+-s = d-s := by ring
  simp only [Pi.add_apply,gap,e]

lemma gap_west_concave {s d : ℝ} (hd : 1/2 ≤ d ∧ d ≤ Real.pi/4) :
    ConcaveOn ℝ (Set.Icc (-(2/5)) 0) (fun w => gap w s d) := by
  let A := 2+3*(Real.cos d+Real.sin d)
  let B := 3*(Real.sin d-Real.cos d)
  have he (w : ℝ) : A*Real.cos w+B*Real.sin w=
      2*Real.cos w+3*(Real.cos (d-w)+Real.sin (d-w)) := by
    dsimp [A,B]
    rw [Real.cos_sub,Real.sin_sub]
    ring
  have hh : ConcaveOn ℝ (Set.Icc (-(2/5)) 0) (radicalTrig A B 1 0 0) := by
    apply radicalTrig_concave (by norm_num) (by norm_num)
    · intro _ _; norm_num
    · intro w hw
      have hc := cos_small ⟨hw.1,by linarith [hw.2]⟩
      have ht := first_quadrant_trig (offset_range hd ⟨hw.1,by linarith [hw.2]⟩)
      rw [he]
      nlinarith [ht.2.2.2]
  let K := 9-6*c0+southTerm s+diagonalTerm (d-s)-R0*Real.sqrt (13+12*Real.sin d)
  have h := hh.add (concave_constant K (-(2/5)) 0)
  apply concave_congr_on h
  intro w _
  dsimp [radicalTrig,K,gap,westTerm]
  rw [he]
  ring

lemma gap_south_concave {w d l u : ℝ}
    (hd : 1/2 ≤ d ∧ d ≤ Real.pi/4)
    (hl : -(2/5) ≤ l) (hu : u ≤ 2/5)
    (hs : ConcaveOn ℝ (Set.Icc l u) southTerm) :
    ConcaveOn ℝ (Set.Icc l u) (fun s => gap w s d) := by
  have hh := concave_affine_argument (a := -1) (b := d) diagonalTerm_concave
    (fun s hs => by
      have hm := offset_range hd ⟨hl.trans hs.1,hs.2.trans hu⟩
      exact ⟨by linarith [hm.1],by linarith [hm.2]⟩)
  let K := 9-6*c0+2*Real.cos w+westTerm w d
  have h := (hs.add hh).add (concave_constant K l u)
  apply concave_congr_on h
  intro s _
  dsimp [gap,K]
  ring

end SquaresInCircles.Six.Analytic.MixedCardinalWest

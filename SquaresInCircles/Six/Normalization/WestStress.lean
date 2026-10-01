import SquaresInCircles.Six.Normalization.WestPair
import SquaresInCircles.Six.Analysis
import SquaresInCircles.Six.Supports

/-!
# D is not separated along the west side of C

Let W and D be at the phases `π + t` and `π + u`, with `-2/3 ≤ t ≤ u` and
`-2/5 ≤ u ≤ 2/5`, let W be separated from C along its own axis and D along the
west side of C, and let W and D be disjoint, hence separated along the secondary
axis of W or of D (`west_secondary_axes`), at the angle `z = t` or `z = u`. The
weights `3/10`, `9/20` and `1/4` on these three separations give forces whose
works are at most the support of the box `[0, c0]²` for C and the vertex
supports of W and D. So the threshold sum minus these bounds is nonpositive; but
at `z = t` and `z = u` it is `westStressW t u` and `westStressD t u`, which are
positive (`west_cardinal_impossible`). Both are positive on the triangle of
`(t, u)` by one argument (`triangle_positive`): where the signs of `sin t` and
`sin u` are constant, each is, or is at least, a constant plus concave terms in
`t`, in `u` and in `u - t`, so it is concave in `t` and along the edges of the
three parts of the triangle, and it is positive at their seven vertices, by
Taylor bounds at rational angles. A term `A cos x + B sin x` is concave where it
is nonnegative, and `A cos x + B sin x - R √(p + q sin x)` where the curvature
bound of `radicalTrig_concave` holds.
-/

noncomputable section
open Set
namespace SquaresInCircles.Six
open Normalization

open Normalization

/-- The bound on the work of the force on C, for its centre in `[0, c0]²`. -/
def westCentralSupport (t:ℝ) : ℝ :=
  c0*(3/10+(9/20)*Real.cos t+(9/20)*max (Real.sin t) 0)

/-- The threshold sum of the west stress minus the bounds on the works, with W
and D separated along the secondary axis of W. -/
def westStressW (t u:ℝ) : ℝ :=
  17/20+(3/10)*Real.cos u+(3/10)*max (-Real.sin u) 0+
    (9/40)*(Real.cos t+|Real.sin t|)+(1/4)*(Real.cos (u-t)+Real.sin (u-t))-
    westCentralSupport t-R0*Real.sqrt (53/200)-R0*Real.sqrt (61/400-(3/20)*Real.sin t)

/-- The same with W and D separated along the secondary axis of D. -/
def westStressD (t u:ℝ) : ℝ :=
  17/20+(3/10)*Real.cos u+(3/10)*max (-Real.sin u) 0+
    (9/40)*(Real.cos t+|Real.sin t|)+(1/4)*(Real.cos (u-t)+Real.sin (u-t))-
    westCentralSupport t-R0*Real.sqrt (53/200+(9/40)*Real.sin (u-t))-
    R0*Real.sqrt (61/400-(3/20)*Real.sin u)

lemma west_root_bound : Real.sqrt (53/200:ℝ)≤103/200 := by
  have h := Real.sqrt_le_sqrt (show (53:ℝ)/200≤((103:ℝ)/200)^2 by norm_num)
  rwa [Real.sqrt_sq (by norm_num)] at h

lemma west_angle_bounds {t:ℝ} (ht:-2/3≤t ∧ t≤2/5) :
    7/9≤Real.cos t ∧ -2/3≤Real.sin t ∧ Real.sin t≤2/5 := by
  have h := small_angle (show |t|≤2/3 from abs_le.mpr ⟨by linarith [ht.1],by linarith [ht.2]⟩)
  have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi/2)≤t by linarith [ht.1,Real.pi_gt_d2])
    (show (2:ℝ)/5≤Real.pi/2 by linarith [Real.pi_gt_d2]) ht.2
  exact ⟨by linarith [h.1],by linarith [(abs_le.mp h.2).1],
    hs.trans (Real.sin_le (by norm_num))⟩

/-- `√(61/400 - 3z/20) ≤ 99/250 - 13z/80` for `z ≤ 2/5`: the difference of the
squares is a completed square plus `7/338000`. -/
lemma west_affine_radical {z:ℝ} (hz:z≤2/5) :
    Real.sqrt (61/400-(3/20)*z)≤99/250-(13/80)*z := by
  have hpos : 0≤99/250-(13/80)*z := by linarith
  have hid : (99/250-(13/80)*z)^2-(61/400-(3/20)*z) =
      (169/6400)*(z+1704/4225)^2+7/338000 := by ring
  have hs : 61/400-(3/20)*z≤(99/250-(13/80)*z)^2 := by
    nlinarith [sq_nonneg (z+1704/4225)]
  have hh := Real.sqrt_le_sqrt hs
  rwa [Real.sqrt_sq hpos] at hh

lemma westCentralSupport_upper {t:ℝ} (ht:-2/3≤t ∧ t≤2/5) :
    westCentralSupport t ≤ (113/1000)*(3/10+(9/20)*Real.cos t+
      (9/20)*max (Real.sin t) 0) := by
  have htr := west_angle_bounds ht
  have hnonneg : 0≤3/10+(9/20)*Real.cos t+(9/20)*max (Real.sin t) 0 := by
    nlinarith [le_max_right (Real.sin t) 0]
  have hc : c0≤113/1000 := by dsimp [c0]; linarith [rho0_bounds.2]
  exact mul_le_mul_of_nonneg_right hc hnonneg

private lemma radicals_bound {t:ℝ} (ht:-2/3≤t ∧ t≤2/5) :
    R0*Real.sqrt (53/200)+R0*Real.sqrt (61/400-(3/20)*Real.sin t) ≤
      (8443/5000)*(103/200)+(8443/5000)*(99/250-(13/80)*Real.sin t) := by
  have htr := west_angle_bounds ht
  have hroot := west_affine_radical htr.2.2
  have ha := mul_le_mul R0_bounds.2.le west_root_bound
    (Real.sqrt_nonneg _) (by norm_num : (0:ℝ)≤8443/5000)
  have hb := mul_le_mul R0_bounds.2.le hroot
    (Real.sqrt_nonneg _) (by norm_num : (0:ℝ)≤8443/5000)
  linarith

lemma west_sin_nonpos {t:ℝ} (ht:-2/3≤t ∧ t≤0) : Real.sin t≤0 :=
  Real.sin_nonpos_of_nonpos_of_neg_pi_le ht.2 (by linarith [ht.1,Real.pi_gt_three])

/-! ### Positivity on the triangle -/

/-- `x ↦ J x + G (u - x)` and `x ↦ G (x - t)` keep the concavity of `J` and `G`. -/
private lemma concave_shift {G : ℝ → ℝ} (hG : ConcaveOn ℝ (Icc 0 (16/15)) G) {l h s : ℝ}
    (hs : ∀ x ∈ Icc l h, s - x ∈ Icc 0 (16/15)) :
    ConcaveOn ℝ (Icc l h) (fun x => G (s - x)) := by
  have hc := concave_affine_argument (a := -1) (b := s) hG (by
    intro x hx; simpa only [neg_one_mul, neg_add_eq_sub] using hs x hx)
  refine hc.congr fun x _ => ?_
  simp only [neg_one_mul, neg_add_eq_sub]

private lemma concave_shift' {G : ℝ → ℝ} (hG : ConcaveOn ℝ (Icc 0 (16/15)) G) {l h s : ℝ}
    (hs : ∀ x ∈ Icc l h, x - s ∈ Icc 0 (16/15)) :
    ConcaveOn ℝ (Icc l h) (fun x => G (x - s)) := by
  have hc := concave_affine_argument (a := 1) (b := -s) hG (by
    intro x hx; simpa only [one_mul, ← sub_eq_add_neg] using hs x hx)
  refine hc.congr fun x _ => ?_
  simp only [one_mul, ← sub_eq_add_neg]

section Triangle
variable {C : ℝ} {Jn Jp Hn Hp G : ℝ → ℝ}

/-- A function `C + J t + H u + G (u - t)`, with `J`, `H` and `G` concave, is
positive on the triangle `-2/3 ≤ t ≤ u`, `-2/5 ≤ u ≤ 2/5` once it is positive at
the seven vertices of its parts `u ≤ 0`, `t ≤ 0 ≤ u` and `0 ≤ t`, where `J` is
`Jn` for `t ≤ 0` and `Jp` for `t ≥ 0`, and `H` is `Hn` for `u ≤ 0` and `Hp` for
`u ≥ 0`: it is concave in `t`, and in `u` along the edges `t = -2/3`, `t = 0`
and `t = u` that bound the parts. -/
theorem triangle_positive
    (hJn : ConcaveOn ℝ (Icc (-2/3) 0) Jn) (hJp : ConcaveOn ℝ (Icc 0 (2/5)) Jp)
    (hHn : ConcaveOn ℝ (Icc (-2/5) 0) Hn) (hHp : ConcaveOn ℝ (Icc 0 (2/5)) Hp)
    (hG : ConcaveOn ℝ (Icc 0 (16/15)) G) (hJ0 : Jn 0 = Jp 0) (hH0 : Hn 0 = Hp 0)
    (v1 : 0 < C + Jn (-2/3) + Hn (-2/5) + G (4/15))
    (v2 : 0 < C + Jn (-2/5) + Hn (-2/5) + G 0)
    (v3 : 0 < C + Jn (-2/3) + Hn 0 + G (2/3))
    (v4 : 0 < C + Jn 0 + Hn 0 + G 0)
    (v5 : 0 < C + Jn (-2/3) + Hp (2/5) + G (16/15))
    (v6 : 0 < C + Jn 0 + Hp (2/5) + G (2/5))
    (v7 : 0 < C + Jp (2/5) + Hp (2/5) + G 0) :
    (∀ {t u}, -2/3 ≤ t → t ≤ u → -2/5 ≤ u → u ≤ 0 → 0 < C + Jn t + Hn u + G (u - t)) ∧
    (∀ {t u}, -2/3 ≤ t → t ≤ 0 → 0 ≤ u → u ≤ 2/5 → 0 < C + Jn t + Hp u + G (u - t)) ∧
    (∀ {t u}, 0 ≤ t → t ≤ u → u ≤ 2/5 → 0 < C + Jp t + Hp u + G (u - t)) := by
  have cst := fun (c l h : ℝ) => concaveOn_const (𝕜 := ℝ) c (convex_Icc l h)
  -- the edge `t = -2/3`
  have edgeN : ∀ {u}, -2/5 ≤ u → u ≤ 0 → 0 < C + Jn (-2/3) + Hn u + G (u - -2/3) := by
    intro u hu0 hu1
    have hf := ((cst (C + Jn (-2/3)) (-2/5) 0).add hHn).add
      (concave_shift' hG (s := -2/3) (by intro x hx; constructor <;> linarith [hx.1, hx.2]))
    refine concave_gt_of_endpoints (f := fun u => C + Jn (-2/3) + Hn u + G (u - -2/3)) ?_ ⟨hu0, hu1⟩
      (by norm_num; linarith) (by norm_num; linarith)
    exact hf.congr fun x _ => by simp only [Pi.add_apply]
  have edgeM : ∀ {u}, 0 ≤ u → u ≤ 2/5 → 0 < C + Jn (-2/3) + Hp u + G (u - -2/3) := by
    intro u hu0 hu1
    have hf := ((cst (C + Jn (-2/3)) 0 (2/5)).add hHp).add
      (concave_shift' hG (s := -2/3) (by intro x hx; constructor <;> linarith [hx.1, hx.2]))
    refine concave_gt_of_endpoints (f := fun u => C + Jn (-2/3) + Hp u + G (u - -2/3)) ?_ ⟨hu0, hu1⟩
      (by norm_num; rw [← hH0]; linarith) (by norm_num; linarith)
    exact hf.congr fun x _ => by simp only [Pi.add_apply]
  -- the edge `t = 0`
  have edgeZ : ∀ {u}, 0 ≤ u → u ≤ 2/5 → 0 < C + Jn 0 + Hp u + G (u - 0) := by
    intro u hu0 hu1
    have hf := ((cst (C + Jn 0) 0 (2/5)).add hHp).add
      (concave_shift' hG (s := 0) (by intro x hx; constructor <;> linarith [hx.1, hx.2]))
    refine concave_gt_of_endpoints (f := fun u => C + Jn 0 + Hp u + G (u - 0)) ?_ ⟨hu0, hu1⟩
      (by norm_num; rw [← hH0]; linarith) (by norm_num; linarith)
    exact hf.congr fun x _ => by simp only [Pi.add_apply]
  -- the diagonal
  have diagN : ∀ {u}, -2/5 ≤ u → u ≤ 0 → 0 < C + Jn u + Hn u + G (u - u) := by
    intro u hu0 hu1
    have hf := ((cst C (-2/5) 0).add (hJn.subset (Icc_subset_Icc (by norm_num) le_rfl)
      (convex_Icc _ _))).add hHn
    refine concave_gt_of_endpoints (f := fun u => C + Jn u + Hn u + G (u - u)) ?_ ⟨hu0, hu1⟩
      (by simpa using v2) (by simpa using v4)
    exact (hf.add (cst (G 0) _ _)).congr fun x _ => by simp
  have diagP : ∀ {u}, 0 ≤ u → u ≤ 2/5 → 0 < C + Jp u + Hp u + G (u - u) := by
    intro u hu0 hu1
    have hf := ((cst C 0 (2/5)).add hJp).add hHp
    refine concave_gt_of_endpoints (f := fun u => C + Jp u + Hp u + G (u - u)) ?_ ⟨hu0, hu1⟩
      (by simp; rw [← hJ0, ← hH0]; linarith) (by simpa using v7)
    exact (hf.add (cst (G 0) _ _)).congr fun x _ => by simp
  refine ⟨fun {t u} ht htu hu0 hu1 => ?_, fun {t u} ht ht0 hu0 hu1 => ?_,
    fun {t u} ht htu hu1 => ?_⟩
  · have hf := ((hJn.subset (Icc_subset_Icc le_rfl hu1) (convex_Icc _ _)).add
      (cst (C + Hn u) (-2/3) u)).add
      (concave_shift hG (s := u) (by intro x hx; constructor <;> linarith [hx.1, hx.2]))
    refine concave_gt_of_endpoints (f := fun t => C + Jn t + Hn u + G (u - t)) ?_ ⟨ht, htu⟩
      (edgeN hu0 hu1) (diagN hu0 hu1)
    exact hf.congr fun x _ => by simp only [Pi.add_apply]; ring
  · have hf := (hJn.add (cst (C + Hp u) (-2/3) 0)).add
      (concave_shift hG (s := u) (by intro x hx; constructor <;> linarith [hx.1, hx.2]))
    refine concave_gt_of_endpoints (f := fun t => C + Jn t + Hp u + G (u - t)) ?_ ⟨ht, ht0⟩
      (edgeM hu0 hu1) (edgeZ hu0 hu1)
    exact hf.congr fun x _ => by simp only [Pi.add_apply]; ring
  · have hu0 : 0 ≤ u := ht.trans htu
    have hf := ((hJp.subset (Icc_subset_Icc le_rfl hu1) (convex_Icc _ _)).add
      (cst (C + Hp u) 0 u)).add
      (concave_shift hG (s := u) (by intro x hx; constructor <;> linarith [hx.1, hx.2]))
    refine concave_gt_of_endpoints (f := fun t => C + Jp t + Hp u + G (u - t)) ?_ ⟨ht, htu⟩
      (by have := edgeZ hu0 hu1; rw [hJ0] at this; simpa using this) (diagP hu0 hu1)
    exact hf.congr fun x _ => by simp only [Pi.add_apply]; ring

end Triangle

/-! ### The stress along the secondary axis of W -/

private def cW : ℝ := -3611073/5000000
private def aW : ℝ := 3483/20000
private def kNeg : ℝ := 19759/400000
private def kPos : ℝ := 179419/400000

/-- A rational minorant of `westStressW`: where the signs of `sin t` and
`sin u` are constant, a constant plus `aW cos t + K sin t`, `(3/10) cos u + L sin u` and
`(cos (u - t) + sin (u - t))/4`, positive on the three parts of the triangle. -/
private lemma west_minorant_positive :
    (∀ {t u}, -2/3 ≤ t → t ≤ u → -2/5 ≤ u → u ≤ 0 →
      0 < cW + (aW*Real.cos t+kNeg*Real.sin t) + ((3/10)*Real.cos u+(-3/10)*Real.sin u) +
        ((1/4)*Real.cos (u-t)+(1/4)*Real.sin (u-t))) ∧
    (∀ {t u}, -2/3 ≤ t → t ≤ 0 → 0 ≤ u → u ≤ 2/5 →
      0 < cW + (aW*Real.cos t+kNeg*Real.sin t) + ((3/10)*Real.cos u+0*Real.sin u) +
        ((1/4)*Real.cos (u-t)+(1/4)*Real.sin (u-t))) ∧
    (∀ {t u}, 0 ≤ t → t ≤ u → u ≤ 2/5 →
      0 < cW + (aW*Real.cos t+kPos*Real.sin t) + ((3/10)*Real.cos u+0*Real.sin u) +
        ((1/4)*Real.cos (u-t)+(1/4)*Real.sin (u-t))) := by
  have c23 := cos_lower_six (x:=(2:ℝ)/3) (by norm_num)
  have s23 := sin_lower_seven (x:=(2:ℝ)/3) (by norm_num)
  have u23 := sin_upper_five (x:=(2:ℝ)/3) (by norm_num)
  have c25 := cos_lower_six (x:=(2:ℝ)/5) (by norm_num)
  have s25 := sin_lower_seven (x:=(2:ℝ)/5) (by norm_num)
  have u25 := sin_upper_five (x:=(2:ℝ)/5) (by norm_num)
  have c415 := cos_lower_six (x:=(4:ℝ)/15) (by norm_num)
  have s415 := sin_lower_seven (x:=(4:ℝ)/15) (by norm_num)
  have c1615 := cos_lower_six (x:=(16:ℝ)/15) (by norm_num)
  have s1615 := sin_lower_seven (x:=(16:ℝ)/15) (by norm_num)
  norm_num at c23 s23 u23 c25 s25 u25 c415 s415 c1615 s1615
  apply triangle_positive (C := cW) (Jn := fun x => aW*Real.cos x+kNeg*Real.sin x)
    (Jp := fun x => aW*Real.cos x+kPos*Real.sin x)
    (Hn := fun x => (3/10)*Real.cos x+(-3/10)*Real.sin x)
    (Hp := fun x => (3/10)*Real.cos x+0*Real.sin x)
    (G := fun x => (1/4)*Real.cos x+(1/4)*Real.sin x)
  · apply harmonic_concave
    intro x hx
    have h := west_angle_bounds (t:=x) ⟨hx.1,by linarith [hx.2]⟩
    dsimp [aW,kNeg]
    nlinarith
  · apply harmonic_concave
    intro x hx
    have h := west_angle_bounds (t:=x) ⟨by linarith [hx.1],hx.2⟩
    have hs := Real.sin_nonneg_of_nonneg_of_le_pi hx.1 (by linarith [hx.2,Real.pi_gt_d2])
    dsimp [aW,kPos]
    nlinarith
  · apply harmonic_concave
    intro x hx
    have h := west_angle_bounds (t:=x) ⟨by linarith [hx.1],by linarith [hx.2]⟩
    have hs := west_sin_nonpos (t:=x) ⟨by linarith [hx.1],hx.2⟩
    nlinarith
  · apply harmonic_concave
    intro x hx
    have h := west_angle_bounds (t:=x) ⟨by linarith [hx.1],hx.2⟩
    nlinarith
  · apply harmonic_concave
    intro x hx
    have h := west_difference_trig hx
    nlinarith
  · simp
  · simp
  all_goals norm_num [cW,aW,kNeg,kPos,Real.cos_neg,Real.sin_neg]
  all_goals linarith

/-- `westStressW` is positive on the domain `-2/3 ≤ t ≤ u`, `-2/5 ≤ u ≤ 2/5`: with
`R0 < 8443/5000`, `c0 ≤ 113/1000` and the affine bound on its second radical it
is at least the minorant. -/
theorem westStressW_positive {t u:ℝ}
    (ht:-2/3≤t) (hu0:-2/5≤u) (hu1:u≤2/5) (htu:t≤u) : 0<westStressW t u := by
  have htb : -2/3≤t ∧ t≤2/5 := ⟨ht,htu.trans hu1⟩
  have hc := westCentralSupport_upper htb
  have hr := radicals_bound htb
  obtain ⟨hN,hM,hP⟩ := west_minorant_positive
  by_cases ht0:t≤0
  · have hs := west_sin_nonpos ⟨ht,ht0⟩
    by_cases hu0':u≤0
    · have hsu := west_sin_nonpos ⟨by linarith,hu0'⟩
      have hm := hN ht htu hu0 hu0'
      dsimp [cW,aW,kNeg] at hm
      unfold westStressW
      rw [abs_of_nonpos hs,max_eq_right hs,max_eq_left (by linarith : 0≤-Real.sin u)] at *
      nlinarith [hc,hr]
    · have hsu := Real.sin_nonneg_of_nonneg_of_le_pi
        (show 0≤u by linarith) (show u≤Real.pi by linarith [Real.pi_gt_d2])
      have hm := hM ht ht0 (by linarith) hu1
      dsimp [cW,aW,kNeg] at hm
      unfold westStressW
      rw [abs_of_nonpos hs,max_eq_right hs,max_eq_right (by linarith : -Real.sin u≤0)] at *
      nlinarith [hc,hr]
  · have hst := Real.sin_nonneg_of_nonneg_of_le_pi (show 0≤t by linarith)
      (show t≤Real.pi by linarith [Real.pi_gt_d2])
    have hsu := Real.sin_nonneg_of_nonneg_of_le_pi (show 0≤u by linarith)
      (show u≤Real.pi by linarith [Real.pi_gt_d2])
    have hm := hP (by linarith) htu hu1
    dsimp [cW,aW,kPos] at hm
    unfold westStressW
    rw [abs_of_nonneg hst,max_eq_left hst,max_eq_right (by linarith : -Real.sin u≤0)] at *
    nlinarith [hc,hr]

/-! ### The stress along the secondary axis of D -/

open Normalization

/-- The term of `westStressD` in `t`, where the sign of `sin t` is `positive`. -/
def westJ (positive:Bool) (t:ℝ) : ℝ :=
  (9/40-(9/20)*c0)*Real.cos t+
    (if positive then 9/40-(9/20)*c0 else -9/40)*Real.sin t

/-- The term of `westStressD` in `u`, where the sign of `sin u` is `positive`. -/
def westH (positive:Bool) (u:ℝ) : ℝ :=
  radicalTrig (3/10) (if positive then 0 else -3/10) (61/400) (-3/20) R0 u

/-- The term of `westStressD` in `u - t`. -/
def westG (d:ℝ) : ℝ := radicalTrig (1/4) (1/4) (53/200) (9/40) R0 d

/-- `westStressD` where `sin t` has the sign `pt` and `sin u` the sign `pu`,
as a sum of terms in `t`, in `u` and in `u - t`. -/
def westDForm (pt pu:Bool) (t u:ℝ) : ℝ :=
  17/20-(3/10)*c0+westJ pt t+westH pu u+westG (u-t)

lemma westDForm_eq {t u:ℝ} (pt pu:Bool)
    (ht:-2/3≤t ∧ t≤2/5) (hu:-2/5≤u ∧ u≤2/5)
    (htsign:if pt then 0≤t else t≤0) (husign:if pu then 0≤u else u≤0) :
    westDForm pt pu t u=westStressD t u := by
  have hsinT : if pt then 0≤Real.sin t else Real.sin t≤0 := by
    cases pt
    · exact west_sin_nonpos ⟨ht.1,htsign⟩
    · exact Real.sin_nonneg_of_nonneg_of_le_pi htsign
        (by linarith [ht.2,Real.pi_gt_d2])
  have hsinU : if pu then 0≤Real.sin u else Real.sin u≤0 := by
    cases pu
    · exact west_sin_nonpos ⟨by linarith [hu.1],husign⟩
    · exact Real.sin_nonneg_of_nonneg_of_le_pi husign
        (by linarith [hu.2,Real.pi_gt_d2])
  cases pt <;> cases pu
  all_goals simp only [Bool.false_eq_true,ite_false,ite_true] at hsinT hsinU
  all_goals simp only [westDForm,westJ,westH,westG,radicalTrig,westStressD,
    westCentralSupport,Bool.false_eq_true,ite_false,ite_true]
  all_goals first
    | rw [abs_of_nonpos hsinT,max_eq_right hsinT,max_eq_left (by linarith : 0≤-Real.sin u)]
    | rw [abs_of_nonpos hsinT,max_eq_right hsinT,max_eq_right (by linarith : -Real.sin u≤0)]
    | rw [abs_of_nonneg hsinT,max_eq_left hsinT,max_eq_left (by linarith : 0≤-Real.sin u)]
    | rw [abs_of_nonneg hsinT,max_eq_left hsinT,max_eq_right (by linarith : -Real.sin u≤0)]
  all_goals ring_nf

lemma westJ_coefficient_pos : 0<9/40-(9/20)*c0 := by linarith [c0_bounds.2]

private lemma westJ_concave_aux (B l u:ℝ)
    (hcos:∀x∈Set.Icc l u,0≤Real.cos x)
    (hsin:∀x∈Set.Icc l u,0≤B*Real.sin x) :
    ConcaveOn ℝ (Set.Icc l u)
      (fun x=>(9/40-(9/20)*c0)*Real.cos x+B*Real.sin x) := by
  have h := radicalTrig_concave (A:=9/40-(9/20)*c0) (B:=B)
    (p:=1) (q:=0) (R:=0) (l:=l) (u:=u) (by norm_num) (by norm_num)
    (by intro x hx; norm_num)
    (by
      intro x hx
      have hp := mul_nonneg westJ_coefficient_pos.le (hcos x hx)
      have hs := hsin x hx
      simp only [zero_mul,add_zero]
      nlinarith)
  refine h.congr ?_
  intro x _
  simp only [radicalTrig]
  ring

lemma westJ_negative_concave : ConcaveOn ℝ (Set.Icc (-2/3) 0) (westJ false) := by
  apply westJ_concave_aux (-9/40) (-2/3) 0
  · intro x hx
    have h := west_angle_bounds ⟨hx.1,by linarith [hx.2]⟩
    linarith [h.1]
  · intro x hx
    have hs := west_sin_nonpos hx
    nlinarith

lemma westJ_positive_concave : ConcaveOn ℝ (Set.Icc 0 (2/5)) (westJ true) := by
  apply westJ_concave_aux (9/40-(9/20)*c0) 0 (2/5)
  · intro x hx
    have h := west_angle_bounds ⟨by linarith [hx.1],hx.2⟩
    linarith [h.1]
  · intro x hx
    exact mul_nonneg westJ_coefficient_pos.le
      (Real.sin_nonneg_of_nonneg_of_le_pi hx.1 (by linarith [hx.2,Real.pi_gt_d2]))

lemma westG_concave : ConcaveOn ℝ (Set.Icc 0 (16/15)) westG := by
  apply radicalTrig_concave R0_nonneg (by norm_num : ((9:ℝ)/40)^2≤((53:ℝ)/200)^2)
  · intro x hx
    have h := (west_difference_trig hx).2.1
    linarith
  · intro x hx
    have htr := west_difference_trig hx
    have hrad : 0≤53/200+(9/40)*Real.sin x := by linarith [htr.2.1]
    have hs := Real.sq_sqrt hrad
    have hid : (R0*Real.sqrt (53/200+(9/40)*Real.sin x))^2=
        Q0*(53/200+(9/40)*Real.sin x) := by
      calc
        _ = R0^2*(Real.sqrt (53/200+(9/40)*Real.sin x))^2 := by ring
        _ = _ := by rw [R0_sq,hs]
    have hp := mul_nonneg (show 0≤Real.cos x-12/25 by linarith [htr.1]) htr.2.1
    have hsq : (R0*Real.sqrt (53/200+(9/40)*Real.sin x))^2≤
        (Real.cos x+Real.sin x)^2 := by
      rw [hid]
      norm_num [Q0]
      nlinarith [htr.2.2]
    have hcs : 0≤Real.cos x+Real.sin x := by linarith [htr.1,htr.2.1]
    have hbound : R0*Real.sqrt (53/200+(9/40)*Real.sin x)≤Real.cos x+Real.sin x := by
      by_contra! hbad
      have hmul := mul_pos (sub_pos.mpr hbad)
        (show 0<R0*Real.sqrt (53/200+(9/40)*Real.sin x)+(Real.cos x+Real.sin x) by linarith)
      nlinarith
    nlinarith

private lemma westH_concave_aux (B l u:ℝ)
    (hsmall:∀x∈Set.Icc l u,|x|≤2/5)
    (hsign:∀x∈Set.Icc l u,0≤B*Real.sin x) :
    ConcaveOn ℝ (Set.Icc l u) (radicalTrig (3/10) B (61/400) (-3/20) R0) := by
  have hb (x:ℝ) (hx:x∈Set.Icc l u) :
      23/25≤Real.cos x ∧ -2/5≤Real.sin x ∧ Real.sin x≤2/5 := by
    have h := small_angle (hsmall x hx)
    exact ⟨by linarith [h.1],by linarith [(abs_le.mp h.2).1],(abs_le.mp h.2).2⟩
  apply radicalTrig_concave R0_nonneg (by norm_num : ((-3:ℝ)/20)^2≤((61:ℝ)/400)^2)
  · intro x hx
    have h := hb x hx
    linarith [h.2.2]
  · intro x hx
    have h := hb x hx
    have hroot : Real.sqrt (61/400+(-3/20)*Real.sin x)≤1/2 := by
      have hh := Real.sqrt_le_sqrt
        (show 61/400+(-3/20)*Real.sin x≤((1:ℝ)/2)^2 by linarith [h.2.1])
      rwa [Real.sqrt_sq (by norm_num)] at hh
    have hm := mul_le_mul (show R0≤17/10 by linarith [R0_bounds.2]) hroot
      (Real.sqrt_nonneg _) (by norm_num : (0:ℝ)≤17/10)
    have hn := hsign x hx
    nlinarith [h.1]

lemma westH_negative_concave : ConcaveOn ℝ (Set.Icc (-2/5) 0) (westH false) := by
  apply westH_concave_aux (-3/10) (-2/5) 0
  · intro x hx
    exact abs_le.mpr ⟨by linarith [hx.1],by linarith [hx.2]⟩
  · intro x hx
    have h := west_sin_nonpos (t:=x) ⟨by linarith [hx.1],hx.2⟩
    nlinarith

lemma westH_positive_concave : ConcaveOn ℝ (Set.Icc 0 (2/5)) (westH true) := by
  apply westH_concave_aux 0 0 (2/5)
  · intro x hx
    exact abs_le.mpr ⟨by linarith [hx.1],hx.2⟩
  · intro x hx
    simp

open Normalization

private def diagonalVertexExpression (t u p q:ℝ) : ℝ :=
  17/20-(113/1000)*(3/10)+(3/10)*Real.cos u+(3/10)*max (-Real.sin u) 0+
    (3483/20000)*Real.cos t+(9/40)*|Real.sin t|-(1017/20000)*max (Real.sin t) 0+
    (1/4)*(Real.cos (u-t)+Real.sin (u-t))-(8443/5000)*(p+q)

private lemma diagonal_lower_from_roots {t u p q:ℝ} (ht:-2/3≤t ∧ t≤2/5)
    (hp:Real.sqrt (53/200+(9/40)*Real.sin (u-t))≤p)
    (hq:Real.sqrt (61/400-(3/20)*Real.sin u)≤q) :
    diagonalVertexExpression t u p q≤westStressD t u := by
  have hc := westCentralSupport_upper ht
  have hRp := mul_le_mul R0_bounds.2.le hp (Real.sqrt_nonneg _)
    (by norm_num : (0:ℝ)≤8443/5000)
  have hRq := mul_le_mul R0_bounds.2.le hq (Real.sqrt_nonneg _)
    (by norm_num : (0:ℝ)≤8443/5000)
  dsimp [diagonalVertexExpression,westStressD]
  nlinarith

/-- Rational upper bounds for the two radicals at the vertices. -/
private lemma diagonal_root_endpoints :
    Real.sqrt (53/200+(9/40)*Real.sin (4/15))≤57/100 ∧
    Real.sqrt (53/200:ℝ)≤103/200 ∧
    Real.sqrt (53/200+(9/40)*Real.sin (2/3))≤637/1000 ∧
    Real.sqrt (53/200+(9/40)*Real.sin (16/15))≤17/25 ∧
    Real.sqrt (53/200+(9/40)*Real.sin (2/5))≤297/500 ∧
    Real.sqrt (61/400-(3/20)*Real.sin (-2/5))≤23/50 ∧
    Real.sqrt (61/400:ℝ)≤391/1000 ∧
    Real.sqrt (61/400-(3/20)*Real.sin (2/5))≤307/1000 := by
  have s415 := sin_upper_five (x:=(4:ℝ)/15) (by norm_num)
  have s23 := sin_upper_five (x:=(2:ℝ)/3) (by norm_num)
  have s1615 := sin_upper_five (x:=(16:ℝ)/15) (by norm_num)
  have s25 := sin_upper_five (x:=(2:ℝ)/5) (by norm_num)
  have l25 := sin_lower_seven (x:=(2:ℝ)/5) (by norm_num)
  norm_num at s415 s23 s1615 s25 l25
  refine ⟨?_,west_root_bound,?_,?_,?_,?_,?_,?_⟩
  all_goals refine Real.sqrt_le_iff.mpr ⟨by norm_num,?_⟩
  all_goals (norm_num <;> linarith)

private lemma diagonal_minorant_endpoints :
    0<diagonalVertexExpression (-2/3) (-2/5) (57/100) (23/50) ∧
    0<diagonalVertexExpression (-2/5) (-2/5) (103/200) (23/50) ∧
    0<diagonalVertexExpression (-2/3) 0 (637/1000) (391/1000) ∧
    0<diagonalVertexExpression 0 0 (103/200) (391/1000) ∧
    0<diagonalVertexExpression (-2/3) (2/5) (17/25) (307/1000) ∧
    0<diagonalVertexExpression 0 (2/5) (297/500) (307/1000) ∧
    0<diagonalVertexExpression (2/5) (2/5) (103/200) (307/1000) := by
  have c23 := cos_lower_six (x:=(2:ℝ)/3) (by norm_num)
  have s23 := sin_lower_seven (x:=(2:ℝ)/3) (by norm_num)
  have c25 := cos_lower_six (x:=(2:ℝ)/5) (by norm_num)
  have s25 := sin_lower_seven (x:=(2:ℝ)/5) (by norm_num)
  have c415 := cos_lower_six (x:=(4:ℝ)/15) (by norm_num)
  have s415 := sin_lower_seven (x:=(4:ℝ)/15) (by norm_num)
  have c1615 := cos_lower_six (x:=(16:ℝ)/15) (by norm_num)
  have s1615 := sin_lower_seven (x:=(16:ℝ)/15) (by norm_num)
  norm_num at c23 s23 c25 s25 c415 s415 c1615 s1615
  have hs23 : 0≤Real.sin ((2:ℝ)/3) := by linarith
  have hs25 : 0≤Real.sin ((2:ℝ)/5) := by linarith
  have hn23 : -Real.sin ((2:ℝ)/3)≤0 := by linarith
  have hn25 : -Real.sin ((2:ℝ)/5)≤0 := by linarith
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  all_goals norm_num [diagonalVertexExpression,Real.cos_neg,Real.sin_neg,
    abs_neg,abs_of_nonneg hs23,abs_of_nonneg hs25,max_eq_right hn23,
    max_eq_right hn25,max_eq_left hs23,max_eq_left hs25]
  all_goals linarith

/-- `westStressD` is positive at the seven vertices. -/
theorem westStressD_vertices :
    0<westStressD (-2/3) (-2/5) ∧
    0<westStressD (-2/5) (-2/5) ∧
    0<westStressD (-2/3) 0 ∧
    0<westStressD 0 0 ∧
    0<westStressD (-2/3) (2/5) ∧
    0<westStressD 0 (2/5) ∧
    0<westStressD (2/5) (2/5) := by
  obtain ⟨w415,w0,w23,w1615,w25,dn,d0,dp⟩ := diagonal_root_endpoints
  obtain ⟨h0,h1,h2,h3,h4,h5,h6⟩ := diagonal_minorant_endpoints
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · exact h0.trans_le (diagonal_lower_from_roots (by norm_num)
      (by convert w415 using 1; norm_num) dn)
  · exact h1.trans_le (diagonal_lower_from_roots (by norm_num)
      (by simpa using w0) dn)
  · exact h2.trans_le (diagonal_lower_from_roots (by norm_num)
      (by convert w23 using 1; norm_num) (by simpa using d0))
  · exact h3.trans_le (diagonal_lower_from_roots (by norm_num)
      (by simpa using w0) (by simpa using d0))
  · exact h4.trans_le (diagonal_lower_from_roots (by norm_num)
      (by convert w1615 using 1; norm_num) dp)
  · exact h5.trans_le (diagonal_lower_from_roots (by norm_num)
      (by simpa using w25) dp)
  · exact h6.trans_le (diagonal_lower_from_roots (by norm_num)
      (by simpa using w0) dp)

/-- `westStressD` is positive on the domain `-2/3 ≤ t ≤ u`, `-2/5 ≤ u ≤ 2/5`: on
each part where the signs of `sin t` and `sin u` are constant it is `westDForm`,
whose terms are concave, and it is positive at the seven vertices. -/
theorem westStressD_positive {t u:ℝ}
    (ht:-2/3≤t) (hu0:-2/5≤u) (hu1:u≤2/5) (htu:t≤u) : 0<westStressD t u := by
  obtain ⟨v1,v2,v3,v4,v5,v6,v7⟩ := westStressD_vertices
  rw [← westDForm_eq false false (by norm_num) (by norm_num) (by norm_num) (by norm_num)] at v1 v2
  rw [← westDForm_eq false false (by norm_num) (by norm_num) (by norm_num) (by norm_num)] at v3 v4
  rw [← westDForm_eq false true (by norm_num) (by norm_num) (by norm_num) (by norm_num)] at v5 v6
  rw [← westDForm_eq true true (by norm_num) (by norm_num) (by norm_num) (by norm_num)] at v7
  have hJ : westJ false 0 = westJ true 0 := by simp [westJ]
  have hH : westH false 0 = westH true 0 := by simp [westH,radicalTrig]
  have hv6 : 0 < westDForm false true 0 (2/5) := v6
  rw [show westDForm false false (-2/3) 0 = westDForm false true (-2/3) 0 by
    simp only [westDForm,hH]] at v3
  obtain ⟨hN,hM,hP⟩ := triangle_positive (C := 17/20-(3/10)*c0)
    westJ_negative_concave westJ_positive_concave westH_negative_concave
    westH_positive_concave westG_concave hJ hH
    (by norm_num [westDForm] at v1 ⊢; linarith) (by norm_num [westDForm] at v2 ⊢; linarith)
    (by norm_num [westDForm,hH] at v3 ⊢; linarith) (by norm_num [westDForm] at v4 ⊢; linarith)
    (by norm_num [westDForm] at v5 ⊢; linarith) (by norm_num [westDForm] at hv6 ⊢; linarith)
    (by norm_num [westDForm] at v7 ⊢; linarith)
  by_cases huSign:u≤0
  · rw [← westDForm_eq false false ⟨ht,by linarith⟩ ⟨hu0,hu1⟩ (show t≤0 by linarith) huSign]
    exact hN ht htu hu0 huSign
  · by_cases htSign:t≤0
    · rw [← westDForm_eq false true ⟨ht,by linarith⟩ ⟨hu0,hu1⟩ htSign (show 0≤u by linarith)]
      exact hM ht htSign (by linarith) hu1
    · rw [← westDForm_eq true true ⟨ht,by linarith⟩ ⟨hu0,hu1⟩ (show 0≤t by linarith)
        (show 0≤u by linarith)]
      exact hP (by linarith) htu hu1

/-! ### The stress and the three separations -/

open Normalization

/-- The force of the west stress on C. -/
def westForceC (t:ℝ) : Point := (3/10+(9/20)*Real.cos t,(9/20)*Real.sin t)
/-- The force on W, for the separation of W and D along the normal at `z`. -/
def westForceW (t z:ℝ) : Point :=
  (-(9/20)*Real.cos t-(1/4)*Real.sin z,-(9/20)*Real.sin t+(1/4)*Real.cos z)
/-- The force on D. -/
def westForceD (z:ℝ) : Point := (-3/10+(1/4)*Real.sin z,-(1/4)*Real.cos z)
/-- The secondary normal `(sin z, -cos z)` of a square at the phase `π + z`. -/
def westNormal (z:ℝ) : Point := (Real.sin z,-Real.cos z)

/-- The threshold sum of the west stress. -/
def westThreshold (t u:ℝ) : ℝ :=
  (3/10)*(1/2+angularWidth u)+(9/20)*(1/2+angularWidth t)+(1/4)*(1/2+angularWidth (u-t))

/-- A lower bound for the half-width of W along its force. -/
def westWidthW (t z:ℝ) : ℝ := 9/40+(1/8)*(Real.sin (z-t)+Real.cos (z-t))
/-- A lower bound for the half-width of D along its force. -/
def westWidthD (u z:ℝ) : ℝ :=
  (3/20)*Real.cos u-(3/20)*Real.sin u+(1/8)*(Real.sin (u-z)+Real.cos (u-z))

/-- The threshold sum of the west stress minus the bounds on the works, with W
and D separated along the normal `(sin z, -cos z)`. -/
def westGeometricDefect (t u z:ℝ) : ℝ :=
  westThreshold t u-westCentralSupport t-
    R0*Real.sqrt (53/200+(9/40)*Real.sin (z-t))-
    R0*Real.sqrt (61/400-(3/20)*Real.sin z)+westWidthW t z+westWidthD u z

/-- The weighted separations are the works of the three forces. -/
lemma west_force_balance (c W D:Point) (t z:ℝ) :
    (3/10)*dot (-1,0) (sub D c)+(9/20)*dot (-Real.cos t,-Real.sin t) (sub W c)+
      (1/4)*dot (westNormal z) (sub D W) =
      dot (westForceC t) c+dot (westForceW t z) W+dot (westForceD z) D := by
  dsimp [dot,sub,westNormal,westForceC,westForceW,westForceD]
  ring

lemma west_forceW_norm (t z:ℝ) : normSq (westForceW t z)=53/200+(9/40)*Real.sin (z-t) := by
  dsimp [normSq,westForceW]
  rw [Real.sin_sub]
  linear_combination (81/400)*(Real.sin_sq_add_cos_sq t)+(1/16)*(Real.sin_sq_add_cos_sq z)

lemma west_forceD_norm (z:ℝ) : normSq (westForceD z)=61/400-(3/20)*Real.sin z := by
  dsimp [normSq,westForceD]
  linear_combination (1/16)*(Real.sin_sq_add_cos_sq z)

lemma west_forceW_frameX (t z a b:ℝ) :
    frameX (orientedSquare (Real.pi+t) a b) (westForceW t z)=9/20+(1/4)*Real.sin (z-t) := by
  dsimp [frameX,orientedSquare,westForceW]
  rw [cos_pi_add,sin_pi_add,Real.sin_sub]
  linear_combination (9/20)*(Real.sin_sq_add_cos_sq t)

lemma west_forceW_frameY (t z a b:ℝ) :
    frameY (orientedSquare (Real.pi+t) a b) (westForceW t z)=-(1/4)*Real.cos (z-t) := by
  dsimp [frameY,orientedSquare,westForceW]
  rw [cos_pi_add,sin_pi_add,Real.cos_sub]
  ring

lemma west_forceD_frameX (u z A B:ℝ) :
    frameX (orientedSquare (Real.pi+u) A B) (westForceD z)=
      (3/10)*Real.cos u+(1/4)*Real.sin (u-z) := by
  dsimp [frameX,orientedSquare,westForceD]
  rw [cos_pi_add,sin_pi_add,Real.sin_sub]
  ring

lemma west_forceD_frameY (u z A B:ℝ) :
    frameY (orientedSquare (Real.pi+u) A B) (westForceD z)=
      -(3/10)*Real.sin u+(1/4)*Real.cos (u-z) := by
  dsimp [frameY,orientedSquare,westForceD]
  rw [cos_pi_add,sin_pi_add,Real.cos_sub]
  ring

lemma west_widthW_lower (t z a b:ℝ) :
    westWidthW t z≤width (orientedSquare (Real.pi+t) a b) (westForceW t z) := by
  rw [width,west_forceW_frameX,west_forceW_frameY]
  have hx := le_abs_self (9/20+(1/4)*Real.sin (z-t))
  have hy := neg_le_abs (-(1/4)*Real.cos (z-t))
  dsimp [westWidthW]
  linarith

lemma west_widthD_lower (u z A B:ℝ) :
    westWidthD u z≤width (orientedSquare (Real.pi+u) A B) (westForceD z) := by
  rw [width,west_forceD_frameX,west_forceD_frameY]
  have hx := le_abs_self ((3/10)*Real.cos u+(1/4)*Real.sin (u-z))
  have hy := le_abs_self (-(3/10)*Real.sin u+(1/4)*Real.cos (u-z))
  dsimp [westWidthD]
  linarith

lemma west_central_support {c:Point} {t:ℝ}
    (hc:(0≤c.1 ∧ c.1≤c0) ∧ (0≤c.2 ∧ c.2≤c0))
    (ht:-2/3≤t ∧ t≤2/5) : dot (westForceC t) c≤westCentralSupport t := by
  have htr := west_angle_bounds ht
  have hx := mul_nonneg (sub_nonneg.mpr hc.1.2)
    (show 0≤3/10+(9/20)*Real.cos t by linarith [htr.1])
  have hy := scalar_box_support (v:=Real.sin t) hc.2
  dsimp [dot,westForceC,westCentralSupport]
  nlinarith

/-- The separating inequality of C and W along the own axis of W, in the plane. -/
lemma west_own_separator {c:Point} {t a b:ℝ}
    (h:0≤centralMargin .own (Real.pi+t) a b c.1 c.2) :
    1/2+angularWidth t≤dot (-Real.cos t,-Real.sin t)
      (sub (orientedSquare (Real.pi+t) a b).center c) := by
  have hp := primary_difference (Real.pi+t) a b c.1 c.2
  have hd : dot (-Real.cos t,-Real.sin t)
      (sub (orientedSquare (Real.pi+t) a b).center c)=a-centralNormal (Real.pi+t) c.1 c.2 := by
    simpa only [frameX,orientedSquare,dot,cos_pi_add,sin_pi_add,Prod.mk.eta] using hp
  rw [hd]
  simp only [centralMargin,angularWidth,cos_pi_add,sin_pi_add,abs_neg] at h
  dsimp [angularWidth]
  linarith

/-- The separating inequality of C and D along the west side of C. -/
lemma west_cardinal_separator {c:Point} {u A B:ℝ}
    (h:0≤centralMargin .west (Real.pi+u) A B c.1 c.2) :
    1/2+angularWidth u≤dot (-1,0) (sub (orientedSquare (Real.pi+u) A B).center c) := by
  simp only [centralMargin,angularWidth,cos_pi_add,sin_pi_add,abs_neg] at h
  dsimp [dot,sub,orientedSquare,centerX,angularWidth] at h ⊢
  simp only [cos_pi_add,sin_pi_add] at h ⊢
  linarith

/-- The three separating inequalities make the defect nonpositive. -/
theorem west_geometric_defect_nonpos {c:Point} {t u z a b A B:ℝ}
    (hc:(0≤c.1 ∧ c.1≤c0) ∧ (0≤c.2 ∧ c.2≤c0))
    (hW:ContainedChart a |b|) (hD:ContainedChart A |B|)
    (ht:-2/3≤t ∧ t≤2/5)
    (hCW:0≤centralMargin .own (Real.pi+t) a b c.1 c.2)
    (hCD:0≤centralMargin .west (Real.pi+u) A B c.1 c.2)
    (hWD:1/2+angularWidth (u-t)≤dot (westNormal z)
      (sub (orientedSquare (Real.pi+u) A B).center (orientedSquare (Real.pi+t) a b).center)) :
    westGeometricDefect t u z≤0 := by
  have hCW' := west_own_separator hCW
  have hCD' := west_cardinal_separator hCD
  have hsep : westThreshold t u≤
      dot (westForceC t) c+
      dot (westForceW t z) (orientedSquare (Real.pi+t) a b).center+
      dot (westForceD z) (orientedSquare (Real.pi+u) A B).center := by
    rw [← west_force_balance]
    dsimp [westThreshold]
    linarith
  have hWsup := center_le_vertexSupport R0_nonneg
    (oriented_contained_of_chart (t:=Real.pi+t) hW) (westForceW t z)
  have hDsup := center_le_vertexSupport R0_nonneg
    (oriented_contained_of_chart (t:=Real.pi+u) hD) (westForceD z)
  simp only [vertexSupport,vectorLength,west_forceW_norm,west_forceD_norm] at hWsup hDsup
  have hw := west_widthW_lower t z a b
  have hd := west_widthD_lower u z A B
  have hcc := west_central_support hc ht
  dsimp [westGeometricDefect]
  linarith

/-- Along the secondary axis of W (`z = t`) or of D (`z = u`) the defect is
`westStressW` or `westStressD`. -/
lemma west_defect_at_secondary_axes {t u:ℝ}
    (ht:-2/3≤t) (hu0:-2/5≤u) (hu1:u≤2/5) (htu:t≤u) :
    westGeometricDefect t u t=westStressW t u ∧
      westGeometricDefect t u u=westStressD t u := by
  have hct : 0≤Real.cos t := by
    linarith [(west_angle_bounds ⟨ht,htu.trans hu1⟩).1]
  have hcu : 0≤Real.cos u := by
    linarith [(west_angle_bounds ⟨by linarith,hu1⟩).1]
  have hδ := west_difference_trig (d:=u-t) ⟨by linarith,by linarith⟩
  have hcδ : 0≤Real.cos (u-t) := by linarith [hδ.1]
  have hsδ := hδ.2.1
  have habs : |Real.sin u|-Real.sin u=2*max (-Real.sin u) 0 := by
    by_cases h:0≤Real.sin u
    · rw [abs_of_nonneg h,max_eq_right (by linarith)]
      ring
    · rw [abs_of_neg (lt_of_not_ge h),max_eq_left (by linarith)]
      ring
  constructor
  all_goals simp only [westGeometricDefect,westThreshold,westWidthW,westWidthD,
    westStressW,westStressD,sub_self,Real.sin_zero,Real.cos_zero,mul_zero,add_zero,
    angularWidth,abs_of_nonneg hct,abs_of_nonneg hcu,abs_of_nonneg hcδ,abs_of_nonneg hsδ]
  all_goals linarith only [habs]

/-- For `-2/3 ≤ t ≤ u` and `-2/5 ≤ u ≤ 2/5`, W separated from C along its
primary axis and D along the west side of C cannot be disjoint. -/
theorem west_cardinal_impossible {c:Point} {t u a b A B:ℝ}
    (hc:(0≤c.1 ∧ c.1≤c0) ∧ (0≤c.2 ∧ c.2≤c0))
    (hW:ContainedChart a |b|) (hD:ContainedChart A |B|)
    (hWcore:AvoidsCore a |b|) (hDcore:AvoidsCore A |B|)
    (ht:-2/3≤t) (hu0:-2/5≤u) (hu1:u≤2/5) (htu:t≤u)
    (hCW:0≤centralMargin .own (Real.pi+t) a b c.1 c.2)
    (hCD:0≤centralMargin .west (Real.pi+u) A B c.1 c.2)
    (hWD:∀ p,¬(openSquare (orientedSquare (Real.pi+t) a b) p ∧
      openSquare (orientedSquare (Real.pi+u) A B) p)) : False := by
  have hforms := west_defect_at_secondary_axes ht hu0 hu1 htu
  rcases west_secondary_axes hW hD hWcore hDcore ht hu1 htu hWD with h | h
  · have h' : 1/2+angularWidth (u-t)≤dot (westNormal t)
        (sub (orientedSquare (Real.pi+u) A B).center (orientedSquare (Real.pi+t) a b).center) := by
      simpa only [westNormal,normalY,orientedSquare,sin_pi_add,cos_pi_add,neg_neg] using h
    have hn := west_geometric_defect_nonpos hc hW hD ⟨ht,htu.trans hu1⟩ hCW hCD h'
    rw [hforms.1] at hn
    linarith [westStressW_positive ht hu0 hu1 htu]
  · have h' : 1/2+angularWidth (u-t)≤dot (westNormal u)
        (sub (orientedSquare (Real.pi+u) A B).center (orientedSquare (Real.pi+t) a b).center) := by
      simpa only [westNormal,normalY,orientedSquare,sin_pi_add,cos_pi_add,neg_neg] using h
    have hn := west_geometric_defect_nonpos hc hW hD ⟨ht,htu.trans hu1⟩ hCW hCD h'
    rw [hforms.2] at hn
    linarith [westStressD_positive ht hu0 hu1 htu]

end SquaresInCircles.Six

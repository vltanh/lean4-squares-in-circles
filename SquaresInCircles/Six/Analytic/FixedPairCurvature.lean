import SquaresInCircles.Six.Analytic.FixedPairOpposition

/-!
# Curvature bounds for the four geometric pair sources

The finite source cases only identify the rotating and fixed vector lengths.
A single whole-circle theorem bounds each root. The exceptional alternate
n-slice uses the proved opposition inequality, not a loose positive bound.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.FixedPair
open Stress Normalization

private lemma northWave_shape (no : Bool) (u : Fin 4) (k : Fin 3) (n w : ℝ) :
    (∃ z, northWave no u k n w=Wave.constant z) ∨
      ((northWave no u k n w).rotor=rStar ∧ (northWave no u k n w).baseSq=1) := by
  fin_cases k <;> cases no <;> fin_cases u
  all_goals first | exact Or.inl ⟨_,rfl⟩ | exact Or.inr ⟨rfl,rfl⟩

lemma north_curvature_bound (no : Bool) (u : Fin 4) (k : Fin 3) (n w x : ℝ) :
    (northWave no u k n w).curvature (northRadius u) x≤457/1000 := by
  rcases northWave_shape no u k n w with ⟨z,hz⟩ | ⟨hr,hb⟩
  · rw [hz,Wave.constant_curvature]
    norm_num
  · let W := northWave no u k n w
    have hP : W.parameter=rStar^2+(1:ℝ)^2 := by
      simp only [W,Wave.parameter,hr,hb,one_pow]
    have hQT : W.cosine^2+W.sine^2=4*rStar^2*(1:ℝ)^2 := by
      simpa only [W,hr,hb,one_pow,mul_one] using northWave_amplitude no u k n w
    have hx : 0<W.arg x := harmonic_arg_positive rStar_pos.le (by norm_num)
      (by linarith [pair_multiplier_bounds] : rStar≠1) hP hQT
    have hh := harmonicCurvature_le_harmonic_mean (northRadius_nonneg u)
      rStar_pos.le (by norm_num : (0:ℝ)≤1) (by linarith [rStar_pos]) hP hQT hx
    have hm := mul_le_mul_of_nonneg_right (northRadius_le_circle u)
      (div_pos rStar_pos one_add_rStar_pos).le
    have hh' : W.curvature (northRadius u) x≤northRadius u*rStar/(1+rStar) := by
      simpa only [Wave.curvature,add_comm,mul_one] using hh
    have hm' : northRadius u*rStar/(1+rStar)≤Six.radius*rStar/(1+rStar) := by
      simpa only [mul_div_assoc] using hm
    exact hh'.trans (hm'.trans north_curvature_reserve.le)

lemma north_n_cardinal_first {u : Fin 4} (hu : u=0 ∨ u=1) (n w x : ℝ) :
    (northWave false u 0 n w).curvature (northRadius u) x=0 := by
  rcases hu with rfl | rfl <;> simp [northWave,Wave.constant_curvature]

lemma north_n_own_last {u : Fin 4} (hu : u=2 ∨ u=3) (n w x : ℝ) :
    (northWave true u 0 n w).curvature (northRadius u) x=0 := by
  rcases hu with rfl | rfl <;> simp [northWave,Wave.constant_curvature]

lemma north_w_last (no : Bool) {u : Fin 4} (hu : u=2 ∨ u=3) (n w x : ℝ) :
    (northWave no u 1 n w).curvature (northRadius u) x=0 := by
  rcases hu with rfl | rfl <;> cases no <;> simp [northWave,Wave.constant_curvature]

lemma west_n_first (wo : Bool) {u : Fin 4} (hu : u=0 ∨ u=1) (n w x : ℝ) :
    (westWave wo u 0 n w).curvature Six.radius x=0 := by
  rcases hu with rfl | rfl <;> cases wo <;> simp [westWave,Wave.constant_curvature]

lemma west_w_own_first {u : Fin 4} (hu : u=0 ∨ u=1) (n w x : ℝ) :
    (westWave true u 1 n w).curvature Six.radius x=0 := by
  rcases hu with rfl | rfl <;> simp [westWave,Wave.constant_curvature]

lemma west_diagonal_own (u : Fin 4) (n w x : ℝ) :
    (westWave true u 2 n w).curvature Six.radius x=0 := by
  fin_cases u <;> simp [westWave,Wave.constant_curvature]

private lemma multiplier_squares :
    rStar^2≤(37/100:ℝ)^2 ∧ mStar^2≤(893/1000:ℝ)^2 ∧
      (mStar-rStar)^2≤(21/40:ℝ)^2 := by
  have h := pair_multiplier_bounds
  have hr := pow_le_pow_left₀ rStar_pos.le h.2.1.le 2
  have hm := pow_le_pow_left₀ mStar_pos.le h.2.2.2.le 2
  have hmr : 0≤ mStar-rStar := by linarith [h.2.1,h.2.2.1]
  have hmr' : mStar-rStar≤21/40 := by linarith [h.1,h.2.2.2]
  exact ⟨hr,hm,pow_le_pow_left₀ hmr hmr' 2⟩

private lemma sine_domain_bounds {no wo : Bool} {n w : ℝ} (hd : Domain no wo n w) :
    -3/10≤Real.sin n ∧ Real.sin w≤2/5 := by
  have h := domain_bounds hd
  constructor
  · by_cases hn : n≤0
    · exact h.1.trans (sin_lower_of_nonpos hn)
    · have hs := Real.sin_nonneg_of_nonneg_of_le_pi (le_of_not_ge hn)
        (by linarith [h.2.1,Real.pi_gt_d2])
      linarith
  · by_cases hw : 0≤w
    · exact (Real.sin_le hw).trans h.2.2.2.1
    · have hh := Real.sin_nonneg_of_nonneg_of_le_pi (show 0≤-w by linarith)
        (by linarith [h.2.2.1,Real.pi_gt_d2])
      rw [Real.sin_neg] at hh
      linarith

private lemma west_n_base_upper {no wo : Bool} {n w : ℝ}
    (hd : Domain no wo n w) {u : Fin 4} (hu : u=2 ∨ u=3) :
    (westWave wo u 0 n w).baseSq≤(8/5:ℝ)^2 := by
  have hm := multiplier_squares.2.1
  have hs := (sine_domain_bounds hd).2
  have hp := mul_le_mul_of_nonneg_left hs (show 0≤2*mStar by linarith [mStar_pos])
  rcases hu with rfl | rfl <;> cases wo <;> dsimp [westWave]
  all_goals nlinarith [pair_multiplier_bounds]

lemma west_n_third_bound {no wo : Bool} {n w : ℝ} (hd : Domain no wo n w) :
    (westWave wo 3 0 n w).curvature Six.radius n≤51/100 := by
  have hr : 0<(westWave wo 3 0 n w).rotor := by cases wo <;> exact rStar_pos
  have hx : 0<(westWave wo 3 0 n w).arg n := by
    apply westWave_positive (no := no) 3 0
    simpa [sliceN,sliceW] using hd
  apply Wave.curvature_le_rational (A := (37:ℝ)/100) (B := (8:ℝ)/5)
    hr (westWave_amplitude wo 3 0 n w) hx
  · cases wo <;> exact pair_multiplier_bounds.2.1.le
  · exact west_n_base_upper hd (Or.inr rfl)
  · norm_num
  · norm_num

/-- Only r rotates on the own-W w-slice; its fixed base has length at most 27/20. -/
lemma west_w_own_bound {no : Bool} {n w : ℝ} (hd : Domain no true n w) (u : Fin 4) :
    (westWave true u 1 n w).curvature Six.radius w≤491/1000 := by
  by_cases hu : u=0 ∨ u=1
  · rw [west_w_own_first hu]
    norm_num
  · have hlast : u=2 ∨ u=3 := by omega
    have hr : 0<(westWave true u 1 n w).rotor := by
      rcases hlast with rfl | rfl <;> exact rStar_pos
    have hx : 0<(westWave true u 1 n w).arg w := by
      apply westWave_positive (no := no) u 1
      simpa [sliceN,sliceW] using hd
    apply Wave.curvature_le_rational (A := (37:ℝ)/100) (B := (27:ℝ)/20)
      hr (westWave_amplitude true u 1 n w) hx
    · rcases hlast with rfl | rfl <;> exact pair_multiplier_bounds.2.1.le
    · have hm := multiplier_squares.2.1
      rcases hlast with rfl | rfl <;> dsimp [westWave] <;> nlinarith
    · norm_num
    · norm_num

/-- The four entries are the four source axes, not numerical subintervals. -/
def westWCap : Fin 4 → ℝ := ![831/1000,582/1000,43/50,23/25]
private def westWRotorCap : Fin 4 → ℝ := ![1,1,893/1000,893/1000]
private def westWBaseCap : Fin 4 → ℝ := ![967/1000,21/40,7/6,137/100]

lemma west_w_cardinal_bound {no : Bool} {n w : ℝ} (hd : Domain no false n w) (u : Fin 4) :
    (westWave false u 1 n w).curvature Six.radius w≤westWCap u := by
  have hsq := multiplier_squares
  have hsn := (sine_domain_bounds hd).1
  have hp := mul_le_mul_of_nonneg_left hsn (show 0≤2*rStar by linarith [rStar_pos])
  have hc := mul_le_mul_of_nonneg_left (Real.cos_le_one n) (show 0≤2*rStar by linarith [rStar_pos])
  have hr : 0<(westWave false u 1 n w).rotor := by
    fin_cases u <;> dsimp [westWave] <;> norm_num [mStar_pos]
  have hx : 0<(westWave false u 1 n w).arg w := by
    apply westWave_positive (no := no) u 1
    simpa [sliceN,sliceW] using hd
  apply Wave.curvature_le_rational (A := westWRotorCap u) (B := westWBaseCap u)
    hr (westWave_amplitude false u 1 n w) hx
  · fin_cases u <;> dsimp [westWave,westWRotorCap] <;>
      first | exact le_rfl | exact pair_multiplier_bounds.2.2.2.le
  · fin_cases u <;> dsimp [westWave,westWBaseCap] <;>
      nlinarith [hsq.1,hsq.2.1,hsq.2.2,pair_multiplier_bounds]
  · fin_cases u <;> norm_num [westWBaseCap]
  · fin_cases u <;> norm_num [westWRotorCap,westWBaseCap,westWCap]

lemma west_diagonal_cardinal_bound {no : Bool} {x : ℝ}
    (hd : Domain no false x x) (u : Fin 4) :
    (westWave false u 2 x x).curvature Six.radius x≤831/1000 := by
  have hr : 0<(westWave false u 2 x x).rotor := by fin_cases u <;> norm_num [westWave]
  have hx : 0<(westWave false u 2 x x).arg x := by
    apply westWave_positive (no := no) u 2
    simpa [sliceN,sliceW] using hd
  apply Wave.curvature_le_rational (A := (1:ℝ)) (B := (967:ℝ)/1000)
    hr (westWave_amplitude false u 2 x x) hx
  · fin_cases u <;> exact le_rfl
  · have hsq := multiplier_squares
    fin_cases u <;> dsimp [westWave] <;> nlinarith [hsq.1,hsq.2.1,hsq.2.2]
  · norm_num
  · norm_num

end SquaresInCircles.Six.Analytic.FixedPair

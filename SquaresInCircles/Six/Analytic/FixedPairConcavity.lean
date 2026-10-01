import SquaresInCircles.Six.Analytic.FixedPairCurvature
import SquaresInCircles.Six.Analytic.FixedPairNegativeCardinal

/-!
# Concavity of the pair minorant along slices

Along a slice the sector formula is a smooth function of the parameter,
`primitiveSlice`, with explicit first and second derivatives. Inside a sign
sector of the domain the second derivative is at most `-1/500`: each
trigonometric term contributes at most minus its lower bound from
`FixedPairTrig`, and each radical term at most its curvature bound, case by case
over the four source axes and the three slice directions. For a W separated
along a side of C and source `0`, the cases `w ≤ 0` and `w ≥ 0` use the sharper
north bound and the sharper west bound respectively. So the formula is concave
on every closed segment of a slice that lies in one sector.
-/
noncomputable section
namespace SquaresInCircles.Six.Analytic.FixedPair
open Stress Normalization

private def trigValue (A B x : ℝ) : ℝ := A*Real.cos x+B*Real.sin x
private def trigSlope (A B x : ℝ) : ℝ := -A*Real.sin x+B*Real.cos x

private lemma trigValue_deriv (A B x : ℝ) :
    HasDerivAt (trigValue A B) (trigSlope A B x) x := by
  have h := ((Real.hasDerivAt_cos x).const_mul A).add
    ((Real.hasDerivAt_sin x).const_mul B)
  have e : A*(-Real.sin x)+B*Real.cos x=trigSlope A B x := by
    simp only [trigSlope]; ring
  exact h.congr_deriv e

private lemma trigSlope_deriv (A B x : ℝ) :
    HasDerivAt (trigSlope A B) (-trigValue A B x) x := by
  have h := ((Real.hasDerivAt_sin x).const_mul (-A)).add
    ((Real.hasDerivAt_cos x).const_mul B)
  have e : -A*Real.cos x+B*(-Real.sin x)=-trigValue A B x := by
    simp only [trigValue]; ring
  exact h.congr_deriv e

private def nSpeed (k : Fin 3) : ℝ := if k=1 then 0 else 1
private def wSpeed (k : Fin 3) : ℝ := if k=0 then 0 else 1

private lemma sliceN_deriv (k : Fin 3) (n w x : ℝ) :
    HasDerivAt (sliceN k n w) (nSpeed k) x := by
  fin_cases k
  · exact hasDerivAt_id x
  · exact hasDerivAt_const x n
  · exact hasDerivAt_id x

private lemma sliceW_deriv (k : Fin 3) (n w x : ℝ) :
    HasDerivAt (sliceW k n w) (wSpeed k) x := by
  fin_cases k
  · exact hasDerivAt_const x w
  · exact hasDerivAt_id x
  · exact hasDerivAt_id x

def primitiveSlice (no wo : Bool) (u : Fin 4) (pn pw pq : Bool)
    (k : Fin 3) (n w x : ℝ) : ℝ :=
  constant no wo u+
    northTrig no u pn (sliceN k n w x)+westTrig wo pw (sliceW k n w x)+
    differenceTrig u pq (sliceN k n w x-sliceW k n w x)+
    harmonicRoot (northRadius u) (northWave no u k n w).parameter
      (northWave no u k n w).cosine (northWave no u k n w).sine x+
    harmonicRoot Six.radius (westWave wo u k n w).parameter
      (westWave wo u k n w).cosine (westWave wo u k n w).sine x

def primitiveSliceD (no wo : Bool) (u : Fin 4) (pn pw pq : Bool)
    (k : Fin 3) (n w x : ℝ) : ℝ :=
  (if k=0 then
      trigSlope (northCosCoeff no u) (northSinCoeff no u pn) x+
        trigSlope (differenceCosCoeff u) (differenceSinCoeff u pq) (x-w)
    else if k=1 then
      trigSlope (westCosCoeff wo) (westSinCoeff wo pw) x-
        trigSlope (differenceCosCoeff u) (differenceSinCoeff u pq) (n-x)
    else
      trigSlope (northCosCoeff no u) (northSinCoeff no u pn) x+
        trigSlope (westCosCoeff wo) (westSinCoeff wo pw) x)+
    harmonicRootD (northRadius u) (northWave no u k n w).parameter
      (northWave no u k n w).cosine (northWave no u k n w).sine x+
    harmonicRootD Six.radius (westWave wo u k n w).parameter
      (westWave wo u k n w).cosine (westWave wo u k n w).sine x

def sliceCurvature (no wo : Bool) (u : Fin 4) (pn pw pq : Bool)
    (k : Fin 3) (n w x : ℝ) : ℝ :=
  (if k=0 then -northTrig no u pn x-differenceTrig u pq (x-w)
    else if k=1 then -westTrig wo pw x-differenceTrig u pq (n-x)
    else -northTrig no u pn x-westTrig wo pw x)+
    (northWave no u k n w).curvature (northRadius u) x+
    (westWave wo u k n w).curvature Six.radius x

lemma primitiveSlice_eq (no wo : Bool) (u : Fin 4) (pn pw pq : Bool)
    (k : Fin 3) (n w x : ℝ) :
    primitiveSlice no wo u pn pw pq k n w x=
      formula no wo u pn pw pq (sliceN k n w x) (sliceW k n w x) := by
  have hn := northWave_arg no u k n w x
  have hw := westWave_arg wo u k n w x
  dsimp [Wave.arg] at hn hw
  dsimp [primitiveSlice,formula,harmonicRoot]
  rw [hn,hw]
  ring

lemma primitiveSlice_deriv {no wo : Bool} (u : Fin 4) (pn pw pq : Bool)
    (k : Fin 3) {n w x : ℝ}
    (hd : Domain no wo (sliceN k n w x) (sliceW k n w x)) :
    HasDerivAt (primitiveSlice no wo u pn pw pq k n w)
      (primitiveSliceD no wo u pn pw pq k n w x) x := by
  have hn := sliceN_deriv k n w x
  have hw := sliceW_deriv k n w x
  have hq := hn.sub hw
  have hN := (trigValue_deriv (northCosCoeff no u) (northSinCoeff no u pn) _).comp x hn
  have hW := (trigValue_deriv (westCosCoeff wo) (westSinCoeff wo pw) _).comp x hw
  have hQ := (trigValue_deriv (differenceCosCoeff u) (differenceSinCoeff u pq) _).comp x hq
  have hrN := harmonicRoot_deriv (R := northRadius u) (northWave_positive u k hd)
  have hrW := harmonicRoot_deriv (R := Six.radius) (westWave_positive u k hd)
  have hh := ((((hN.const_add (constant no wo u)).add hW).add hQ).add hrN).add hrW
  convert hh using 1
  all_goals first
    | rfl
    | ((fin_cases k <;> simp [primitiveSliceD,nSpeed,wSpeed,sliceN,sliceW]); ring)

lemma primitiveSlice_second {no wo : Bool} (u : Fin 4) (pn pw pq : Bool)
    (k : Fin 3) {n w x : ℝ}
    (hd : Domain no wo (sliceN k n w x) (sliceW k n w x)) :
    HasDerivAt (primitiveSliceD no wo u pn pw pq k n w)
      (sliceCurvature no wo u pn pw pq k n w x) x := by
  have hn := sliceN_deriv k n w x
  have hw := sliceW_deriv k n w x
  have hq := hn.sub hw
  have hN := ((trigSlope_deriv (northCosCoeff no u) (northSinCoeff no u pn) _).comp x hn).const_mul (nSpeed k)
  have hW := ((trigSlope_deriv (westCosCoeff wo) (westSinCoeff wo pw) _).comp x hw).const_mul (wSpeed k)
  have hQ := ((trigSlope_deriv (differenceCosCoeff u) (differenceSinCoeff u pq) _).comp x hq).const_mul (nSpeed k-wSpeed k)
  have hrN := harmonicRoot_second (R := northRadius u) (northWave_positive u k hd)
  have hrW := harmonicRoot_second (R := Six.radius) (westWave_positive u k hd)
  have hh := (((hN.add hW).add hQ).add hrN).add hrW
  convert hh using 1
  all_goals first
    | rfl
    | (funext y; (fin_cases k <;>
        simp [primitiveSliceD,nSpeed,wSpeed,sliceN,sliceW]); ring)
    | (fin_cases k <;>
        simp [sliceCurvature,nSpeed,wSpeed,sliceN,sliceW,trigValue,
          northTrig,westTrig,differenceTrig,Wave.curvature] <;> ring)

/-- Inside a sign sector of the domain, the second derivative of the formula
along any slice is at most `-1/500`. -/
theorem sliceCurvature_negative {no wo pn pw pq : Bool} (u : Fin 4) (k : Fin 3)
    {n w x : ℝ} (hd : Domain no wo (sliceN k n w x) (sliceW k n w x))
    (hs : Sector pn pw pq (sliceN k n w x) (sliceW k n w x)) :
    sliceCurvature no wo u pn pw pq k n w x≤-1/500 := by
  fin_cases k
  · change Domain no wo x w at hd
    change Sector pn pw pq x w at hs
    change -northTrig no u pn x-differenceTrig u pq (x-w)+
      (northWave no u 0 x w).curvature (northRadius u) x+
      (westWave wo u 0 x w).curvature Six.radius x≤-1/500
    have hN := north_curvature_bound no u 0 x w x
    have htN := northTrig_lower (u := u) hd hs
    have hu4 : u=0 ∨ u=1 ∨ u=2 ∨ u=3 := by fin_cases u <;> simp
    rcases hu4 with rfl | rfl | rfl | rfl
    · have hW := west_n_first wo (u := 0) (Or.inl rfl) x w x
      have hQ := differenceTrig_candidate hd hs (u := 0) (Or.inl rfl)
      linarith
    · have hW := west_n_first wo (u := 1) (Or.inr rfl) x w x
      have hQ := differenceTrig_alternate_one hd hs
      linarith
    · have hW := west_alternate_two_curvature_nonpos hd
      have hQ := differenceTrig_alternate_two hd hs
      linarith
    · have hW := west_n_third_bound hd
      have hQ := differenceTrig_candidate hd hs (u := 3) (Or.inr rfl)
      cases no
      · have htN' := northTrig_cardinal_candidate hd hs (u := 3) (Or.inr rfl)
        linarith
      · have hN0 := north_n_own_last (u := 3) (Or.inr rfl) x w x
        linarith
  · change Domain no wo n x at hd
    change Sector pn pw pq n x at hs
    change -westTrig wo pw x-differenceTrig u pq (n-x)+
      (northWave no u 1 n x).curvature (northRadius u) x+
      (westWave wo u 1 n x).curvature Six.radius x≤-1/500
    have hN := north_curvature_bound no u 1 n x x
    have hu4 : u=0 ∨ u=1 ∨ u=2 ∨ u=3 := by fin_cases u <;> simp
    rcases hu4 with rfl | rfl | rfl | rfl
    · cases wo
      · have hW := west_w_cardinal_bound hd 0
        norm_num [westWCap] at hW
        by_cases hx : x≤0
        · have hNc := negative_cardinal_north_curvature hd hx
          have htW := westTrig_cardinal_coarse hd hs
          have hQ := differenceTrig_candidate hd hs (u := 0) (Or.inl rfl)
          linarith
        · have hx0 : 0≤x := le_of_not_ge hx
          have htW := westTrig_cardinal_lower hd hs hx0
          have hQ := differenceTrig_cardinal_west hd hs (u := 0) (Or.inl rfl) hx0
          linarith
      · have hW := west_w_own_first (u := 0) (Or.inl rfl) n x x
        have htW := westTrig_own_lower hd hs
        have hQ := differenceTrig_candidate hd hs (u := 0) (Or.inl rfl)
        linarith
    · have hQ := differenceTrig_alternate_one hd hs
      cases wo
      · have hW := west_w_cardinal_bound hd 1
        norm_num [westWCap] at hW
        have htW := westTrig_cardinal_coarse hd hs
        linarith
      · have hW := west_w_own_first (u := 1) (Or.inr rfl) n x x
        have htW := westTrig_own_lower hd hs
        linarith
    · have hN0 := north_w_last no (u := 2) (Or.inl rfl) n x x
      have hQ := differenceTrig_alternate_two hd hs
      cases wo
      · have hW := west_w_cardinal_bound hd 2
        norm_num [westWCap] at hW
        have htW := westTrig_cardinal_coarse hd hs
        linarith
      · have hW := west_w_own_bound hd 2
        have htW := westTrig_own_lower hd hs
        linarith
    · have hN0 := north_w_last no (u := 3) (Or.inr rfl) n x x
      have hQ := differenceTrig_candidate hd hs (u := 3) (Or.inr rfl)
      cases wo
      · have hW := west_w_cardinal_bound hd 3
        norm_num [westWCap] at hW
        have htW := westTrig_cardinal_coarse hd hs
        linarith
      · have hW := west_w_own_bound hd 3
        have htW := westTrig_own_lower hd hs
        linarith
  · change Domain no wo x x at hd
    change Sector pn pw pq x x at hs
    change -northTrig no u pn x-westTrig wo pw x+
      (northWave no u 2 x x).curvature (northRadius u) x+
      (westWave wo u 2 x x).curvature Six.radius x≤-1/500
    have hN := north_curvature_bound no u 2 x x x
    have htN := northTrig_lower (u := u) hd hs
    cases wo
    · have hW := west_diagonal_cardinal_bound hd u
      have htW := westTrig_cardinal_coarse hd hs
      linarith
    · have hW := west_diagonal_own u x x x
      have htW := westTrig_own_lower hd hs
      linarith

/-- The sector formula is concave on every closed segment of a slice that lies
in the domain and in the sector. -/
theorem formula_slice_concave {no wo pn pw pq : Bool} (u : Fin 4) (k : Fin 3)
    {n w l r : ℝ}
    (hd : ∀ x ∈ Set.Icc l r, Domain no wo (sliceN k n w x) (sliceW k n w x))
    (hs : ∀ x ∈ Set.Icc l r, Sector pn pw pq (sliceN k n w x) (sliceW k n w x)) :
    ConcaveOn ℝ (Set.Icc l r)
      (fun x => formula no wo u pn pw pq (sliceN k n w x) (sliceW k n w x)) := by
  have hc : ConcaveOn ℝ (Set.Icc l r) (primitiveSlice no wo u pn pw pq k n w) :=
    concaveOn_of_explicit_second
      (fun x hx => primitiveSlice_deriv u pn pw pq k (hd x hx))
      (fun x hx => primitiveSlice_second u pn pw pq k (hd x hx))
      (fun x hx => (sliceCurvature_negative u k (hd x hx) (hs x hx)).trans (by norm_num))
  exact hc.congr (fun x _ => primitiveSlice_eq no wo u pn pw pq k n w x)

end SquaresInCircles.Six.Analytic.FixedPair

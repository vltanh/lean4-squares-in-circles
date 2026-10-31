import Mathlib

/-!
# Finite rectangle cover and robust center-capacity lemmas

UNCOMPILED DRAFT. No Lean executable was available when this source was written.
All proposed proofs are ordinary Lean terms (`ring`, `nlinarith`, `norm_num`,
finite cardinality). No `sorry`, custom axiom, native reduction, or external
certificate result is used. Compilation and axiom inspection are still required.

This module does not assume or prove the unrestricted n=9 bound. Its geometric
caller must supply pairwise center separation and an actual cover of every
remaining center. It does not prove that the D02 equations force the five
reference squares or their stated 1/25 vertex neighborhoods.
-/

noncomputable section

namespace SquaresInCircles.Nine.CenterCapacityDraft

abbrev Point := ℝ × ℝ

def sqdist (p q : Point) : ℝ := (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

structure RationalBox where
  xLo : ℚ
  xHi : ℚ
  yLo : ℚ
  yHi : ℚ

def RationalBox.Mem (b : RationalBox) (p : Point) : Prop :=
  (b.xLo : ℝ) ≤ p.1 ∧ p.1 ≤ (b.xHi : ℝ) ∧
  (b.yLo : ℝ) ≤ p.2 ∧ p.2 ≤ (b.yHi : ℝ)

def RationalBox.diameterSq (b : RationalBox) : ℝ :=
  ((b.xHi : ℝ) - (b.xLo : ℝ)) ^ 2 +
  ((b.yHi : ℝ) - (b.yLo : ℝ)) ^ 2

/-- Every pair of points of a closed box is bounded by its squared diagonal. -/
theorem sqdist_le_box_diagonal (b : RationalBox) (p q : Point)
    (hp : b.Mem p) (hq : b.Mem q) : sqdist p q ≤ b.diameterSq := by
  rcases hp with ⟨hp0, hp1, hp2, hp3⟩
  rcases hq with ⟨hq0, hq1, hq2, hq3⟩
  have hx0 : 0 ≤ ((b.xHi : ℝ) - (b.xLo : ℝ)) - (p.1 - q.1) := by linarith
  have hx1 : 0 ≤ ((b.xHi : ℝ) - (b.xLo : ℝ)) + (p.1 - q.1) := by linarith
  have hy0 : 0 ≤ ((b.yHi : ℝ) - (b.yLo : ℝ)) - (p.2 - q.2) := by linarith
  have hy1 : 0 ≤ ((b.yHi : ℝ) - (b.yLo : ℝ)) + (p.2 - q.2) := by linarith
  have hx := mul_nonneg hx0 hx1
  have hy := mul_nonneg hy0 hy1
  dsimp [sqdist, RationalBox.diameterSq]
  nlinarith

/-- A finite cover by sets of squared diameter < 1 holds at most k separated
centers. The pieces may overlap and need not be convex. -/
theorem capacity_of_finite_cover {n k : Nat} (p : Fin n → Point)
    (piece : Fin k → Set Point)
    (separated : ∀ i j, i ≠ j → 1 ≤ sqdist (p i) (p j))
    (covered : ∀ i, ∃ a, p i ∈ piece a)
    (small : ∀ a x y, x ∈ piece a → y ∈ piece a → sqdist x y < 1) : n ≤ k := by
  classical
  let label : Fin n → Fin k := fun i => Classical.choose (covered i)
  have hlabel (i : Fin n) : p i ∈ piece (label i) := Classical.choose_spec (covered i)
  have hinj : Function.Injective label := by
    intro i j hij
    by_contra hne
    have hj : p j ∈ piece (label i) := by
      rw [hij]
      exact hlabel j
    have hsmall := small (label i) (p i) (p j) (hlabel i) hj
    have hlarge := separated i j hne
    linarith
  have hcard := Fintype.card_le_of_injective label hinj
  simpa using hcard

/-- Rational boxes are a convenient finite-cover certificate language. -/
theorem capacity_of_box_cover {n k : Nat} (p : Fin n → Point)
    (box : Fin k → RationalBox)
    (separated : ∀ i j, i ≠ j → 1 ≤ sqdist (p i) (p j))
    (covered : ∀ i, ∃ a, (box a).Mem (p i))
    (small : ∀ a, (box a).diameterSq < 1) : n ≤ k := by
  apply capacity_of_finite_cover p (fun a => {x | (box a).Mem x}) separated covered
  intro a x y hx hy
  exact lt_of_le_of_lt (sqdist_le_box_diagonal (box a) x y hx hy) (small a)

def lerp (t : ℝ) (p q : Point) : Point :=
  ((1 - t) * p.1 + t * q.1, (1 - t) * p.2 + t * q.2)

/-- Convex interpolation does not enlarge a uniform squared vertex error.
This is the two-point variance identity, rather than a floating norm bound. -/
theorem lerp_error_bound (t r : ℝ) (p₀ p₁ q₀ q₁ : Point)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (h0 : sqdist p₀ q₀ ≤ r) (h1 : sqdist p₁ q₁ ≤ r) :
    sqdist (lerp t p₀ p₁) (lerp t q₀ q₁) ≤ r := by
  have ht : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  have hid :
      (1 - t) * sqdist p₀ q₀ + t * sqdist p₁ q₁ -
        sqdist (lerp t p₀ p₁) (lerp t q₀ q₁) =
      t * (1 - t) *
        (((p₀.1 - q₀.1) - (p₁.1 - q₁.1)) ^ 2 +
         ((p₀.2 - q₀.2) - (p₁.2 - q₁.2)) ^ 2) := by
    dsimp [sqdist, lerp]
    ring
  have hnonneg : 0 ≤
      t * (1 - t) *
        (((p₀.1 - q₀.1) - (p₁.1 - q₁.1)) ^ 2 +
         ((p₀.2 - q₀.2) - (p₁.2 - q₁.2)) ^ 2) :=
    mul_nonneg (mul_nonneg ht0 ht) (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hw0 := mul_le_mul_of_nonneg_left h0 ht
  have hw1 := mul_le_mul_of_nonneg_left h1 ht0
  nlinarith

/-- Bilinear convex witness with weights
((1-u)(1-v), u(1-v), uv, (1-u)v), in the original four-vertex order. -/
def witness (vertices : Fin 4 → Point) (u v : ℝ) : Point :=
  lerp v (lerp u (vertices 0) (vertices 1))
    (lerp u (vertices 3) (vertices 2))

theorem witness_error_bound (reference actual : Fin 4 → Point) (u v r : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hvertex : ∀ i, sqdist (reference i) (actual i) ≤ r) :
    sqdist (witness reference u v) (witness actual u v) ≤ r := by
  apply lerp_error_bound v r _ _ _ _ hv0 hv1
  · exact lerp_error_bound u r _ _ _ _ hu0 hu1 (hvertex 0) (hvertex 1)
  · exact lerp_error_bound u r _ _ _ _ hu0 hu1 (hvertex 3) (hvertex 2)

/-- Exact perturbation identity for the 1/50 reference-center tolerance.
No square root or numerical norm approximation is needed. -/
theorem robust_forbidden_ball (p reference actual : Point)
    (hnear : sqdist p reference < (2401 : ℝ) / 2500)
    (herror : sqdist reference actual ≤ (1 : ℝ) / 2500) :
    sqdist p actual < 1 := by
  have hid :
      50 * sqdist p reference + 2450 * sqdist reference actual -
        49 * sqdist p actual =
      (p.1 - reference.1 - 49 * (reference.1 - actual.1)) ^ 2 +
      (p.2 - reference.2 - 49 * (reference.2 - actual.2)) ^ 2 := by
    dsimp [sqdist]
    ring
  have hnonneg : 0 ≤
      (p.1 - reference.1 - 49 * (reference.1 - actual.1)) ^ 2 +
      (p.2 - reference.2 - 49 * (reference.2 - actual.2)) ^ 2 :=
    add_nonneg (sq_nonneg _) (sq_nonneg _)
  nlinarith

/-- The actual five-core certificate uses a convex-combination witness point
in a nominal core square, with nominal distance < 23/50 and perturbation ≤ 1/25.
The resulting actual-core point is strictly within the extra's 1/2 incircle.
The geometric caller supplies the actual witness's membership in its square. -/
theorem robust_half_ball_witness (p reference actual : Point)
    (hnear : sqdist p reference < (529 : ℝ) / 2500)
    (herror : sqdist reference actual ≤ (1 : ℝ) / 625) :
    sqdist p actual < (1 : ℝ) / 4 := by
  have hid :
      50 * sqdist p reference + 575 * sqdist reference actual -
        46 * sqdist p actual =
      (2 * (p.1 - reference.1) - 23 * (reference.1 - actual.1)) ^ 2 +
      (2 * (p.2 - reference.2) - 23 * (reference.2 - actual.2)) ^ 2 := by
    dsimp [sqdist]
    ring
  have hnonneg : 0 ≤
      (2 * (p.1 - reference.1) - 23 * (reference.1 - actual.1)) ^ 2 +
      (2 * (p.2 - reference.2) - 23 * (reference.2 - actual.2)) ^ 2 :=
    add_nonneg (sq_nonneg _) (sq_nonneg _)
  nlinarith

/-- Companion exact identity for the wider 2/25 vertex neighborhood:
nominal distance < 21/50 plus perturbation ≤ 2/25 gives distance < 1/2.
The concrete version-one certificate below still uses 1/25. -/
theorem robust_half_ball_witness_wide (p reference actual : Point)
    (hnear : sqdist p reference < (441 : ℝ) / 2500)
    (herror : sqdist reference actual ≤ (4 : ℝ) / 625) :
    sqdist p actual < (1 : ℝ) / 4 := by
  have hid :
      100 * sqdist p reference + 525 * sqdist reference actual -
        84 * sqdist p actual =
      (4 * (p.1 - reference.1) - 21 * (reference.1 - actual.1)) ^ 2 +
      (4 * (p.2 - reference.2) - 21 * (reference.2 - actual.2)) ^ 2 := by
    dsimp [sqdist]
    ring
  have hnonneg : 0 ≤
      (4 * (p.1 - reference.1) - 21 * (reference.1 - actual.1)) ^ 2 +
      (4 * (p.2 - reference.2) - 21 * (reference.2 - actual.2)) ^ 2 :=
    add_nonneg (sq_nonneg _) (sq_nonneg _)
  nlinarith

def east : RationalBox := ⟨13/10, 91/60, -1/5, 7/10⟩
def south : RationalBox := ⟨-1, 1/4, -91/60, -3/4⟩
def southLeft : RationalBox := ⟨-1, -3/8, -91/60, -3/4⟩
def southRight : RationalBox := ⟨-3/8, 1/4, -91/60, -3/4⟩

theorem east_diagonal : east.diameterSq = (3085 : ℝ) / 3600 := by
  norm_num [east, RationalBox.diameterSq]

theorem southLeft_diagonal : southLeft.diameterSq = (14089 : ℝ) / 14400 := by
  norm_num [southLeft, RationalBox.diameterSq]

theorem southRight_diagonal : southRight.diameterSq = (14089 : ℝ) / 14400 := by
  norm_num [southRight, RationalBox.diameterSq]

def threeBoxes (k : Fin 3) : RationalBox :=
  if k = 0 then east else if k = 1 then southLeft else southRight

theorem threeBoxes_small (k : Fin 3) : (threeBoxes k).diameterSq < 1 := by
  fin_cases k <;>
    norm_num [threeBoxes, RationalBox.diameterSq, east, southLeft, southRight]

/-- The two-region output of the five-core certificate fits at most three
additional centers. The south rectangle is split at x = -3/8. -/
theorem east_south_capacity {n : Nat} (p : Fin n → Point)
    (separated : ∀ i j, i ≠ j → 1 ≤ sqdist (p i) (p j))
    (covered : ∀ i, east.Mem (p i) ∨ south.Mem (p i)) : n ≤ 3 := by
  apply capacity_of_box_cover p threeBoxes separated
  · intro i
    rcases covered i with he | hs
    · exact ⟨0, by simpa [threeBoxes] using he⟩
    · rcases le_total (p i).1 (-(3 : ℝ)/8) with hl | hr
      · have hm : southLeft.Mem (p i) := by
          norm_num [RationalBox.Mem, south, southLeft] at hs ⊢
          exact ⟨hs.1, hl, hs.2.2.1, hs.2.2.2⟩
        exact ⟨1, by simpa [threeBoxes] using hm⟩
      · have hm : southRight.Mem (p i) := by
          norm_num [RationalBox.Mem, south, southRight] at hs ⊢
          exact ⟨hr, hs.2.1, hs.2.2.1, hs.2.2.2⟩
        exact ⟨2, by simpa [threeBoxes] using hm⟩
  · exact threeBoxes_small

theorem no_four_centers_in_east_south (p : Fin 4 → Point)
    (separated : ∀ i j, i ≠ j → 1 ≤ sqdist (p i) (p j))
    (covered : ∀ i, east.Mem (p i) ∨ south.Mem (p i)) : False := by
  have h := east_south_capacity p separated covered
  omega

/-! ## Soundness of the finite quadtree cover -/

def RationalBox.Subbox (b c : RationalBox) : Prop :=
  c.xLo ≤ b.xLo ∧ b.xHi ≤ c.xHi ∧ c.yLo ≤ b.yLo ∧ b.yHi ≤ c.yHi

theorem mem_of_subbox {b c : RationalBox} {p : Point}
    (hbc : b.Subbox c) (hp : b.Mem p) : c.Mem p := by
  rcases hbc with ⟨hx0, hx1, hy0, hy1⟩
  have hx0' : (c.xLo : ℝ) ≤ (b.xLo : ℝ) := by exact_mod_cast hx0
  have hx1' : (b.xHi : ℝ) ≤ (c.xHi : ℝ) := by exact_mod_cast hx1
  have hy0' : (c.yLo : ℝ) ≤ (b.yLo : ℝ) := by exact_mod_cast hy0
  have hy1' : (b.yHi : ℝ) ≤ (c.yHi : ℝ) := by exact_mod_cast hy1
  exact ⟨le_trans hx0' hp.1, le_trans hp.2.1 hx1',
    le_trans hy0' hp.2.2.1, le_trans hp.2.2.2 hy1'⟩

def lowerSquare (lo hi : ℝ) : ℝ :=
  if 0 ≤ lo then lo ^ 2 else if hi ≤ 0 then hi ^ 2 else 0

theorem lowerSquare_le (lo hi x : ℝ) (hlo : lo ≤ x) (hhi : x ≤ hi) :
    lowerSquare lo hi ≤ x ^ 2 := by
  unfold lowerSquare
  split_ifs with h0 h1
  · have hf0 : 0 ≤ x - lo := sub_nonneg.mpr hlo
    have hf1 : 0 ≤ x + lo := by linarith
    nlinarith [mul_nonneg hf0 hf1]
  · have hf0 : 0 ≤ hi - x := sub_nonneg.mpr hhi
    have hf1 : 0 ≤ -hi - x := by linarith
    nlinarith [mul_nonneg hf0 hf1]
  · exact sq_nonneg x

def RationalBox.minimumNormSq (b : RationalBox) : ℝ :=
  lowerSquare (b.xLo : ℝ) (b.xHi : ℝ) + lowerSquare (b.yLo : ℝ) (b.yHi : ℝ)

theorem box_minimumNorm_le (b : RationalBox) (p : Point) (hp : b.Mem p) :
    b.minimumNormSq ≤ sqdist p (0, 0) := by
  have hx := lowerSquare_le (b.xLo : ℝ) (b.xHi : ℝ) p.1 hp.1 hp.2.1
  have hy := lowerSquare_le (b.yLo : ℝ) (b.yHi : ℝ) p.2 hp.2.2.1 hp.2.2.2
  dsimp [RationalBox.minimumNormSq, sqdist]
  nlinarith

def RationalBox.maximumDistSq (b : RationalBox) (r : Point) : ℝ :=
  (max ((b.xHi : ℝ) - r.1) (r.1 - (b.xLo : ℝ))) ^ 2 +
  (max ((b.yHi : ℝ) - r.2) (r.2 - (b.yLo : ℝ))) ^ 2

theorem sqdist_le_box_maximum (b : RationalBox) (p r : Point) (hp : b.Mem p) :
    sqdist p r ≤ b.maximumDistSq r := by
  let rx := max ((b.xHi : ℝ) - r.1) (r.1 - (b.xLo : ℝ))
  let ry := max ((b.yHi : ℝ) - r.2) (r.2 - (b.yLo : ℝ))
  have hx0 : p.1 - r.1 ≤ rx :=
    le_trans (sub_le_sub_right hp.2.1 r.1) (le_max_left _ _)
  have hx1 : -(p.1 - r.1) ≤ rx := by
    have h := le_max_right ((b.xHi : ℝ) - r.1) (r.1 - (b.xLo : ℝ))
    change r.1 - (b.xLo : ℝ) ≤ rx at h
    linarith [hp.1]
  have hy0 : p.2 - r.2 ≤ ry :=
    le_trans (sub_le_sub_right hp.2.2.2 r.2) (le_max_left _ _)
  have hy1 : -(p.2 - r.2) ≤ ry := by
    have h := le_max_right ((b.yHi : ℝ) - r.2) (r.2 - (b.yLo : ℝ))
    change r.2 - (b.yLo : ℝ) ≤ ry at h
    linarith [hp.2.2.1]
  have hx := mul_nonneg (sub_nonneg.mpr hx0)
    (show 0 ≤ rx + (p.1 - r.1) by linarith)
  have hy := mul_nonneg (sub_nonneg.mpr hy0)
    (show 0 ≤ ry + (p.2 - r.2) by linarith)
  change (p.1 - r.1) ^ 2 + (p.2 - r.2) ^ 2 ≤ rx ^ 2 + ry ^ 2
  nlinarith

def RationalBox.lowerLeft (b : RationalBox) : RationalBox :=
  ⟨b.xLo, (b.xLo + b.xHi) / 2, b.yLo, (b.yLo + b.yHi) / 2⟩
def RationalBox.lowerRight (b : RationalBox) : RationalBox :=
  ⟨(b.xLo + b.xHi) / 2, b.xHi, b.yLo, (b.yLo + b.yHi) / 2⟩
def RationalBox.upperLeft (b : RationalBox) : RationalBox :=
  ⟨b.xLo, (b.xLo + b.xHi) / 2, (b.yLo + b.yHi) / 2, b.yHi⟩
def RationalBox.upperRight (b : RationalBox) : RationalBox :=
  ⟨(b.xLo + b.xHi) / 2, b.xHi, (b.yLo + b.yHi) / 2, b.yHi⟩

theorem mem_four_children (b : RationalBox) (p : Point) (hp : b.Mem p) :
    b.lowerLeft.Mem p ∨ b.lowerRight.Mem p ∨ b.upperLeft.Mem p ∨ b.upperRight.Mem p := by
  rcases le_total p.1 (((b.xLo + b.xHi) / 2 : ℚ) : ℝ) with hx | hx
  · rcases le_total p.2 (((b.yLo + b.yHi) / 2 : ℚ) : ℝ) with hy | hy
    · exact Or.inl ⟨hp.1, hx, hp.2.2.1, hy⟩
    · exact Or.inr (Or.inr (Or.inl ⟨hp.1, hx, hy, hp.2.2.2⟩))
  · rcases le_total p.2 (((b.yLo + b.yHi) / 2 : ℚ) : ℝ) with hy | hy
    · exact Or.inr (Or.inl ⟨hx, hp.2.1, hp.2.2.1, hy⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨hx, hp.2.1, hy, hp.2.2.2⟩))

/-- A proof-carrying certificate. Every leaf requires an exact numeric proof;
the split constructors preserve all closed edges. No Python Boolean is trusted. -/
inductive CoverCertificate {ι : Type} (reference : ι → Point) : RationalBox → Type
  | outside {b} (h : ((91 : ℝ) / 60) ^ 2 ≤ b.minimumNormSq) : CoverCertificate reference b
  | east {b} (h : b.Subbox east) : CoverCertificate reference b
  | south {b} (h : b.Subbox south) : CoverCertificate reference b
  | near {b} (i : ι) (h : b.maximumDistSq (reference i) < (529 : ℝ) / 2500) :
      CoverCertificate reference b
  | split {b}
      (ll : CoverCertificate reference b.lowerLeft)
      (lr : CoverCertificate reference b.lowerRight)
      (ul : CoverCertificate reference b.upperLeft)
      (ur : CoverCertificate reference b.upperRight) : CoverCertificate reference b

theorem CoverCertificate.sound {ι : Type} {reference : ι → Point}
    {b : RationalBox} (certificate : CoverCertificate reference b) :
    ∀ p, b.Mem p → sqdist p (0, 0) < ((91 : ℝ) / 60) ^ 2 →
      (∀ i, (529 : ℝ) / 2500 ≤ sqdist p (reference i)) →
      east.Mem p ∨ south.Mem p := by
  induction certificate with
  | outside h =>
      intro p hp hn _
      have hm := box_minimumNorm_le _ p hp
      exfalso
      linarith
  | east h =>
      intro p hp _ _
      exact Or.inl (mem_of_subbox h hp)
  | south h =>
      intro p hp _ _
      exact Or.inr (mem_of_subbox h hp)
  | near i h =>
      intro p hp _ hf
      have hm := sqdist_le_box_maximum _ p (reference i) hp
      have hi := hf i
      exfalso
      linarith
  | split ll lr ul ur ihll ihlr ihul ihur =>
      intro p hp hn hf
      rcases mem_four_children _ p hp with hll | hlr | hul | hur
      · exact ihll p hll hn hf
      · exact ihlr p hlr hn hf
      · exact ihul p hul hn hf
      · exact ihur p hur hn hf

def rootBox : RationalBox := ⟨-91/60, 91/60, -91/60, 91/60⟩

theorem mem_rootBox (p : Point) (hn : sqdist p (0, 0) < ((91 : ℝ) / 60) ^ 2) :
    rootBox.Mem p := by
  norm_num [RationalBox.Mem, rootBox]
  dsimp [sqdist] at hn
  constructor
  · nlinarith [sq_nonneg (p.1 + 91/60), sq_nonneg p.2]
  constructor
  · nlinarith [sq_nonneg (p.1 - 91/60), sq_nonneg p.2]
  constructor
  · nlinarith [sq_nonneg (p.2 + 91/60), sq_nonneg p.1]
  · nlinarith [sq_nonneg (p.2 - 91/60), sq_nonneg p.1]

#print axioms capacity_of_finite_cover
#print axioms robust_forbidden_ball
#print axioms robust_half_ball_witness
#print axioms no_four_centers_in_east_south

end SquaresInCircles.Nine.CenterCapacityDraft

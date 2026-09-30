module
public import SquaresInCircles.Six.Analytic.WestMixed.Diagonal

@[expose] public section

/-!
# Three boundary points, with no partition of the south variable

The remaining actual domain is
  16/25<=d<=11/14, 53/50-d<=v<=31/50, -2/5<=s<=12/25.
For fixed s, concavity in v leaves v=53/50-d and v=31/50. The first boundary
is concave in d; the second is increasing in d because the diagonal derivative
is at least 7/10. Thus only (v,d)=(21/50,16/25), (31/50,16/25),
(48/175,11/14) remain. An arbitrary south-only summand can be retained.
Compilation and kernel acceptance remain unverified.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.WestMixed

def beta : ℝ := 41/20
def A : ℝ := 19359/50000
def B : ℝ := 30641/50000

def wing (v : ℝ) : ℝ := A*Real.cos v+B*Real.sin v
def gapWave (q : ℝ) : ℝ := (1/2)*Real.cos q-B*Real.sin q

def base (v s d : ℝ) : ℝ := beta*wing v+gapWave (v+d)+diagonalWave (d-s)

private lemma wing_concave : ConcaveOn ℝ (Set.Icc 0 (2/3)) wing := by
  let f' : ℝ → ℝ := fun v => -A*Real.sin v+B*Real.cos v
  let f'' : ℝ → ℝ := fun v => -A*Real.cos v-B*Real.sin v
  have hf (v : ℝ) : HasDerivAt wing (f' v) v := by
    convert ((Real.hasDerivAt_cos v).const_mul A).add
      ((Real.hasDerivAt_sin v).const_mul B) using 1 <;> dsimp [wing,f'] <;> ring
  have hff (v : ℝ) : HasDerivAt f' (f'' v) v := by
    convert ((Real.hasDerivAt_sin v).const_mul (-A)).add
      ((Real.hasDerivAt_cos v).const_mul B) using 1 <;> dsimp [f',f''] <;> ring
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc 0 (2/3))
    (f' := f') (f'' := f'') (by dsimp [wing]; fun_prop)
  · intro v _; exact (hf v).hasDerivWithinAt
  · intro v _; exact (hff v).hasDerivWithinAt
  · intro v hv
    have h := interior_subset hv
    have hc := Real.cos_nonneg_of_mem_Icc
      (show v ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by
        constructor <;> linarith [h.1,h.2,Real.pi_gt_d2])
    have hs := Real.sin_nonneg_of_nonneg_of_le_pi h.1
      (by linarith [h.2,Real.pi_gt_d2])
    dsimp [f'',A,B]
    linarith

lemma west_concave {s d : ℝ} (hd : 16/25 ≤ d ∧ d ≤ 11/14) :
    ConcaveOn ℝ (Set.Icc 0 (31/50)) (fun v => base v s d) := by
  let a := beta*A+(1/2)*Real.cos d-B*Real.sin d
  let b := beta*B-(1/2)*Real.sin d-B*Real.cos d
  have hcd := Real.cos_nonneg_of_mem_Icc
    (show d ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hd.1,hd.2,Real.pi_gt_d2])
  have hA : 0 ≤ a := by
    dsimp [a,beta,A,B]
    linarith [Real.sin_le_one d]
  have hB : 0 ≤ b := by
    have h := WestCoreBounds.adverse_harmonic d
    dsimp [b,beta,B,WestCoreBounds.B] at *
    linarith
  let f' : ℝ → ℝ := fun v => -a*Real.sin v+b*Real.cos v
  let f'' : ℝ → ℝ := fun v => -a*Real.cos v-b*Real.sin v
  have ident (v : ℝ) : base v s d=diagonalWave (d-s)+a*Real.cos v+b*Real.sin v := by
    dsimp [base,wing,gapWave,a,b]
    rw [Real.cos_add,Real.sin_add]
    ring
  have hf (v : ℝ) : HasDerivAt (fun x => base x s d) (f' v) v := by
    simp_rw [ident]
    convert (((Real.hasDerivAt_cos v).const_mul a).const_add (diagonalWave (d-s))).add
      ((Real.hasDerivAt_sin v).const_mul b) using 1 <;> dsimp [f'] <;> ring
  have hff (v : ℝ) : HasDerivAt f' (f'' v) v := by
    convert ((Real.hasDerivAt_sin v).const_mul (-a)).add
      ((Real.hasDerivAt_cos v).const_mul b) using 1 <;> dsimp [f',f''] <;> ring
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc 0 (31/50))
    (f' := f') (f'' := f'') (by dsimp [base,wing,gapWave,diagonalWave]; fun_prop)
  · intro v _; exact (hf v).hasDerivWithinAt
  · intro v _; exact (hff v).hasDerivWithinAt
  · intro v hv
    have h := interior_subset hv
    have hc := Real.cos_nonneg_of_mem_Icc
      (show v ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by
        constructor <;> linarith [h.1,h.2,Real.pi_gt_d2])
    have hs := Real.sin_nonneg_of_nonneg_of_le_pi h.1
      (by linarith [h.2,Real.pi_gt_d2])
    have hp := add_nonneg (mul_nonneg hA hc) (mul_nonneg hB hs)
    dsimp [f'']
    linarith

lemma wall_concave {s : ℝ} (hs : -(2/5) ≤ s ∧ s ≤ 12/25) :
    ConcaveOn ℝ (Set.Icc (16/25) (11/14)) (fun d => base (53/50-d) s d) := by
  have hw0 := concave_affine_argument (a := -1) (b := 53/50) wing_concave
    (l := 16/25) (u := 11/14) (by
      intro d hd
      constructor <;> linarith [hd.1,hd.2])
  have hw : ConcaveOn ℝ (Set.Icc (16/25) (11/14)) (fun d => beta*wing (53/50-d)) := by
    have h := hw0.smul (by norm_num [beta] : 0 ≤ beta)
    convert h using 1
    funext d
    simp only [smul_eq_mul]
    congr 2
    ring
  have hr0 := concave_affine_argument (a := 1) (b := -s) diagonal_concave
    (l := 16/25) (u := 11/14) (by
      intro d hd
      constructor <;> linarith [hd.1,hd.2,hs.1,hs.2])
  have hr : ConcaveOn ℝ (Set.Icc (16/25) (11/14)) (fun d => diagonalWave (d-s)) := by
    simpa only [one_mul,sub_eq_add_neg] using hr0
  have h := (hw.add (concave_constant (gapWave (53/50)) (16/25) (11/14))).add hr
  convert h using 1
  funext d
  dsimp [base]
  rw [show 53/50-d+d=(53:ℝ)/50 by ring]

lemma top_monotone {s : ℝ} (hs : -(2/5) ≤ s ∧ s ≤ 12/25) :
    MonotoneOn (fun d => base (31/50) s d) (Set.Icc (16/25) (11/14)) := by
  have hf (d : ℝ) : HasDerivAt (fun x => base (31/50) s x)
      (-(1/2)*Real.sin (31/50+d)-B*Real.cos (31/50+d)+diagonalFirst (d-s)) d := by
    have hc := (((hasDerivAt_id d).const_add (31/50)).cos).const_mul (1/2)
    have hs' := (((hasDerivAt_id d).const_add (31/50)).sin).const_mul B
    have hr := (diagonal_hasDeriv (d-s)).comp d ((hasDerivAt_id d).sub_const s)
    convert ((hc.sub hs').add hr).const_add (beta*wing (31/50)) using 1 <;>
      dsimp [base,gapWave] <;> ring
  apply Seven.monoOn_of_hasDeriv_nonneg
    (by dsimp [base,gapWave,diagonalWave]; fun_prop) (fun d _ => hf d)
  intro d hd
  have hr : 0 ≤ d-s ∧ d-s ≤ 6/5 := by
    constructor <;> linarith [hd.1,hd.2,hs.1,hs.2]
  have hD := diagonal_first_lower hr
  have hmono := Real.cos_le_cos_of_nonneg_of_le_pi
    (by norm_num : (0:ℝ) ≤ 63/50)
    (show 31/50+d ≤ Real.pi by linarith [hd.2,Real.pi_gt_d2])
    (show (63:ℝ)/50 ≤ 31/50+d by linarith [hd.1])
  have ht := Seven.cos_upper_four (x := (63:ℝ)/50) (by norm_num)
  have hcos : Real.cos (31/50+d) ≤ 31/100 := by nlinarith only [hmono,ht]
  dsimp [B]
  linarith [Real.sin_le_one (31/50+d)]

/-- The south-only term K may be an explicit function of s in an application. -/
theorem positive_of_three_points {K v s d : ℝ}
    (hs : -(2/5) ≤ s ∧ s ≤ 12/25) (hd : 16/25 ≤ d ∧ d ≤ 11/14)
    (hv : 53/50-d ≤ v ∧ v ≤ 31/50)
    (hleft : 0 < K+base (21/50) s (16/25))
    (hright : 0 < K+base (48/175) s (11/14))
    (htop : 0 < K+base (31/50) s (16/25)) :
    0 < K+base v s d := by
  have hwallc := (concave_constant K (16/25) (11/14)).add (wall_concave hs)
  have hl : 0 < K+base (53/50-16/25) s (16/25) := by
    convert hleft using 1 <;> norm_num
  have hu : 0 < K+base (53/50-11/14) s (11/14) := by
    convert hright using 1 <;> norm_num
  have hwall := positive_on_concave_interval hwallc hd hl hu
  have hm := top_monotone hs (by norm_num : (16:ℝ)/25 ∈ Set.Icc (16/25) (11/14)) hd hd.1
  have htop' : 0 < K+base (31/50) s d := by linarith
  have hc := (concave_constant K 0 (31/50)).add (west_concave (s := s) hd)
  have hmin := hc.min_le_of_mem_Icc
    (show 53/50-d ∈ Set.Icc 0 (31/50) by constructor <;> linarith [hd.1,hd.2])
    (by norm_num : (31:ℝ)/50 ∈ Set.Icc 0 (31/50)) hv
  exact (lt_min hwall htop').trans_le hmin

end SquaresInCircles.Six.Analytic.WestMixed

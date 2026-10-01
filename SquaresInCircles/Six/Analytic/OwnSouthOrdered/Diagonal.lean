import SquaresInCircles.Six.Analytic.OwnSouthOrdered.Chord

/-!
# Diagonal monotonicity without a partition

The chord derivative is decreasing; the opposite-wing derivative is increasing.
Since v,s >= 0, the full d derivative is bounded by its v=s=0 expression.
Taylor inequalities reduce that expression to
  -53/320 + (613/1000)d - (461/800)d^2,
whose completed-square remainder is -47973/18440000.
Thus the whole domain reduces to d=11/14. No grid or root finder is involved.
Compilation remains unverified.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.OwnSouthOrdered

def wingCos : ℝ := 19359/50000
def wingSin : ℝ := 30641/50000

def wing (x : ℝ) : ℝ := wingCos*Real.cos x+wingSin*Real.sin x

def southTerm (x : ℝ) : ℝ := -wingSin*Real.cos x+(1/2)*Real.sin x

def southDerivative (x : ℝ) : ℝ := wingSin*Real.sin x+(1/2)*Real.cos x

def profile (v s d : ℝ) : ℝ :=
  -83178077/125000000+westWeight*wing v+southWeight*wing s+
    chord (d+v)+southTerm (d-s)

lemma south_hasDeriv (x : ℝ) : HasDerivAt southTerm (southDerivative x) x := by
  convert ((Real.hasDerivAt_cos x).const_mul (-wingSin)).add
    ((Real.hasDerivAt_sin x).const_mul (1/2)) using 1
  · funext y
    simp only [southTerm,Pi.add_apply]
  · simp only [southDerivative]
    ring

lemma south_derivative_hasDeriv (x : ℝ) :
    HasDerivAt southDerivative (wingSin*Real.cos x-(1/2)*Real.sin x) x := by
  convert ((Real.hasDerivAt_sin x).const_mul wingSin).add
    ((Real.hasDerivAt_cos x).const_mul (1/2)) using 1
  · funext y
    simp only [southDerivative,Pi.add_apply]
  · ring

lemma south_derivative_monotone :
    MonotoneOn southDerivative (Set.Icc (-(1/6)) (4/5)) := by
  apply Seven.monoOn_of_hasDeriv_nonneg (f := southDerivative)
    (fun x _ => (south_derivative_hasDeriv x).continuousAt.continuousWithinAt)
    (fun x _ => south_derivative_hasDeriv x)
  intro x hx
  have hxx : x^2 ≤ (4/5:ℝ)^2 := by
    have h := mul_nonneg
      (show 0 ≤ 4/5-x by linarith [hx.2])
      (show 0 ≤ 4/5+x by linarith [hx.1])
    nlinarith only [h]
  have hc : 17/25 ≤ Real.cos x := by
    nlinarith only [hxx,Real.one_sub_sq_div_two_le_cos (x := x)]
  have hmono := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi/2) ≤ x by linarith [hx.1,Real.pi_gt_d2])
    (show (4:ℝ)/5 ≤ Real.pi/2 by linarith [Real.pi_gt_d2]) hx.2.le
  have hs : Real.sin x ≤ 4/5 := hmono.trans (Real.sin_le (by norm_num))
  dsimp [wingSin]
  linarith

/-- The only scalar reserve needed for the diagonal derivative. -/
lemma diagonal_comparison_negative {d : ℝ} (hd : 1/2 ≤ d ∧ d ≤ 11/14) :
    (159/100)*Real.cos d+wingSin*Real.sin d-
      (chordCoefficient/2)*Real.cos (d/2) < 0 := by
  have hd0 : 0 ≤ d := by linarith [hd.1]
  have hd8 : d ≤ 4/5 := by linarith [hd.2]
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi hd0
    (by linarith [hd.2,Real.pi_gt_d2])
  have hc0 := Real.cos_nonneg_of_mem_Icc
    (show d/2 ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hd.1,hd.2,Real.pi_gt_d2])
  have hC := mul_nonneg
    (show 0 ≤ chordCoefficient/2-7/4 by norm_num [chordCoefficient]) hc0
  have hB := mul_nonneg (show 0 ≤ 613/1000-wingSin by norm_num [wingSin]) hs0
  have hcos := Seven.cos_upper_four hd0
  have hsin := Seven.sin_upper_five hd0
  have hhalf := Real.one_sub_sq_div_two_le_cos (x := d/2)
  have hd3 : 0 ≤ d^3 := by positivity
  have h4 := mul_nonneg (sub_nonneg.mpr hd8) hd3
  have hsq := mul_nonneg (sub_nonneg.mpr hd8) (show 0 ≤ 4/5+d by linarith)
  have h5 := mul_nonneg (show 0 ≤ 16/25-d^2 by nlinarith only [hsq]) hd3
  have hcub := mul_nonneg (show 0 ≤ d-1/2 by linarith [hd.1])
    (show 0 ≤ d^2+d/2+1/4 by positivity)
  have hbound : (159/100)*Real.cos d+wingSin*Real.sin d-
      (chordCoefficient/2)*Real.cos (d/2) ≤
      -53/320+(613/1000)*d-(461/800)*d^2 := by
    dsimp [wingSin,chordCoefficient] at *
    nlinarith only [hC,hB,hcos,hsin,hhalf,h4,h5,hcub,hd3]
  have hcomplete := sq_nonneg (d-1226/2305)
  nlinarith only [hbound,hcomplete]

lemma diagonal_derivative_negative {v s d : ℝ}
    (hv : 0 ≤ v ∧ v ≤ 12/25) (hs : 0 ≤ s ∧ s ≤ 2/3)
    (hd : 1/2 ≤ d ∧ d ≤ 11/14) :
    chordDerivative (d+v)+southDerivative (d-s) < 0 := by
  have hdmem : d ∈ Set.Icc (1/2) (4/3) := ⟨hd.1,by linarith [hd.2]⟩
  have hqmem : d+v ∈ Set.Icc (1/2) (4/3) := by
    constructor <;> linarith [hd.1,hd.2,hv.1,hv.2]
  have hchord := chord_derivative_antitone hdmem hqmem (by linarith [hv.1])
  have hrmem : d-s ∈ Set.Icc (-(1/6)) (4/5) := by
    constructor <;> linarith [hd.1,hd.2,hs.1,hs.2]
  have hdmem' : d ∈ Set.Icc (-(1/6)) (4/5) := by
    constructor <;> linarith [hd.1,hd.2]
  have hsouth := south_derivative_monotone hrmem hdmem' (by linarith [hs.1])
  have hlast := diagonal_comparison_negative hd
  dsimp [chordDerivative,southDerivative] at *
  linarith

lemma profile_at_upper_diagonal {v s d : ℝ}
    (hv : 0 ≤ v ∧ v ≤ 12/25) (hs : 0 ≤ s ∧ s ≤ 2/3)
    (hd : 1/2 ≤ d ∧ d ≤ 11/14) : profile v s (11/14) ≤ profile v s d := by
  have hf (x : ℝ) : HasDerivAt (profile v s)
      (chordDerivative (x+v)+southDerivative (x-s)) x := by
    have hq := (chord_hasDeriv (x+v)).comp x ((hasDerivAt_id x).add_const v)
    have hr := (south_hasDeriv (x-s)).comp x ((hasDerivAt_id x).sub_const s)
    convert (hq.add hr).const_add
      (-83178077/125000000+westWeight*wing v+southWeight*wing s) using 1
    · funext y
      simp only [profile,Pi.add_apply,Function.comp_apply,id]
      ring
    · ring
  have hm : MonotoneOn (fun x => -profile v s x) (Set.Icc (1/2) (11/14)) := by
    apply Seven.monoOn_of_hasDeriv_nonneg (f := fun x => -profile v s x)
      (fun x _ => (hf x).neg.continuousAt.continuousWithinAt)
      (fun x _ => (hf x).neg)
    intro x hx
    exact neg_nonneg.mpr (diagonal_derivative_negative hv hs ⟨hx.1.le,hx.2.le⟩).le
  have h := hm hd (by norm_num : (11:ℝ)/14 ∈ Set.Icc (1/2) (11/14)) hd.2
  linarith

end SquaresInCircles.Six.Analytic.OwnSouthOrdered

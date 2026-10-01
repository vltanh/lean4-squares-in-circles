import SquaresInCircles.Six.Wings.Chord
import SquaresInCircles.Six.Wings.Chart

/-!
# Own wings, W turned at least as far as S

Let W and S be separated from C along their own axes, at the angles `v` and `s`
with `0 ≤ s ≤ v`, W and D along the secondary axis of W, and D and S along that
of D. Weights `9/4`, `3/4`, `9/20`, `1`, `1` on C–W, C–S, C–D, W–D and D–S,
against the far-vertex support of W, the chord support of D, the soft support of
S and a face `y` of the box for C, leave the profile: a constant, harmonics in
`v`, `s` and `d`, the chord term in `d + v` and the transverse term
`J(r) = -B cos r + (1/2) sin r - sin² r/12` in `r = d - s`. On
`0 ≤ s ≤ v ≤ 2/3`, `v + s ≤ 24/25`, `1/2 ≤ d ≤ 163/175` it is concave in each
angle: in `v` by the chord curvature; in `s` because `J''' ≤ -2/5` on `[0, 1]`
and the harmonic in `s` lies above a line; in `d` because
`(d + v) + (d - s) ≥ 1`. So it is positive once it is at the four vertices of
the domain in `(v, s)` for the two ends of `d`, where Taylor polynomials exceed
`1/500`. The domain holds for a missing south wing and, read in the reflection
in the diagonal, for a missing west wing with W and S on their own axes and
`v ≤ s`.
-/

noncomputable section
namespace SquaresInCircles.Six.Wings.WestTurned
open Normalization

/-- The transverse term `J(r) = -B cos r + (1/2) sin r - sin² r/12` and its
derivatives. -/
def transverse (r : ℝ) : ℝ := -B*Real.cos r+(1/2)*Real.sin r-1/24+(1/24)*Real.cos (2*r)
def transverseFirst (r : ℝ) : ℝ := B*Real.sin r+(1/2)*Real.cos r-(1/12)*Real.sin (2*r)
def transverseSecond (r : ℝ) : ℝ := B*Real.cos r-(1/2)*Real.sin r-(1/6)*Real.cos (2*r)
def transverseThird (r : ℝ) : ℝ := -B*Real.sin r-(1/2)*Real.cos r+(1/3)*Real.sin (2*r)

lemma transverse_eq (r : ℝ) :
    transverse r=-B*Real.cos r+(1/2)*Real.sin r-Real.sin r^2/12 := by
  have h := Real.cos_two_mul r
  dsimp [transverse]
  nlinarith only [h,Real.sin_sq_add_cos_sq r]

lemma transverse_hasDerivAt (r : ℝ) : HasDerivAt transverse (transverseFirst r) r :=
  (((((Real.hasDerivAt_cos r).const_mul (-B)).fun_add
    ((Real.hasDerivAt_sin r).const_mul (1/2))).sub_const (1/24)).fun_add
    ((((hasDerivAt_id' r).const_mul 2).cos).const_mul (1/24))).congr_deriv
    (by simp only [transverseFirst]; ring)

lemma transverseFirst_hasDerivAt (r : ℝ) :
    HasDerivAt transverseFirst (transverseSecond r) r :=
  ((((Real.hasDerivAt_sin r).const_mul B).fun_add
    ((Real.hasDerivAt_cos r).const_mul (1/2))).fun_sub
    ((((hasDerivAt_id' r).const_mul 2).sin).const_mul (1/12))).congr_deriv
    (by simp only [transverseSecond]; ring)

lemma transverseSecond_hasDerivAt (r : ℝ) :
    HasDerivAt transverseSecond (transverseThird r) r :=
  ((((Real.hasDerivAt_cos r).const_mul B).fun_sub
    ((Real.hasDerivAt_sin r).const_mul (1/2))).fun_sub
    ((((hasDerivAt_id' r).const_mul 2).cos).const_mul (1/6))).congr_deriv
    (by simp only [transverseThird]; ring)

/-- `J''' ≤ -2/5` on `[0, 1]`: for `sin r ≤ 3/4` by `cos r ≥ 1 - (31/50) sin² r`
and a cubic in `sin r`, and otherwise because `cos r ((2/3) sin r - 1/2)` is
small. -/
lemma transverse_third_upper {r : ℝ} (hr : 0 ≤ r ∧ r ≤ 1) :
    transverseThird r ≤ -(2/5) := by
  obtain ⟨hc,hs⟩ := cos_sin_nonneg (x := r) ⟨hr.1,by linarith [Real.pi_gt_d2]⟩
  have hid := Real.sin_two_mul r
  have hB := mul_nonneg (show 0 ≤ B-61/100 by norm_num [B]) hs
  have hpy := Real.sin_sq_add_cos_sq r
  rcases le_total (Real.sin r) (3/4) with hx | hx
  · have hcos : 1-(31/50)*Real.sin r^2 ≤ Real.cos r := by
      nlinarith [mul_nonneg hs (sub_nonneg.mpr hx)]
    have hp := mul_nonpos_of_nonneg_of_nonpos
      (show 0 ≤ Real.cos r-(1-(31/50)*Real.sin r^2) by linarith)
      (show (2/3)*Real.sin r-1/2 ≤ 0 by linarith)
    have hcubic : 0 ≤ 1/10-(17/300)*Real.sin r-(31/100)*Real.sin r^2+(31/75)*Real.sin r^3 := by
      nlinarith [sq_nonneg (Real.sin r-29/50),mul_nonneg hs (sq_nonneg (Real.sin r-29/50))]
    dsimp [transverseThird]
    nlinarith only [hp,hB,hid,hcubic]
  · have hs1 := (Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_gt_d2])
      (by linarith [Real.pi_gt_d2]) hr.2).trans (sin_upper_five (x := 1) (by norm_num))
    have hc2 : Real.cos r ≤ 331/500 := by nlinarith
    have hp := mul_le_mul_of_nonneg_left
      (show (2/3)*Real.sin r-1/2 ≤ 31/500 by norm_num at hs1; linarith) hc
    dsimp [transverseThird,B]
    nlinarith only [hp,hid,hc2,hx,hc]

lemma transverse_second_upper {r : ℝ} (hr : 0 ≤ r ∧ r ≤ 1) :
    transverseSecond r ≤ B-1/6-(2/5)*r := by
  have hd (x : ℝ) : HasDerivAt (fun x => -(transverseSecond x+(2/5)*x))
      (-(transverseThird x+2/5)) x :=
    (((transverseSecond_hasDerivAt x).fun_add
      ((hasDerivAt_id' x).const_mul (2/5))).fun_neg).congr_deriv (by ring)
  have hm : MonotoneOn (fun x => -(transverseSecond x+(2/5)*x)) (Set.Icc 0 1) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun x _ => (hd x).continuousAt.continuousWithinAt) (fun x _ => hd x)
    intro x hx
    linarith [transverse_third_upper ⟨hx.1.le,hx.2.le⟩]
  have h0 : transverseSecond 0 = B-1/6 := by norm_num [transverseSecond]
  have h := hm (by norm_num : (0:ℝ) ∈ Set.Icc 0 1) hr hr.1
  dsimp only at h
  linarith

/-- The harmonic `A cos s + B sin s` lies above `A + (49/100) s` on `[0, 12/25]`,
being concave there and above the line at both ends. -/
lemma wing_affine_lower {s : ℝ} (hs : 0 ≤ s ∧ s ≤ 12/25) :
    A+(49/100)*s ≤ harmonic A B s := by
  have hc : ConcaveOn ℝ (Set.Icc 0 (12/25)) (fun x => harmonic A B x-A-(49/100)*x) :=
    concave_of_deriv2 (f' := fun x => harmonic B (-A) x-49/100)
      (f'' := fun x => harmonic (-A) (-B) x)
      (fun x _ => ((harmonic_hasDerivAt A B x).sub_const A).sub
        ((hasDerivAt_id' x).const_mul (49/100)) |>.congr_deriv (by ring))
      (fun x _ => ((harmonic_hasDerivAt B (-A) x).sub_const _).congr_deriv (by simp [harmonic]))
      (fun x ⟨h1,h2⟩ => by
        obtain ⟨hc,hs⟩ := cos_sin_nonneg (x := x) ⟨h1,by linarith [Real.pi_gt_d2]⟩
        simp only [harmonic,A,B]
        nlinarith)
  have hright : 0 ≤ harmonic A B (12/25)-A-(49/100)*(12/25) := by
    have hcos := cos_lower_six (x := (12:ℝ)/25) (by norm_num)
    have hsin := sin_lower_seven (x := (12:ℝ)/25) (by norm_num)
    simp only [harmonic,A,B]
    nlinarith only [hcos,hsin]
  have h := (le_min (show (0:ℝ) ≤ harmonic A B 0-A-(49/100)*0 by norm_num [harmonic]) hright).trans
    (hc.min_le_of_mem_Icc (by norm_num) (by norm_num) hs)
  linarith

lemma diagonal_trig_lower {d : ℝ} (hd : 1/2 ≤ d ∧ d ≤ 163/175) :
    4/3 ≤ Real.cos d+Real.sin d := by
  have h := harmonic_pos_of_endpoints (K := -(4/3)) (A := 1) (B := 1)
    (l := 1/2) (u := 163/175) (x := d) (by norm_num) (by norm_num)
    (by norm_num) (by linarith [Real.pi_gt_d2]) hd
    (by nlinarith only [Real.one_sub_sq_div_two_le_cos (x := (1:ℝ)/2),
      Real.sin_ge_sub_cube (x := (1:ℝ)/2) (by norm_num)])
    (by nlinarith only [Real.one_sub_sq_div_two_le_cos (x := (163:ℝ)/175),
      Real.sin_ge_sub_cube (x := (163:ℝ)/175) (by norm_num)])
  linarith

/-! ### The profile and its concavity -/

/-- The constant term of the profile. -/
def constantTerm : ℝ := 20670077/250000000

/-- The terms of the profile in `v` and in `s`, for the face `y` of the box. -/
def westPart (y d v : ℝ) : ℝ := harmonic ((9/4)*A) ((9/4)*(1/2+y)) v+chord chordSin chordCos (d+v)
def southPart (y d s : ℝ) : ℝ := harmonic ((3/4)*(1/2-y)) ((3/4)*B) s+transverse (d-s)

/-- The threshold sum less the supports, up to the width of `d + v`. -/
def profile (y v s d : ℝ) : ℝ :=
  constantTerm+harmonic ((9/20)*A) ((9/20)*(1/2-y)) d+westPart y d v+southPart y d s

lemma west_concave {y d : ℝ} (hy : 0 ≤ y ∧ y ≤ 1/2) (hd : 1/2 ≤ d ∧ d ≤ 163/175) :
    ConcaveOn ℝ (Set.Icc 0 (2/3)) (westPart y d) :=
  concave_of_deriv2
    (f' := fun v => harmonic ((9/4)*(1/2+y)) (-((9/4)*A)) v+chordFirst chordSin chordCos (d+v))
    (f'' := fun v => -harmonic ((9/4)*A) ((9/4)*(1/2+y)) v+chordSecond chordSin chordCos (d+v))
    (fun v _ => ((harmonic_hasDerivAt _ _ v).add ((chord_hasDerivAt _ _ (d+v)).comp v
      ((hasDerivAt_id' v).const_add d))).congr_deriv (by simp))
    (fun v _ => ((harmonic_hasDerivAt _ _ v).add ((chordFirst_hasDerivAt _ _ (d+v)).comp v
      ((hasDerivAt_id' v).const_add d))).congr_deriv (by simp [harmonic]; ring))
    (fun v ⟨h1,h2⟩ => by
      obtain ⟨hc,hs⟩ := cos_sin_nonneg (x := v) ⟨h1,by linarith [Real.pi_gt_d2]⟩
      have hq := chord_second_nonpositive le_rfl le_rfl
        (show 1/2 ≤ d+v ∧ d+v ≤ 5/3 by constructor <;> linarith)
      have hp : 0 ≤ harmonic ((9/4)*A) ((9/4)*(1/2+y)) v := by
        simp only [harmonic,A]; nlinarith
      linarith)

lemma south_curvature_negative {y s d : ℝ} (hy : 0 ≤ y ∧ y ≤ coreUpper)
    (hs : 0 ≤ s ∧ s ≤ 12/25) (hd : 1/2 ≤ d ∧ d ≤ 163/175) :
    -harmonic ((3/4)*(1/2-y)) ((3/4)*B) s+transverseSecond (d-s) < 0 := by
  obtain ⟨hc,-⟩ := cos_sin_nonneg (x := s) ⟨hs.1,by linarith [Real.pi_gt_d2]⟩
  have hwing := wing_affine_lower hs
  have htrans := transverse_second_upper (show 0 ≤ d-s ∧ d-s ≤ 1 by constructor <;> linarith)
  have hp := mul_nonneg (show 0 ≤ (1/2-y)-A by dsimp [A,coreUpper] at hy ⊢; linarith) hc
  simp only [harmonic,A,B] at *
  nlinarith

lemma south_concave {y d : ℝ} (hy : 0 ≤ y ∧ y ≤ coreUpper) (hd : 1/2 ≤ d ∧ d ≤ 163/175) :
    ConcaveOn ℝ (Set.Icc 0 (12/25)) (southPart y d) :=
  concave_of_deriv2
    (f' := fun s => harmonic ((3/4)*B) (-((3/4)*(1/2-y))) s-transverseFirst (d-s))
    (f'' := fun s => -harmonic ((3/4)*(1/2-y)) ((3/4)*B) s+transverseSecond (d-s))
    (fun s _ => ((harmonic_hasDerivAt _ _ s).add ((transverse_hasDerivAt (d-s)).comp s
      ((hasDerivAt_id' s).const_sub d))).congr_deriv (by ring))
    (fun s _ => ((harmonic_hasDerivAt _ _ s).sub ((transverseFirst_hasDerivAt (d-s)).comp s
      ((hasDerivAt_id' s).const_sub d))).congr_deriv (by simp [harmonic]; ring))
    (fun s hs => (south_curvature_negative hy hs hd).le)

lemma diagonal_concave {y v s : ℝ} (hy : 0 ≤ y ∧ y ≤ coreUpper)
    (hv : v ≤ 2/3) (hs : 0 ≤ s) (horder : s ≤ v) (hsum : v+s ≤ 24/25) :
    ConcaveOn ℝ (Set.Icc (1/2) (163/175)) (profile y v s) := by
  have e : profile y v s = fun d => (constantTerm+harmonic ((9/4)*A) ((9/4)*(1/2+y)) v+
      harmonic ((3/4)*(1/2-y)) ((3/4)*B) s)+(harmonic ((9/20)*A) ((9/20)*(1/2-y)) d+
      chord chordSin chordCos (d+v)+transverse (d-s)) := by
    funext d; simp only [profile,westPart,southPart]; ring
  rw [e]
  refine concave_of_deriv2
    (f' := fun d => harmonic ((9/20)*(1/2-y)) (-((9/20)*A)) d+
      chordFirst chordSin chordCos (d+v)+transverseFirst (d-s))
    (f'' := fun d => -harmonic ((9/20)*A) ((9/20)*(1/2-y)) d+
      chordSecond chordSin chordCos (d+v)+transverseSecond (d-s))
    (fun d _ => ((((harmonic_hasDerivAt _ _ d).add ((chord_hasDerivAt _ _ (d+v)).comp d
      ((hasDerivAt_id' d).add_const v))).add ((transverse_hasDerivAt (d-s)).comp d
      ((hasDerivAt_id' d).sub_const s))).const_add _).congr_deriv (by simp))
    (fun d _ => (((harmonic_hasDerivAt _ _ d).add ((chordFirst_hasDerivAt _ _ (d+v)).comp d
      ((hasDerivAt_id' d).add_const v))).add ((transverseFirst_hasDerivAt (d-s)).comp d
      ((hasDerivAt_id' d).sub_const s))).congr_deriv (by simp [harmonic]; ring))
    (fun d ⟨h1,h2⟩ => ?_)
  have hd : 1/2 ≤ d ∧ d ≤ 163/175 := ⟨h1,h2⟩
  obtain ⟨-,hsd⟩ := cos_sin_nonneg (x := d) ⟨by linarith,by linarith [Real.pi_gt_d2]⟩
  have htrig := diagonal_trig_lower hd
  have hp := mul_nonneg (show 0 ≤ (1/2-y)-A by dsimp [A,coreUpper] at hy ⊢; linarith) hsd
  have htrans := transverse_second_upper (show 0 ≤ d-s ∧ d-s ≤ 1 by constructor <;> linarith)
  by_cases hq : d+v ≤ 3/2
  · have hmin : 1 ≤ min (d+v) 1+(d-s) := by
      rcases le_total (d+v) 1 with h | h
      · rw [min_eq_left h]; linarith
      · rw [min_eq_right h]; linarith
    have hchord := chord_second_envelope le_rfl le_rfl
      (show 1/2 ≤ d+v ∧ d+v ≤ 3/2 by constructor <;> linarith)
    simp only [harmonic,A,B] at *
    nlinarith
  · have hchord := chord_second_high le_rfl le_rfl
      (show 157/200 ≤ d+v ∧ d+v ≤ 5/3 by constructor <;> linarith)
    simp only [harmonic,A,B] at *
    nlinarith

/-! ### Positivity -/

/-- At each `d`, positivity at the four vertices `(0, 0)`, `(2/3, 0)`,
`(2/3, 22/75)` and `(12/25, 12/25)` of the domain in `(v, s)` gives positivity
on the domain: the profile is concave in `v`, and along the edges `v = s`,
`v = 2/3` and `v + s = 24/25` it is a sum of concave parts. -/
lemma positive_of_vertices {y v s d : ℝ} (hy : 0 ≤ y ∧ y ≤ coreUpper)
    (hv : v ≤ 2/3) (hs : 0 ≤ s) (horder : s ≤ v) (hsum : v+s ≤ 24/25)
    (hd : 1/2 ≤ d ∧ d ≤ 163/175)
    (h1 : 0 < profile y 0 0 d) (h2 : 0 < profile y (2/3) 0 d)
    (h3 : 0 < profile y (2/3) (22/75) d) (h4 : 0 < profile y (12/25) (12/25) d) :
    0 < profile y v s d := by
  have hy' : 0 ≤ y ∧ y ≤ 1/2 := ⟨hy.1,by dsimp [coreUpper] at hy; linarith⟩
  have hW := west_concave hy' hd
  have hS := south_concave hy hd
  have K := fun l u : ℝ => concaveOn_const (𝕜 := ℝ)
    (constantTerm+harmonic ((9/20)*A) ((9/20)*(1/2-y)) d) (convex_Icc l u)
  have hequal : 0 < profile y s s d :=
    concave_gt_of_endpoints (f := fun s => profile y s s d)
      (((K 0 (12/25)).add (hW.subset (Set.Icc_subset_Icc le_rfl (by norm_num))
        (convex_Icc 0 (12/25)))).add hS) ⟨hs,by linarith⟩ h1 h4
  have hcv : ConcaveOn ℝ (Set.Icc 0 (2/3)) (fun x => profile y x s d) :=
    ((K 0 (2/3)).add hW).add (concaveOn_const (southPart y d s) (convex_Icc 0 (2/3)))
  by_cases hcut : s ≤ 22/75
  · have htop : 0 < profile y (2/3) s d :=
      concave_gt_of_endpoints (f := fun s => profile y (2/3) s d)
        ((concaveOn_const (constantTerm+harmonic ((9/20)*A) ((9/20)*(1/2-y)) d+
          westPart y d (2/3)) (convex_Icc 0 (22/75))).add (hS.subset
          (Set.Icc_subset_Icc le_rfl (by norm_num)) (convex_Icc 0 (22/75)))) ⟨hs,hcut⟩ h2 h3
    exact (lt_min hequal htop).trans_le (hcv.min_le_of_mem_Icc
      (show s ∈ Set.Icc 0 (2/3) by constructor <;> linarith)
      (by norm_num : (2:ℝ)/3 ∈ Set.Icc 0 (2/3)) ⟨horder,hv⟩)
  · have hw : ConcaveOn ℝ (Set.Icc (22/75) (12/25)) (fun s => westPart y d (24/25-s)) := by
      have h := concave_affine_argument (a := -1) (b := 24/25) hW (l := 22/75) (u := 12/25)
        (fun s hs => by constructor <;> linarith [hs.1,hs.2])
      convert h using 2
      ring_nf
    have htop : 0 < profile y (24/25-s) s d :=
      concave_gt_of_endpoints (f := fun s => profile y (24/25-s) s d)
        (((K (22/75) (12/25)).add hw).add (hS.subset (Set.Icc_subset_Icc (by norm_num) le_rfl)
          (convex_Icc (22/75) (12/25)))) ⟨le_of_not_ge hcut,by linarith⟩
        (by norm_num; exact h3) (by norm_num; exact h4)
    exact (lt_min hequal htop).trans_le (hcv.min_le_of_mem_Icc
      (show s ∈ Set.Icc 0 (2/3) by constructor <;> linarith)
      (show 24/25-s ∈ Set.Icc 0 (2/3) by constructor <;> linarith)
      (show s ≤ v ∧ v ≤ 24/25-s by constructor <;> linarith))

/-- The profile with Taylor polynomials in place of `cos` and `sin`. -/
def lower (y v s d : ℝ) : ℝ :=
  constantTerm+(9/20)*A*cosLower d+(9/20)*(1/2-y)*sinBelow d+
    (9/4)*A*cosLower v+(9/4)*(1/2+y)*sinBelow v+
    sinBelow (d+v)-chordSin*sinAbove ((d+v)/2)-chordCos*cosUpper ((d+v)/2)+
    (3/4)*(1/2-y)*cosLower s+(3/4)*B*sinBelow s-
    B*cosUpper (d-s)+(1/2)*sinBelow (d-s)-1/24+(1/24)*cosLower (2*(d-s))

lemma lower_le {y v s d : ℝ} (hy : 0 ≤ y ∧ y ≤ 1/2) :
    lower y v s d ≤ profile y v s d := by
  have cv := cosLower_le v
  have sv := sinBelow_le v
  have cs := cosLower_le s
  have ss := sinBelow_le s
  have cd := cosLower_le d
  have sd := sinBelow_le d
  have sq := sinBelow_le (d+v)
  have ch := le_cosUpper ((d+v)/2)
  have sh := le_sinAbove ((d+v)/2)
  have cr := le_cosUpper (d-s)
  have sr := sinBelow_le (d-s)
  have crr := cosLower_le (2*(d-s))
  have hA : (0:ℝ) ≤ A := by norm_num [A]
  have hB : (0:ℝ) ≤ B := by norm_num [B]
  simp only [lower,profile,westPart,southPart,harmonic,chord,transverse]
  nlinarith [mul_le_mul_of_nonneg_left cv (show 0 ≤ (9/4)*A by positivity),
    mul_le_mul_of_nonneg_left sv (show 0 ≤ (9/4)*(1/2+y) by linarith),
    mul_le_mul_of_nonneg_left cs (show 0 ≤ (3/4)*(1/2-y) by linarith),
    mul_le_mul_of_nonneg_left ss (show 0 ≤ (3/4)*B by positivity),
    mul_le_mul_of_nonneg_left cd (show 0 ≤ (9/20)*A by positivity),
    mul_le_mul_of_nonneg_left sd (show 0 ≤ (9/20)*(1/2-y) by linarith),
    mul_le_mul_of_nonneg_left sh (show (0:ℝ) ≤ chordSin by norm_num [chordSin]),
    mul_le_mul_of_nonneg_left ch (show (0:ℝ) ≤ chordCos by norm_num [chordCos]),
    mul_le_mul_of_nonneg_left cr hB]

/-- The profile is positive on `0 ≤ s ≤ v ≤ 2/3`, `v + s ≤ 24/25`,
`1/2 ≤ d ≤ 163/175` for both faces of the box. -/
theorem positive {y v s d : ℝ} (hy : y = 0 ∨ y = coreUpper)
    (hv : v ≤ 2/3) (hs : 0 ≤ s) (horder : s ≤ v) (hsum : v+s ≤ 24/25)
    (hd : 1/2 ≤ d ∧ d ≤ 163/175) : 0 < profile y v s d := by
  have hy' : 0 ≤ y ∧ y ≤ coreUpper := by
    rcases hy with rfl | rfl <;> norm_num [coreUpper]
  have hy'' : 0 ≤ y ∧ y ≤ 1/2 := ⟨hy'.1,by dsimp [coreUpper] at hy'; linarith⟩
  have vertex (d : ℝ) (hd : d = 1/2 ∨ d = 163/175) :
      0 < profile y 0 0 d ∧ 0 < profile y (2/3) 0 d ∧
        0 < profile y (2/3) (22/75) d ∧ 0 < profile y (12/25) (12/25) d := by
    refine ⟨lt_of_lt_of_le ?_ (lower_le hy''),lt_of_lt_of_le ?_ (lower_le hy''),
      lt_of_lt_of_le ?_ (lower_le hy''),lt_of_lt_of_le ?_ (lower_le hy'')⟩ <;>
    rcases hd with rfl | rfl <;> rcases hy with rfl | rfl <;>
      norm_num [lower,constantTerm,A,B,chordSin,chordCos,coreUpper,
        cosLower,cosUpper,sinBelow,sinAbove,sinLower,sinUpper]
  have h1 := vertex (1/2) (Or.inl rfl)
  have h2 := vertex (163/175) (Or.inr rfl)
  exact concave_gt_of_endpoints (diagonal_concave hy' hv hs horder hsum) hd
    (positive_of_vertices hy' hv hs horder hsum (by norm_num) h1.1 h1.2.1 h1.2.2.1 h1.2.2.2)
    (positive_of_vertices hy' hv hs horder hsum (by norm_num) h2.1 h2.2.1 h2.2.2.1 h2.2.2.2)

/-! ### The stress -/

/-- The first and second components of the force on C. -/
def forceX (v s d : ℝ) : ℝ := (9/4)*Real.cos v-(3/4)*Real.sin s+(9/20)*Real.cos d
def forceY (v s d : ℝ) : ℝ := -(9/4)*Real.sin v+(3/4)*Real.cos s+(9/20)*Real.sin d

/-- The threshold sum less the supports of W, D, S and the face `y` of the box,
which the separations make nonpositive. -/
def defect (y v s d : ℝ) : ℝ :=
  (9/4)*(1/2+angularWidth v)+(3/4)*(1/2+angularWidth s)+(9/20)*(1/2+angularWidth d)+
    (1/2+angularWidth (d+v))+(1/2+angularWidth (d-s))-
    (radiusBound*(123111/50000)-(9/4+1)/2)-
    (radiusBound*chordMajorant (9/20) (d+v)-
      (9/20+Real.sin (d+v)+1-Real.cos (d+v))/2)-
    (rhoBound*(3/4+Real.cos (d-s))+Real.sin (d-s)^2/12)-
    (coreUpper*forceX v s d+y*forceY v s d)

lemma profile_le_defect {y v s d : ℝ} (hv : 0 ≤ v ∧ v ≤ 2/3) (hs : 0 ≤ s ∧ s ≤ 12/25)
    (hd : 1/2 ≤ d ∧ d ≤ 163/175) (hr : d-s ≤ Real.pi/4) :
    profile y v s d ≤ defect y v s d := by
  have hW := angularWidth_eq (x := v) ⟨hv.1,by linarith [Real.pi_gt_d2]⟩
  have hS := angularWidth_eq (x := s) ⟨hs.1,by linarith [Real.pi_gt_d2]⟩
  have hD := angularWidth_eq (x := d) ⟨by linarith,by linarith [Real.pi_gt_d2]⟩
  have hR := angularWidth_eq (x := d-s) ⟨by linarith,by linarith [Real.pi_pos]⟩
  have hQ := angularWidth_lower (d+v)
  rw [profile,westPart,southPart,transverse_eq]
  simp only [defect,forceX,forceY,harmonic,chord,chordMajorant,constantTerm,A,B,
    chordSin,chordCos,radiusBound,rhoBound,
    coreUpper,hW,hS,hD,hR]
  linarith

/-- The separations of a missing south wing with W and S on their own axes and
`s ≤ v` are incompatible on `v ≤ 2/3`, `v + s ≤ 24/25`, `1/2 ≤ d ≤ 163/175`,
`d - s ≤ π/4`. -/
theorem impossible {X : Chart} (hW : X.WestOwn) (hS : X.SouthOwn) (h : X.MissingSouth)
    (hv : X.v ≤ 2/3) (hs : 0 ≤ X.s) (horder : X.s ≤ X.v) (hsum : X.v+X.s ≤ 24/25)
    (hd : 1/2 ≤ X.d ∧ X.d ≤ 163/175) (hr : X.d-X.s ≤ Real.pi/4) : False := by
  have hWD := h.west
  have hDS := h.south
  have hCD := X.diagonal_own
  simp only [Chart.WestOwn,Chart.SouthOwn,Chart.WestWing,Chart.SouthDiagonal] at hW hS hWD hDS
  have hv0 : 0 ≤ X.v := hs.trans horder
  have hw := vertex_support X.west (U := 9/4) (V := -1) (r := 123111/50000) (by norm_num)
    (by norm_num)
  have hdiag := chord_support X.diagonal (z := 9/20) (by norm_num)
    (show 0 ≤ X.d+X.v ∧ X.d+X.v ≤ Real.pi by constructor <;> linarith [Real.pi_gt_d2])
  obtain ⟨hcr,hsr⟩ := cos_sin_nonneg (x := X.d-X.s) ⟨by linarith,by linarith [Real.pi_pos]⟩
  have hc4 : Real.sqrt 2/2 ≤ Real.cos (X.d-X.s) := by
    rw [← Real.cos_pi_div_four]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos]) hr
  have hsqrt : (7071/10000:ℝ) ≤ Real.sqrt 2/2 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num),Real.sqrt_nonneg (2:ℝ)]
  have hsin : Real.sin (X.d-X.s) ≤ 7072/10000 := by
    nlinarith [Real.sin_sq_add_cos_sq (X.d-X.s)]
  have hsouth := soft_support X.south (U := 3/4+Real.cos (X.d-X.s)) (V := Real.sin (X.d-X.s))
    (by linarith) (by rw [abs_of_nonneg hsr]; linarith)
  obtain ⟨hcv,-⟩ := cos_sin_nonneg (x := X.v) ⟨hv0,by linarith [Real.pi_gt_d2]⟩
  obtain ⟨hcd,-⟩ := cos_sin_nonneg (x := X.d) ⟨by linarith,by linarith [Real.pi_gt_d2]⟩
  have hss := (Real.sin_le hs).trans (show X.s ≤ 12/25 by linarith)
  have hcv' : 7/9 ≤ Real.cos X.v := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := X.v)]
  obtain ⟨y,hy,hc⟩ := center_face (X := forceX X.v X.s X.d) (Y := forceY X.v X.s X.d)
    (by simp only [forceX]; nlinarith) (X.box.1.2.trans ceiling_bounds.2.2.2)
    ⟨X.box.2.1,X.box.2.2.trans ceiling_bounds.2.2.2⟩
  have hn : defect y X.v X.s X.d ≤ 0 := by
    norm_num [abs_of_pos] at hw
    simp only [defect,forceX,forceY] at hc ⊢
    linarith
  linarith [positive hy hv hs horder hsum hd,
    profile_le_defect (y := y) ⟨hv0,hv⟩ ⟨hs,by linarith⟩ hd hr]

end SquaresInCircles.Six.Wings.WestTurned

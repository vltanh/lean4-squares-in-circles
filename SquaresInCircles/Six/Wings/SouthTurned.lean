module

public import SquaresInCircles.Six.Wings.Chord
public import SquaresInCircles.Six.Wings.Chart

/-!
# Six squares: own wings, S turned at least as far as W

Let W and S be separated from C along their own axes, at the angles `v` and `s`
with `0 ≤ v ≤ s`, W and D along the secondary axis of W, and D and S along that
of D. Weights `1.82`, `1.59`, `1.09` and `1` on C–W, C–S, W–D and D–S give D
the force `(1.09 sin q, 1.09 cos q - 1)`, `q = d + v`, of squared length
`0.09² + 4.36 sin² (q/2)`, at most `(0.011 + 2.076 sin (q/2))²` since the
difference is a concave quadratic in `sin (q/2)`, positive at both ends. With
the far-vertex supports of W and D, the axial cone support of S and the corner
of the box for C, the separations leave the profile `K + 1.82 h(v) + 1.59 h(s)
+ 1.09 H(q) - B cos r + (1/2) sin r`, with `h = A cos + B sin`, the chord term
`H` and `r = d - s`; the weights have little room, as with `1.8`, `1.6`, `1.1`
the profile keeps less than `10⁻³`. Its derivative in `d` is negative: the chord term is
concave and `B sin r + (1/2) cos r` increases, so the derivative is at most its
value at `v = s = 0`, negative by Taylor bounds. At `d = 11/14` it is a harmonic
in `s` with nonnegative coefficients, and concave along the edges `s = v`,
`s = 2/3` and `v + s = 24/25`; Taylor polynomials at the four vertices give the
sign.
-/

@[expose] public section

noncomputable section
namespace SquaresInCircles.Six.Wings.SouthTurned
open Normalization

/-- With `chordL = R̄ · 2.076/1.09`, the terms of the stress in `q` are
`1.09 chord chordL 0 q`. -/
def chordL : ℝ := radiusBound*2.076/1.09

lemma chordL_le : chordL ≤ chordSin := by norm_num [chordL,chordSin,radiusBound]

/-! ### The force on D -/

lemma half_sine_bounds {q : ℝ} (hq : 1/2 ≤ q ∧ q ≤ 11/14+12/25) :
    6/25 ≤ Real.sin (q/2) ∧ Real.sin (q/2) ≤ 3/5 := by
  obtain ⟨hs,hs',-,-⟩ := trig_bracket (l := 1/4) (u := (11/14+12/25)/2) (x := q/2)
    (by norm_num) (by linarith [Real.pi_gt_d2]) ⟨by linarith [hq.1],by linarith [hq.2]⟩
  norm_num at hs hs'
  exact ⟨by linarith,by linarith⟩

/-- The far-vertex support of D: `(0.011 + 2.076 t)²`, `t = sin (q/2)`, exceeds
the squared length of its force by a concave quadratic in `t`, positive at both
ends of `[6/25, 3/5]`. -/
lemma diagonal_support {a b q : ℝ} (hc : ContainedChart a |b|)
    (hq : 1/2 ≤ q ∧ q ≤ 11/14+12/25) :
    1.09*Real.sin q*a+(1.09*Real.cos q-1)*b ≤
      radiusBound*(0.011+2.076*Real.sin (q/2))-(1.09*Real.sin q+1-1.09*Real.cos q)/2 := by
  obtain ⟨hl,hu⟩ := half_sine_bounds hq
  have hcos : Real.cos q=1-2*Real.sin (q/2)^2 := by
    have h := Real.cos_two_mul (q/2)
    rw [show 2*(q/2)=q by ring] at h
    nlinarith only [h,Real.sin_sq_add_cos_sq (q/2)]
  have hsq : (1.09*Real.sin q)^2+(1.09*Real.cos q-1)^2=0.09^2+4.36*Real.sin (q/2)^2 := by
    rw [show (1.09*Real.sin q)^2+(1.09*Real.cos q-1)^2=(1.09:ℝ)^2+1-2.18*Real.cos q by
        linear_combination (1.09:ℝ)^2*(Real.sin_sq_add_cos_sq q),hcos]
    ring
  have h := vertex_support hc (U := 1.09*Real.sin q) (V := 1.09*Real.cos q-1)
    (r := 0.011+2.076*Real.sin (q/2)) (by linarith) (by
      rw [hsq]
      nlinarith [mul_nonneg (sub_nonneg.mpr hl) (sub_nonneg.mpr hu)])
  linarith [le_abs_self (1.09*Real.sin q),neg_le_abs (1.09*Real.cos q-1)]

/-! ### The profile -/

/-- The term `-B cos r + (1/2) sin r` of the separation D–S, and its derivative. -/
def south (r : ℝ) : ℝ := -B*Real.cos r+(1/2)*Real.sin r
def southFirst (r : ℝ) : ℝ := B*Real.sin r+(1/2)*Real.cos r

lemma south_hasDerivAt (r : ℝ) : HasDerivAt south (southFirst r) r :=
  (((Real.hasDerivAt_cos r).const_mul (-B)).add
    ((Real.hasDerivAt_sin r).const_mul (1/2))).congr_deriv (by simp only [southFirst]; ring)

lemma southFirst_hasDerivAt (r : ℝ) :
    HasDerivAt southFirst (B*Real.cos r-(1/2)*Real.sin r) r :=
  (((Real.hasDerivAt_sin r).const_mul B).add
    ((Real.hasDerivAt_cos r).const_mul (1/2))).congr_deriv (by ring)

/-- The constant term of the profile: the halves `4.705` of the thresholds and
of the far-vertex supports of W and D, less `R̄` times the length bound `2.122`
of the force on W and the intercept `0.011` of that on D, and less `ρ̄` times
the weight `1.59` in the support of S. -/
def constantTerm : ℝ := 4.705-radiusBound*(2.122+0.011)-rhoBound*1.59

/-- The threshold sum less the supports. -/
def profile (v s d : ℝ) : ℝ :=
  constantTerm+1.82*harmonic A B v+1.59*harmonic A B s+1.09*chord chordL 0 (d+v)+south (d-s)

lemma chordFirst_antitone : AntitoneOn (chordFirst chordL 0) (Set.Icc (1/2) (5/3)) := by
  have hm : MonotoneOn (fun q => -chordFirst chordL 0 q) (Set.Icc (1/2) (5/3)) :=
    monoOn_of_hasDeriv_nonneg
      (fun q _ => (chordFirst_hasDerivAt _ _ q).neg.continuousAt.continuousWithinAt)
      (fun q _ => (chordFirst_hasDerivAt _ _ q).neg)
      (fun q hq => neg_nonneg.mpr (chord_second_nonpositive (M := 0) chordL_le
        (by norm_num [chordCos]) ⟨hq.1.le,hq.2.le⟩))
  intro q hq r hr hqr
  linarith [hm hq hr hqr]

/-- The derivative in `d` at `v = s = 0` is negative on `[1/2, 11/14]`: by
Taylor bounds, `d⁴ ≤ (11/14)² d²`, `d⁵ ≤ (11/14)² d³` and `d³ ≥ d²/2` it lies
below a quadratic in `d` whose maximum, near `21/40`, is negative. -/
lemma diagonal_comparison_negative {d : ℝ} (hd : 1/2 ≤ d ∧ d ≤ 11/14) :
    1.59*Real.cos d+B*Real.sin d-1.09*(chordL/2)*Real.cos (d/2) < 0 := by
  have hd0 : 0 ≤ d := by linarith [hd.1]
  have hcos := cos_upper_four hd0
  have hsin := sin_upper_five hd0
  have hhalf := Real.one_sub_sq_div_two_le_cos (x := d/2)
  have hsq : d^2 ≤ (11/14)^2 := by nlinarith
  have h4 := mul_nonneg (sq_nonneg d) (sub_nonneg.mpr hsq)
  have h5 := mul_nonneg (pow_nonneg hd0 3) (sub_nonneg.mpr hsq)
  have h3 := mul_nonneg (sq_nonneg d) (show 0 ≤ d-1/2 by linarith)
  simp only [B,chordL,radiusBound]
  nlinarith only [hcos,hsin,hhalf,h3,h4,h5,hd0,sq_nonneg (d-21/40)]

/-- The profile decreases in `d` on `[1/2, 11/14]`. -/
lemma profile_at_upper_diagonal {v s d : ℝ}
    (hv : 0 ≤ v ∧ v ≤ 12/25) (hs : 0 ≤ s ∧ s ≤ 2/3)
    (hd : 1/2 ≤ d ∧ d ≤ 11/14) : profile v s (11/14) ≤ profile v s d := by
  have hf (x : ℝ) : HasDerivAt (profile v s)
      (1.09*chordFirst chordL 0 (x+v)+southFirst (x-s)) x := by
    have hq := ((chord_hasDerivAt chordL 0 (x+v)).comp x ((hasDerivAt_id' x).add_const v)).const_mul
      (1.09:ℝ)
    have hr := (south_hasDerivAt (x-s)).comp x ((hasDerivAt_id' x).sub_const s)
    have e : profile v s = fun x => (constantTerm+1.82*harmonic A B v+
        1.59*harmonic A B s)+(1.09*chord chordL 0 (x+v)+south (x-s)) := by
      funext x; simp only [profile]; ring
    rw [e]
    exact ((hq.add hr).const_add _).congr_deriv (by simp)
  have hsm : MonotoneOn southFirst (Set.Icc (-(1/6)) (4/5)) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun x _ => (southFirst_hasDerivAt x).continuousAt.continuousWithinAt)
      (fun x _ => southFirst_hasDerivAt x)
    intro x hx
    have hc : 17/25 ≤ Real.cos x := by
      nlinarith [Real.one_sub_sq_div_two_le_cos (x := x),
        mul_nonneg (show 0 ≤ 4/5-x by linarith [hx.2]) (show 0 ≤ 4/5+x by linarith [hx.1])]
    have hs' := (Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [hx.1,Real.pi_gt_d2])
      (show (4:ℝ)/5 ≤ Real.pi/2 by linarith [Real.pi_gt_d2]) hx.2.le).trans
      (Real.sin_le (by norm_num : (0:ℝ) ≤ 4/5))
    simp only [B]
    linarith
  have hm : MonotoneOn (fun x => -profile v s x) (Set.Icc (1/2) (11/14)) := by
    apply monoOn_of_hasDeriv_nonneg (fun x _ => (hf x).neg.continuousAt.continuousWithinAt)
      (fun x _ => (hf x).neg)
    intro x hx
    have hchord := chordFirst_antitone (show x ∈ Set.Icc (1/2) (5/3) by
      constructor <;> linarith [hx.1,hx.2]) (show x+v ∈ Set.Icc (1/2) (5/3) by
      constructor <;> linarith [hx.1,hx.2,hv.1,hv.2]) (by linarith [hv.1])
    have hsouth := hsm (show x-s ∈ Set.Icc (-(1/6)) (4/5) by
      constructor <;> linarith [hx.1,hx.2,hs.1,hs.2]) (show x ∈ Set.Icc (-(1/6)) (4/5) by
      constructor <;> linarith [hx.1,hx.2]) (by linarith [hs.1])
    have hlast := diagonal_comparison_negative ⟨hx.1.le,hx.2.le⟩
    simp only [chordFirst,southFirst] at *
    linarith
  linarith [hm hd (by norm_num : (11:ℝ)/14 ∈ Set.Icc (1/2) (11/14)) hd.2]

/-! ### Positivity at `d = 11/14` -/

/-- A constant plus a harmonic with nonnegative coefficients plus the chord term
at `11/14 + v` is concave on `[l, u] ⊆ [0, 12/25]`. -/
lemma edge_concave {P Q K l u : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hl : 0 ≤ l)
    (hu : u ≤ 12/25) :
    ConcaveOn ℝ (Set.Icc l u) (fun v => K+harmonic P Q v+1.09*chord chordL 0 (11/14+v)) :=
  concave_of_deriv2
    (f' := fun v => harmonic Q (-P) v+1.09*chordFirst chordL 0 (11/14+v))
    (f'' := fun v => -harmonic P Q v+1.09*chordSecond chordL 0 (11/14+v))
    (fun v _ => (((harmonic_hasDerivAt P Q v).const_add K).add
      (((chord_hasDerivAt chordL 0 (11/14+v)).comp v
        ((hasDerivAt_id' v).const_add _)).const_mul _)).congr_deriv (by simp))
    (fun v _ => ((harmonic_hasDerivAt Q (-P) v).add
      (((chordFirst_hasDerivAt chordL 0 (11/14+v)).comp v
        ((hasDerivAt_id' v).const_add _)).const_mul _)).congr_deriv (by simp [harmonic]; ring))
    (fun v ⟨h1,h2⟩ => by
      obtain ⟨hc,hs⟩ := cos_sin_nonneg (x := v) ⟨by linarith,by linarith [Real.pi_gt_d2]⟩
      have hq := chord_second_nonpositive (M := 0) chordL_le (by norm_num [chordCos])
        (show 1/2 ≤ 11/14+v ∧ 11/14+v ≤ 5/3 by constructor <;> linarith)
      have hp : 0 ≤ harmonic P Q v := by simp only [harmonic]; positivity
      linarith)

private lemma upper_trig :
    0 ≤ Real.sin ((11:ℝ)/14) ∧ Real.sin ((11:ℝ)/14) ≤ 4/5 ∧
    Real.cos ((11:ℝ)/14) ≤ 3/4 := by
  obtain ⟨-,hs⟩ := cos_sin_nonneg (x := 11/14) ⟨by norm_num,by linarith [Real.pi_gt_d2]⟩
  have hu := Real.sin_le (x := (11:ℝ)/14) (by norm_num)
  have hc := cos_upper_four (x := (11:ℝ)/14) (by norm_num)
  exact ⟨hs,by linarith,by nlinarith only [hc]⟩

/-- At `d = 11/14` the profile is a harmonic in `s` with nonnegative
coefficients. -/
private lemma s_identity (v s : ℝ) :
    profile v s (11/14) = (constantTerm+1.82*harmonic A B v+1.09*chord chordL 0 (11/14+v))+
      (1.59*A-B*Real.cos (11/14)+(1/2)*Real.sin (11/14))*Real.cos s+
      (1.59*B-B*Real.sin (11/14)-(1/2)*Real.cos (11/14))*Real.sin s := by
  simp only [profile,harmonic,south]
  rw [Real.cos_sub,Real.sin_sub]
  ring

private lemma s_coefficients :
    0 ≤ 1.59*A-B*Real.cos (11/14)+(1/2)*Real.sin (11/14) ∧
      0 ≤ 1.59*B-B*Real.sin (11/14)-(1/2)*Real.cos (11/14) := by
  have h := upper_trig
  simp only [A,B]
  constructor <;> linarith [Real.cos_le_one ((11:ℝ)/14)]

/-- The profile with Taylor polynomials at `d = 11/14`. -/
def lower (v s : ℝ) : ℝ :=
  constantTerm+1.82*(A*cosLower v+B*sinBelow v)+1.59*(A*cosLower s+B*sinBelow s)+
    1.09*(sinBelow (11/14+v)-chordL*sinAbove ((11/14+v)/2))-
    B*cosUpper (11/14-s)+(1/2)*sinBelow (11/14-s)

lemma lower_le {v s : ℝ} : lower v s ≤ profile v s (11/14) := by
  have cv := cosLower_le v
  have sv := sinBelow_le v
  have cs := cosLower_le s
  have ss := sinBelow_le s
  have sq := sinBelow_le (11/14+v)
  have sh := le_sinAbove ((11/14+v)/2)
  have cr := le_cosUpper (11/14-s)
  have sr := sinBelow_le (11/14-s)
  simp only [lower,profile,harmonic,chord,south,A,B,chordL,radiusBound] at *
  nlinarith only [cv,sv,cs,ss,sq,sh,cr,sr]

lemma four_vertices :
    0 < profile 0 0 (11/14) ∧ 0 < profile 0 (2/3) (11/14) ∧
    0 < profile (22/75) (2/3) (11/14) ∧ 0 < profile (12/25) (12/25) (11/14) := by
  refine ⟨lt_of_lt_of_le ?_ lower_le,lt_of_lt_of_le ?_ lower_le,
    lt_of_lt_of_le ?_ lower_le,lt_of_lt_of_le ?_ lower_le⟩ <;>
  norm_num [lower,constantTerm,A,B,chordL,radiusBound,rhoBound,cosLower,cosUpper,sinBelow,
    sinAbove,sinLower,sinUpper]

/-- The profile is positive on `0 ≤ v ≤ s ≤ 2/3`, `v + s ≤ 24/25`,
`1/2 ≤ d ≤ 11/14`. -/
theorem positive {v s d : ℝ} (hv : 0 ≤ v) (hvs : v ≤ s) (hs : s ≤ 2/3)
    (hsum : v+s ≤ 24/25) (hd : 1/2 ≤ d ∧ d ≤ 11/14) : 0 < profile v s d := by
  have hvmax : v ≤ 12/25 := by linarith
  have hs0 : 0 ≤ s := hv.trans hvs
  obtain ⟨h1,h2,h3,h4⟩ := four_vertices
  obtain ⟨hk,hku,hkc⟩ := upper_trig
  have hequal : 0 < profile v v (11/14) := by
    have hc := edge_concave (K := constantTerm)
      (P := (1.82+1.59)*A-B*Real.cos (11/14)+(1/2)*Real.sin (11/14))
      (Q := (1.82+1.59)*B-B*Real.sin (11/14)-(1/2)*Real.cos (11/14))
      (by simp only [A,B]; linarith [Real.cos_le_one ((11:ℝ)/14)])
      (by simp only [B]; linarith [Real.sin_le_one ((11:ℝ)/14),Real.cos_le_one ((11:ℝ)/14)])
      le_rfl (le_refl (12/25:ℝ))
    have e (x : ℝ) : profile x x (11/14) = constantTerm+
        harmonic ((1.82+1.59)*A-B*Real.cos (11/14)+(1/2)*Real.sin (11/14))
          ((1.82+1.59)*B-B*Real.sin (11/14)-(1/2)*Real.cos (11/14)) x+
        1.09*chord chordL 0 (11/14+x) := by
      rw [s_identity]; simp only [harmonic]; ring
    have h := concave_gt_of_endpoints hc ⟨hv,hvmax⟩
      (by rw [← e]; exact h1) (by rw [← e]; exact h4)
    rwa [← e] at h
  have hupper : 0 < profile v s (11/14) := by
    rcases le_total v (22/75) with hcut | hcut
    · have hc := edge_concave (K := constantTerm+1.59*harmonic A B (2/3)+
          south (11/14-2/3)) (P := 1.82*A) (Q := 1.82*B) (by norm_num [A])
          (by norm_num [B]) le_rfl (show (22/75:ℝ) ≤ 12/25 by norm_num)
      have e (x : ℝ) : profile x (2/3) (11/14) = constantTerm+1.59*harmonic A B (2/3)+
          south (11/14-2/3)+harmonic (1.82*A) (1.82*B) x+1.09*chord chordL 0 (11/14+x) := by
        simp only [profile,harmonic]; ring_nf
      have htop := concave_gt_of_endpoints hc ⟨hv,hcut⟩
        (by rw [← e]; exact h2) (by rw [← e]; exact h3)
      rw [← e] at htop
      rw [s_identity] at hequal htop ⊢
      exact harmonic_pos_of_endpoints s_coefficients.1 s_coefficients.2 hv
        (by linarith [Real.pi_gt_d2]) ⟨hvs,hs⟩ hequal htop
    · have hck : 1/2 ≤ Real.cos (24/25) := by
        nlinarith [Real.one_sub_sq_div_two_le_cos (x := (24:ℝ)/25)]
      obtain ⟨-,hsk⟩ := cos_sin_nonneg (x := 24/25) ⟨by norm_num,by linarith [Real.pi_gt_d2]⟩
      have hst : -(1/5) ≤ Real.sin (11/14-24/25) := by
        have h := Real.sin_le (x := -(11/14-24/25)) (by norm_num)
        rw [Real.sin_neg] at h
        norm_num at h ⊢
        linarith
      obtain ⟨hct,-⟩ := cos_sin_nonneg (x := -(11/14-24/25))
        ⟨by norm_num,by linarith [Real.pi_gt_d2]⟩
      rw [Real.cos_neg] at hct
      have hc := edge_concave (K := constantTerm) (l := 22/75) (u := 12/25)
        (P := 1.82*A+1.59*(A*Real.cos (24/25)+B*Real.sin (24/25))-
          B*Real.cos (11/14-24/25)+(1/2)*Real.sin (11/14-24/25))
        (Q := 1.82*B+1.59*(A*Real.sin (24/25)-B*Real.cos (24/25))+
          B*Real.sin (11/14-24/25)+(1/2)*Real.cos (11/14-24/25))
        (by simp only [A,B]; nlinarith [Real.cos_le_one (11/14-24/25:ℝ)])
        (by simp only [A,B]; nlinarith [Real.cos_le_one (24/25:ℝ)]) (by norm_num) le_rfl
      have e (x : ℝ) : profile x (24/25-x) (11/14) = constantTerm+
          harmonic (1.82*A+1.59*(A*Real.cos (24/25)+B*Real.sin (24/25))-
            B*Real.cos (11/14-24/25)+(1/2)*Real.sin (11/14-24/25))
            (1.82*B+1.59*(A*Real.sin (24/25)-B*Real.cos (24/25))+
            B*Real.sin (11/14-24/25)+(1/2)*Real.cos (11/14-24/25)) x+
          1.09*chord chordL 0 (11/14+x) := by
        simp only [profile,harmonic,south]
        rw [show (11:ℝ)/14-(24/25-x)=(11/14-24/25)+x by ring,Real.cos_sub,Real.sin_sub,
          Real.cos_add,Real.sin_add]
        ring
      have htop := concave_gt_of_endpoints hc ⟨hcut,hvmax⟩
        (by rw [← e]; norm_num; exact h3) (by rw [← e]; norm_num; exact h4)
      rw [← e] at htop
      rw [s_identity] at hequal htop ⊢
      exact harmonic_pos_of_endpoints s_coefficients.1 s_coefficients.2 hv
        (by linarith [Real.pi_gt_d2]) ⟨hvs,by linarith⟩ hequal htop
  exact hupper.trans_le (profile_at_upper_diagonal ⟨hv,hvmax⟩ ⟨hs0,hs⟩ hd)

/-! ### The stress -/

/-- The separations of a missing south wing with W and S on their own axes and
`v ≤ s` are incompatible. -/
theorem impossible {X : Chart} (hW : X.WestOwn) (hS : X.SouthOwn) (h : X.MissingSouth)
    (hv : 0 ≤ X.v) (hvs : X.v ≤ X.s) (hs : X.s ≤ 2/3) (hsum : X.v+X.s ≤ 24/25)
    (hd : 1/2 ≤ X.d ∧ X.d ≤ Real.pi/4) : False := by
  have hWD := h.west
  have hDS := h.south
  simp only [Chart.WestOwn,Chart.SouthOwn,Chart.WestWing,Chart.SouthDiagonal] at hW hS hWD hDS
  have hvmax : X.v ≤ 12/25 := by linarith
  have hs0 : 0 ≤ X.s := hv.trans hvs
  have hd' : 1/2 ≤ X.d ∧ X.d ≤ 11/14 := ⟨hd.1,by linarith [Real.pi_lt_d4]⟩
  have hq : 1/2 ≤ X.d+X.v ∧ X.d+X.v ≤ 11/14+12/25 := by constructor <;> linarith
  rw [angularWidth_eq ⟨hv,by linarith [Real.pi_gt_d2]⟩] at hW
  rw [angularWidth_eq ⟨hs0,by linarith [Real.pi_gt_d2]⟩] at hS
  rw [angularWidth_eq ⟨by linarith,by linarith [Real.pi_gt_d2]⟩] at hWD
  have hwr := angularWidth_lower (X.d-X.s)
  have hw := vertex_support X.west (U := 1.82) (V := -1.09) (r := 2.122)
    (by norm_num) (by norm_num)
  have hdiag := diagonal_support X.diagonal hq
  have hc4 : (0.707:ℝ) ≤ Real.cos (X.d-X.s) := by
    have h4 : Real.sqrt 2/2 ≤ Real.cos (X.d-X.s) := by
      rw [← Real.cos_pi_div_four,← Real.cos_abs (X.d-X.s)]
      exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos])
        (abs_le.mpr ⟨by linarith [Real.pi_gt_d2],by linarith⟩)
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num),Real.sqrt_nonneg (2:ℝ)]
  have hsin : |Real.sin (X.d-X.s)| ≤ 0.708 := by
    rw [abs_le]
    constructor <;> nlinarith [Real.sin_sq_add_cos_sq (X.d-X.s)]
  have hsouth := cone_support X.south (U := 1.59+Real.cos (X.d-X.s))
    (V := Real.sin (X.d-X.s)) (by linarith) (by linarith)
  obtain ⟨hcv,hsv⟩ := cos_sin_nonneg (x := X.v) ⟨hv,by linarith [Real.pi_gt_d2]⟩
  obtain ⟨hcs,hss⟩ := cos_sin_nonneg (x := X.s) ⟨hs0,by linarith [Real.pi_gt_d2]⟩
  have hcv' : 7/9 ≤ Real.cos X.v := by nlinarith [Real.one_sub_sq_div_two_le_cos (x := X.v)]
  have hcs' : 7/9 ≤ Real.cos X.s := by nlinarith [Real.one_sub_sq_div_two_le_cos (x := X.s)]
  have hsv' := (Real.sin_le hv).trans (show X.v ≤ 2/3 by linarith)
  have hss' := (Real.sin_le hs0).trans hs
  have hc := mul_le_mul_of_nonneg_left (X.box.1.2.trans ceiling_bounds.2.2.2)
    (show 0 ≤ 1.82*Real.cos X.v-1.59*Real.sin X.s by linarith)
  have hc' := mul_le_mul_of_nonneg_left (X.box.2.2.trans ceiling_bounds.2.2.2)
    (show 0 ≤ -1.82*Real.sin X.v+1.59*Real.cos X.s by linarith)
  have hp := positive hv hvs hs hsum hd'
  norm_num at hw
  simp only [profile,constantTerm,harmonic,chord,south,A,B,chordL,radiusBound,
    rhoBound,coreUpper] at hp hdiag hsouth hc hc' hw
  linarith

end SquaresInCircles.Six.Wings.SouthTurned

module

public import SquaresInCircles.Six.Stress.PairStress
public import SquaresInCircles.Common.Trigonometry

/-!
# Six squares: concavity of the pair gap along lines

The signs of `n`, `w` and `n - w` cut the domain into sectors. On a sector
`|sin|`, `max (sin ·) 0`, the line and `|n|` are constant multiples of `sin` and
of the angle, so the gap is a constant, plus terms `A cos t + B sin t` in
`t = n, w, n - w`, plus an affine function, minus the scaled lengths of the two
forces (`sectorGap`). Along a line of one of three directions, on which `n`,
`w`, or both together vary (a `Sweep`), each trigonometric term is minus its own
second derivative, and each force is a constant vector plus a vector of constant
length that turns with the parameter, so minus `R` times its length has second
derivative at most `R a b/(a + b)`, for bounds `a` and `b` on the two lengths
(`harmonicCurvature_le_harmonic_mean`). Lower bounds for the trigonometric
terms, from `cos x ≥ 1 - x²/2`, `cos x + |sin x| ≥ 1` and the signs of the
sector, make the second derivative nonpositive in every case: the gap is concave
on every segment of these lines that stays in one sector.
-/

@[expose] public section

noncomputable section
namespace SquaresInCircles.Six.Stress.Pair
open Normalization

/-! ### Sectors -/

/-- The sign `±1` and the positive part `1` or `0` of a sign. -/
def sign (p : Bool) : ℝ := if p then 1 else -1
def positivePart (p : Bool) : ℝ := if p then 1 else 0
/-- `x` is nonnegative if `p`, nonpositive otherwise. -/
def HasSign (p : Bool) (x : ℝ) : Prop := if p then 0≤x else x≤0

/-- The sign sector of `(n, w)`: the signs of `n`, `w` and `n - w`. -/
def Sector (pn pw pq : Bool) (n w : ℝ) : Prop :=
  HasSign pn n ∧ HasSign pw w ∧ HasSign pq (n-w)

lemma domain_cos_pos {no wo : Bool} {n w : ℝ} (h : Domain no wo n w) :
    0<Real.cos n ∧ 0<Real.cos w ∧ 0<Real.cos (n-w) := by
  obtain ⟨hn0,hn1,hw0,hw1,hq0,hq1⟩ := domain_bounds h
  refine ⟨?_,?_,?_⟩ <;> apply Real.cos_pos_of_mem_Ioo <;> constructor <;>
    linarith [Real.pi_gt_d2]

lemma sign_abs {p : Bool} {x : ℝ} (hp : HasSign p x) : |x|=sign p*x := by
  cases p
  · simpa [sign] using abs_of_nonpos (show x≤0 from hp)
  · simpa [sign] using abs_of_nonneg (show 0≤x from hp)

lemma sign_sin {p : Bool} {x : ℝ} (hp : HasSign p x) (hx : |x|≤Real.pi) :
    |Real.sin x|=sign p*Real.sin x ∧ max (Real.sin x) 0=positivePart p*Real.sin x := by
  cases p
  · have hs : Real.sin x≤0 := by
      have := Real.sin_nonneg_of_nonneg_of_le_pi (show 0≤-x by linarith [show x≤0 from hp])
        (by linarith [(abs_le.mp hx).1])
      rw [Real.sin_neg] at this
      linarith
    simp [sign,positivePart,abs_of_nonpos hs,max_eq_right hs]
  · have hs := Real.sin_nonneg_of_nonneg_of_le_pi (show 0≤x from hp) ((le_abs_self x).trans hx)
    simp [sign,positivePart,abs_of_nonneg hs,max_eq_left hs]

/-! ### The gap on a sector -/

/-- The constant term of the gap on a sector. -/
def constant (no wo : Bool) (f : Facet) : ℝ :=
  1+mStar-pairBase+(if wo then 1/2 else 0)-(if no then c0 else 0)+
    (match f with
      | .westFirst | .northSecond => rStar+(if no then 1/2 else 0)
      | .westSecond => 0
      | .northFirst => rStar/2)

/-- The coefficients of the terms in `n`, `w` and `q = n - w` of the gap on a
sector. -/
def aN (no : Bool) (f : Facet) : ℝ := if no then 1/2+c0 else if f.model then 1 else 1/2
def bN (no : Bool) (f : Facet) (pn : Bool) : ℝ :=
  sign pn/2+(if no then -c0*positivePart pn else if f.model then 1/2 else 0)
def aW (wo : Bool) : ℝ := if wo then 1/2 else 1
def bW (wo pw : Bool) : ℝ := sign pw/2+(if wo then -c0*positivePart pw else 1/2)
def aQ : Facet → ℝ
  | .westFirst => rStar
  | .westSecond => rStar/2
  | .northFirst => 0
  | .northSecond => rStar
def bQ (f : Facet) (pq : Bool) : ℝ :=
  if f=.westSecond then rStar*sign pq/2 else rStar*(sign pq-1)/2

def trigN (no : Bool) (f : Facet) (pn : Bool) : ℝ → ℝ := harmonic (aN no f) (bN no f pn)
def trigW (wo pw : Bool) : ℝ → ℝ := harmonic (aW wo) (bW wo pw)
def trigQ (f : Facet) (pq : Bool) : ℝ → ℝ := harmonic (aQ f) (bQ f pq)

/-- The slope of the line on the sector of `w`. -/
def slope (pw : Bool) : ℝ := if pw then -13/50 else -18/25

/-- The radius in the bound for the force on N. -/
def northRadius (f : Facet) : ℝ := if f.model then radius else rhoStar

/-- The gap on the sector of the signs `pn`, `pw`, `pq`. -/
def sectorGap (no wo : Bool) (f : Facet) (pn pw pq : Bool) (n w : ℝ) : ℝ :=
  constant no wo f+trigN no f pn n+trigW wo pw w+trigQ f pq (n-w)-slope pw*w-sign pn/1000*n-
    northRadius f*Real.sqrt ((northForce no f n w).1^2+(northForce no f n w).2^2)-
    radius*Real.sqrt ((westForce wo f n w).1^2+(westForce wo f n w).2^2)

/-- On each sector of the domain the gap is `sectorGap`. -/
theorem gap_eq_sectorGap {no wo : Bool} {f : Facet} {pn pw pq : Bool} {n w : ℝ}
    (hd : Domain no wo n w) (hs : Sector pn pw pq n w) :
    gap no wo f n w=sectorGap no wo f pn pw pq n w := by
  have hc := domain_cos_pos hd
  obtain ⟨hn0,hn1,hw0,hw1,hq0,hq1⟩ := domain_bounds hd
  have hpi := Real.pi_gt_d2
  have hN := sign_sin hs.1 (abs_le.mpr ⟨by linarith,by linarith⟩)
  have hW := sign_sin hs.2.1 (abs_le.mpr ⟨by linarith,by linarith⟩)
  have hQ := sign_sin hs.2.2 (abs_le.mpr ⟨by linarith,by linarith⟩)
  have hline : line w=slope pw*w := by
    cases pw
    · have h : w≤0 := hs.2.1
      simp [line,slope,max_eq_left (neg_nonneg.mpr h),max_eq_right h]; ring
    · have h : 0≤w := hs.2.1
      simp [line,slope,max_eq_right (neg_nonpos.mpr h),max_eq_left h]; ring
  unfold gap value threshold northBound vertexBound penalty sectorGap
  rw [hline,sign_abs hs.1]
  simp only [angularWidth,abs_of_pos hc.1,abs_of_pos hc.2.1,abs_of_pos hc.2.2,hN.1,hN.2,hW.1,
    hW.2,hQ.1]
  cases no <;> cases wo <;> cases f <;>
    simp [northForce,westForce,central,Facet.north,Facet.west,Facet.model,constant,trigN,trigW,
      trigQ,harmonic,aN,bN,aW,bW,aQ,bQ,northRadius] <;> ring

/-! ### Lower bounds for the trigonometric terms -/

lemma cos_add_abs_sin {t : ℝ} (ht : |t|≤Real.pi/2) : 1≤Real.cos t+|Real.sin t| := by
  have hc := Real.cos_nonneg_of_mem_Icc (abs_le.mp ht)
  simpa only [abs_of_nonneg hc] using one_le_abs_cos_add_abs_sin t

/-- `trigN ≥ 1/2` on the domain, and `> 9/10` for N along the north side of C
and a facet of the model. -/
lemma trigN_lower {no wo pn pw pq : Bool} {f : Facet} {n w : ℝ}
    (hd : Domain no wo n w) (hs : Sector pn pw pq n w) :
    1/2≤trigN no f pn n ∧ (no=false → f.model → 9/10<trigN no f pn n) := by
  have hnb := (domain_abs hd).1
  have hsign := sign_sin hs.1 (by linarith [Real.pi_gt_d2] : |n|≤Real.pi)
  have hwidth := cos_add_abs_sin (by linarith [Real.pi_gt_d2] : |n|≤Real.pi/2)
  have hcos := (small_angle hnb).1
  have hsin := (Real.abs_sin_le_abs (x := n)).trans hnb
  have hc0 := c0_bounds
  have hsn : 0≤(sign pn+1)*Real.sin n := by
    cases pn <;> simp only [sign] at hsign ⊢ <;> nlinarith [abs_nonneg (Real.sin n),
      neg_abs_le (Real.sin n),le_abs_self (Real.sin n)]
  refine ⟨?_,fun hno hf => ?_⟩
  · cases no
    · cases hf : f.model <;> simp only [trigN,harmonic,aN,bN,hf,Bool.false_eq_true,ite_false,
        ite_true] <;> nlinarith [hsign.1]
    · have hpos : positivePart pn*Real.sin n≤|Real.sin n| := by
        cases pn <;> simp [positivePart,le_abs_self]
      have hmax := (abs_le.mp hsin).2
      simp only [trigN,harmonic,aN,bN,ite_true]
      nlinarith [hsign.1,mul_le_mul_of_nonneg_left hpos c0_pos.le]
  · subst hno
    simp only [trigN,harmonic,aN,bN,hf,Bool.false_eq_true,ite_false,ite_true]
    nlinarith

/-- `trigW ≥ 1/2` for W along its own axis; `≥ 23/25` for W along the west side of
C, and `≥ 1` there when `w ≥ 0`. -/
lemma trigW_lower {no wo pn pw pq : Bool} {n w : ℝ}
    (hd : Domain no wo n w) (hs : Sector pn pw pq n w) :
    (wo=true → 1/2≤trigW wo pw w) ∧
      (wo=false → 23/25≤trigW wo pw w ∧ (0≤w → 1≤trigW wo pw w)) := by
  have hpi := Real.pi_gt_d2
  have hwb := (domain_abs hd).2.1
  have hsign := sign_sin hs.2.1 (by linarith : |w|≤Real.pi)
  have hwidth := cos_add_abs_sin (by linarith : |w|≤Real.pi/2)
  refine ⟨fun hwo => ?_,fun hwo => ?_⟩
  · subst hwo
    cases pw
    · simp only [trigW,harmonic,aW,bW,ite_true,sign,positivePart,Bool.false_eq_true,
        ite_false] at hsign ⊢
      nlinarith [hsign.1]
    · have hw0 : w=0 := le_antisymm (by simpa [wHigh] using hd.2.2) hs.2.1
      subst hw0
      norm_num [trigW,harmonic,aW]
  · subst hwo
    have hw : |w|≤2/5 := by
      have := hd.2
      simp only [wLow,wHigh,Bool.false_eq_true,ite_false] at this
      exact abs_le.mpr ⟨by linarith,by linarith⟩
    have hc := (small_angle hw).1
    have hpos : 0≤(sign pw+1)*Real.sin w := by
      cases pw <;> simp only [sign] at hsign ⊢ <;> nlinarith [neg_abs_le (Real.sin w),
        abs_nonneg (Real.sin w)]
    refine ⟨by simp only [trigW,harmonic,aW,bW,Bool.false_eq_true,ite_false]; nlinarith,
      fun hw0 => ?_⟩
    have hsin := Real.sin_nonneg_of_nonneg_of_le_pi hw0 (by linarith [(abs_le.mp hw).2])
    rw [abs_of_nonneg hsin] at hsign hwidth
    simp only [trigW,harmonic,aW,bW,Bool.false_eq_true,ite_false]
    nlinarith [hsign.1]

/-- `trigQ > 11/50` for a facet of the model, and `> 1/3` there when W is along the
west side of C and `w ≥ 0`; `> 9/50` for the second axis of W, and `≥ 0` for the
first axis of N. -/
lemma trigQ_lower {no wo pn pw pq : Bool} {f : Facet} {n w : ℝ}
    (hd : Domain no wo n w) (hs : Sector pn pw pq n w) :
    (f.model → 11/50<trigQ f pq (n-w) ∧ (wo=false → 0≤w → 1/3<trigQ f pq (n-w))) ∧
    (f=.westSecond → 9/50<trigQ f pq (n-w)) ∧ (f=.northFirst → 0≤trigQ f pq (n-w)) := by
  have hpi := Real.pi_gt_d2
  have hqb := (domain_abs hd).2.2
  have hsign := sign_sin hs.2.2 (by linarith : |n-w|≤Real.pi)
  have hwidth := cos_add_abs_sin (by linarith : |n-w|≤Real.pi/2)
  have hr := rStar_bounds
  have hneg : 0≤(sign pq-1)*Real.sin (n-w) := by
    cases pq <;> simp only [sign] at hsign ⊢ <;> nlinarith [le_abs_self (Real.sin (n-w))]
  have hcos : 31/49≤Real.cos (n-w) := by nlinarith [(small_angle hqb).1]
  have hmodel : f.model → trigQ f pq (n-w)=rStar*Real.cos (n-w)+
      rStar*(sign pq-1)/2*Real.sin (n-w) := by
    cases f <;> simp [trigQ,harmonic,aQ,bQ,Facet.model]
  refine ⟨fun hf => ⟨?_,fun hwo hw0 => ?_⟩,fun hf => ?_,fun hf => ?_⟩
  · rw [hmodel hf]
    nlinarith [mul_nonneg rStar_pos.le hneg,mul_le_mul_of_nonneg_left hcos rStar_pos.le]
  · subst hwo
    rcases le_total (n-w) 0 with hq | hq
    · rw [hmodel hf]
      have hs0 : Real.sin (n-w)≤0 := by
        have := Real.sin_nonneg_of_nonneg_of_le_pi (show 0≤-(n-w) by linarith)
          (by linarith [(abs_le.mp hqb).1])
        rw [Real.sin_neg] at this
        linarith
      rw [abs_of_nonpos hs0] at hsign hwidth
      nlinarith [mul_le_mul_of_nonneg_left hwidth rStar_pos.le,hsign.1]
    · have hq1 : |n-w|≤5/12 := abs_le.mpr ⟨by linarith,by linarith [(domain_bounds hd).2.1]⟩
      have hc := (small_angle hq1).1
      rw [hmodel hf]
      nlinarith [mul_nonneg rStar_pos.le hneg,mul_le_mul_of_nonneg_left hc rStar_pos.le]
  · subst hf
    simp only [trigQ,harmonic,aQ,bQ,ite_true]
    have hm := mul_le_mul_of_nonneg_left hwidth rStar_pos.le
    nlinarith [hsign.1]
  · subst hf
    simp [trigQ,harmonic,aQ,bQ]
    nlinarith [mul_nonneg rStar_pos.le hneg]

/-! ### The forces along the lines -/

/-- The three directions of lines: `n` varies, `w` varies, or both together. -/
inductive Sweep where
  | north | west | diagonal

/-- The angle `n` at the parameter `x` of the line through `(n, w)`. -/
def Sweep.n : Sweep → ℝ → ℝ → ℝ → ℝ
  | north, _, _, x => x
  | west, n, _, _ => n
  | diagonal, _, _, x => x

/-- The angle `w` at the parameter `x` of the line through `(n, w)`. -/
def Sweep.w : Sweep → ℝ → ℝ → ℝ → ℝ
  | north, _, w, _ => w
  | west, _, _, x => x
  | diagonal, _, _, x => x

/-- The squared length `rotor² + baseSq + cosine cos x + sine sin x` of a vector of
squared length `baseSq` plus a vector of length `rotor` that turns with `x`. -/
structure Harmonic where
  rotor : ℝ
  baseSq : ℝ
  cosine : ℝ
  sine : ℝ

/-- The constant squared length `z`. -/
def Harmonic.constant (z : ℝ) : Harmonic := ⟨0,z,0,0⟩
def Harmonic.parameter (W : Harmonic) : ℝ := W.rotor^2+W.baseSq
/-- The squared length at `x`. -/
def Harmonic.arg (W : Harmonic) (x : ℝ) : ℝ := harmonicArg W.parameter W.cosine W.sine x
/-- The second derivative of `-R` times the length. -/
def Harmonic.curvature (W : Harmonic) (R x : ℝ) : ℝ :=
  harmonicCurvature R W.parameter W.cosine W.sine x

/-- The squared length of the force on N along a line. -/
def northHarmonic : Sweep → Bool → Facet → ℝ → ℝ → Harmonic
  | .north, true, .westFirst, _, w => ⟨rStar,1,2*rStar*Real.sin w,-2*rStar*Real.cos w⟩
  | .north, true, .westSecond, _, w => ⟨rStar,1,2*rStar*Real.cos w,2*rStar*Real.sin w⟩
  | .north, true, .northFirst, _, _ => .constant ((1+rStar)^2)
  | .north, true, .northSecond, _, _ => .constant (1+rStar^2)
  | .north, false, .westFirst, _, w => .constant (1+rStar^2+2*rStar*Real.sin w)
  | .north, false, .westSecond, _, w => .constant (1+rStar^2+2*rStar*Real.cos w)
  | .north, false, .northFirst, _, _ => ⟨rStar,1,2*rStar,0⟩
  | .north, false, .northSecond, _, _ => ⟨rStar,1,0,2*rStar⟩
  | .west, true, .westFirst, n, _ => ⟨rStar,1,-2*rStar*Real.sin n,2*rStar*Real.cos n⟩
  | .west, true, .westSecond, n, _ => ⟨rStar,1,2*rStar*Real.cos n,2*rStar*Real.sin n⟩
  | .west, false, .westFirst, _, _ => ⟨rStar,1,0,2*rStar⟩
  | .west, false, .westSecond, _, _ => ⟨rStar,1,2*rStar,0⟩
  | .west, true, .northFirst, _, _ => .constant ((1+rStar)^2)
  | .west, true, .northSecond, _, _ => .constant (1+rStar^2)
  | .west, false, .northFirst, n, _ => .constant (1+rStar^2+2*rStar*Real.cos n)
  | .west, false, .northSecond, n, _ => .constant (1+rStar^2+2*rStar*Real.sin n)
  | .diagonal, true, .westFirst, _, _ => .constant (1+rStar^2)
  | .diagonal, true, .westSecond, _, _ => .constant ((1+rStar)^2)
  | .diagonal, true, .northFirst, _, _ => .constant ((1+rStar)^2)
  | .diagonal, true, .northSecond, _, _ => .constant (1+rStar^2)
  | .diagonal, false, .westFirst, _, _ => ⟨rStar,1,0,2*rStar⟩
  | .diagonal, false, .westSecond, _, _ => ⟨rStar,1,2*rStar,0⟩
  | .diagonal, false, .northFirst, _, _ => ⟨rStar,1,2*rStar,0⟩
  | .diagonal, false, .northSecond, _, _ => ⟨rStar,1,0,2*rStar⟩

/-- The squared length of the force on W along a line. -/
def westHarmonic : Sweep → Bool → Facet → ℝ → ℝ → Harmonic
  | .north, true, .westFirst, _, _ => .constant ((1+rStar)^2+mStar^2)
  | .north, true, .westSecond, _, _ => .constant (1+(mStar-rStar)^2)
  | .north, true, .northFirst, _, w => ⟨rStar,1+mStar^2,
      2*rStar*Real.sin w-2*rStar*mStar*Real.cos w,-2*rStar*Real.cos w-2*rStar*mStar*Real.sin w⟩
  | .north, true, .northSecond, _, w => ⟨rStar,1+mStar^2,
      2*rStar*Real.cos w+2*rStar*mStar*Real.sin w,2*rStar*Real.sin w-2*rStar*mStar*Real.cos w⟩
  | .north, false, .westFirst, _, w =>
      .constant (1+rStar^2+mStar^2+2*rStar*Real.cos w+2*mStar*Real.sin w)
  | .north, false, .westSecond, _, w =>
      .constant (1+(mStar-rStar)^2+2*(mStar-rStar)*Real.sin w)
  | .north, false, .northFirst, _, w => ⟨rStar,1+mStar^2+2*mStar*Real.sin w,
      -2*rStar*mStar*Real.cos w,-2*rStar-2*rStar*mStar*Real.sin w⟩
  | .north, false, .northSecond, _, w => ⟨rStar,1+mStar^2+2*mStar*Real.sin w,
      2*rStar+2*rStar*mStar*Real.sin w,-2*rStar*mStar*Real.cos w⟩
  | .west, true, .westFirst, _, _ => .constant ((1+rStar)^2+mStar^2)
  | .west, true, .westSecond, _, _ => .constant (1+(mStar-rStar)^2)
  | .west, true, .northFirst, n, _ => ⟨rStar,1+mStar^2,
      -2*rStar*Real.sin n-2*rStar*mStar*Real.cos n,2*rStar*Real.cos n-2*rStar*mStar*Real.sin n⟩
  | .west, true, .northSecond, n, _ => ⟨rStar,1+mStar^2,
      2*rStar*Real.cos n-2*rStar*mStar*Real.sin n,2*rStar*Real.sin n+2*rStar*mStar*Real.cos n⟩
  | .west, false, .westFirst, _, _ => ⟨1,rStar^2+mStar^2,2*rStar,2*mStar⟩
  | .west, false, .westSecond, _, _ => ⟨1,(mStar-rStar)^2,0,2*(mStar-rStar)⟩
  | .west, false, .northFirst, n, _ => ⟨mStar,1+rStar^2-2*rStar*Real.sin n,
      -2*rStar*mStar*Real.cos n,2*mStar-2*rStar*mStar*Real.sin n⟩
  | .west, false, .northSecond, n, _ => ⟨mStar,1+rStar^2+2*rStar*Real.cos n,
      -2*rStar*mStar*Real.sin n,2*mStar+2*rStar*mStar*Real.cos n⟩
  | .diagonal, true, .westFirst, _, _ => .constant ((1+rStar)^2+mStar^2)
  | .diagonal, true, .westSecond, _, _ => .constant (1+(mStar-rStar)^2)
  | .diagonal, true, .northFirst, _, _ => .constant (1+(mStar-rStar)^2)
  | .diagonal, true, .northSecond, _, _ => .constant ((1+rStar)^2+mStar^2)
  | .diagonal, false, .westFirst, _, _ => ⟨1,rStar^2+mStar^2,2*rStar,2*mStar⟩
  | .diagonal, false, .westSecond, _, _ => ⟨1,(mStar-rStar)^2,0,2*(mStar-rStar)⟩
  | .diagonal, false, .northFirst, _, _ => ⟨1,(mStar-rStar)^2,0,2*(mStar-rStar)⟩
  | .diagonal, false, .northSecond, _, _ => ⟨1,rStar^2+mStar^2,2*rStar,2*mStar⟩

lemma northHarmonic_arg (k : Sweep) (no : Bool) (f : Facet) (n w x : ℝ) :
    (northHarmonic k no f n w).arg x=(northForce no f (k.n n w x) (k.w n w x)).1^2+
      (northForce no f (k.n n w x) (k.w n w x)).2^2 := by
  cases k <;> cases no <;> cases f <;>
    simp only [northHarmonic,Harmonic.arg,Harmonic.parameter,Harmonic.constant,harmonicArg,
      northForce,central,
      Facet.north,Sweep.n,Sweep.w,Bool.false_eq_true,ite_true,ite_false,sub_self,Real.sin_zero,
      Real.cos_zero,Real.sin_sub,Real.cos_sub] <;> ring_nf <;> simp only [Real.sin_sq] <;> ring

lemma westHarmonic_arg (k : Sweep) (wo : Bool) (f : Facet) (n w x : ℝ) :
    (westHarmonic k wo f n w).arg x=(westForce wo f (k.n n w x) (k.w n w x)).1^2+
      (westForce wo f (k.n n w x) (k.w n w x)).2^2 := by
  cases k <;> cases wo <;> cases f <;>
    simp only [westHarmonic,Harmonic.arg,Harmonic.parameter,Harmonic.constant,harmonicArg,
      westForce,central,
      Facet.west,Sweep.n,Sweep.w,Bool.false_eq_true,ite_true,ite_false,sub_self,Real.sin_zero,
      Real.cos_zero,Real.sin_sub,Real.cos_sub] <;> ring_nf <;> simp only [Real.sin_sq] <;> ring

lemma northHarmonic_amplitude (k : Sweep) (no : Bool) (f : Facet) (n w : ℝ) :
    (northHarmonic k no f n w).cosine^2+(northHarmonic k no f n w).sine^2=
      4*(northHarmonic k no f n w).rotor^2*(northHarmonic k no f n w).baseSq := by
  cases k <;> cases no <;> cases f <;> simp only [northHarmonic,Harmonic.constant] <;> ring_nf <;>
    simp only [Real.sin_sq] <;> ring

lemma westHarmonic_amplitude (k : Sweep) (wo : Bool) (f : Facet) (n w : ℝ) :
    (westHarmonic k wo f n w).cosine^2+(westHarmonic k wo f n w).sine^2=
      4*(westHarmonic k wo f n w).rotor^2*(westHarmonic k wo f n w).baseSq := by
  cases k <;> cases wo <;> cases f <;> simp only [westHarmonic,Harmonic.constant] <;> ring_nf <;>
    simp only [Real.sin_sq] <;> ring

/-! ### Curvature bounds for the lengths of the forces -/

lemma northForce_first {no wo : Bool} {f : Facet} {n w : ℝ} (hd : Domain no wo n w) :
    1/2<(northForce no f n w).1 := by
  have hc := (small_angle (domain_abs hd).1).1
  have hq := (domain_abs hd).2.2
  have hr := rStar_bounds
  cases no <;> cases f <;>
    simp only [northForce,central,Facet.north,Bool.false_eq_true,ite_false,ite_true] <;>
    nlinarith [Real.sin_le_one (n-w),Real.neg_one_le_cos (n-w)]

lemma westForce_first {no wo : Bool} {f : Facet} {n w : ℝ} (hd : Domain no wo n w) :
    1/2<(westForce wo f n w).1 := by
  have hc := (small_angle (domain_abs hd).2.1).1
  have hr := rStar_bounds
  cases wo <;> cases f <;>
    simp only [westForce,central,Facet.west,Bool.false_eq_true,ite_false,ite_true] <;>
    nlinarith [Real.sin_le_one (n-w),Real.neg_one_le_cos (n-w)]

lemma northHarmonic_pos {k : Sweep} {no wo : Bool} {f : Facet} {n w x : ℝ}
    (hd : Domain no wo (k.n n w x) (k.w n w x)) : 0<(northHarmonic k no f n w).arg x := by
  rw [northHarmonic_arg]
  nlinarith [northForce_first (f := f) hd]

lemma westHarmonic_pos {k : Sweep} {no wo : Bool} {f : Facet} {n w x : ℝ}
    (hd : Domain no wo (k.n n w x) (k.w n w x)) : 0<(westHarmonic k wo f n w).arg x := by
  rw [westHarmonic_arg]
  nlinarith [westForce_first (f := f) hd]

@[simp] lemma Harmonic.constant_curvature (z R x : ℝ) :
    (Harmonic.constant z).curvature R x=0 := by
  simp [Harmonic.curvature,Harmonic.constant,Harmonic.parameter,harmonicCurvature]

/-- If the turning length is at most `A` and the constant one at most `B`, the
curvature at a radius `R ≤ 17/10` is at most `M ≥ (17/10) A B/(A + B)`. -/
lemma Harmonic.curvature_le {W : Harmonic} {R x A B M : ℝ} (hR : 0≤R) (hR1 : R≤17/10)
    (hr : 0<W.rotor) (ha : W.cosine^2+W.sine^2=4*W.rotor^2*W.baseSq) (hx : 0<W.arg x)
    (hA : W.rotor≤A) (hB : W.baseSq≤B^2) (hB0 : 0≤B) (hm : (17/10)*A*B/(A+B)≤M) :
    W.curvature R x≤M := by
  have hb : 0≤W.baseSq := by
    by_contra! hb
    nlinarith [sq_nonneg W.cosine,sq_nonneg W.sine,mul_pos (pow_pos hr 2) (neg_pos.mpr hb)]
  have hbs := Real.sq_sqrt hb
  have hb0 := Real.sqrt_nonneg W.baseSq
  have hbup : Real.sqrt W.baseSq≤B := by nlinarith
  have hp : W.parameter=W.rotor^2+(Real.sqrt W.baseSq)^2 := by rw [hbs]; rfl
  have h := harmonicCurvature_le_harmonic_mean hR hr.le hb0 (by linarith) hp
    (by rwa [hbs]) hx
  have hmono := harmonic_mean_mono hr.le hb0 (by linarith) hA hbup
  have hAB : 0≤A*B/(A+B) := div_nonneg (mul_nonneg (by linarith) hB0) (by linarith)
  calc W.curvature R x≤R*(W.rotor*Real.sqrt W.baseSq/(W.rotor+Real.sqrt W.baseSq)) := by
        simpa only [Harmonic.curvature,mul_div_assoc,mul_assoc] using h
    _≤(17/10)*(A*B/(A+B)) := mul_le_mul hR1 hmono (div_nonneg (mul_nonneg hr.le hb0)
        (by linarith)) (by norm_num)
    _≤M := by simpa only [mul_div_assoc,mul_assoc] using hm

/-- Along every line the length of the force on N has curvature at most
`23/50`: it is constant, or a unit vector plus a turning vector of length
`rStar`. -/
lemma north_curvature (k : Sweep) (no : Bool) (f : Facet) (n w x : ℝ) :
    (northHarmonic k no f n w).curvature (northRadius f) x≤23/50 := by
  have hshape : (∃ z, northHarmonic k no f n w=.constant z) ∨
      ((northHarmonic k no f n w).rotor=rStar ∧ (northHarmonic k no f n w).baseSq=1) := by
    cases k <;> cases no <;> cases f <;>
      first | exact Or.inl ⟨_,rfl⟩ | exact Or.inr ⟨rfl,rfl⟩
  rcases hshape with ⟨z,hz⟩ | ⟨hr,hb⟩
  · rw [hz,Harmonic.constant_curvature]; norm_num
  · have hR : 0≤northRadius f ∧ northRadius f≤17/10 := by
      unfold northRadius
      split_ifs <;> constructor <;> linarith [radius_bounds,rhoStar_bounds]
    have hamp := northHarmonic_amplitude k no f n w
    rw [hr,hb] at hamp
    have hx : 0<(northHarmonic k no f n w).arg x :=
      harmonic_arg_positive rStar_pos.le zero_le_one (by linarith [rStar_bounds.2])
        (by simp only [Harmonic.parameter,hr,hb]; ring) (by rw [hamp]; ring)
    apply Harmonic.curvature_le hR.1 hR.2 (by rw [hr]; exact rStar_pos)
      (by rw [hr,hb]; exact hamp) hx (A := 37/100) (B := 1)
      (by rw [hr]; linarith [rStar_bounds.2]) (by rw [hb]; norm_num) (by norm_num)
    norm_num

/-- If the turning vector points against the constant one, so that the squared
length is at most the difference of the squared lengths, the curvature is
nonpositive. -/
lemma Harmonic.curvature_nonpos {W : Harmonic} {R x : ℝ} (hR : 0≤R) (hr : 0<W.rotor)
    (ha : W.cosine^2+W.sine^2=4*W.rotor^2*W.baseSq) (hx : 0<W.arg x)
    (hop : W.cosine*Real.cos x+W.sine*Real.sin x≤-2*W.rotor^2) : W.curvature R x≤0 := by
  have hb : 0≤W.baseSq := by
    by_contra! hb
    nlinarith [sq_nonneg W.cosine,sq_nonneg W.sine,mul_pos (pow_pos hr 2) (neg_pos.mpr hb)]
  have hs := Real.sq_sqrt hb
  have horder : W.rotor≤Real.sqrt W.baseSq := by
    have harg := hx
    simp only [Harmonic.arg,Harmonic.parameter,harmonicArg] at harg
    nlinarith [Real.sqrt_nonneg W.baseSq]
  exact harmonicCurvature_nonpos_of_opposition hR hr.le horder
    (by simp only [Harmonic.parameter,hs])
    (by rwa [hs]) hx hop

/-- The squared length `P + z` with `z = Q cos x + T sin x`: the curvature is
`(R/4)(L - D/L³)` with `L` the length and `D = P² - Q² - T²`, so at most
`(R/4)(B - D₀/B³)` when `L ≤ B` and `D ≥ D₀ ≥ 0`. -/
lemma harmonicCurvature_le_length {R P Q T x D B : ℝ} (hR : 0≤R) (hx : 0<harmonicArg P Q T x)
    (hD : 0≤D) (hDD : D≤P^2-Q^2-T^2) (hB : 0<B) (hL : harmonicArg P Q T x≤B^2) :
    harmonicCurvature R P Q T x≤(R/4)*(B-D/B^3) := by
  set z := Q*Real.cos x+T*Real.sin x
  set L := Real.sqrt (harmonicArg P Q T x)
  have harg : harmonicArg P Q T x=P+z := by simp only [harmonicArg,z]; ring
  have hL0 : 0<L := Real.sqrt_pos.mpr hx
  have hsq : L^2=P+z := by rw [← harg]; exact Real.sq_sqrt hx.le
  have hLB : L≤B := by
    rw [show L=Real.sqrt (harmonicArg P Q T x) from rfl]
    exact Real.sqrt_le_iff.mpr ⟨hB.le,hL⟩
  have hroot : Real.sqrt (P+z)=L := by rw [← harg]
  have hform : harmonicCurvature R P Q T x=(R/4)*(L-(P^2-Q^2-T^2)/L^3) := by
    have hn : z^2+2*P*z+Q^2+T^2=L^4-(P^2-Q^2-T^2) := by
      have : L^4=(P+z)^2 := by rw [← hsq]; ring
      rw [this]; ring
    change R*(z^2+2*P*z+Q^2+T^2)/(4*(P+z)*Real.sqrt (P+z))=_
    rw [hroot,hn,← hsq]
    field_simp
  have hp := pow_le_pow_left₀ hL0.le hLB 3
  have hdiv : D/B^3≤(P^2-Q^2-T^2)/L^3 :=
    (div_le_div_iff₀ (pow_pos hB 3) (pow_pos hL0 3)).mpr
      (mul_le_mul hDD hp (pow_nonneg hL0.le 3) (hD.trans hDD))
  rw [hform]
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- Along the line in `w`, at `x ≤ 0`, for N–W along the first axis of W, the
force on N has curvature at most `3/10`: its length is at most `7/6`. -/
lemma north_curvature_westFirst {no wo : Bool} {n w x : ℝ} (hd : Domain no wo n x) (hx0 : x≤0) :
    (northHarmonic .west no .westFirst n w).curvature (northRadius .westFirst) x≤3/10 := by
  have hr := rStar_bounds
  have hR := radius_bounds
  have hb := domain_bounds hd
  have hz : (northHarmonic .west no .westFirst n w).cosine*Real.cos x+
      (northHarmonic .west no .westFirst n w).sine*Real.sin x≤(3/5)*rStar := by
    cases no
    · have hs : Real.sin x≤0 := by
        have := Real.sin_nonneg_of_nonneg_of_le_pi (show 0≤-x by linarith) (by linarith [hb.2.2.1,
          Real.pi_gt_d2])
        rw [Real.sin_neg] at this; linarith
      simp only [northHarmonic]
      nlinarith [rStar_pos]
    · have hq : -3/10≤Real.sin (n-x) := by
        rcases le_total (n-x) 0 with h | h
        · linarith [Real.le_sin h]
        · linarith [Real.sin_nonneg_of_nonneg_of_le_pi h (by linarith [Real.pi_gt_d2])]
      have he : (northHarmonic .west true .westFirst n w).cosine*Real.cos x+
          (northHarmonic .west true .westFirst n w).sine*Real.sin x=-2*rStar*Real.sin (n-x) := by
        simp only [northHarmonic,Real.sin_sub]; ring
      rw [he]
      nlinarith [rStar_pos]
  have hx := northHarmonic_pos (k := .west) (f := .westFirst) (n := n) (w := w) (x := x) (no := no)
    (wo := wo) (by simpa only [Sweep.n,Sweep.w] using hd)
  have hshape : (northHarmonic .west no .westFirst n w).rotor=rStar ∧
      (northHarmonic .west no .westFirst n w).baseSq=1 := by cases no <;> exact ⟨rfl,rfl⟩
  have hamp := northHarmonic_amplitude .west no .westFirst n w
  rw [hshape.1,hshape.2] at hamp
  have hsq := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤43/50)
    (show (43:ℝ)/50≤1-rStar^2 by nlinarith) 2
  have h := harmonicCurvature_le_length (R := radius) (D := (43/50)^2) (B := 7/6) radius_pos.le hx
    (by norm_num) (by simp only [Harmonic.parameter,hshape.1,hshape.2]; nlinarith) (by norm_num)
    (by simp only [harmonicArg,Harmonic.parameter,hshape.1,hshape.2] at hz ⊢; nlinarith)
  have hcurv : (northHarmonic .west no .westFirst n w).curvature (northRadius .westFirst) x=
      harmonicCurvature radius (northHarmonic .west no .westFirst n w).parameter
        (northHarmonic .west no .westFirst n w).cosine
        (northHarmonic .west no .westFirst n w).sine x := by
    simp [Harmonic.curvature,northRadius,Facet.model]
  rw [hcurv]
  nlinarith

/-- For N–W along the first axis of N the turning part of the force on W points
against its constant part along the line in `n`:
`rStar ≤ sin (n - w) + mStar cos (n - w)` for W along its own axis, and
`rStar ≤ sin n + mStar cos (n - w)` for W along the west side of C. -/
lemma west_opposition {no wo : Bool} {n w : ℝ} (hd : Domain no wo n w) :
    rStar≤(if wo then Real.sin (n-w) else Real.sin n)+mStar*Real.cos (n-w) := by
  obtain ⟨hn0,hn1,hw0,hw1,hq0,hq1⟩ := domain_bounds hd
  have hpi := Real.pi_gt_d2
  have hm := mStar_bounds
  have hr := rStar_bounds
  cases wo
  · have hw : -2/5≤w := by simpa [wLow] using hd.2.1
    simp only [Bool.false_eq_true,ite_false]
    rcases le_total n 0 with hn | hn
    · have hc := (small_angle (show |n-w|≤7/10 from abs_le.mpr ⟨by linarith,by linarith⟩)).1
      nlinarith [Real.le_sin hn,mul_le_mul_of_nonneg_left hc mStar_pos.le]
    · have hc := (small_angle (show |n-w|≤6/7 from abs_le.mpr ⟨by linarith,hq1⟩)).1
      nlinarith [Real.sin_nonneg_of_nonneg_of_le_pi hn (by linarith),
        mul_le_mul_of_nonneg_left hc mStar_pos.le]
  · have hw : w≤0 := by simpa [wHigh] using hd.2.2
    simp only [ite_true]
    rcases le_total (n-w) 0 with hq | hq
    · have hc := (small_angle (show |n-w|≤3/10 from abs_le.mpr ⟨by linarith,by linarith⟩)).1
      nlinarith [Real.le_sin hq,mul_le_mul_of_nonneg_left hc mStar_pos.le]
    · have hc := (small_angle (show |n-w|≤6/7 from abs_le.mpr ⟨by linarith,hq1⟩)).1
      nlinarith [Real.sin_nonneg_of_nonneg_of_le_pi hq (by linarith),
        mul_le_mul_of_nonneg_left hc mStar_pos.le]

/-- Bounds for the curvature of the length of the force on W along the lines. -/
def westCap : Sweep → Bool → Facet → ℝ
  | .north, _, .northSecond => 3/5
  | .north, _, _ => 0
  | .west, true, .westFirst => 0
  | .west, true, .westSecond => 0
  | .west, true, _ => 1/2
  | .west, false, .westFirst => 21/25
  | .west, false, .westSecond => 3/5
  | .west, false, .northFirst => 9/10
  | .west, false, .northSecond => 1
  | .diagonal, true, _ => 0
  | .diagonal, false, _ => 21/25

lemma west_curvature {k : Sweep} {no wo : Bool} {f : Facet} {n w x : ℝ}
    (hd : Domain no wo (k.n n w x) (k.w n w x)) :
    (westHarmonic k wo f n w).curvature radius x≤westCap k wo f := by
  have hx : 0<(westHarmonic k wo f n w).arg x := westHarmonic_pos hd
  have hamp := westHarmonic_amplitude k wo f n w
  have hR := radius_bounds
  have hr := rStar_bounds
  have hm := mStar_bounds
  have hR0 := radius_pos.le
  have hR1 : radius≤17/10 := by linarith
  have hb := domain_bounds hd
  cases k <;> cases wo <;> cases f
  all_goals simp only [Sweep.n,Sweep.w] at hd hb
  all_goals first
    | (simp [westHarmonic,westCap]; done)
    | skip
  · -- north, false, northFirst
    apply (Harmonic.curvature_nonpos hR0 rStar_pos hamp hx ?_).trans (by norm_num [westCap])
    have := west_opposition hd
    simp only [Bool.false_eq_true,ite_false] at this
    simp only [westHarmonic,Real.cos_sub] at this ⊢
    nlinarith [rStar_pos]
  · -- north, false, northSecond
    have hw : |w|≤2/5 := by
      have := hd.2; simp only [wLow,wHigh,Bool.false_eq_true,ite_false] at this
      exact abs_le.mpr ⟨by linarith,by linarith⟩
    have hs := (le_abs_self _).trans ((Real.abs_sin_le_abs (x := w)).trans hw)
    exact Harmonic.curvature_le hR0 hR1 rStar_pos hamp hx (A := 37/100) (B := 8/5)
      (by simp [westHarmonic]; linarith) (by simp only [westHarmonic]; nlinarith) (by norm_num)
      (by norm_num [westCap])
  · -- north, true, northFirst
    apply (Harmonic.curvature_nonpos hR0 rStar_pos hamp hx ?_).trans (by norm_num [westCap])
    have := west_opposition hd
    simp only [ite_true] at this
    simp only [westHarmonic,Real.cos_sub,Real.sin_sub] at this ⊢
    nlinarith [rStar_pos]
  · -- north, true, northSecond
    exact Harmonic.curvature_le hR0 hR1 rStar_pos hamp hx (A := 37/100) (B := 8/5)
      (by simp [westHarmonic]; linarith) (by simp only [westHarmonic]; nlinarith) (by norm_num)
      (by norm_num [westCap])
  · -- west, false, westFirst
    exact Harmonic.curvature_le hR0 hR1 one_pos hamp hx (A := 1) (B := 97/100)
      (by simp [westHarmonic]) (by simp only [westHarmonic]; nlinarith) (by norm_num)
      (by norm_num [westCap])
  · -- west, false, westSecond
    exact Harmonic.curvature_le hR0 hR1 one_pos hamp hx (A := 1) (B := 21/40)
      (by simp [westHarmonic]) (by simp only [westHarmonic]; nlinarith) (by norm_num)
      (by norm_num [westCap])
  · -- west, false, northFirst
    have hn : -3/10≤Real.sin n := by
      rcases le_total n 0 with h | h
      · linarith [Real.le_sin h]
      · linarith [Real.sin_nonneg_of_nonneg_of_le_pi h (by linarith [Real.pi_gt_d2])]
    exact Harmonic.curvature_le hR0 hR1 mStar_pos hamp hx (A := 9/10) (B := 7/6)
      (by simp only [westHarmonic]; linarith) (by simp only [westHarmonic]; nlinarith) (by norm_num)
      (by norm_num [westCap])
  · -- west, false, northSecond
    exact Harmonic.curvature_le hR0 hR1 mStar_pos hamp hx (A := 9/10) (B := 137/100)
      (by simp only [westHarmonic]; linarith)
      (by simp only [westHarmonic]; nlinarith [Real.cos_le_one n])
      (by norm_num) (by norm_num [westCap])
  · -- west, true, northFirst
    exact Harmonic.curvature_le hR0 hR1 rStar_pos hamp hx (A := 37/100) (B := 27/20)
      (by simp only [westHarmonic]; linarith) (by simp only [westHarmonic]; nlinarith) (by norm_num)
      (by norm_num [westCap])
  · -- west, true, northSecond
    exact Harmonic.curvature_le hR0 hR1 rStar_pos hamp hx (A := 37/100) (B := 27/20)
      (by simp only [westHarmonic]; linarith) (by simp only [westHarmonic]; nlinarith) (by norm_num)
      (by norm_num [westCap])
  all_goals
    exact Harmonic.curvature_le hR0 hR1 one_pos hamp hx (A := 1) (B := 97/100)
      (by simp [westHarmonic]) (by simp only [westHarmonic]; nlinarith) (by norm_num)
      (by norm_num [westCap])

/-! ### Concavity along the lines -/

lemma north_curvature_zero {k : Sweep} {no : Bool} {f : Facet} {n w x : ℝ}
    (hk : k=.west ∨ (k=.north ∧ no=true)) (hf : f=.northFirst ∨ f=.northSecond) :
    (northHarmonic k no f n w).curvature (northRadius f) x=0 := by
  rcases hk with rfl | ⟨rfl,rfl⟩ <;> rcases hf with rfl | rfl <;> (try cases no) <;>
    simp [northHarmonic]

/-- The second derivative of the gap along a line, on a sector. -/
def sweepCurvature (no wo : Bool) (f : Facet) (pn pw pq : Bool) (k : Sweep) (n w x : ℝ) : ℝ :=
  (match k with
    | .north => -trigN no f pn x-trigQ f pq (x-w)
    | .west => -trigW wo pw x-trigQ f pq (n-x)
    | .diagonal => -trigN no f pn x-trigW wo pw x)+
    (northHarmonic k no f n w).curvature (northRadius f) x+
    (westHarmonic k wo f n w).curvature radius x

/-- Inside a sector of the domain, the second derivative of the gap along every
line is nonpositive. -/
theorem sweepCurvature_nonpos {no wo pn pw pq : Bool} (f : Facet) (k : Sweep) {n w x : ℝ}
    (hd : Domain no wo (k.n n w x) (k.w n w x)) (hs : Sector pn pw pq (k.n n w x) (k.w n w x)) :
    sweepCurvature no wo f pn pw pq k n w x≤0 := by
  have hN := north_curvature k no f n w x
  have hW := west_curvature (f := f) hd
  have htN := trigN_lower (f := f) hd hs
  have htW := trigW_lower hd hs
  have htQ := trigQ_lower (f := f) hd hs
  cases k <;> simp only [Sweep.n,Sweep.w] at hd hs htN htW htQ <;> simp only [sweepCurvature]
  · -- n varies
    cases f
    · have hW0 : (westHarmonic .north wo .westFirst n w).curvature radius x≤0 := hW
      linarith [htN.1,(htQ.1 rfl).1]
    · have hW0 : (westHarmonic .north wo .westSecond n w).curvature radius x≤0 := hW
      linarith [htN.1,htQ.2.1 rfl]
    · have hW0 : (westHarmonic .north wo .northFirst n w).curvature radius x≤0 := hW
      linarith [htN.1,htQ.2.2 rfl]
    · have hW0 : (westHarmonic .north wo .northSecond n w).curvature radius x≤3/5 := hW
      cases no
      · linarith [htN.2 rfl rfl,(htQ.1 rfl).1]
      · have := north_curvature_zero (k := .north) (no := true) (f := .northSecond) (n := n)
          (w := w) (x := x) (Or.inr ⟨rfl,rfl⟩) (Or.inr rfl)
        linarith [htN.1,(htQ.1 rfl).1]
  · -- w varies
    cases f <;> cases wo
    · have hW0 : (westHarmonic .west false .westFirst n w).curvature radius x≤21/25 := hW
      rcases le_total x 0 with hx | hx
      · have := north_curvature_westFirst (w := w) hd hx
        linarith [(htW.2 rfl).1,(htQ.1 rfl).1]
      · linarith [(htW.2 rfl).2 hx,(htQ.1 rfl).2 rfl hx]
    · have hW0 : (westHarmonic .west true .westFirst n w).curvature radius x≤0 := hW
      linarith [htW.1 rfl,(htQ.1 rfl).1]
    · have hW0 : (westHarmonic .west false .westSecond n w).curvature radius x≤3/5 := hW
      linarith [(htW.2 rfl).1,htQ.2.1 rfl]
    · have hW0 : (westHarmonic .west true .westSecond n w).curvature radius x≤0 := hW
      linarith [htW.1 rfl,htQ.2.1 rfl]
    · have hW0 : (westHarmonic .west false .northFirst n w).curvature radius x≤9/10 := hW
      have := north_curvature_zero (k := .west) (no := no) (f := .northFirst) (n := n) (w := w)
        (x := x) (Or.inl rfl) (Or.inl rfl)
      linarith [(htW.2 rfl).1,htQ.2.2 rfl]
    · have hW0 : (westHarmonic .west true .northFirst n w).curvature radius x≤1/2 := hW
      have := north_curvature_zero (k := .west) (no := no) (f := .northFirst) (n := n) (w := w)
        (x := x) (Or.inl rfl) (Or.inl rfl)
      linarith [htW.1 rfl,htQ.2.2 rfl]
    · have hW0 : (westHarmonic .west false .northSecond n w).curvature radius x≤1 := hW
      have := north_curvature_zero (k := .west) (no := no) (f := .northSecond) (n := n) (w := w)
        (x := x) (Or.inl rfl) (Or.inr rfl)
      linarith [(htW.2 rfl).1,(htQ.1 rfl).1]
    · have hW0 : (westHarmonic .west true .northSecond n w).curvature radius x≤1/2 := hW
      have := north_curvature_zero (k := .west) (no := no) (f := .northSecond) (n := n) (w := w)
        (x := x) (Or.inl rfl) (Or.inr rfl)
      linarith [htW.1 rfl,(htQ.1 rfl).1]
  · -- n and w vary together
    cases wo
    · have hW0 : (westHarmonic .diagonal false f n w).curvature radius x≤21/25 := hW
      linarith [htN.1,(htW.2 rfl).1]
    · have hW0 : (westHarmonic .diagonal true f n w).curvature radius x≤0 := hW
      linarith [htN.1,htW.1 rfl]

/-- The speeds of `n` and of `w` along a line. -/
def Sweep.speedN : Sweep → ℝ
  | north => 1
  | west => 0
  | diagonal => 1

def Sweep.speedW : Sweep → ℝ
  | north => 0
  | west => 1
  | diagonal => 1

lemma Sweep.n_deriv (k : Sweep) (n w x : ℝ) : HasDerivAt (k.n n w) k.speedN x := by
  cases k
  exacts [hasDerivAt_id x,hasDerivAt_const x n,hasDerivAt_id x]

lemma Sweep.w_deriv (k : Sweep) (n w x : ℝ) : HasDerivAt (k.w n w) k.speedW x := by
  cases k
  exacts [hasDerivAt_const x w,hasDerivAt_id x,hasDerivAt_id x]

/-- The gap along a line, with the squared lengths of the forces as harmonics. -/
def sweepGap (no wo : Bool) (f : Facet) (pn pw pq : Bool) (k : Sweep) (n w x : ℝ) : ℝ :=
  constant no wo f+trigN no f pn (k.n n w x)+trigW wo pw (k.w n w x)+
    trigQ f pq (k.n n w x-k.w n w x)-slope pw*k.w n w x-sign pn/1000*k.n n w x+
    harmonicRoot (northRadius f) (northHarmonic k no f n w).parameter
      (northHarmonic k no f n w).cosine
      (northHarmonic k no f n w).sine x+
    harmonicRoot radius (westHarmonic k wo f n w).parameter (westHarmonic k wo f n w).cosine
      (westHarmonic k wo f n w).sine x

/-- Its first derivative. -/
def sweepGapD (no wo : Bool) (f : Facet) (pn pw pq : Bool) (k : Sweep) (n w x : ℝ) : ℝ :=
  harmonic (bN no f pn) (-aN no f) (k.n n w x)*k.speedN+
    harmonic (bW wo pw) (-aW wo) (k.w n w x)*k.speedW+
    harmonic (bQ f pq) (-aQ f) (k.n n w x-k.w n w x)*(k.speedN-k.speedW)-
    slope pw*k.speedW-sign pn/1000*k.speedN+
    harmonicRootD (northRadius f) (northHarmonic k no f n w).parameter
      (northHarmonic k no f n w).cosine
      (northHarmonic k no f n w).sine x+
    harmonicRootD radius (westHarmonic k wo f n w).parameter (westHarmonic k wo f n w).cosine
      (westHarmonic k wo f n w).sine x

lemma sweepGap_eq (no wo : Bool) (f : Facet) (pn pw pq : Bool) (k : Sweep) (n w x : ℝ) :
    sweepGap no wo f pn pw pq k n w x=sectorGap no wo f pn pw pq (k.n n w x) (k.w n w x) := by
  have hn := northHarmonic_arg k no f n w x
  have hw := westHarmonic_arg k wo f n w x
  simp only [Harmonic.arg] at hn hw
  simp only [sweepGap,sectorGap,harmonicRoot,hn,hw]
  ring

lemma sweepGap_deriv {no wo : Bool} (f : Facet) (pn pw pq : Bool) (k : Sweep) {n w x : ℝ}
    (hd : Domain no wo (k.n n w x) (k.w n w x)) :
    HasDerivAt (sweepGap no wo f pn pw pq k n w) (sweepGapD no wo f pn pw pq k n w x) x := by
  have hn := k.n_deriv n w x
  have hw := k.w_deriv n w x
  have hN := (harmonic_hasDerivAt (aN no f) (bN no f pn) _).comp x hn
  have hW := (harmonic_hasDerivAt (aW wo) (bW wo pw) _).comp x hw
  have hQ := (harmonic_hasDerivAt (aQ f) (bQ f pq) _).comp x (hn.sub hw)
  have hrN := harmonicRoot_deriv (R := northRadius f) (northHarmonic_pos (f := f) hd)
  have hrW := harmonicRoot_deriv (R := radius) (westHarmonic_pos (f := f) hd)
  have hh := (((((((hN.const_add (constant no wo f)).add hW).add hQ).sub
    (hw.const_mul (slope pw))).sub (hn.const_mul (sign pn/1000))).add hrN).add hrW)
  convert hh using 1
  · funext y
    simp only [sweepGap,trigN,trigW,trigQ,Pi.add_apply,Pi.sub_apply,Function.comp_apply]
  · simp only [sweepGapD,Pi.sub_apply]

lemma sweepGapD_deriv {no wo : Bool} (f : Facet) (pn pw pq : Bool) (k : Sweep) {n w x : ℝ}
    (hd : Domain no wo (k.n n w x) (k.w n w x)) :
    HasDerivAt (sweepGapD no wo f pn pw pq k n w) (sweepCurvature no wo f pn pw pq k n w x) x := by
  have hn := k.n_deriv n w x
  have hw := k.w_deriv n w x
  have hN := ((harmonic_hasDerivAt (bN no f pn) (-aN no f) _).comp x hn).mul_const k.speedN
  have hW := ((harmonic_hasDerivAt (bW wo pw) (-aW wo) _).comp x hw).mul_const k.speedW
  have hQ := ((harmonic_hasDerivAt (bQ f pq) (-aQ f) _).comp x (hn.sub hw)).mul_const
    (k.speedN-k.speedW)
  have hrN := harmonicRoot_second (R := northRadius f) (northHarmonic_pos (f := f) hd)
  have hrW := harmonicRoot_second (R := radius) (westHarmonic_pos (f := f) hd)
  have hh := (((((hN.add hW).add hQ).sub_const (slope pw*k.speedW)).sub_const
    (sign pn/1000*k.speedN)).add hrN).add hrW
  convert hh using 1
  · funext y
    simp only [sweepGapD,Pi.add_apply,Pi.sub_apply,Function.comp_apply]
  · cases k <;> simp only [sweepCurvature,Sweep.n,Sweep.w,Sweep.speedN,Sweep.speedW,trigN,trigW,
      trigQ,harmonic,Harmonic.curvature,Pi.sub_apply] <;> ring

/-- The gap is concave on every segment of a line that lies in the domain and in
one sector. -/
theorem gap_sweep_concave {no wo pn pw pq : Bool} (f : Facet) (k : Sweep) {n w l r : ℝ}
    (hd : ∀ x ∈ Set.Icc l r, Domain no wo (k.n n w x) (k.w n w x))
    (hs : ∀ x ∈ Set.Icc l r, Sector pn pw pq (k.n n w x) (k.w n w x)) :
    ConcaveOn ℝ (Set.Icc l r) (fun x => gap no wo f (k.n n w x) (k.w n w x)) := by
  have hc : ConcaveOn ℝ (Set.Icc l r) (sweepGap no wo f pn pw pq k n w) :=
    concave_of_deriv2 (fun x hx => sweepGap_deriv f pn pw pq k (hd x hx))
      (fun x hx => sweepGapD_deriv f pn pw pq k (hd x hx))
      (fun x hx => sweepCurvature_nonpos f k (hd x hx) (hs x hx))
  exact hc.congr fun x hx => by
    rw [sweepGap_eq,gap_eq_sectorGap (hd x hx) (hs x hx)]

end SquaresInCircles.Six.Stress.Pair

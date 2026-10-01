import SquaresInCircles.Six.Stress.PairStress
import SquaresInCircles.Common.Trigonometry

/-!
# Six squares: the pair gap at the vertices of the sectors

The gap is positive at the corners of the domain, at the points where its sides
meet the axes, and at the points where the diagonal `n = w` meets a side or an
axis, except at the origin for the facets of the model, where it vanishes. In a
model of the gap the sine and cosine are their Taylor polynomials of degrees
seven and six, within `10⁻⁵` on `|t| ≤ 6/7`; `rStar` and `mStar` are decimals
within `10⁻⁵`, `c0` is replaced by its ceiling `coreUpper`, the squared radius by
the ceiling `Q0`, `rhoStar` by `rhoBound` and `pairBase` by `0.071`. On the whole
domain the coordinates of the forces move by at most `4·10⁻⁵`, their lengths by
twice that, and the thresholds and the penalty by at most `5·10⁻⁵`, together less
than the `5·10⁻⁴` set aside. The margin is smallest, about `6.6·10⁻⁴`, at the
corner `n = 0`, `w = -11/25` for N–W along the second axis of N, which is what
needs `rStar` to five decimals. At each point the model is checked by rational
arithmetic, after two squarings remove its roots.
-/

noncomputable section
namespace SquaresInCircles.Six.Stress.Pair
open Normalization

/-! ### Taylor polynomials -/

lemma cos_upper_eight {x : ℝ} (hx : 0≤x) : Real.cos x≤cosLower x+x^8/40320 := by
  have hh := nonneg_of_deriv_nonneg (fun t => cosLower t+t^8/40320-Real.cos t)
    (by dsimp [cosLower]; fun_prop) (by norm_num [cosLower])
    (fun t ht => by
      have hs := sin_lower_seven ht
      simp (disch := fun_prop) [cosLower]
      linarith) hx
  linarith

lemma sin_upper_nine {x : ℝ} (hx : 0≤x) : Real.sin x≤sinLower x+x^9/362880 := by
  have hh := nonneg_of_deriv_nonneg (fun t => sinLower t+t^9/362880-Real.sin t)
    (by dsimp [sinLower]; fun_prop) (by norm_num [sinLower])
    (fun t ht => by
      have hc := cos_upper_eight ht
      dsimp [cosLower] at hc
      simp (disch := fun_prop) [sinLower]
      linarith) hx
  linarith

lemma trig_error {x : ℝ} (hx : |x|≤6/7) :
    |Real.sin x-sinLower x|≤1e-5 ∧ |Real.cos x-cosLower x|≤1e-5 := by
  have key {y : ℝ} (hy0 : 0≤y) (hy : y≤6/7) :
      |Real.sin y-sinLower y|≤1e-5 ∧ |Real.cos y-cosLower y|≤1e-5 := by
    have h9 := pow_le_pow_left₀ hy0 hy 9
    have h8 := pow_le_pow_left₀ hy0 hy 8
    have hs := sin_lower_seven hy0
    have hc := cos_lower_six hy0
    have hs' := sin_upper_nine hy0
    have hc' := cos_upper_eight hy0
    norm_num at h8 h9
    dsimp [sinLower,cosLower] at *
    exact ⟨abs_le.mpr ⟨by linarith,by linarith⟩,abs_le.mpr ⟨by linarith,by linarith⟩⟩
  rcases le_total 0 x with h | h
  · exact key h ((le_abs_self x).trans hx)
  · have hk := key (neg_nonneg.mpr h) (by linarith [neg_abs_le x])
    rw [Real.sin_neg,Real.cos_neg] at hk
    have he : sinLower (-x)=-sinLower x := by simp only [sinLower]; ring
    have hc : cosLower (-x)=cosLower x := by simp only [cosLower]; ring
    rw [he,hc,show -Real.sin x- -sinLower x=-(Real.sin x-sinLower x) by ring,abs_neg] at hk
    exact hk

/-! ### The model of the gap -/

/-- Decimals within `10⁻⁵` of `rStar` and `mStar`. -/
def rA : ℝ := 0.36878
def mA : ℝ := 0.8897
/-- An upper bound for `pairBase`. -/
def baseA : ℝ := 0.071

/-! The models of the normals, of the forces on N and W, of the thresholds and of
the penalty, with `sinLower` and `cosLower` in place of `sin` and `cos`. -/

def centralP (own : Bool) (t : ℝ) : Point := if own then (1,0) else (cosLower t,-sinLower t)

def northP : Facet → ℝ → Point
  | .westFirst, q => (-sinLower q,-cosLower q)
  | .westSecond, q => (cosLower q,-sinLower q)
  | .northFirst, _ => (1,0)
  | .northSecond, _ => (0,-1)

def westP : Facet → ℝ → Point
  | .westFirst, _ => (1,0)
  | .westSecond, _ => (0,1)
  | .northFirst, q => (-sinLower q,cosLower q)
  | .northSecond, q => (cosLower q,sinLower q)

def northForceP (no : Bool) (f : Facet) (n w : ℝ) : Point :=
  ((centralP no n).1+rA*(northP f (n-w)).1,(centralP no n).2+rA*(northP f (n-w)).2)

def westForceP (wo : Bool) (f : Facet) (n w : ℝ) : Point :=
  ((centralP wo w).1+rA*(westP f (n-w)).1,(centralP wo w).2+rA*(westP f (n-w)).2-mA)

def widthP (t : ℝ) : ℝ := 1/2+(|cosLower t|+|sinLower t|)/2

def penaltyP (no wo : Bool) (n w : ℝ) : ℝ :=
  (if no then coreUpper*(max (sinLower n) 0+1-cosLower n) else 0)+
    (if wo then coreUpper*max (sinLower w) 0 else 0)

/-- The model of the linear part of the gap, less the `5·10⁻⁴` set aside for the
errors of the model. -/
def linearP (no wo : Bool) (f : Facet) (n w : ℝ) : ℝ :=
  widthP n+widthP w+rA*widthP (n-w)+mA/2+
    (if f.model then ((northForceP no f n w).1-(northForceP no f n w).2)/2 else 0)+
    ((westForceP wo f n w).1-(westForceP wo f n w).2)/2-penaltyP no wo n w-baseA-line w-
    |n|/1000-5e-4

/-- The model of the square of `northRadius f`. -/
def scaleSq (f : Facet) : ℝ := if f.model then Q0 else rhoBound^2

/-- The model exceeds the scaled lengths of the two model forces, written without
roots. -/
def ModelCheck (no wo : Bool) (f : Facet) (n w : ℝ) : Prop :=
  0<linearP no wo f n w ∧
    scaleSq f*((northForceP no f n w).1^2+(northForceP no f n w).2^2)+
      Q0*((westForceP wo f n w).1^2+(westForceP wo f n w).2^2)<linearP no wo f n w^2 ∧
    4*(scaleSq f*((northForceP no f n w).1^2+(northForceP no f n w).2^2))*
      (Q0*((westForceP wo f n w).1^2+(westForceP wo f n w).2^2))<
      (linearP no wo f n w^2-scaleSq f*((northForceP no f n w).1^2+(northForceP no f n w).2^2)-
        Q0*((westForceP wo f n w).1^2+(westForceP wo f n w).2^2))^2

/-! ### The errors of the model -/

/-- `|x - X|, |y - Y| ≤ e` raise the length of `(x, y)` by at most `2e`. -/
lemma length_le {x y X Y e : ℝ} (he : 0≤e) (hx : |x-X|≤e) (hy : |y-Y|≤e) :
    Real.sqrt (x^2+y^2)≤Real.sqrt (X^2+Y^2)+2*e := by
  set L := Real.sqrt (X^2+Y^2)
  have hL0 : 0≤L := Real.sqrt_nonneg _
  have hLsq : L^2=X^2+Y^2 := Real.sq_sqrt (by positivity)
  have hX : |X|≤L := Real.abs_le_sqrt (by nlinarith [sq_nonneg Y])
  have hY : |Y|≤L := Real.abs_le_sqrt (by nlinarith [sq_nonneg X])
  have hdx := mul_le_mul hX hx (abs_nonneg _) hL0
  have hdy := mul_le_mul hY hy (abs_nonneg _) hL0
  rw [← abs_mul] at hdx hdy
  have hnorm : x^2+y^2≤(L+2*e)^2 := by
    nlinarith [le_abs_self (X*(x-X)),le_abs_self (Y*(y-Y)),sq_abs (x-X),sq_abs (y-Y),
      pow_le_pow_left₀ (abs_nonneg (x-X)) hx 2,pow_le_pow_left₀ (abs_nonneg (y-Y)) hy 2]
  exact Real.sqrt_le_iff.mpr ⟨by positivity,hnorm⟩

/-- `√X + √Y < E` when `X + Y < E²` and `4XY < (E² - X - Y)²`. -/
lemma two_roots_lt {E X Y : ℝ} (hE : 0<E) (hX : 0≤X) (hY : 0≤Y)
    (hsum : X+Y<E^2) (hdisc : 4*X*Y<(E^2-X-Y)^2) : Real.sqrt X+Real.sqrt Y<E := by
  have hx := Real.sq_sqrt hX
  have hy := Real.sq_sqrt hY
  by_contra! hbad
  have hd : E^2-X-Y≤2*Real.sqrt X*Real.sqrt Y := by
    nlinarith [Real.sqrt_nonneg X,Real.sqrt_nonneg Y]
  have hs := pow_le_pow_left₀ (by linarith) hd 2
  nlinarith

lemma product_error {a b x y : ℝ} : |a*x-b*y|≤|a-b| * |x|+|b| * |x-y| := by
  rw [show a*x-b*y=(a-b)*x+b*(x-y) by ring,← abs_mul,← abs_mul]
  exact abs_add_le _ _

/-- `R` times a length within `e` of `√M`, for `R ≤ 17/10` with `R² ≤ S`, is at most
`√(S M) + (17/10) e`. -/
lemma scaled_length_le {R S L M e : ℝ} (hR : 0≤R) (hR1 : R≤17/10) (hRS : R^2≤S) (hM : 0≤M)
    (he : 0≤e) (hL : L≤Real.sqrt M+e) : R*L≤Real.sqrt (S*M)+(17/10)*e := by
  have h : R*Real.sqrt M≤Real.sqrt (S*M) := by
    rw [← Real.sqrt_sq hR,← Real.sqrt_mul (sq_nonneg R)]
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hRS hM)
  nlinarith [mul_le_mul_of_nonneg_left hL hR]

lemma constants_close : |rStar-rA|≤1e-5 ∧ |mStar-mA|≤1e-5 ∧ |c0-coreUpper|≤1e-5 := by
  have hr := rStar_bounds
  have hm := mStar_bounds
  have hc := c0_bounds
  have hu := ceiling_bounds.2.2.2
  refine ⟨abs_le.mpr ⟨?_,?_⟩,abs_le.mpr ⟨?_,?_⟩,abs_le.mpr ⟨?_,?_⟩⟩ <;>
    simp only [rA,mA,coreUpper] at hu ⊢ <;> linarith

/-- On `|t| ≤ 6/7` the coordinates of the normals differ from their models by at
most `10⁻⁵`, and are at most `1` in absolute value. -/
lemma normal_error (f : Facet) (own : Bool) {t q : ℝ} (ht : |t|≤6/7) (hq : |q|≤6/7) :
    (|(central own t).1-(centralP own t).1|≤1e-5 ∧
      |(central own t).2-(centralP own t).2|≤1e-5) ∧
    (|(f.north q).1-(northP f q).1|≤1e-5 ∧ |(f.north q).2-(northP f q).2|≤1e-5) ∧
    (|(f.west q).1-(westP f q).1|≤1e-5 ∧ |(f.west q).2-(westP f q).2|≤1e-5) ∧
    (|(f.north q).1|≤1 ∧ |(f.north q).2|≤1) ∧
    (|(f.west q).1|≤1 ∧ |(f.west q).2|≤1) := by
  obtain ⟨hst,hct⟩ := trig_error ht
  obtain ⟨hsq,hcq⟩ := trig_error hq
  have hs1 : |Real.sin q|≤1 := Real.abs_sin_le_one q
  have hc1 : |Real.cos q|≤1 := Real.abs_cos_le_one q
  have e (a b : ℝ) : |-a- -b|=|a-b| := by rw [← abs_neg]; ring_nf
  cases own <;> cases f <;>
    simp only [central,centralP,Facet.north,northP,Facet.west,westP,
      Bool.false_eq_true,ite_false,ite_true,e,abs_neg,sub_self,abs_zero,abs_one] <;>
    refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩⟩ <;>
    first | assumption | linarith

lemma force_error {no wo : Bool} {f : Facet} {n w : ℝ} (hd : Domain no wo n w) :
    (|(northForce no f n w).1-(northForceP no f n w).1|≤4e-5 ∧
      |(northForce no f n w).2-(northForceP no f n w).2|≤4e-5) ∧
    (|(westForce wo f n w).1-(westForceP wo f n w).1|≤4e-5 ∧
      |(westForce wo f n w).2-(westForceP wo f n w).2|≤4e-5) := by
  obtain ⟨hn,hw,hq⟩ := domain_abs hd
  obtain ⟨⟨hN1,hN2⟩,⟨hn1,hn2⟩,-,⟨hb1,hb2⟩,-⟩ :=
    normal_error f no (t := n) (q := n-w) (by linarith) hq
  obtain ⟨⟨hW1,hW2⟩,-,⟨hw1,hw2⟩,-,⟨hc1,hc2⟩⟩ :=
    normal_error f wo (t := w) (q := n-w) (by linarith) hq
  obtain ⟨hr,hm,-⟩ := constants_close
  have hrA : |rA|≤37/100 := by norm_num [rA]
  have p (x X : ℝ) (hx : |x|≤1) (he : |x-X|≤1e-5) : |rStar*x-rA*X|≤2e-5 := by
    have := product_error (a := rStar) (b := rA) (x := x) (y := X)
    have := mul_le_mul hr hx (abs_nonneg _) (by norm_num)
    have := mul_le_mul hrA he (abs_nonneg _) (by norm_num)
    linarith
  have t (a b A B e : ℝ) (ha : |a-A|≤1e-5) (hb : |b-B|≤e) : |a+b-(A+B)|≤1e-5+e := by
    rw [show a+b-(A+B)=(a-A)+(b-B) by ring]
    exact (abs_add_le _ _).trans (by linarith)
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩
  · exact (t _ _ _ _ _ hN1 (p _ _ hb1 hn1)).trans (by norm_num)
  · exact (t _ _ _ _ _ hN2 (p _ _ hb2 hn2)).trans (by norm_num)
  · exact (t _ _ _ _ _ hW1 (p _ _ hc1 hw1)).trans (by norm_num)
  · have := t _ _ _ _ _ hW2 (p _ _ hc2 hw2)
    simp only [westForce,westForceP]
    rw [show (central wo w).2+rStar*(f.west (n-w)).2-mStar-((centralP wo w).2+
        rA*(westP f (n-w)).2-mA)=((central wo w).2+rStar*(f.west (n-w)).2-
        ((centralP wo w).2+rA*(westP f (n-w)).2))-(mStar-mA) by ring]
    exact (abs_sub _ _).trans (by linarith)

lemma width_error {t : ℝ} (ht : |t|≤6/7) : |(1/2+angularWidth t)-widthP t|≤1e-5 := by
  obtain ⟨hs,hc⟩ := trig_error ht
  have h1 := (abs_abs_sub_abs_le_abs_sub (Real.cos t) (cosLower t)).trans hc
  have h2 := (abs_abs_sub_abs_le_abs_sub (Real.sin t) (sinLower t)).trans hs
  rw [show 1/2+angularWidth t-widthP t=
      ((|Real.cos t|-|cosLower t|)+(|Real.sin t|-|sinLower t|))/2 by
    simp only [angularWidth,widthP]; ring,abs_div,abs_two]
  linarith [abs_add_le (|Real.cos t|-|cosLower t|) (|Real.sin t|-|sinLower t|)]

lemma threshold_error {no wo : Bool} {n w : ℝ} (hd : Domain no wo n w) :
    |threshold n w-(widthP n+widthP w+rA*widthP (n-w)+mA/2)|≤5e-5 := by
  obtain ⟨hn,hw,hq⟩ := domain_abs hd
  have en := width_error (show |n|≤6/7 by linarith)
  have ew := width_error (show |w|≤6/7 by linarith)
  have eq := width_error hq
  obtain ⟨hr,hm,-⟩ := constants_close
  have hb : |1/2+angularWidth (n-w)|≤3/2 := by
    rw [abs_of_nonneg (by simp only [angularWidth]; positivity)]
    simp only [angularWidth]
    linarith [Real.abs_cos_le_one (n-w),Real.abs_sin_le_one (n-w)]
  have hp := product_error (a := rStar) (b := rA) (x := 1/2+angularWidth (n-w)) (y := widthP (n-w))
  have := mul_le_mul hr hb (abs_nonneg _) (by norm_num)
  have := mul_le_mul (show |rA|≤37/100 by norm_num [rA]) eq (abs_nonneg _) (by norm_num)
  rw [show threshold n w-(widthP n+widthP w+rA*widthP (n-w)+mA/2)=
    ((1/2+angularWidth n)-widthP n)+((1/2+angularWidth w)-widthP w)+
      (rStar*(1/2+angularWidth (n-w))-rA*widthP (n-w))+(mStar-mA)/2 by simp only [threshold]; ring]
  have h4 := abs_add_le (((1/2+angularWidth n)-widthP n)+((1/2+angularWidth w)-widthP w)+
    (rStar*(1/2+angularWidth (n-w))-rA*widthP (n-w))) ((mStar-mA)/2)
  have h3 := abs_add_le (((1/2+angularWidth n)-widthP n)+((1/2+angularWidth w)-widthP w))
    (rStar*(1/2+angularWidth (n-w))-rA*widthP (n-w))
  have h2 := abs_add_le ((1/2+angularWidth n)-widthP n) ((1/2+angularWidth w)-widthP w)
  rw [abs_div,abs_two] at h4
  linarith

lemma penalty_error {no wo : Bool} {n w : ℝ} (hd : Domain no wo n w) :
    |penalty no wo n w-penaltyP no wo n w|≤5e-5 := by
  obtain ⟨hn,hw,-⟩ := domain_abs hd
  obtain ⟨hsn,hcn⟩ := trig_error (show |n|≤6/7 by linarith)
  obtain ⟨hsw,-⟩ := trig_error (show |w|≤6/7 by linarith)
  obtain ⟨-,-,hc⟩ := constants_close
  have hmn := (abs_max_sub_max_le_abs (Real.sin n) (sinLower n) 0).trans hsn
  have hmw := (abs_max_sub_max_le_abs (Real.sin w) (sinLower w) 0).trans hsw
  have hm0 := le_max_right (Real.sin n) 0
  have hm1 := max_le (Real.sin_le_one n) zero_le_one
  have hw0 := le_max_right (Real.sin w) 0
  have hw1 := max_le (Real.sin_le_one w) zero_le_one
  have hcos := (small_angle hn).1
  have b1 : |max (Real.sin n) 0+1-Real.cos n|≤2 :=
    abs_le.mpr ⟨by linarith [Real.cos_le_one n],by linarith⟩
  have b2 : |max (Real.sin w) 0|≤1 := abs_le.mpr ⟨by linarith,hw1⟩
  have hcA : |coreUpper|≤1/5 := by norm_num [coreUpper]
  have e1 : |c0*(max (Real.sin n) 0+1-Real.cos n)-
      coreUpper*(max (sinLower n) 0+1-cosLower n)|≤3e-5 := by
    have := product_error (a := c0) (b := coreUpper) (x := max (Real.sin n) 0+1-Real.cos n)
      (y := max (sinLower n) 0+1-cosLower n)
    have := mul_le_mul hc b1 (abs_nonneg _) (by norm_num)
    have he : |max (Real.sin n) 0+1-Real.cos n-(max (sinLower n) 0+1-cosLower n)|≤2e-5 := by
      rw [show max (Real.sin n) 0+1-Real.cos n-(max (sinLower n) 0+1-cosLower n)=
        (max (Real.sin n) 0-max (sinLower n) 0)-(Real.cos n-cosLower n) by ring]
      exact (abs_sub _ _).trans (by linarith)
    have := mul_le_mul hcA he (abs_nonneg _) (by norm_num)
    linarith
  have e2 : |c0*max (Real.sin w) 0-coreUpper*max (sinLower w) 0|≤2e-5 := by
    have := product_error (a := c0) (b := coreUpper) (x := max (Real.sin w) 0)
      (y := max (sinLower w) 0)
    have := mul_le_mul hc b2 (abs_nonneg _) (by norm_num)
    have := mul_le_mul hcA hmw (abs_nonneg _) (by norm_num)
    linarith
  cases no <;> cases wo <;> simp only [penalty,penaltyP,Bool.false_eq_true,ite_false,ite_true,
    add_zero,zero_add,sub_self,abs_zero]
  · norm_num
  · linarith
  · linarith
  · rw [show c0*(max (Real.sin n) 0+1-Real.cos n)+c0*max (Real.sin w) 0-
      (coreUpper*(max (sinLower n) 0+1-cosLower n)+coreUpper*max (sinLower w) 0)=
      (c0*(max (Real.sin n) 0+1-Real.cos n)-coreUpper*(max (sinLower n) 0+1-cosLower n))+
      (c0*max (Real.sin w) 0-coreUpper*max (sinLower w) 0) by ring]
    exact (abs_add_le _ _).trans (by linarith)

/-- On the domain the gap is at least the model less the roots of the scaled squared
lengths of the two model forces. -/
theorem gap_ge_model {no wo : Bool} {f : Facet} {n w : ℝ} (hd : Domain no wo n w) :
    linearP no wo f n w-
      Real.sqrt (scaleSq f*((northForceP no f n w).1^2+(northForceP no f n w).2^2))-
      Real.sqrt (Q0*((westForceP wo f n w).1^2+(westForceP wo f n w).2^2))≤
      gap no wo f n w := by
  obtain ⟨⟨hN1,hN2⟩,⟨hW1,hW2⟩⟩ := force_error (f := f) hd
  have hT := abs_le.mp (threshold_error hd)
  have hP := abs_le.mp (penalty_error hd)
  have hB : pairBase≤baseA := by simp only [baseA]; linarith [pairBase_bounds.2]
  have hR := radius_bounds
  have hR2 : radius^2≤Q0 := by rw [radius_sq]; exact qStar_lt_Q0.le
  have hρ0 : 0≤rhoStar := by linarith [rhoStar_bounds.1]
  have hρ2 : rhoStar^2≤rhoBound^2 := pow_le_pow_left₀ hρ0
    (rhoStar_lt_rho0.le.trans ceiling_bounds.2.1) 2
  have lN := length_le (by norm_num) hN1 hN2
  have lW := length_le (by norm_num) hW1 hW2
  have hWl := scaled_length_le radius_pos.le (by linarith) hR2 (by positivity) (by norm_num) lW
  have e1 := abs_le.mp hN1
  have e2 := abs_le.mp hN2
  have e3 := abs_le.mp hW1
  have e4 := abs_le.mp hW2
  unfold gap value northBound vertexBound linearP scaleSq
  split_ifs
  · have := scaled_length_le radius_pos.le (by linarith) hR2 (by positivity) (by norm_num) lN
    linarith
  · have := scaled_length_le hρ0 (by linarith [rhoStar_bounds.2]) hρ2 (by positivity)
      (by norm_num) lN
    linarith

/-- The gap is positive wherever the model check holds. -/
theorem gap_pos_of_check {no wo : Bool} {f : Facet} {n w : ℝ} (hd : Domain no wo n w)
    (h : ModelCheck no wo f n w) : 0<gap no wo f n w := by
  have hQ : 0≤Q0 := by norm_num [Q0]
  have hs : 0≤scaleSq f := by unfold scaleSq; split_ifs; exacts [hQ,sq_nonneg _]
  have hlt := two_roots_lt h.1 (mul_nonneg hs (by positivity))
    (mul_nonneg hQ (by positivity)) h.2.1 h.2.2
  linarith [gap_ge_model (f := f) hd]

/-- Unfolds the model check at a rational point and decides it. -/
macro "model_check" : tactic =>
  `(tactic| norm_num [ModelCheck,linearP,northForceP,westForceP,centralP,northP,westP,widthP,
    penaltyP,scaleSq,Facet.model,rA,mA,baseA,Q0,rhoBound,coreUpper,sinLower,cosLower,line,nLow,
    nHigh,wLow,wHigh])

/-- The model check at the corners and axis points other than the origin. -/
macro "corner_checks" : tactic =>
  `(tactic| (intro f x y hx hy h0; rcases hx with h | h | h <;> subst h <;>
    rcases hy with h | h | h <;> subst h <;> cases f <;>
      first | (exfalso; exact h0 ⟨rfl,rfl⟩) | model_check))

/-- The model check at the points of the diagonal other than the origin. -/
macro "diagonal_checks" : tactic =>
  `(tactic| (intro f z hz h0; rcases hz with h | h | h <;> subst h <;> cases f <;>
      first | (exfalso; exact h0 rfl) | (norm_num [nLow,nHigh,wLow,wHigh] at h0; done) |
        model_check))

private abbrev CornerChecks (no wo : Bool) : Prop :=
  ∀ (f : Facet) (x y : ℝ), (x=nLow no ∨ x=nHigh no ∨ x=0) →
    (y=wLow wo ∨ y=wHigh wo ∨ y=0) →
    ¬(x=0 ∧ y=0) → ModelCheck no wo f x y

private abbrev DiagonalChecks (no wo : Bool) : Prop :=
  ∀ (f : Facet) (z : ℝ), (z=max (nLow no) (wLow wo) ∨ z=min (nHigh no) (wHigh wo) ∨ z=0) →
    ¬z=0 → ModelCheck no wo f z z

private lemma corners_ff : CornerChecks false false := by corner_checks
private lemma corners_ft : CornerChecks false true := by corner_checks
private lemma corners_tf : CornerChecks true false := by corner_checks
private lemma corners_tt : CornerChecks true true := by corner_checks
private lemma diagonal_ff : DiagonalChecks false false := by diagonal_checks
private lemma diagonal_ft : DiagonalChecks false true := by diagonal_checks
private lemma diagonal_tf : DiagonalChecks true false := by diagonal_checks
private lemma diagonal_tt : DiagonalChecks true true := by diagonal_checks

/-- At zero angles the gap vanishes for the facets of the model, and is positive
for the other two. -/
lemma gap_origin (no wo : Bool) (f : Facet) :
    (f.model → gap no wo f 0 0=0) ∧ (f.model=false → 0<gap no wo f 0 0) := by
  have hd : Domain no wo 0 0 := by cases no <;> cases wo <;> norm_num [Domain,nLow,nHigh,wLow,wHigh]
  refine ⟨fun hf => by rw [gap,value_origin no wo hf]; norm_num [line],fun hf => ?_⟩
  cases f <;> simp only [Facet.model,Bool.true_eq_false] at hf <;>
    exact gap_pos_of_check hd (by cases no <;> cases wo <;> model_check)

/-- The gap is nonnegative at the corners and axis points of the domain, and at the
points where the diagonal meets them. -/
theorem gap_vertices (no wo : Bool) (f : Facet) :
    (∀ x y, (x=nLow no ∨ x=nHigh no ∨ x=0) → (y=wLow wo ∨ y=wHigh wo ∨ y=0) →
      0≤gap no wo f x y) ∧
    (∀ z, (z=max (nLow no) (wLow wo) ∨ z=min (nHigh no) (wHigh wo) ∨ z=0) →
      0≤gap no wo f z z) := by
  constructor
  · intro x y hx hy
    by_cases h0 : x=0 ∧ y=0
    · rw [h0.1,h0.2]
      cases hf : f.model
      · exact ((gap_origin no wo f).2 hf).le
      · exact ((gap_origin no wo f).1 hf).ge
    · have hd : Domain no wo x y := by
        rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
          cases no <;> cases wo <;> norm_num [Domain,nLow,nHigh,wLow,wHigh]
      refine (gap_pos_of_check hd ?_).le
      cases no <;> cases wo
      exacts [corners_ff f x y hx hy h0,corners_ft f x y hx hy h0,corners_tf f x y hx hy h0,
        corners_tt f x y hx hy h0]
  · intro z hz
    by_cases h0 : z=0
    · rw [h0]
      cases hf : f.model
      · exact ((gap_origin no wo f).2 hf).le
      · exact ((gap_origin no wo f).1 hf).ge
    · have hd : Domain no wo z z := by
        rcases hz with rfl | rfl | rfl <;> cases no <;> cases wo <;>
          norm_num [Domain,nLow,nHigh,wLow,wHigh]
      refine (gap_pos_of_check hd ?_).le
      cases no <;> cases wo
      exacts [diagonal_ff f z hz h0,diagonal_ft f z hz h0,diagonal_tf f z hz h0,
        diagonal_tt f z hz h0]

end SquaresInCircles.Six.Stress.Pair

import SquaresInCircles.Common.Basic
import SquaresInCircles.Common.Trigonometry

/-!
# Six squares: the constants

The constants of the six-square proof, each with one rational bracket.

The model (defined with the statement, in `Geometry.lean`) is built from
`h = √2/2` and the smaller root `s*` of `s² - A s + B`; `t*`, `d*` and the
squared radius `q* = 2s*² + 4s* + 5/2` follow from it. The far corners of E and
W and the far vertices of D lie on the circle of squared radius `q*`. The
stress of the model has weight `1` on the four contacts of
C, `r* = (s* + 1/2)/(s* + 3/2)` on N–W and E–S, and `m* = (1 + r*) k*`, with
`k* = (t* + 1/2)/(3/2 - s*)`, on W–D and D–S; the force on D has length
`diagonalK = 2h m*`, the centre of D lies at distance `ρ* = √(q* - 1/4) - 1/2`
from the disk centre, and `pairBase = m* (1/2 - t*)`. The forces of the model
point at the far corners of N and W on the circle, which gives their lengths,
and `2 pairBase + diagonalK (1 - ρ*) = 0` because `ρ* = 2h d*`. Each constant
gets one bracket of width at most `6·10⁻⁷`: `s*` from the sign of its
quadratic, the others from it by products, quotients and square roots.

The normalization works below the rational ceiling `Q0 = 142559/50000 > q*` on
the squared radius. With `R0 = √Q0`, the number `ρ0 = √(Q0 - 1/4) - 1/2` is
the largest radial coordinate of a square in the disk, `c0 = ρ0 - 1` bounds the
centre of the central square C, `coreRadius = 3/2 - ρ0` is the radius of a disk
about the origin inside C, `aMin = 2 - ρ0` is the least radial coordinate of a
square outside that disk and `U0` its largest transverse coordinate. The
rationals `radiusBound`, `rhoBound`, `coreLower` and `coreUpper` stand for
`R0`, `ρ0` and `c0` in the estimates, and `A` and `B` for `1/2 ∓ coreUpper`.
-/

noncomputable section
namespace SquaresInCircles.Six

/-! ### The model -/

lemma trig_bracket_half :
    (8775:ℝ)/10000 ≤ Real.cos (1/2) ∧ Real.cos (1/2) ≤ 878/1000 ∧
    (4794:ℝ)/10000 ≤ Real.sin (1/2) ∧ Real.sin (1/2) ≤ 4795/10000 := by
  have h := trig_bracket (l := 1/2) (u := 1/2) (x := 1/2) (by norm_num)
    (by linarith [Real.pi_gt_three]) ⟨le_rfl,le_rfl⟩
  norm_num at h
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

lemma trig_bracket_two_thirds :
    (157:ℝ)/200 ≤ Real.cos (2/3) ∧ Real.cos (2/3) ≤ 787/1000 ∧
    (309:ℝ)/500 ≤ Real.sin (2/3) ∧ Real.sin (2/3) ≤ 619/1000 := by
  have h := trig_bracket (l := 2/3) (u := 2/3) (x := 2/3) (by norm_num)
    (by linarith [Real.pi_gt_three]) ⟨le_rfl,le_rfl⟩
  norm_num at h
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

lemma trig_bracket_seven_sixths :
    (3931:ℝ)/10000 ≤ Real.cos (7/6) ∧ Real.cos (7/6) ≤ 2/5 ∧
    (9194:ℝ)/10000 ≤ Real.sin (7/6) ∧ Real.sin (7/6) ≤ 9201/10000 := by
  have h := trig_bracket (l := 7/6) (u := 7/6) (x := 7/6) (by norm_num)
    (by linarith [Real.pi_gt_d2]) ⟨le_rfl,le_rfl⟩
  norm_num at h
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

lemma hStar_pos : 0 < hStar := halfDiagonal_pos

lemma hStar_sq : hStar^2=1/2 := halfDiagonal_sq

/-- `hStar` is the cosine and the sine of `π/4`. -/
lemma cos_quarter : Real.cos (Real.pi/4)=hStar := by simp [hStar]

lemma sin_quarter : Real.sin (Real.pi/4)=hStar := by simp [hStar]

lemma hStar_bounds : (707106781:ℝ)/1000000000 < hStar ∧ hStar < 707106782/1000000000 := by
  have hl : Real.sqrt ((1414213562/1000000000:ℝ)^2) < Real.sqrt 2 :=
    Real.sqrt_lt_sqrt (by positivity) (by norm_num)
  have hu : Real.sqrt 2 < Real.sqrt ((1414213564/1000000000:ℝ)^2) :=
    Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rw [Real.sqrt_sq (by norm_num)] at hl hu
  dsimp [hStar]
  constructor <;> linarith

private lemma AStar_bounds : 10 < AStar ∧ AStar < 11 := by
  dsimp [AStar]
  constructor <;> linarith [hStar_bounds.1,hStar_bounds.2]

private lemma BStar_bounds : 4/5 < BStar ∧ BStar < 1 := by
  dsimp [BStar]
  constructor <;> linarith [hStar_bounds.1,hStar_bounds.2]

private lemma discriminant_pos : 0 < discriminant := by
  dsimp [discriminant]
  nlinarith [AStar_bounds.1,BStar_bounds.2,sq_nonneg (AStar-10)]

private lemma sStar_den_pos : 0 < AStar+Real.sqrt discriminant := by
  linarith [AStar_bounds.1,Real.sqrt_nonneg discriminant]

lemma sStar_pos : 0 < sStar := by
  dsimp [sStar]
  exact div_pos (by linarith [BStar_bounds.1]) sStar_den_pos

private lemma sStar_lt_fifth : sStar < 1/5 := by
  rw [sStar,div_lt_iff₀ sStar_den_pos]
  linarith [BStar_bounds.2,AStar_bounds.1,Real.sqrt_nonneg discriminant]

/-- `s*` is a root of `s² - A s + B`. -/
lemma sStar_polynomial : sStar^2-AStar*sStar+BStar=0 := by
  have hd : AStar+Real.sqrt discriminant ≠ 0 := ne_of_gt sStar_den_pos
  have hs : sStar*(AStar+Real.sqrt discriminant)=2*BStar := by
    rw [sStar]
    exact div_mul_cancel₀ _ hd
  have hr := Real.sq_sqrt discriminant_pos.le
  have hp : (sStar^2-AStar*sStar+BStar)*(AStar+Real.sqrt discriminant)^2=0 := by
    calc
      _ = (sStar*(AStar+Real.sqrt discriminant))^2-
          AStar*(sStar*(AStar+Real.sqrt discriminant))*(AStar+Real.sqrt discriminant)+
          BStar*(AStar+Real.sqrt discriminant)^2 := by ring
      _ = BStar*((Real.sqrt discriminant)^2-discriminant) := by
        rw [hs]
        dsimp [discriminant]
        ring
      _ = 0 := by rw [hr]; ring
  exact (mul_eq_zero.mp hp).resolve_right (pow_ne_zero 2 hd)

/-- `s*` is the root of the quadratic below `1/5`, where the quadratic changes
sign between the two ends of the bracket. -/
lemma sStar_bounds : (8424567:ℝ)/100000000 < sStar ∧ sStar < 842457/10000000 := by
  have pl : 0 < (8424567/100000000:ℝ)^2-AStar*(8424567/100000000)+BStar := by
    dsimp [AStar,BStar]
    linarith [hStar_bounds.1,hStar_bounds.2]
  have pu : (842457/10000000:ℝ)^2-AStar*(842457/10000000)+BStar < 0 := by
    dsimp [AStar,BStar]
    linarith [hStar_bounds.1,hStar_bounds.2]
  constructor
  · by_contra! hl
    have hm := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ 8424567/100000000-sStar by linarith)
      (show 8424567/100000000+sStar-AStar ≤ 0 by linarith [sStar_lt_fifth,AStar_bounds.1])
    nlinarith [sStar_polynomial]
  · by_contra! hu
    have hm := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ sStar-842457/10000000 by linarith)
      (show sStar+842457/10000000-AStar ≤ 0 by linarith [sStar_lt_fifth,AStar_bounds.1])
    nlinarith [sStar_polynomial]

lemma tStar_bounds : (4202266:ℝ)/10000000 < tStar ∧ tStar < 4202267/10000000 := by
  have hs := sStar_bounds
  have hc0 : 0 ≤ -20+30*hStar := by linarith [hStar_bounds.1]
  have hlo := mul_le_mul
    (show (121320343:ℝ)/100000000 ≤ -20+30*hStar by linarith [hStar_bounds.1])
    hs.1.le (by norm_num) hc0
  have hhi := mul_le_mul
    (show -20+30*hStar ≤ (60660173:ℝ)/50000000 by linarith [hStar_bounds.2])
    hs.2.le sStar_pos.le (by norm_num)
  dsimp [tStar]
  constructor <;> nlinarith [hStar_bounds.1,hStar_bounds.2]

lemma dStar_pos : 0 < dStar := by
  dsimp [dStar]
  linarith [hStar_bounds.1,tStar_bounds.2]

lemma qStar_pos : 0 < qStar := by
  dsimp [qStar]
  nlinarith [sStar_pos,sq_nonneg sStar]

lemma qStar_bounds :
    (14255886729137489:ℝ)/5000000000000000 < qStar ∧
      qStar < (142558873796849:ℝ)/50000000000000 := by
  have hs := sStar_bounds
  have hl := mul_nonneg (sub_nonneg.mpr hs.1.le)
    (show 0 ≤ sStar+8424567/100000000 by linarith [sStar_pos])
  have hu := mul_nonneg (sub_nonneg.mpr hs.2.le)
    (show 0 ≤ 842457/10000000+sStar by linarith [sStar_pos])
  dsimp [qStar]
  constructor <;> nlinarith

lemma radius_pos : 0 < radius := Real.sqrt_pos.mpr qStar_pos

lemma radius_sq : radius^2=qStar := Real.sq_sqrt qStar_pos.le

lemma radius_bounds : (16885429:ℝ)/10000000 < radius ∧ radius < 16885431/10000000 := by
  have hq := qStar_bounds
  constructor
  · rw [radius,Real.lt_sqrt (by norm_num)]; linarith
  · rw [radius,Real.sqrt_lt' (by norm_num)]; linarith

/-- The far corner `(s* + 3/2, s* + 1/2)` of E lies on the circle. -/
lemma east_radius_identity : qStar=(sStar+1/2)^2+(sStar+3/2)^2 := by
  dsimp [qStar]
  ring

/-- The far corner `(3/2 - s*, t* + 1/2)` of W, reflected, lies on the circle. -/
lemma west_radius_identity : qStar=(3/2-sStar)^2+(tStar+1/2)^2 := by
  have hp := sStar_polynomial
  have hh := hStar_sq
  dsimp [qStar,tStar,AStar,BStar] at *
  linear_combination (1200*hStar-849)*hp-
    ((320400*sStar^2-3200120*sStar+266409)/356)*hh

/-- The far vertices of D lie on the circle. -/
lemma diagonal_radius_identity : qStar=2*dStar^2+2*hStar*dStar+1/2 := by
  have hp := sStar_polynomial
  have hh := hStar_sq
  dsimp [qStar,dStar,tStar,AStar,BStar] at *
  linear_combination (2400*hStar-1698)*hp-
    ((320400*sStar^2-3232160*sStar+271927)/178)*hh

/-! ### The stress of the model -/

/-- The weight of N–W and E–S in the stress of the model. -/
def rStar : ℝ := (sStar+1/2)/(sStar+3/2)
/-- The factor `k*` of the weight `m* = (1 + r*) k*`. -/
def kStar : ℝ := (tStar+1/2)/(3/2-sStar)
/-- The weight of W–D and D–S in the stress of the model. -/
def mStar : ℝ := (1+rStar)*kStar
/-- The length of the force on D in the model. -/
def diagonalK : ℝ := 2*hStar*mStar
/-- The distance of the centre of D from the disk centre in the model, the largest
first coordinate of the centre of a unit square in the disk whose second
coordinate is `0`. -/
def rhoStar : ℝ := Real.sqrt (radius^2-1/4)-1/2
/-- The amount by which the thresholds of the pair N, W of the model exceed the
supports of its forces. -/
def pairBase : ℝ := mStar*(1/2-tStar)

lemma rStar_den_pos : 0 < sStar+3/2 := by linarith [sStar_pos]
lemma kStar_den_pos : 0 < 3/2-sStar := by linarith [sStar_bounds.2]

lemma rStar_bounds : (3687847:ℝ)/10000000 < rStar ∧ rStar < 3687848/10000000 := by
  have hs := sStar_bounds
  constructor
  · rw [rStar,lt_div_iff₀ rStar_den_pos]; linarith
  · rw [rStar,div_lt_iff₀ rStar_den_pos]; linarith

lemma kStar_bounds : (6499903:ℝ)/10000000 < kStar ∧ kStar < 6499904/10000000 := by
  have hs := sStar_bounds
  have ht := tStar_bounds
  constructor
  · rw [kStar,lt_div_iff₀ kStar_den_pos]; linarith
  · rw [kStar,div_lt_iff₀ kStar_den_pos]; linarith

lemma rStar_pos : 0 < rStar := by linarith [rStar_bounds.1]
lemma kStar_pos : 0 < kStar := by linarith [kStar_bounds.1]
lemma one_add_rStar_pos : 0 < 1+rStar := by linarith [rStar_bounds.1]

lemma mStar_bounds : (8896967:ℝ)/10000000 < mStar ∧ mStar < 8896970/10000000 := by
  have hr := rStar_bounds
  have hk := kStar_bounds
  have hl := mul_lt_mul'' (show (13687847:ℝ)/10000000 < 1+rStar by linarith) hk.1
    (by norm_num) (by norm_num)
  have hu := mul_lt_mul'' (show 1+rStar < (13687848:ℝ)/10000000 by linarith) hk.2
    one_add_rStar_pos.le kStar_pos.le
  dsimp [mStar]
  constructor <;> norm_num at hl hu ⊢ <;> linarith

lemma mStar_pos : 0 < mStar := by linarith [mStar_bounds.1]

lemma diagonalK_bounds :
    (12582211:ℝ)/10000000 < diagonalK ∧ diagonalK < 12582217/10000000 := by
  have hm := mStar_bounds
  have hl := mul_lt_mul''
    (show (1414213562:ℝ)/1000000000 < 2*hStar by linarith [hStar_bounds.1])
    hm.1 (by norm_num) (by norm_num)
  have hu := mul_lt_mul''
    (show 2*hStar < (1414213564:ℝ)/1000000000 by linarith [hStar_bounds.2])
    hm.2 (by linarith [hStar_pos]) mStar_pos.le
  dsimp [diagonalK]
  constructor <;> norm_num at hl hu ⊢ <;> linarith

lemma diagonalK_pos : 0 < diagonalK := by linarith [diagonalK_bounds.1]

lemma pairBase_bounds : (709739:ℝ)/10000000 < pairBase ∧ pairBase < 709742/10000000 := by
  have hm := mStar_bounds
  have ht := tStar_bounds
  have hl := mul_lt_mul'' hm.1 (show (797733:ℝ)/10000000 < 1/2-tStar by linarith)
    (by norm_num) (by norm_num)
  have hu := mul_lt_mul'' hm.2 (show 1/2-tStar < (797734:ℝ)/10000000 by linarith)
    mStar_pos.le (by linarith)
  dsimp [pairBase]
  constructor <;> norm_num at hl hu ⊢ <;> linarith

lemma rhoStar_bounds : (11128165:ℝ)/10000000 < rhoStar ∧ rhoStar < 11128167/10000000 := by
  have hq := qStar_bounds
  have hR := radius_sq
  constructor
  · rw [rhoStar,lt_sub_iff_add_lt,Real.lt_sqrt (by norm_num)]; linarith
  · rw [rhoStar,sub_lt_iff_lt_add,Real.sqrt_lt' (by norm_num)]; linarith

lemma rhoStar_identity : rhoStar^2+rhoStar+1/2=qStar := by
  have hR := radius_sq
  have h := Real.sq_sqrt (show 0 ≤ radius^2-1/4 by nlinarith [radius_bounds.1])
  dsimp [rhoStar]
  nlinarith

/-- The centre of D in the model is at distance `rhoStar` from the disk centre. -/
lemma rhoStar_eq_two_h_d : rhoStar=2*hStar*dStar := by
  have hx : (2*hStar*dStar)^2+2*hStar*dStar+1/2=qStar := by
    linear_combination 4*dStar^2*hStar_sq-diagonal_radius_identity
  have hsum : 0 < rhoStar+2*hStar*dStar+1 := by
    have := mul_pos hStar_pos dStar_pos
    linarith [rhoStar_bounds.1]
  have hf : (rhoStar-2*hStar*dStar)*(rhoStar+2*hStar*dStar+1)=0 := by
    linear_combination rhoStar_identity-hx
  exact sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_right hsum.ne')

/-- The force `(1, rStar)` on E of the model points at its far corner
`(sStar + 3/2, sStar + 1/2)` on the circle, so `radius` times its length is its
work on that corner. -/
lemma radius_mul_north_length :
    radius*Real.sqrt (1+rStar^2)=(sStar+3/2)+rStar*(sStar+1/2) := by
  have hd := rStar_den_pos
  have hr : rStar*(sStar+3/2)=sStar+1/2 := div_mul_cancel₀ _ hd.ne'
  have h1 : 1+rStar^2=(radius/(sStar+3/2))^2 := by
    rw [div_pow,radius_sq,eq_div_iff (pow_ne_zero 2 hd.ne')]
    linear_combination (rStar*(sStar+3/2)+(sStar+1/2))*hr-east_radius_identity
  rw [h1,Real.sqrt_sq (div_nonneg radius_pos.le hd.le),mul_div_assoc',← pow_two,radius_sq,
    div_eq_iff hd.ne']
  linear_combination east_radius_identity-(sStar+1/2)*hr

/-- The force `(1 + rStar, mStar)` on S of the model points at its far corner
`(3/2 - sStar, tStar + 1/2)` on the circle. -/
lemma radius_mul_west_length :
    radius*Real.sqrt ((1+rStar)^2+mStar^2)=(1+rStar)*(3/2-sStar)+mStar*(tStar+1/2) := by
  have hd := kStar_den_pos
  have hr := one_add_rStar_pos
  have hk : kStar*(3/2-sStar)=tStar+1/2 := div_mul_cancel₀ _ hd.ne'
  have h1 : (1+rStar)^2+mStar^2=((1+rStar)*radius/(3/2-sStar))^2 := by
    rw [div_pow,mul_pow,radius_sq,eq_div_iff (pow_ne_zero 2 hd.ne'),mStar]
    linear_combination (1+rStar)^2*(kStar*(3/2-sStar)+(tStar+1/2))*hk-
      (1+rStar)^2*west_radius_identity
  rw [h1,Real.sqrt_sq (div_nonneg (mul_nonneg hr.le radius_pos.le) hd.le),mul_div_assoc',
    show radius*((1+rStar)*radius)=(1+rStar)*radius^2 by ring,radius_sq,div_eq_iff hd.ne',mStar]
  linear_combination (1+rStar)*west_radius_identity-(1+rStar)*(tStar+1/2)*hk

/-- The pairs N, W and E, S of the model exceed their supports by `pairBase` each,
and the turned square falls short of its support by `diagonalK (rhoStar - 1)`:
the two cancel. -/
lemma pairBase_diagonal_identity : 2*pairBase+diagonalK*(1-rhoStar)=0 := by
  rw [rhoStar_eq_two_h_d]
  dsimp [pairBase,diagonalK,dStar]
  linear_combination (-4*mStar*(1/2+hStar-tStar))*hStar_sq

/-! ### The ceiling of the normalization -/

/-- The rational ceiling on the squared radius, just above `qStar`. -/
def Q0 : ℝ := 142559/50000

/-- The radius of the disk of squared radius `Q0`. -/
def R0 : ℝ := Real.sqrt Q0

/-- The largest radial offset of a square in the disk: its far corner
`(ρ0 + 1/2, 1/2)` lies on the circle of radius `R0`. -/
def rho0 : ℝ := Real.sqrt (Q0-1/4)-1/2

/-- The bound on the coordinates of the centre of C in its frame. -/
def c0 : ℝ := rho0-1

/-- The radius of a disk about the origin inside C, for the centre of C in
`[0, c0]²`. -/
def coreRadius : ℝ := 3/2-rho0

/-- The least radial coordinate of an exterior square that avoids the core. -/
def aMin : ℝ := 2-rho0

/-- The largest transverse coordinate of an exterior square that avoids the
core: its far corner at `a = aMin`. -/
def U0 : ℝ := Real.sqrt (Q0-(5/2-rho0)^2)-1/2

/-- The squared optimal radius lies below the ceiling `Q0`. -/
lemma qStar_lt_Q0 : qStar < Q0 := by
  dsimp [Q0]
  linarith [qStar_bounds.2]

lemma Q0_pos : 0 < Q0 := by norm_num [Q0]

lemma R0_nonneg : 0 ≤ R0 := Real.sqrt_nonneg _

lemma R0_sq : R0^2=Q0 := Real.sq_sqrt Q0_pos.le

lemma R0_pos : 0 < R0 := Real.sqrt_pos.mpr Q0_pos

lemma R0_bounds : (16885:ℝ)/10000 < R0 ∧ R0 < 8443/5000 := by
  have hl : Real.sqrt ((16885/10000:ℝ)^2) < Real.sqrt Q0 :=
    Real.sqrt_lt_sqrt (by positivity) (by norm_num [Q0])
  have hu : Real.sqrt Q0 < Real.sqrt ((8443/5000:ℝ)^2) :=
    Real.sqrt_lt_sqrt Q0_pos.le (by norm_num [Q0])
  rw [Real.sqrt_sq (by norm_num)] at hl hu
  exact ⟨hl,hu⟩

/-- The corners `(ρ0 + 1/2, ±1/2)` lie on the circle of radius `R0`. -/
lemma rho0_identity : (rho0+1/2)^2+1/4=Q0 := by
  have hs := Real.sq_sqrt (show 0 ≤ Q0-1/4 by norm_num [Q0])
  dsimp [rho0]
  nlinarith

lemma rho0_sq : rho0^2+rho0+1/2=Q0 := by
  nlinarith [rho0_identity]

lemma rho0_bounds : (11128174:ℝ)/10000000 < rho0 ∧ rho0 < 11128175/10000000 := by
  constructor
  · rw [rho0,lt_sub_iff_add_lt,Real.lt_sqrt (by norm_num)]
    norm_num [Q0]
  · rw [rho0,sub_lt_iff_lt_add,Real.sqrt_lt' (by norm_num)]
    norm_num [Q0]

lemma c0_bounds : (1128174:ℝ)/10000000 < c0 ∧ c0 < 1128175/10000000 := by
  dsimp [c0]
  constructor <;> linarith [rho0_bounds.1,rho0_bounds.2]

lemma c0_pos : 0 < c0 := by linarith [c0_bounds.1]

lemma coreRadius_bounds : (3871825:ℝ)/10000000 < coreRadius ∧ coreRadius < 3871826/10000000 := by
  dsimp [coreRadius]
  constructor <;> linarith [rho0_bounds.1,rho0_bounds.2]

lemma coreRadius_pos : 0 < coreRadius := by linarith [coreRadius_bounds.1]

lemma c0_add_coreRadius : c0+coreRadius=1/2 := by
  dsimp [c0,coreRadius]
  ring

lemma aMin_eq_coreRadius_add_half : aMin=coreRadius+1/2 := by
  dsimp [aMin,coreRadius]
  ring

lemma aMin_bounds : (8871825:ℝ)/10000000 < aMin ∧ aMin < 8871826/10000000 := by
  dsimp [aMin]
  constructor <;> linarith [rho0_bounds.1,rho0_bounds.2]

lemma U0_radicand : Q0-(5/2-rho0)^2=6*rho0-23/4 := by
  nlinarith [rho0_sq]

lemma U0_radicand_pos : 0 < Q0-(5/2-rho0)^2 := by
  rw [U0_radicand]
  linarith [rho0_bounds.1]

lemma U0_upper : U0 < 463/1000 := by
  have hs : Real.sqrt (Q0-(5/2-rho0)^2) < Real.sqrt ((963/1000:ℝ)^2) :=
    Real.sqrt_lt_sqrt U0_radicand_pos.le (by rw [U0_radicand]; nlinarith [rho0_bounds.2])
  rw [Real.sqrt_sq (by norm_num)] at hs
  dsimp [U0]
  linarith

/-! ### Rational ceilings -/

/-- A rational ceiling for `R0`. -/
def radiusBound : ℝ := 8443/5000
/-- A rational ceiling for `ρ0`. -/
def rhoBound : ℝ := 55641/50000
/-- A rational ceiling for `c0`. -/
def coreUpper : ℝ := 5641/50000
/-- A rational floor for `c0`. -/
def coreLower : ℝ := 141/1250

lemma ceiling_bounds : R0 ≤ radiusBound ∧ rho0 ≤ rhoBound ∧ coreLower ≤ c0 ∧ c0 ≤ coreUpper := by
  dsimp [radiusBound,rhoBound,coreLower,coreUpper]
  exact ⟨R0_bounds.2.le,by linarith [rho0_bounds.2],by linarith [c0_bounds.1],
    by linarith [c0_bounds.2]⟩

namespace Wings

/-- `1/2 - coreUpper` and `1/2 + coreUpper`: the coefficients that the half-width
of a square and the box of the centre of C leave in the separating inequalities
of the wings. -/
def A : ℝ := 19359/50000
def B : ℝ := 30641/50000

end Wings

end SquaresInCircles.Six

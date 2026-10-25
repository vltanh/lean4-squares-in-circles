module

public import Mathlib.Algebra.Order.Star.Real
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2PolynomialData

/-!
# Eight squares: the negative-A / nonnegative-TD2 coefficient families

The polynomial weights `k`, `l` and `c` are given by the low and high formulas, and the tilted
coefficient stays a trigonometric expression. The elementary range proofs (`low_ranges`,
`high_ranges`) use factorizations and completed squares.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.Explicit
open Candidate Secondary Polynomial
open Certificate (Family)

def lowKAt (t : ℝ) : ℝ := 169/250-t/5+(19/5)*t^2-5*t^3
def lowLAt (t : ℝ) : ℝ := 41/40-t/4+(29/2)*t^2+(55/4)*t^3-200*t^4
def lowCAt (t : ℝ) : ℝ := 1+(11/10)*t+17*t^2
def highKAt (t : ℝ) : ℝ := 169/250+t/5+(9/10)*t^2-(13/10)*t^3
def highLAt (t : ℝ) : ℝ := 41/40+(11/50)*t-(3/10)*t^2
def highCAt (t : ℝ) : ℝ := 1-(7/10)*t+(22/25)*t^2
def k : Family→ℝ→ℝ | .low,z => lowKAt (1/5-z) | .high,z => highKAt (z-1/5)
def l : Family→ℝ→ℝ | .low,z => lowLAt (1/5-z) | .high,z => highLAt (z-1/5)
def c : Family→ℝ→ℝ | .low,z => lowCAt (1/5-z) | .high,z => highCAt (z-1/5)
def m (f : Family) (z : ℝ) : ℝ := PositiveTD.tilted (c f z) z

@[simp] theorem k_eval (f : Family) (z : ℝ) : aeval z (Certificate.k f)=k f z := by
  cases f <;> norm_num [Certificate.k,Certificate.t,Certificate.split,k,lowKAt,highKAt] <;> ring
@[simp] theorem l_eval (f : Family) (z : ℝ) : aeval z (Certificate.l f)=l f z := by
  cases f <;> norm_num [Certificate.l,Certificate.t,Certificate.split,l,lowLAt,highLAt]
  ring
@[simp] theorem c_eval (f : Family) (z : ℝ) : aeval z (Certificate.c f)=c f z := by
  cases f <;> norm_num [Certificate.c,Certificate.t,Certificate.split,c,lowCAt,highCAt]

theorem low_L_derivative (t : ℝ) :
    HasDerivAt lowLAt (-1/4+29*t+(165/4)*t^2-800*t^3) t := by
  have hd := ((((hasDerivAt_const t (41/40:ℝ)).sub ((hasDerivAt_id' t).div_const 4)).add
    ((hasDerivAt_pow 2 t).const_mul (29/2:ℝ))).add
    ((hasDerivAt_pow 3 t).const_mul (55/4:ℝ))).sub ((hasDerivAt_pow 4 t).const_mul (200:ℝ))
  exact hd.congr_deriv (by norm_num; ring)

theorem low_L_increasing : MonotoneOn lowLAt (Icc (1/21:ℝ) (1/5:ℝ)) := by
  apply monoOn_of_hasDeriv_nonneg
    (fun t _ => (low_L_derivative t).continuousAt.continuousWithinAt)
    (fun t _ => low_L_derivative t)
  intro t ht
  have ht0 : 0≤t := by linarith [ht.1]
  have hprod := mul_nonneg (mul_nonneg ht0
      (show 0≤1/5-t by linarith [ht.2]))
    (show 0≤800*t+475/4 by linarith)
  have hid : -1/4+29*t+(165/4)*t^2-800*t^3=
      -1/4+(21/4)*t+t*(1/5-t)*(800*t+475/4) := by ring
  rw [hid]
  linarith [ht.1]

theorem low_at_ranges {t : ℝ} (ht : t∈Icc 0 (1/5:ℝ)) :
    2/3<lowKAt t ∧ lowKAt t≤187/250 ∧
      1023/1000<lowLAt t ∧ lowLAt t≤269/200 ∧
      1≤lowCAt t ∧ lowCAt t≤19/10 := by
  have ht2 := pow_le_pow_left₀ ht.1 ht.2 2
  have hkfactor := mul_nonneg (sq_nonneg t) (sub_nonneg.mpr ht.2)
  have hkchord := mul_nonneg (mul_nonneg ht.1 (sub_nonneg.mpr ht.2))
    (show 0≤14/5-5*t by linarith [ht.2])
  have hklo : (2/3:ℝ)<lowKAt t := by
    dsimp [lowKAt]
    nlinarith [sq_nonneg (t-(1/5)/(2*(14/5)))]
  have hkhi : lowKAt t≤187/250 := by
    dsimp [lowKAt]
    nlinarith [ht.2]
  have hlprod := mul_nonneg (mul_nonneg (sq_nonneg t) (sub_nonneg.mpr ht.2))
    (show 0≤105/4+200*t by linarith [ht.1])
  have hllo : (1023/1000:ℝ)<lowLAt t := by
    dsimp [lowLAt]
    nlinarith [sq_nonneg (t-(1/4)/(2*(37/4)))]
  have hlhi : lowLAt t≤269/200 := by
    by_cases hsmall : t≤1/21
    · have h2 := pow_le_pow_left₀ ht.1 hsmall 2
      have h3 := pow_le_pow_left₀ ht.1 hsmall 3
      have h4 := pow_nonneg ht.1 4
      dsimp [lowLAt]
      nlinarith
    · have hh := low_L_increasing ⟨by linarith,ht.2⟩
        (show (1/5:ℝ)∈Icc (1/21:ℝ) (1/5:ℝ) by norm_num) ht.2
      have hv : lowLAt (1/5)=269/200 := by norm_num [lowLAt]
      linarith
  have hc : 1≤lowCAt t ∧ lowCAt t≤19/10 := by
    dsimp [lowCAt]
    constructor <;> nlinarith [sq_nonneg t,ht.1,ht.2]
  exact ⟨hklo,hkhi,hllo,hlhi,hc.1,hc.2⟩

theorem low_ratio {z : ℝ} (hz : z∈Icc 0 (1/5:ℝ)) :
    (11/20)*l .low z<k .low z ∧ k .low z<(33/50)*l .low z := by
  obtain ⟨t,htd⟩ : ∃ t : ℝ, t=1/5-z := ⟨_,rfl⟩
  have ht : t∈Icc 0 (1/5:ℝ) := ⟨by linarith [hz.2],by linarith [hz.1]⟩
  have hupper : (0:ℝ)<(33/50)*lowLAt t-lowKAt t := by
    have hfactor := mul_nonneg (sub_nonneg.mpr ht.2)
      (show 0≤493/40+132*t by linarith [ht.1])
    have hscaled := mul_nonneg (sq_nonneg t) hfactor
    dsimp [lowLAt,lowKAt]
    nlinarith [ht.1,sq_nonneg t]
  have hid : k .low z-(11/20)*l .low z=
      33/4000-(7/25)*z+z^2*(235/16-(1207/16)*z+110*z^2) := by
    dsimp [k,l,lowKAt,lowLAt]
    ring
  have hfactor := mul_nonneg (sub_nonneg.mpr hz.2)
    (show 0≤855/16-110*z by linarith [hz.2])
  have hscaled := mul_nonneg (sq_nonneg z) hfactor
  have hlower : (0:ℝ)<k .low z-(11/20)*l .low z := by
    rw [hid]
    nlinarith [sq_nonneg (z-7/200)]
  refine ⟨by linarith,?_⟩
  have hk : k .low z=lowKAt t := by rw [htd]; rfl
  have hl : l .low z=lowLAt t := by rw [htd]; rfl
  rw [hk,hl]
  linarith

theorem low_ranges {z : ℝ} (hz : z∈Icc 0 (1/5:ℝ)) :
    2/3<k .low z ∧ k .low z≤187/250 ∧
      1023/1000<l .low z ∧ l .low z≤269/200 ∧
      1≤c .low z ∧ c .low z≤19/10 := by
  apply low_at_ranges
  exact ⟨by linarith [hz.2],by linarith [hz.1]⟩

theorem high_at_ranges {t : ℝ} (ht : t∈Icc 0 (1/2:ℝ)) :
    169/250≤highKAt t ∧ highKAt t≤1677/2000 ∧
      41/40≤highLAt t ∧ highLAt t≤799/750 ∧
      43/50<highCAt t ∧ highCAt t≤1 ∧
      highKAt t<highCAt t ∧ highKAt t<highLAt t := by
  have htchord := mul_nonneg ht.1 (sub_nonneg.mpr ht.2)
  have hklofactor := mul_nonneg (sq_nonneg t)
    (show 0≤9/10-(13/10)*t by linarith [ht.2])
  have hkhiinner : 0≤13/40+t/4-(13/10)*t^2 := by nlinarith
  have hkhiouter := mul_nonneg (sub_nonneg.mpr ht.2) hkhiinner
  have hk : 169/250≤highKAt t ∧ highKAt t≤1677/2000 := by
    dsimp [highKAt]
    constructor <;> nlinarith [ht.1]
  have hl : 41/40≤highLAt t ∧ highLAt t≤799/750 := by
    have hprod := mul_nonneg ht.1
      (show 0≤11/50-(3/10)*t by linarith [ht.2])
    dsimp [highLAt]
    constructor
    · linarith
    · nlinarith [sq_nonneg (t-11/30)]
  have hc : 43/50<highCAt t ∧ highCAt t≤1 := by
    have hprod := mul_nonneg ht.1
      (show 0≤7/10-(22/25)*t by linarith [ht.2])
    dsimp [highCAt]
    constructor
    · nlinarith [sq_nonneg (t-35/88)]
    · linarith
  have hck : highKAt t<highCAt t := by
    have hprod := mul_nonneg ht.1 (sq_nonneg (t-1/2))
    dsimp [highCAt,highKAt]
    nlinarith [sq_nonneg (t-(49/40)/(2*(32/25)))]
  have hlk : highKAt t<highLAt t := by
    have h2 := pow_le_pow_left₀ ht.1 ht.2 2
    have h3 := pow_nonneg ht.1 3
    dsimp [highLAt,highKAt]
    nlinarith [ht.1]
  exact ⟨hk.1,hk.2,hl.1,hl.2,hc.1,hc.2,hck,hlk⟩

theorem high_ranges {z : ℝ} (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) :
    169/250≤k .high z ∧ k .high z≤1677/2000 ∧
      41/40≤l .high z ∧ l .high z≤799/750 ∧
      43/50<c .high z ∧ c .high z≤1 ∧
      k .high z<c .high z ∧ k .high z<l .high z := by
  apply high_at_ranges
  exact ⟨by linarith [hz.1],by linarith [hz.2]⟩

theorem high_ratio_lower {z : ℝ} (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) :
    (659/1000)*l .high z<k .high z := by
  let t : ℝ := z-1/5
  have ht : t∈Icc 0 (1/2:ℝ) := ⟨by dsimp [t]; linarith [hz.1],
    by dsimp [t]; linarith [hz.2]⟩
  have hprod := mul_nonneg (sq_nonneg t)
    (show 0≤10977/10000-(13/10)*t by linarith [ht.2])
  have hh : (659/1000)*highLAt t<highKAt t := by
    dsimp [highLAt,highKAt]
    nlinarith [ht.1]
  exact hh

theorem family_frame_domain (f : Family) {z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ)) :
    z∈Icc 0 frameCap := by
  cases f <;> norm_num [Certificate.left,Certificate.right,Certificate.split,
    PositiveTD.Certificate.h,frameCap] at hz ⊢ <;> constructor <;> linarith [hz.1,hz.2]

theorem family_positive (f : Family) {z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ)) :
    0<k f z ∧ 0<l f z ∧ 0<c f z ∧ 0< m f z := by
  have hbase : 0<k f z ∧ 0<l f z ∧ 0<c f z := by
    cases f
    · have hz' : z∈Icc 0 (1/5:ℝ) := by
        norm_num [Certificate.left,Certificate.right,Certificate.split] at hz
        exact ⟨hz.1,by linarith [hz.2]⟩
      obtain ⟨hk,_,hl,_,hc,_⟩ := low_ranges hz'
      exact ⟨by linarith,by linarith,by linarith⟩
    · have hz' : z∈Icc (1/5:ℝ) (7/10:ℝ) := by
        norm_num [Certificate.left,Certificate.right,Certificate.split,
          PositiveTD.Certificate.h] at hz
        exact ⟨by linarith [hz.1],by linarith [hz.2]⟩
      obtain ⟨hk,_,hl,_,hc,_,_,_⟩ := high_ranges hz'
      exact ⟨by linarith,by linarith,by linarith⟩
  exact ⟨hbase.1,hbase.2.1,hbase.2.2,
    PositiveTD.tilted_pos hbase.2.2 (family_frame_domain f hz)⟩

end SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.Explicit

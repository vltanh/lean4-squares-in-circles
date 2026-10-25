module

public import SquaresInCircles.Eight.Words.Second.Mixed.Zero.Data
public import SquaresInCircles.Eight.Words.Short.Mixed.ZeroPositiveCore

/-!
# Eight squares: both positive-core/positive-outer zero rows

A single circle support applies throughout
the original frame interval.  Its rotating-vector speed is at most the
core slope, so the fixed initial lower bound pays the entire possible
angle loss.  Every source point on both closed core pieces is included.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedZero.SameCore
open CommonQuarter CorePairGeometry Arithmetic

def N (r : SameRow) (x : ℝ) : ℝ :=
  CircularNorm.norm ((coreG r)^2+(11/10)^2) (-2*coreG r*(11/10)) 0 x
def Nd (r : SameRow) (x : ℝ) : ℝ := coreG r*(11/10)*Real.sin x/N r x
def F (r : SameRow) (x : ℝ) : ℝ :=
  x+coreC r+(coreG r+11/10)/2+coreG r*Real.sin x-CommonQuarter.radius*N r x
def Fd (r : SameRow) (x : ℝ) : ℝ := 1+coreG r*Real.cos x-CommonQuarter.radius*Nd r x

lemma energy_positive (r : SameRow) (x : ℝ) :
    0<CircularNorm.energy ((coreG r)^2+(11/10)^2)
      (-2*coreG r*(11/10)) 0 x := by
  fin_cases r <;> norm_num [coreG,CircularNorm.energy] <;>
    nlinarith [Real.cos_le_one x]

lemma N_positive (r : SameRow) (x : ℝ) : 0<N r x :=
  CircularNorm.norm_pos (energy_positive r x)

lemma N_square (r : SameRow) (x : ℝ) :
    (N r x)^2=(coreG r)^2+(11/10)^2-2*coreG r*(11/10)*Real.cos x := by
  have hh := CircularNorm.norm_sq (energy_positive r x).le
  simp only [N]
  rw [hh]
  simp only [CircularNorm.energy]
  ring

lemma N_hasDerivAt (r : SameRow) (x : ℝ) : HasDerivAt (N r) (Nd r x) x := by
  have hn : CircularNorm.norm ((coreG r)^2+(11/10)^2)
      (-2*coreG r*(11/10)) 0 x≠0 := (N_positive r x).ne'
  convert CircularNorm.norm_hasDerivAt (energy_positive r x) using 1
  · rfl
  · dsimp [Nd,N,CircularNorm.d1,CircularNorm.slope]
    field_simp [hn]
    <;> ring

lemma speed_upper (r : SameRow) (x : ℝ) : Nd r x≤coreG r := by
  have hn := N_square r x
  have hid : ((11/10)*Real.sin x)^2+
      (coreG r-(11/10)*Real.cos x)^2=(N r x)^2 := by
    linear_combination (121/100:ℝ)*(Real.sin_sq_add_cos_sq x)-hn
  have hs : (11/10)*Real.sin x≤N r x := by
    nlinarith [sq_nonneg (coreG r-(11/10)*Real.cos x),N_positive r x]
  have hg : 0≤coreG r := by linarith [(core_coefficients r).1]
  apply (div_le_iff₀ (N_positive r x)).2
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hs hg

lemma F_hasDerivAt (r : SameRow) (x : ℝ) : HasDerivAt (F r) (Fd r x) x := by
  have h := (((((hasDerivAt_id' x).add_const (coreC r)).add_const
    ((coreG r+11/10)/2)).add ((Real.hasDerivAt_sin x).const_mul (coreG r))).sub
      ((N_hasDerivAt r x).const_mul CommonQuarter.radius))
  exact h.congr_deriv (by simp only [Fd])

lemma derivative_lower (r : SameRow) {x : ℝ} (hx : x∈Icc (2/5) (7/10)) :
    -(27/100:ℝ)<Fd r x := by
  have hr := radius_bounds
  have hg : 0<coreG r := by linarith [(core_coefficients r).1]
  have hR : 0<CommonQuarter.radius := by linarith [hr.1]
  have hs := mul_le_mul_of_nonneg_left (speed_upper r x) hR.le
  have hc := mul_lt_mul_of_pos_left
    (ShortMixedZero.PositiveCore.angle_trig hx).2 hg
  have hu := mul_lt_mul_of_pos_right hr.2 hg
  dsimp [Fd]
  fin_cases r <;> norm_num [coreG] at hs hc hu ⊢ <;> linarith

lemma initial_norm (r : SameRow) : N r (2/5)<(217/500:ℝ) := by
  have hh := N_square r (2/5)
  have hp := N_positive r (2/5)
  have hc := mul_lt_mul_of_pos_left ShortMixedZero.PositiveCore.initial_trig.2.2
    (show 0<2*coreG r*(11/10) by linarith [(core_coefficients r).1])
  generalize N r (2/5) = n at hh hp ⊢
  fin_cases r <;> norm_num [coreG] at hh hc ⊢ <;> nlinarith

lemma initial_value (r : SameRow) : (49/50:ℝ)<F r (2/5) := by
  have hR : 0<CommonQuarter.radius := by linarith [radius_bounds.1]
  have hn := mul_lt_mul_of_pos_left (initial_norm r) hR
  have hr := mul_lt_mul_of_pos_right radius_bounds.2
    (by norm_num : (0:ℝ)<217/500)
  have hs := mul_lt_mul_of_pos_left ShortMixedZero.PositiveCore.initial_trig.1
    (show 0<coreG r by linarith [(core_coefficients r).1])
  dsimp only [F]
  generalize N r (2/5) = n at hn ⊢
  fin_cases r <;> norm_num [coreC,coreG] at hs ⊢ <;> linarith

lemma support_lower (r : SameRow) {x : ℝ} (hx : x∈Icc (2/5) (7/10)) :
    (17953/20000:ℝ)<F r x := by
  have hd (t : ℝ) : HasDerivAt (fun t => F r t+(27/100)*t) (Fd r t+27/100) t :=
    ((F_hasDerivAt r t).add ((hasDerivAt_id' t).const_mul (27/100:ℝ))).congr_deriv (by ring)
  have hm : MonotoneOn (fun t => F r t+(27/100)*t) (Icc (2/5) (7/10)) :=
    monoOn_of_hasDeriv_nonneg
      (fun t _ => (hd t).continuousAt.continuousWithinAt)
      (fun t _ => hd t)
      (fun t ht => by linarith [derivative_lower r (Ioo_subset_Icc_self ht)])
  have hh := hm (by norm_num) hx hx.1
  simp only at hh
  linarith [initial_value r,hx.2]

theorem original (r : SameRow) {a b A B x : ℝ}
    (hs : CoreState a b) (ht : OuterState A B) (hx : |x|≤7/10)
    (hm : 0≤Eight.forwardMargin 0 a b A B 1 1 x) :
    (17953/20000:ℝ)<x+coreC r+coreG r*b-(targetLabel r).outer B := by
  have hangle : x∈Icc (2/5) (7/10) :=
    ⟨(ShortMixedZero.PositiveCore.original_angle hs ht hx hm).le,(abs_le.mp hx).2⟩
  have tr := positive_trig
    (show x∈Icc 0 (7/10) from ⟨by linarith [hangle.1],hangle.2⟩)
  have hw : pairWidth x=(1+Real.sin x+Real.cos x)/2 := by
    rw [signed_width hx,abs_of_nonneg tr.2.2.1]
    ring
  have hmargin := mul_nonneg
    (show 0≤coreG r by linarith [(core_coefficients r).1]) hm
  norm_num [Eight.forwardMargin] at hmargin
  rw [hw] at hmargin
  have hB : B∈Icc 0 outerDiagonal := ⟨ht.1,(outer_bounds ht).2.2.2.1⟩
  have htarget := target_affine_upper r hB
  have hsupp := outer_circle_lower (X := -coreG r*Real.sin x)
    (Y := coreG r*Real.cos x-11/10) ht
  have he : (-coreG r*Real.sin x)^2+(coreG r*Real.cos x-11/10)^2=
      (coreG r)^2+(11/10)^2-2*coreG r*(11/10)*Real.cos x := by
    linear_combination (coreG r)^2*(Real.sin_sq_add_cos_sq x)
  have hn : N r x=Real.sqrt ((-coreG r*Real.sin x)^2+
      (coreG r*Real.cos x-11/10)^2) := by
    rw [he]
    simp only [N,CircularNorm.norm,CircularNorm.energy]
    congr 1
    ring
  rw [←hn] at hsupp
  have hl := support_lower r hangle
  dsimp [F] at hl
  nlinarith only [hmargin,hsupp,htarget,hl]

end SquaresInCircles.Eight.SecondWord.MixedZero.SameCore

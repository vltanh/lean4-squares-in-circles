module

public import Mathlib.Algebra.Ring.IsFormallyReal
public import SquaresInCircles.Eight.Frames.Pair.Shape
public import SquaresInCircles.Eight.Words.Short.Mixed.ZeroOuter

/-!
# Eight squares: original role labels and original owners for the mixed opposite cases

The analytic outer-source family is restored to the actual short-word
roles without changing a chosen vertex label. Source-secondary outer/core
pairs and target-secondary core/outer pairs are covered on both complete
angle halves. The reflected presentation of the latter is an exact
coordinate and coefficient identity.
-/

section
/-!
## The original negative-angle cutoff and the first small-slope family

The weak source-secondary inequality forces the whole feasible interval
to end before `.44152`. The first small-slope family's lower envelope
has a concave derivative that starts positive, hence its minimum is at
one of the two geometric endpoints. The endpoint comparisons use exact
Taylor bounds.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.ShortMixedZero

open CommonQuarter CorePairGeometry Arithmetic

def smallCap : ℝ := 5519/12500
def capMargin (x : ℝ) : ℝ := outerDiagonal-1/2+
  (CoreAngleEndpoint.diagonal-1/2)*Real.cos x-
    (CoreAngleEndpoint.diagonal+1/2)*Real.sin x
def capMarginD (x : ℝ) : ℝ :=
  -(CoreAngleEndpoint.diagonal-1/2)*Real.sin x-
    (CoreAngleEndpoint.diagonal+1/2)*Real.cos x

lemma capMargin_hasDerivAt (x : ℝ) : HasDerivAt capMargin (capMarginD x) x := by
  have hh : HasDerivAt (fun y => outerDiagonal-1/2+
      (CoreAngleEndpoint.diagonal-1/2)*Real.cos y-
        (CoreAngleEndpoint.diagonal+1/2)*Real.sin y)
      ((CoreAngleEndpoint.diagonal-1/2)*(-Real.sin x)-
        (CoreAngleEndpoint.diagonal+1/2)*Real.cos x) x :=
    (((Real.hasDerivAt_cos x).const_mul (CoreAngleEndpoint.diagonal-1/2)).const_add
      (outerDiagonal-1/2)).sub
        ((Real.hasDerivAt_sin x).const_mul (CoreAngleEndpoint.diagonal+1/2))
  exact hh.congr_deriv (by dsimp [capMarginD]; ring)

lemma capMargin_antitone : AntitoneOn capMargin (Icc 0 (7/10)) := by
  apply antiOn_of_hasDeriv_nonpos
  · exact fun x _ => (capMargin_hasDerivAt x).continuousAt.continuousWithinAt
  · exact fun x _ => capMargin_hasDerivAt x
  · intro x hx
    have ht := positive_trig (Ioo_subset_Icc_self hx)
    have hc := CoreAngleEndpoint.diagonal_bounds
    have hs := mul_nonneg (show 0≤CoreAngleEndpoint.diagonal-1/2 by linarith [hc.1]) ht.2.2.1
    have hk := mul_nonneg (show 0≤CoreAngleEndpoint.diagonal+1/2 by linarith [hc.1])
      (show 0≤Real.cos x by linarith [ht.1])
    dsimp [capMarginD]
    linarith

lemma smallCap_point_trig :
    (213657/500000:ℝ)<Real.sin smallCap ∧
      Real.cos smallCap<113013/125000 := by
  have hsc : smallCap=5519/12500 := rfl
  have hs := sin_lower_seven (x := smallCap) (by norm_num [smallCap])
  have hcU := cos_le_cos8 (x := smallCap) (by norm_num [smallCap])
  rw [hsc] at hs hcU ⊢
  norm_num [cos8] at hs hcU
  exact ⟨by linarith,by linarith⟩

lemma capMargin_smallCap_neg : capMargin smallCap<0 := by
  have ht := smallCap_point_trig
  have hc := CoreAngleEndpoint.diagonal_bounds
  have hd := fine_diagonal_bounds
  have hp := mul_le_mul_of_nonneg_left ht.2.le
    (show 0≤CoreAngleEndpoint.diagonal-1/2 by linarith [hc.1])
  have hn := mul_le_mul_of_nonneg_left ht.1.le
    (show 0≤CoreAngleEndpoint.diagonal+1/2 by linarith [hc.1])
  dsimp [capMargin]
  nlinarith [hd.2,hc.1,hc.2]

/-- This cutoff is derived from the actual outer/core states and the
original weak source-secondary owner, before a role coefficient is used. -/
theorem negative_angle_cut {a b A B x : ℝ} (hs : OuterState a b)
    (ht : CoreState A B) (hx : x∈Icc 0 (7/10))
    (hm : (1+Real.sin x+Real.cos x)/2≤b-A*Real.sin x+B*Real.cos x) :
    x<smallCap := by
  have htr := positive_trig hx
  have hb := (outer_bounds hs).2.2.2.1
  have hA := core_primary_lower ht
  have hB := (CoreAngleEndpoint.state_bounds ht).2.2.2.2
  have hprim := mul_le_mul_of_nonneg_right hA htr.2.2.1
  have hsec := mul_le_mul_of_nonneg_right hB (show 0≤Real.cos x by linarith [htr.1])
  have hbound : 0≤capMargin x := by dsimp [capMargin]; linarith
  by_contra! hlarge
  have hcap : smallCap∈Icc 0 (7/10) := by norm_num [smallCap]
  have hh := capMargin_antitone hcap hx hlarge
  linarith [capMargin_smallCap_neg]

def firstNegative (x : ℝ) : ℝ :=
  -x+c 0+g 0*CoreAngleEndpoint.diagonal+q 0/2+
    q 0*(1/2-CoreAngleEndpoint.diagonal)*Real.cos x+
      q 0*(1/2+CoreAngleEndpoint.diagonal)*Real.sin x
def firstNegativeD (x : ℝ) : ℝ :=
  -1+q 0*(CoreAngleEndpoint.diagonal-1/2)*Real.sin x+
    q 0*(1/2+CoreAngleEndpoint.diagonal)*Real.cos x
def firstNegativeDD (x : ℝ) : ℝ :=
  q 0*(CoreAngleEndpoint.diagonal-1/2)*Real.cos x-
    q 0*(1/2+CoreAngleEndpoint.diagonal)*Real.sin x
def firstNegativeDDD (x : ℝ) : ℝ :=
  -q 0*(CoreAngleEndpoint.diagonal-1/2)*Real.sin x-
    q 0*(1/2+CoreAngleEndpoint.diagonal)*Real.cos x

lemma firstNegative_hasDerivAt (x : ℝ) :
    HasDerivAt firstNegative (firstNegativeD x) x := by
  have hh : HasDerivAt (fun y => -y+c 0+g 0*CoreAngleEndpoint.diagonal+q 0/2+
      q 0*(1/2-CoreAngleEndpoint.diagonal)*Real.cos y+
        q 0*(1/2+CoreAngleEndpoint.diagonal)*Real.sin y)
      (-1+q 0*(1/2-CoreAngleEndpoint.diagonal)*(-Real.sin x)+
        q 0*(1/2+CoreAngleEndpoint.diagonal)*Real.cos x) x :=
    (((((hasDerivAt_id' x).neg.add_const (c 0)).add_const
      (g 0*CoreAngleEndpoint.diagonal)).add_const (q 0/2)).add
        ((Real.hasDerivAt_cos x).const_mul (q 0*(1/2-CoreAngleEndpoint.diagonal)))).add
          ((Real.hasDerivAt_sin x).const_mul (q 0*(1/2+CoreAngleEndpoint.diagonal)))
  exact hh.congr_deriv (by dsimp [firstNegativeD]; ring)

lemma firstNegativeD_hasDerivAt (x : ℝ) :
    HasDerivAt firstNegativeD (firstNegativeDD x) x := by
  have hh : HasDerivAt (fun y => -1+q 0*(CoreAngleEndpoint.diagonal-1/2)*Real.sin y+
      q 0*(1/2+CoreAngleEndpoint.diagonal)*Real.cos y)
      (q 0*(CoreAngleEndpoint.diagonal-1/2)*Real.cos x+
        q 0*(1/2+CoreAngleEndpoint.diagonal)*(-Real.sin x)) x :=
    (((Real.hasDerivAt_sin x).const_mul (q 0*(CoreAngleEndpoint.diagonal-1/2))).const_add (-1)).add
      ((Real.hasDerivAt_cos x).const_mul (q 0*(1/2+CoreAngleEndpoint.diagonal)))
  exact hh.congr_deriv (by dsimp [firstNegativeDD]; ring)

lemma firstNegativeDD_hasDerivAt (x : ℝ) :
    HasDerivAt firstNegativeDD (firstNegativeDDD x) x := by
  have hh : HasDerivAt (fun y => q 0*(CoreAngleEndpoint.diagonal-1/2)*Real.cos y-
      q 0*(1/2+CoreAngleEndpoint.diagonal)*Real.sin y)
      (q 0*(CoreAngleEndpoint.diagonal-1/2)*(-Real.sin x)-
        q 0*(1/2+CoreAngleEndpoint.diagonal)*Real.cos x) x :=
    ((Real.hasDerivAt_cos x).const_mul (q 0*(CoreAngleEndpoint.diagonal-1/2))).sub
      ((Real.hasDerivAt_sin x).const_mul (q 0*(1/2+CoreAngleEndpoint.diagonal)))
  exact hh.congr_deriv (by dsimp [firstNegativeDDD]; ring)

lemma firstNegativeD_concave : ConcaveOn ℝ (Icc 0 smallCap) firstNegativeD := by
  apply concave_of_deriv2 (fun x _ => firstNegativeD_hasDerivAt x)
    (fun x _ => firstNegativeDD_hasDerivAt x)
  intro x hx
  have ht := positive_trig ⟨hx.1,hx.2.trans (by norm_num [smallCap])⟩
  have hq : 0≤q 0 := by norm_num [q]
  have hd : 0≤CoreAngleEndpoint.diagonal-1/2 := by linarith [CoreAngleEndpoint.diagonal_bounds.1]
  have hs := mul_nonneg (mul_nonneg hq hd) ht.2.2.1
  have hc := mul_nonneg (mul_nonneg hq (show 0≤1/2+CoreAngleEndpoint.diagonal by linarith))
    (show 0≤Real.cos x by linarith [ht.1])
  dsimp [firstNegativeDDD]
  linarith

lemma firstNegative_endpoints :
    0≤firstNegativeD 0 ∧ (449/500:ℝ)<firstNegative 0 ∧
      (449/500:ℝ)<firstNegative smallCap := by
  have hd := CoreAngleEndpoint.diagonal_bounds
  have ht := smallCap_point_trig
  have hsin := mul_le_mul_of_nonneg_left ht.1.le
    (show 0≤1/2+CoreAngleEndpoint.diagonal by linarith [hd.1])
  have hcos := mul_le_mul_of_nonpos_left ht.2.le
    (show 1/2-CoreAngleEndpoint.diagonal≤0 by linarith [hd.1])
  have hsc : smallCap=5519/12500 := rfl
  refine ⟨?_,?_,?_⟩
  · norm_num [firstNegativeD,q]
    nlinarith [hd.1]
  · norm_num [firstNegative,c,q,g]
    nlinarith [hd.1,hd.2]
  · norm_num [firstNegative,c,q,g]
    linarith [hd.1,hd.2]

lemma firstNegative_lower {x : ℝ} (hx : x∈Icc 0 smallCap) :
    (449/500:ℝ)<firstNegative x := by
  have hh := FramePairCalculus.endpoint_minimum_of_concave_derivative hx
    (fun z _ => firstNegative_hasDerivAt z) firstNegativeD_concave firstNegative_endpoints.1
  exact (lt_min firstNegative_endpoints.2.1 firstNegative_endpoints.2.2).trans_le hh

/-- The first small-slope family, including its complete negative half,
both core pieces and every original weak contact. -/
theorem opposite_outer_negative_first {a b A B x : ℝ}
    (hs : OuterState a b) (ht : CoreState A B) (hx : x∈Icc 0 (7/10))
    (hm : (1+Real.sin x+Real.cos x)/2≤b-A*Real.sin x+B*Real.cos x) :
    (449/500:ℝ)< -x+c 0-p 0*a+q 0*b+g 0*B := by
  have hcut := negative_angle_cut hs ht hx hm
  have hh := firstNegative_lower ⟨hx.1,hcut.le⟩
  have htr := positive_trig hx
  have hq : 0<q 0 := by norm_num [q]
  have hcoef : g 0-q 0*Real.cos x≤0 := by
    have hm := mul_lt_mul_of_pos_left htr.1 hq
    norm_num [q,g] at hm ⊢
    linarith
  have hcore := core_diagonal_lower (X := q 0*Real.sin x) (Y := g 0-q 0*Real.cos x)
    ht (mul_nonneg hq.le htr.2.2.1) hcoef
  have hsep := mul_nonneg hq.le (sub_nonneg.mpr hm)
  dsimp [firstNegative] at hh
  norm_num [p]
  nlinarith

end SquaresInCircles.Eight.ShortMixedZero
end
end
end

section
/-!
## The exact diagonal-contact curve of the last mixed negative family

The contact is continued through the single endpoint `.44152`; its
radical stays positive even where that continuation is slightly beyond
the physical outer diagonal. The original cost comparison will use only
the original feasible states. All three derivatives are proved from the
circle equation on this whole interval.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.ShortMixedZero.SmallContact

open CommonQuarter CorePairGeometry Arithmetic

def e : ℝ := 9133/100000
def b (x : ℝ) : ℝ := 1/2+(1/2+CoreAngleEndpoint.diagonal)*Real.sin x+
  (1/2-CoreAngleEndpoint.diagonal)*Real.cos x
def bd (x : ℝ) : ℝ := (1/2+CoreAngleEndpoint.diagonal)*Real.cos x+
  (CoreAngleEndpoint.diagonal-1/2)*Real.sin x
def bdd (x : ℝ) : ℝ := 1/2-b x
def Y (z : ℝ) : ℝ := Real.sqrt (Q0-(z+1/2)^2)
def radial (z : ℝ) : ℝ := -e*(Y z-1/2)+(88074/100000)*z
def fd (z : ℝ) : ℝ := 88074/100000+e*(z+1/2)/Y z
def fdd (z : ℝ) : ℝ := e*Q0/(Y z)^3
def fddd (z : ℝ) : ℝ := 3*e*Q0*(z+1/2)/(Y z)^5

def H (x : ℝ) : ℝ := -x+28271/100000+radial (b x)+
  (62095/100000)*CoreAngleEndpoint.diagonal
def Hd (x : ℝ) : ℝ := -1+fd (b x)*bd x
def Hdd (x : ℝ) : ℝ := fdd (b x)*(bd x)^2+fd (b x)*bdd x
def Hddd (x : ℝ) : ℝ :=
  bd x*(fddd (b x)*(bd x)^2+3*fdd (b x)*bdd x-fd (b x))

lemma b_hasDerivAt (x : ℝ) : HasDerivAt b (bd x) x := by
  convert (((Real.hasDerivAt_sin x).const_mul (1/2+CoreAngleEndpoint.diagonal)).const_add (1/2)).add
    ((Real.hasDerivAt_cos x).const_mul (1/2-CoreAngleEndpoint.diagonal)) using 1
  · funext t
    simp only [b,Pi.add_apply]
  · dsimp only [bd]
    ring

lemma bd_hasDerivAt (x : ℝ) : HasDerivAt bd (bdd x) x := by
  convert ((Real.hasDerivAt_cos x).const_mul (1/2+CoreAngleEndpoint.diagonal)).add
    ((Real.hasDerivAt_sin x).const_mul (CoreAngleEndpoint.diagonal-1/2)) using 1
  · funext t
    simp only [bd,Pi.add_apply]
  · dsimp only [bdd,b]
    ring

lemma bdd_hasDerivAt (x : ℝ) : HasDerivAt bdd (-bd x) x :=
  (b_hasDerivAt x).const_sub (1/2)

lemma bd_lower {x : ℝ} (hx : x∈Icc 0 smallCap) : (19/20:ℝ)<bd x := by
  have hcap : smallCap≤7/10 := by norm_num [smallCap]
  have ht := positive_trig ⟨hx.1,hx.2.trans hcap⟩
  have hc := Real.one_sub_sq_div_two_le_cos (x := x)
  have hx2 := pow_le_pow_left₀ hx.1 hx.2 2
  have hcos : (9/10:ℝ)<Real.cos x := by norm_num [smallCap] at hx2; linarith
  have hd := CoreAngleEndpoint.diagonal_bounds
  have hsin := mul_nonneg (show 0≤CoreAngleEndpoint.diagonal-1/2 by linarith [hd.1]) ht.2.2.1
  have hprimary := mul_lt_mul_of_pos_left hcos
    (show 0<1/2+CoreAngleEndpoint.diagonal by linarith [hd.1])
  dsimp [bd]
  linarith [hd.1]

lemma bd_square_upper (x : ℝ) : (bd x)^2<(53/50:ℝ)^2+(59/1000)^2 := by
  have hid : (bd x)^2+
      ((1/2+CoreAngleEndpoint.diagonal)*Real.sin x-
        (CoreAngleEndpoint.diagonal-1/2)*Real.cos x)^2=
      (1/2+CoreAngleEndpoint.diagonal)^2+(CoreAngleEndpoint.diagonal-1/2)^2 := by
    dsimp [bd]
    linear_combination ((1/2+CoreAngleEndpoint.diagonal)^2+
      (CoreAngleEndpoint.diagonal-1/2)^2)*(Real.sin_sq_add_cos_sq x)
  have hs := sq_nonneg ((1/2+CoreAngleEndpoint.diagonal)*Real.sin x-
    (CoreAngleEndpoint.diagonal-1/2)*Real.cos x)
  have hd := CoreAngleEndpoint.diagonal_bounds
  nlinarith [hd.1,hd.2]

lemma b_monotone : MonotoneOn b (Icc 0 smallCap) :=
  monoOn_of_hasDeriv_nonneg (fun x _ => (b_hasDerivAt x).continuousAt.continuousWithinAt)
    (fun x _ => b_hasDerivAt x) (fun x hx => by linarith [bd_lower (Ioo_subset_Icc_self hx)])

lemma endpoint_trig : Real.sin smallCap<(85463/200000:ℝ) ∧
    (904103/1000000:ℝ)<Real.cos smallCap := by
  have hs := sin_upper_five (x := smallCap) (by norm_num [smallCap])
  have hc := cos_lower_six (x := smallCap) (by norm_num [smallCap])
  simp only [smallCap] at hs hc ⊢
  norm_num at hs hc
  exact ⟨by linarith,by linarith⟩

lemma endpoint_b : (449609/500000:ℝ)<b smallCap ∧ b smallCap<8993/10000 := by
  have hd := CoreAngleEndpoint.diagonal_bounds
  have ht := smallCap_point_trig
  have hu := endpoint_trig
  have hsl := mul_le_mul_of_nonneg_left ht.1.le
    (show 0≤1/2+CoreAngleEndpoint.diagonal by linarith [hd.1])
  have hsu := mul_le_mul_of_nonneg_left hu.1.le
    (show 0≤1/2+CoreAngleEndpoint.diagonal by linarith [hd.1])
  have hcl := mul_le_mul_of_nonpos_left ht.2.le
    (show 1/2-CoreAngleEndpoint.diagonal≤0 by linarith [hd.1])
  have hcu := mul_le_mul_of_nonpos_left hu.2.le
    (show 1/2-CoreAngleEndpoint.diagonal≤0 by linarith [hd.1])
  dsimp [b]
  constructor <;> nlinarith [hd.1,hd.2]

lemma b_bounds {x : ℝ} (hx : x∈Icc 0 smallCap) :
    (11/25:ℝ)<b x ∧ b x<8993/10000 := by
  have hlo := b_monotone (by norm_num [smallCap]) hx hx.1
  have hhi := b_monotone hx (by norm_num [smallCap]) hx.2
  have hd := CoreAngleEndpoint.diagonal_bounds
  have h0 : b 0=1/2+(1/2-CoreAngleEndpoint.diagonal) := by
    simp only [b,Real.sin_zero,Real.cos_zero,mul_zero,mul_one,add_zero]
  rw [h0] at hlo
  exact ⟨by linarith [hd.2],hhi.trans_lt endpoint_b.2⟩

lemma bdd_upper {x : ℝ} (hx : x∈Icc 0 smallCap) : bdd x<(59/1000:ℝ) := by
  have hlo := b_monotone (by norm_num [smallCap]) hx hx.1
  have hd := CoreAngleEndpoint.diagonal_bounds
  have h0 : b 0=1/2+(1/2-CoreAngleEndpoint.diagonal) := by
    simp only [b,Real.sin_zero,Real.cos_zero,mul_zero,mul_one,add_zero]
  rw [h0] at hlo
  dsimp only [bdd]
  linarith [hd.2]

lemma radicand_pos {z : ℝ} (hz : z∈Icc (11/25) (8993/10000)) :
    0<Q0-(z+1/2)^2 := by
  have hs := pow_le_pow_left₀ (show 0≤z+1/2 by linarith [hz.1])
    (show z+1/2≤13993/10000 by linarith [hz.2]) 2
  norm_num [Q0]
  nlinarith

lemma Y_pos {z : ℝ} (hz : z∈Icc (11/25) (8993/10000)) : 0<Y z :=
  Real.sqrt_pos.mpr (radicand_pos hz)

lemma Y_sq {z : ℝ} (hz : z∈Icc (11/25) (8993/10000)) :
    (Y z)^2+(z+1/2)^2=Q0 := by
  have hh := Real.sq_sqrt (radicand_pos hz).le
  dsimp [Y]
  linarith

lemma Y_lower {z : ℝ} (hz : z∈Icc (11/25) (8993/10000)) : (1399/1000:ℝ)<Y z := by
  have hs := Y_sq hz
  have hp := Y_pos hz
  have hz2 := pow_le_pow_left₀ (show 0≤z+1/2 by linarith [hz.1])
    (show z+1/2≤13993/10000 by linarith [hz.2]) 2
  norm_num [Q0] at hs
  nlinarith

lemma Y_hasDerivAt {z : ℝ} (hz : z∈Icc (11/25) (8993/10000)) :
    HasDerivAt Y (-(z+1/2)/Y z) z := by
  have hh := ((hasDerivAt_const z Q0).sub
    (((hasDerivAt_id' z).add_const (1/2)).pow 2)).sqrt (radicand_pos hz).ne'
  have hn := (Y_pos hz).ne'
  convert hh using 1
  · funext t
    simp only [Y,Pi.sub_apply,Pi.pow_apply]
  · have hyy : Real.sqrt (Q0-(z+1/2)^2)=Y z := rfl
    simp only [Pi.sub_apply,Pi.pow_apply,hyy,Nat.cast_ofNat]
    field_simp
    ring

lemma radial_hasDerivAt {z : ℝ} (hz : z∈Icc (11/25) (8993/10000)) :
    HasDerivAt radial (fd z) z := by
  convert (((Y_hasDerivAt hz).sub_const (1/2)).const_mul (-e)).add
    ((hasDerivAt_id' z).const_mul (88074/100000:ℝ)) using 1
  · funext t
    simp only [radial,Pi.add_apply]
  · dsimp only [fd]
    ring

lemma fd_hasDerivAt {z : ℝ} (hz : z∈Icc (11/25) (8993/10000)) :
    HasDerivAt fd (fdd z) z := by
  have hn := (Y_pos hz).ne'
  have hh := ((((hasDerivAt_id z).add_const (1/2)).const_mul e).div
    (Y_hasDerivAt hz) hn).const_add (88074/100000:ℝ)
  convert hh using 1
  · rfl
  · dsimp [fd,fdd,e]
    field_simp [hn]
    nlinarith only [Y_sq hz]

lemma fdd_hasDerivAt {z : ℝ} (hz : z∈Icc (11/25) (8993/10000)) :
    HasDerivAt fdd (fddd z) z := by
  have hn := (Y_pos hz).ne'
  have hh := (hasDerivAt_const z (e*Q0)).div
    ((Y_hasDerivAt hz).pow 3) (pow_ne_zero 3 hn)
  convert hh using 1
  · rfl
  · dsimp [fdd,fddd]
    field_simp [hn]
    ring

lemma curve_domain {x : ℝ} (hx : x∈Icc 0 smallCap) : b x∈Icc (11/25) (8993/10000) :=
  ⟨(b_bounds hx).1.le,(b_bounds hx).2.le⟩

lemma H_hasDerivAt {x : ℝ} (hx : x∈Icc 0 smallCap) : HasDerivAt H (Hd x) x := by
  have hf := (radial_hasDerivAt (curve_domain hx)).comp x (b_hasDerivAt x)
  convert ((((hasDerivAt_id' x).neg).add_const (28271/100000:ℝ)).add hf).add_const
    ((62095/100000)*CoreAngleEndpoint.diagonal) using 1
  · funext t
    simp only [H,Pi.add_apply,Pi.neg_apply,Function.comp_apply]
  · rfl

lemma Hd_hasDerivAt {x : ℝ} (hx : x∈Icc 0 smallCap) : HasDerivAt Hd (Hdd x) x := by
  have hf := (fd_hasDerivAt (curve_domain hx)).comp x (b_hasDerivAt x)
  convert (hf.mul (bd_hasDerivAt x)).const_add (-1) using 1
  · funext t
    simp only [Hd,Pi.mul_apply,Function.comp_apply]
  · simp only [Function.comp_apply]
    dsimp only [Hdd]
    ring

lemma Hdd_hasDerivAt {x : ℝ} (hx : x∈Icc 0 smallCap) : HasDerivAt Hdd (Hddd x) x := by
  have hf₂ := (fdd_hasDerivAt (curve_domain hx)).comp x (b_hasDerivAt x)
  have hf₁ := (fd_hasDerivAt (curve_domain hx)).comp x (b_hasDerivAt x)
  convert (hf₂.mul ((bd_hasDerivAt x).pow 2)).add (hf₁.mul (bdd_hasDerivAt x)) using 1
  · funext t
    simp only [Hdd,Pi.add_apply,Pi.mul_apply,Pi.pow_apply,Function.comp_apply]
  · simp only [Function.comp_apply,Pi.pow_apply,Nat.cast_ofNat]
    dsimp only [Hddd]
    ring

lemma radial_derivative_bounds {z : ℝ} (hz : z∈Icc (11/25) (8993/10000)) :
    (22/25:ℝ)<fd z ∧ 0<fdd z ∧ fdd z<27/200 ∧
      0<fddd z ∧ fddd z<289/1000 := by
  have hy := Y_lower hz
  have hyp := Y_pos hz
  have hy3 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1399/1000) hy.le 3
  have hy5 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1399/1000) hy.le 5
  have he : 0<e := by norm_num [e]
  have hz0 : 0<z+1/2 := by linarith [hz.1]
  refine ⟨?_,?_,?_,?_,?_⟩
  · have hh := div_pos (mul_pos he hz0) hyp
    dsimp [fd]
    linarith
  · exact div_pos (mul_pos he (by norm_num [Q0])) (pow_pos hyp 3)
  · rw [fdd,div_lt_iff₀ (pow_pos hyp 3)]
    norm_num [e,Q0] at hy3 ⊢
    nlinarith
  · exact div_pos (by dsimp [e,Q0]; positivity) (pow_pos hyp 5)
  · rw [fddd,div_lt_iff₀ (pow_pos hyp 5)]
    norm_num [e,Q0] at hy5 ⊢
    nlinarith [hz.2]

/-- The entire contact's third derivative is strictly below `-1/2`.
The estimate comes from geometric radical bounds, not a derivative
envelope supplied to the theorem. -/
lemma Hddd_negative {x : ℝ} (hx : x∈Icc 0 smallCap) : Hddd x< -(1/2:ℝ) := by
  have hb := bd_lower hx
  have hb2 := bd_square_upper x
  have hbdd := bdd_upper hx
  have hf := radial_derivative_bounds (curve_domain hx)
  have hfirst := mul_le_mul_of_nonneg_left hb2.le hf.2.2.2.1.le
  have hfirst' := mul_lt_mul_of_pos_right hf.2.2.2.2
    (by norm_num : (0:ℝ)<(53/50)^2+(59/1000)^2)
  have hsecond := mul_lt_mul_of_pos_left hbdd hf.2.1
  have hsecond' := mul_lt_mul_of_pos_right hf.2.2.1 (by norm_num : (0:ℝ)<59/1000)
  have hbracket : fddd (b x)*(bd x)^2+3*fdd (b x)*bdd x-fd (b x)< -(53/100:ℝ) := by
    nlinarith [hf.1]
  have hprod := mul_lt_mul_of_pos_left hbracket (by linarith : 0<bd x)
  dsimp [Hddd]
  nlinarith

end SquaresInCircles.Eight.ShortMixedZero.SmallContact
end
end
end

section
/-!
## Strict decrease of the last mixed negative contact

The third derivative of the exact contact is below `-1/2`. At the single reference angle `.14`,
its first derivative is below `-.0055` and its second derivative has absolute value below `.005`
(`reference_derivatives`). Strong concavity therefore makes the first derivative negative
everywhere (`Hd_negative`). One final contact value supplies the strict `.898` cost bound
(`H_endpoint`, `H_lower`).

The original separator pays the target-core slack during the comparison to the contact
(`original_cost_lower`), so both squares stay in place.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.ShortMixedZero.SmallContact

open CommonQuarter CorePairGeometry Arithmetic

def reference : ℝ := 7/50

lemma reference_trig :
    (1395431146/10000000000:ℝ)<Real.sin reference ∧
      Real.sin reference<1395431150/10000000000 ∧
      (9902159962/10000000000:ℝ)<Real.cos reference ∧
      Real.cos reference<9902159963/10000000000 := by
  have hs := sin_lower_seven (x := reference) (by norm_num [reference])
  have hsU := sin_upper_five (x := reference) (by norm_num [reference])
  have hc := cos_lower_six (x := reference) (by norm_num [reference])
  have hcU := cos_le_cos8 (x := reference) (by norm_num [reference])
  simp only [reference] at hs hsU hc hcU ⊢
  norm_num [cos8] at hs hsU hc hcU
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

lemma reference_coordinates :
    (5894167/10000000:ℝ)<b reference ∧ b reference<5894168/10000000 ∧
      (10567876/10000000:ℝ)<bd reference ∧ bd reference<10567878/10000000 := by
  have ht := reference_trig
  have hd := CoreAngleEndpoint.diagonal_bounds
  have hu : 0≤1/2+CoreAngleEndpoint.diagonal := by linarith [hd.1]
  have hv : 0≤CoreAngleEndpoint.diagonal-1/2 := by linarith [hd.1]
  have hsL := mul_le_mul_of_nonneg_left ht.1.le hu
  have hsU := mul_le_mul_of_nonneg_left ht.2.1.le hu
  have hcL := mul_le_mul_of_nonneg_left ht.2.2.1.le hv
  have hcU := mul_le_mul_of_nonneg_left ht.2.2.2.le hv
  have hcL' := mul_le_mul_of_nonneg_left ht.2.2.1.le hu
  have hcU' := mul_le_mul_of_nonneg_left ht.2.2.2.le hu
  have hsL' := mul_le_mul_of_nonneg_left ht.1.le hv
  have hsU' := mul_le_mul_of_nonneg_left ht.2.1.le hv
  dsimp [b,bd]
  refine ⟨?_,?_,?_,?_⟩ <;> nlinarith [hd.1,hd.2]

lemma reference_root : (16518992/10000000:ℝ)<Y (b reference) ∧
    Y (b reference)<16518994/10000000 := by
  have hr : reference∈Icc 0 smallCap := by norm_num [reference,smallCap]
  have hp := Y_pos (curve_domain hr)
  have hs := Y_sq (curve_domain hr)
  have hb := reference_coordinates
  have hbL := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤5894167/10000000+1/2)
    (show (5894167/10000000:ℝ)+1/2≤b reference+1/2 by linarith [hb.1]) 2
  have hbU := pow_le_pow_left₀ (show 0≤b reference+1/2 by linarith [hb.1])
    (show b reference+1/2≤(5894168/10000000:ℝ)+1/2 by linarith [hb.2.1]) 2
  norm_num [Q0] at hs
  constructor <;> nlinarith

lemma reference_radial_derivatives :
    (9409714/10000000:ℝ)<fd (b reference) ∧ fd (b reference)<9409717/10000000 ∧
      (793342/10000000:ℝ)<fdd (b reference) ∧ fdd (b reference)<793345/10000000 := by
  have hb := reference_coordinates
  have hy := reference_root
  have hypos : 0<Y (b reference) := by linarith [hy.1]
  have hy3L := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤16518992/10000000) hy.1.le 3
  have hy3U := pow_le_pow_left₀ hypos.le hy.2.le 3
  refine ⟨?_,?_,?_,?_⟩
  · have hh : (9409714/10000000:ℝ)-88074/100000<e*(b reference+1/2)/Y (b reference) := by
      apply (lt_div_iff₀ hypos).2
      norm_num [e]
      nlinarith [hb.1,hy.2]
    dsimp [fd]
    linarith
  · have hh : e*(b reference+1/2)/Y (b reference)<(9409717/10000000:ℝ)-88074/100000 := by
      apply (div_lt_iff₀ hypos).2
      norm_num [e]
      nlinarith [hb.2.1,hy.1]
    dsimp [fd]
    linarith
  · rw [fdd,lt_div_iff₀ (pow_pos hypos 3)]
    norm_num [e,Q0] at hy3U ⊢
    nlinarith
  · rw [fdd,div_lt_iff₀ (pow_pos hypos 3)]
    norm_num [e,Q0] at hy3L ⊢
    nlinarith

lemma reference_derivatives : Hd reference< -(11/2000:ℝ) ∧ |Hdd reference|<(1/200:ℝ) := by
  have hb := reference_coordinates
  have hf := reference_radial_derivatives
  have hbd0 : 0≤bd reference := by linarith [hb.2.2.1]
  have hfd0 : 0≤fd (b reference) := by linarith [hf.1]
  have hfdd0 : 0≤fdd (b reference) := by linarith [hf.2.2.1]
  have hprod := mul_le_mul hf.2.1.le hb.2.2.2.le hbd0 (by norm_num)
  have hsqL := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤10567876/10000000) hb.2.2.1.le 2
  have hsqU := pow_le_pow_left₀ hbd0 hb.2.2.2.le 2
  have hposL := mul_le_mul hf.2.2.1.le hsqL (by positivity) hfdd0
  have hposU := mul_le_mul hf.2.2.2.le hsqU (sq_nonneg (bd reference)) (by norm_num)
  have hbL : (5894167/10000000:ℝ)-1/2≤b reference-1/2 := by linarith [hb.1]
  have hbU : b reference-1/2≤(5894168/10000000:ℝ)-1/2 := by linarith [hb.2.1]
  have hnegL := mul_le_mul hf.1.le hbL (by norm_num) hfd0
  have hnegU := mul_le_mul hf.2.1.le hbU (by linarith [hb.1]) (by norm_num)
  constructor
  · dsimp [Hd]
    nlinarith
  · rw [abs_lt]
    dsimp [Hdd,bdd]
    constructor <;> nlinarith

/-- One reference point and the negative third derivative make the exact first derivative
strictly negative on the whole contact. -/
lemma Hd_negative {x : ℝ} (hx : x∈Icc 0 smallCap) : Hd x<0 := by
  have hr : reference∈Icc 0 smallCap := by norm_num [reference,smallCap]
  have hder := reference_derivatives
  have hval : (-Hdd reference)^2<2*(1/2:ℝ)*(-Hd reference) := by
    have hab := abs_lt.mp hder.2
    have hs : (Hdd reference)^2<(1/200:ℝ)^2 := by nlinarith [hab.1,hab.2]
    nlinarith [hder.1]
  have hh := positive_of_curvature (κ := (1/2:ℝ)) (by norm_num) hx hr
    (f := fun z => -Hd z) (d := fun z => -Hdd z) (dd := fun z => -Hddd z)
    (fun z hz => (Hd_hasDerivAt hz).neg)
    (fun z hz => (Hdd_hasDerivAt hz).neg)
    (fun z hz => by linarith [Hddd_negative hz]) hval
  linarith

lemma H_antitone : AntitoneOn H (Icc 0 smallCap) :=
  antiOn_of_hasDeriv_nonpos (fun _ hx => (H_hasDerivAt hx).continuousAt.continuousWithinAt)
    (fun _ hx => H_hasDerivAt (Ioo_subset_Icc_self hx))
    (fun _ hx => (Hd_negative (Ioo_subset_Icc_self hx)).le)

lemma endpoint_root_upper : Y (b smallCap)<(69961/50000:ℝ) := by
  have hx : smallCap∈Icc 0 smallCap := by norm_num [smallCap]
  have hp := Y_pos (curve_domain hx)
  have hs := Y_sq (curve_domain hx)
  have hb := endpoint_b.1
  have hb2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤449609/500000+1/2)
    (show (449609/500000:ℝ)+1/2≤b smallCap+1/2 by linarith) 2
  norm_num [Q0] at hs
  nlinarith

lemma H_endpoint : (449/500:ℝ)<H smallCap := by
  have hy := endpoint_root_upper
  have hb := endpoint_b.1
  have hc := CoreAngleEndpoint.diagonal_bounds.1
  have hsc : smallCap=5519/12500 := rfl
  have hH : H smallCap=-smallCap+28271/100000+
      (-(9133/100000)*(Y (b smallCap)-1/2)+(88074/100000)*b smallCap)+
        (62095/100000)*CoreAngleEndpoint.diagonal := rfl
  rw [hH]
  linarith

lemma H_lower {x : ℝ} (hx : x∈Icc 0 smallCap) : (449/500:ℝ)<H x :=
  H_endpoint.trans_le (H_antitone hx (by norm_num [smallCap]) hx.2)

/-- The separator pays the original target-core slack while the source outer circle supplies
its exact diagonal-contact value. -/
theorem original_cost_lower {a z A B x : ℝ} (hs : OuterState a z)
    (ht : CoreState A B) (hx : x∈Icc 0 (7/10))
    (hm : (1+Real.sin x+Real.cos x)/2≤z-A*Real.sin x+B*Real.cos x) :
    H x≤-x+28271/100000-e*a+(88074/100000)*z+(62095/100000)*B := by
  have hcut := negative_angle_cut hs ht hx hm
  have hxc : x∈Icc 0 smallCap := ⟨hx.1,hcut.le⟩
  have htr := positive_trig hx
  have hA := core_primary_lower ht
  have hB := (CoreAngleEndpoint.state_bounds ht).2.2.2.2
  have hprim := mul_le_mul_of_nonneg_right hA htr.2.2.1
  have hslack : b x+(CoreAngleEndpoint.diagonal-B)*Real.cos x≤z := by
    dsimp [b]
    linarith
  have hextra := mul_nonneg (sub_nonneg.mpr hB) (show 0≤Real.cos x by linarith [htr.1])
  have hbz : b x≤z := by linarith
  have hcoord := curve_domain hxc
  have hy := Y_pos hcoord
  have hy2 := Y_sq hcoord
  have hroot : a≤Y (b x)-1/2 := by
    have hb2 := pow_le_pow_left₀ (show 0≤b x+1/2 by linarith [hcoord.1])
      (show b x+1/2≤z+1/2 by linarith) 2
    have ha : 0≤a+1/2 := by linarith [hs.1,hs.2.1]
    nlinarith [hs.2.2]
  have hcoef : (62095/100000:ℝ)≤(88074/100000)*Real.cos x := by linarith [htr.1]
  have hpaid := mul_nonneg (sub_nonneg.mpr hcoef) (sub_nonneg.mpr hB)
  have hmargin := mul_le_mul_of_nonneg_left hslack (by norm_num : (0:ℝ)≤88074/100000)
  have hsource := mul_le_mul_of_nonneg_left hroot (show 0≤e by norm_num [e])
  dsimp [H,radial]
  nlinarith

end SquaresInCircles.Eight.ShortMixedZero.SmallContact

namespace SquaresInCircles.Eight.ShortMixedZero

open CommonQuarter CorePairGeometry

theorem opposite_outer_negative_third {a b A B x : ℝ}
    (hs : OuterState a b) (ht : CoreState A B) (hx : x∈Icc 0 (7/10))
    (hm : (1+Real.sin x+Real.cos x)/2≤b-A*Real.sin x+B*Real.cos x) :
    (449/500:ℝ)< -x+c 3-p 3*a+q 3*b+g 3*B := by
  have hcut := negative_angle_cut hs ht hx hm
  have hh := (SmallContact.H_lower ⟨hx.1,hcut.le⟩).trans_le
    (SmallContact.original_cost_lower hs ht hx hm)
  simpa [c,p,q,g,SmallContact.e] using hh

/-- All six outer-source opposite-sign negative-angle families, each from the original core and
outer geometry. -/
theorem opposite_outer_negative (r : Row) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : CoreState A B) (hx : x∈Icc 0 (7/10))
    (hm : (1+Real.sin x+Real.cos x)/2≤b-A*Real.sin x+B*Real.cos x) :
    (449/500:ℝ)< -x+c r-p r*a+q r*b+g r*B := by
  by_cases h0 : r=0
  · subst r
    exact opposite_outer_negative_first hs ht hx hm
  by_cases h3 : r=3
  · subst r
    exact opposite_outer_negative_third hs ht hx hm
  exact opposite_outer_negative_secant r h0 h3 hs ht hx hm

end SquaresInCircles.Eight.ShortMixedZero
end
end
end

section
@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.ShortMixedZero

open CommonQuarter CorePairGeometry WordProblems QuarterWordGeometry

def outerRow (i : Vertex) : Row := if i=0 then 0 else if i=1 then 2 else 4
def coreRow (i : Vertex) : Row := if i=0 then 1 else if i=1 then 3 else 5

lemma zero_role (i : Vertex) (hi : wrongWord .short i=0) : i=0 ∨ i=1 ∨ i=3 := by
  revert hi
  fin_cases i <;> decide

lemma outer_role_cost (i : Vertex) (hi : i=0 ∨ i=1 ∨ i=3)
    (kind : RadialKind) (hk : kind≠.outer) (a b A B φ : ℝ) :
    φ+wrongValue .short i .outer true a b-wrongValue .short (next i) kind false A B=
      φ+c (outerRow i)-p (outerRow i)*a+q (outerRow i)*b+g (outerRow i)*B := by
  rcases hi with rfl | rfl | rfl <;>
    norm_num [outerRow,wrongValue,shortCoefficients,radialIndex,hk,signIndex,sign,next,c,p,q,g] <;> ring

lemma core_role_reversed_cost (i : Vertex) (hi : i=0 ∨ i=1 ∨ i=3)
    (kind : RadialKind) (hk : kind≠.outer) (a b A B φ : ℝ) :
    φ+wrongValue .short i kind true a b-wrongValue .short (next i) .outer false A B=
      φ+c (coreRow i)-p (coreRow i)*A+q (coreRow i)*B+g (coreRow i)*b := by
  rcases hi with rfl | rfl | rfl <;>
    norm_num [coreRow,wrongValue,shortCoefficients,radialIndex,hk,signIndex,sign,next,c,p,q,g] <;> ring

theorem opposite_outer_signed (r : Row) {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : CoreState A B) (hφ : |φ|≤7/10)
    (hm : 0≤forwardMargin 0 a b A B 1 (-1) φ) :
    (449/500:ℝ)<φ+c r-p r*a+q r*b+g r*B := by
  have hm' : pairWidth φ≤b+A*Real.sin φ+B*Real.cos φ := by
    norm_num [forwardMargin] at hm
    linarith
  by_cases hp : 0≤φ
  · have hx : φ∈Icc 0 (7/10) := ⟨hp,(abs_le.mp hφ).2⟩
    have hw := signed_width hφ
    rw [abs_of_nonneg (positive_trig hx).2.2.1] at hw
    apply opposite_outer_positive r hs ht hx
    rw [hw] at hm'
    linarith
  · have hx : -φ∈Icc 0 (7/10) := ⟨by linarith,by linarith [(abs_le.mp hφ).1]⟩
    have hsin : Real.sin φ≤0 := by
      have hh := (positive_trig hx).2.2.1
      simpa only [Real.sin_neg,neg_nonneg] using hh
    have hw := signed_width hφ
    rw [abs_of_nonpos hsin] at hw
    have hh := opposite_outer_negative r hs ht hx (by
      rw [hw] at hm'
      rw [Real.sin_neg,Real.cos_neg]
      linarith)
    simpa only [neg_neg] using hh

/-- Original source-secondary outer/core owner, with the exact fixed
short-word role labels at both ends. -/
theorem original_outer_secondary (i : Vertex) (hi : i=0 ∨ i=1 ∨ i=3)
    (kind : RadialKind) (hk : kind≠.outer) {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : CoreState A B) (hφ : |φ|≤7/10)
    (hm : 0≤forwardMargin 0 a b A B 1 (-1) φ) :
    (449/500:ℝ)<φ+wrongValue .short i .outer true a b-
      wrongValue .short (next i) kind false A B := by
  rw [outer_role_cost i hi kind hk]
  exact opposite_outer_signed (outerRow i) hs ht hφ hm

/-- Original target-secondary core/outer owner. Reflection/reversal
only changes the presentation of its original projection and labels. -/
theorem original_core_target_secondary (i : Vertex) (hi : i=0 ∨ i=1 ∨ i=3)
    (kind : RadialKind) (hk : kind≠.outer) {a b A B φ : ℝ}
    (hs : CoreState a b) (ht : OuterState A B) (hφ : |φ|≤7/10)
    (hm : 0≤forwardMargin 2 a b A B 1 (-1) φ) :
    (449/500:ℝ)<φ+wrongValue .short i kind true a b-
      wrongValue .short (next i) .outer false A B := by
  have hrev : 0≤forwardMargin 0 A B a b 1 (-1) φ := by
    simpa [forwardMargin,add_comm,add_left_comm,add_assoc] using hm
  rw [core_role_reversed_cost i hi kind hk]
  exact opposite_outer_signed (coreRow i) ht hs hφ hrev

end SquaresInCircles.Eight.ShortMixedZero
end
end
end

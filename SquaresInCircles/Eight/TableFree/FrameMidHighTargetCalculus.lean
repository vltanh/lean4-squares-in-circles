module

public import SquaresInCircles.Eight.TableFree.FrameDiagonalSupport
public import SquaresInCircles.Eight.TableFree.FrameMidHighConstantScalars

/-!
# Whole-interval curvature of the target-high circular support

The exact norm has a positive energy and a squared discriminant.  Its
universal lower curvature bound proves concavity before the quarter turn;
after the quarter turn its actual derivative is bounded directly.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameMidHighTargetCalculus
open FramePair FramePairCalculus FrameDiagonalArc FrameDiagonalLabels

def Allowed (l : ℝ) : Prop := l=7/20 ∨ l=2/5
def energyA (l : ℝ) : ℝ := u^2+v^2+2*l^2
def energyB (j : Bool) (l : ℝ) : ℝ := -2*l*(sign j*u+v)
def energyC (j : Bool) (l : ℝ) : ℝ := 2*l*(sign j*u-v)
def N (j : Bool) (l x : ℝ) : ℝ := CircularNorm.norm (energyA l) (energyB j l) (energyC j l) x
def N1 (j : Bool) (l x : ℝ) : ℝ := CircularNorm.d1 (energyA l) (energyB j l) (energyC j l) x
def N2 (j : Bool) (l x : ℝ) : ℝ := CircularNorm.d2 (energyA l) (energyB j l) (energyC j l) x
def K (i j : Bool) (l : ℝ) : ℝ :=
  9/100+l+sign i*cM+sign j*u*R+(-sign i*k-l)*a1+sign i*(q-l)*b1
def F (i j : Bool) (l x : ℝ) : ℝ :=
  K i j l+x+(2*l-9/100)*Real.sin x-(9/100)*Real.cos x-R*N j l x
def Fd (j : Bool) (l x : ℝ) : ℝ :=
  1+(2*l-9/100)*Real.cos x+(9/100)*Real.sin x-R*N1 j l x
def Fdd (j : Bool) (l x : ℝ) : ℝ :=
  -(2*l-9/100)*Real.sin x+(9/100)*Real.cos x-R*N2 j l x
def after (i j : Bool) (l x : ℝ) : ℝ :=
  K i j l+x+(2*l-9/100)*(Real.sin x-Real.cos x)-R*N j l x
def afterD (j : Bool) (l x : ℝ) : ℝ :=
  1+(2*l-9/100)*(Real.cos x+Real.sin x)-R*N1 j l x

theorem allowed_bounds {l : ℝ} (hl : Allowed l) : 0<l ∧ 9/100<2*l := by
  rcases hl with rfl | rfl <;> norm_num

theorem determinant (j : Bool) (l : ℝ) :
    (energyA l)^2-(energyB j l)^2-(energyC j l)^2=(u^2+v^2-2*l^2)^2 := by
  cases j <;> dsimp [energyA,energyB,energyC,sign] <;> ring

theorem coefficient_strict {j : Bool} {l : ℝ} (hl : Allowed l) :
    (energyB j l)^2+(energyC j l)^2<(energyA l)^2 := by
  have hh := determinant j l
  have hp : 0<(u^2+v^2-2*l^2)^2 := by
    rcases hl with rfl | rfl <;> norm_num [u,v]
  linarith

theorem energy_pos {j : Bool} {l : ℝ} (hl : Allowed l) (x : ℝ) :
    0<CircularNorm.energy (energyA l) (energyB j l) (energyC j l) x := by
  have hA : 0<energyA l := by dsimp [energyA,u,v]; positivity
  have hid : (energyB j l*Real.cos x+energyC j l*Real.sin x)^2+
      (energyB j l*Real.sin x-energyC j l*Real.cos x)^2=
        (energyB j l)^2+(energyC j l)^2 := by
    linear_combination ((energyB j l)^2+(energyC j l)^2)*(Real.sin_sq_add_cos_sq x)
  have hc := coefficient_strict (j := j) hl
  dsimp [CircularNorm.energy]
  nlinarith [sq_nonneg (energyB j l*Real.sin x-energyC j l*Real.cos x)]

theorem N_pos {j : Bool} {l : ℝ} (hl : Allowed l) (x : ℝ) : 0<N j l x :=
  CircularNorm.norm_pos (energy_pos hl x)

theorem N_sq {j : Bool} {l : ℝ} (hl : Allowed l) (x : ℝ) :
    (N j l x)^2=energyA l+energyB j l*Real.cos x+energyC j l*Real.sin x :=
  CircularNorm.norm_sq (energy_pos hl x).le

theorem N_circle {j : Bool} {l : ℝ} (hl : Allowed l) (x : ℝ) :
    (N j l x)^2=(sign j*u+l*(Real.sin x-Real.cos x))^2+
      (l*(Real.sin x+Real.cos x)-v)^2 := by
  rw [N_sq hl]
  cases j <;> dsimp [energyA,energyB,energyC,sign] <;>
    linear_combination -2*l^2*(Real.sin_sq_add_cos_sq x)

theorem N_literal {j : Bool} {l : ℝ} (hl : Allowed l) (x : ℝ) :
    N j l x=Real.sqrt ((sign j*u+l*(Real.sin x-Real.cos x))^2+
      (l*(Real.sin x+Real.cos x)-v)^2) := by
  rw [← N_circle hl x,Real.sqrt_sq (N_pos hl x).le]

theorem N_deriv {j : Bool} {l : ℝ} (hl : Allowed l) (x : ℝ) :
    HasDerivAt (N j l) (N1 j l x) x := CircularNorm.norm_hasDerivAt (energy_pos hl x)

theorem N1_deriv {j : Bool} {l : ℝ} (hl : Allowed l) (x : ℝ) :
    HasDerivAt (N1 j l) (N2 j l x) x := CircularNorm.d1_hasDerivAt (energy_pos hl x)

theorem norm_curvature {j : Bool} {l : ℝ} (hl : Allowed l) (x : ℝ) :
    -N j l x/4≤N2 j l x :=
  CircularNorm.curvature_lower (energy_pos hl x) (coefficient_strict hl).le

theorem N1_formula (j : Bool) (l x : ℝ) :
    N1 j l x=l*((sign j*u+v)*Real.sin x-(v-sign j*u)*Real.cos x)/N j l x := by
  dsimp [N1,N,CircularNorm.d1,CircularNorm.slope,energyB,energyC]
  ring

theorem F_deriv (i j : Bool) {l : ℝ} (hl : Allowed l) (x : ℝ) :
    HasDerivAt (F i j l) (Fd j l x) x := by
  convert ((((hasDerivAt_id x).const_add (K i j l)).add
    ((Real.hasDerivAt_sin x).const_mul (2*l-9/100))).sub
    ((Real.hasDerivAt_cos x).const_mul (9/100))).sub ((N_deriv hl x).const_mul R)
    using 1 <;> dsimp [F,Fd] <;> ring

theorem Fd_deriv (j : Bool) {l : ℝ} (hl : Allowed l) (x : ℝ) :
    HasDerivAt (Fd j l) (Fdd j l x) x := by
  convert ((((Real.hasDerivAt_cos x).const_mul (2*l-9/100)).const_add 1).add
    ((Real.hasDerivAt_sin x).const_mul (9/100))).sub ((N1_deriv hl x).const_mul R)
    using 1 <;> dsimp [Fd,Fdd] <;> ring

theorem after_deriv (i j : Bool) {l : ℝ} (hl : Allowed l) (x : ℝ) :
    HasDerivAt (after i j l) (afterD j l x) x := by
  convert (((hasDerivAt_id x).const_add (K i j l)).add
    (((Real.hasDerivAt_sin x).sub (Real.hasDerivAt_cos x)).const_mul (2*l-9/100))).
    sub ((N_deriv hl x).const_mul R) using 1 <;> dsimp [after,afterD] <;> ring

theorem signed_coefficients (j : Bool) : 0<sign j*u+v ∧ 0<v-sign j*u := by
  cases j <;> norm_num [sign,u,v]

theorem norm_monotone_first {j : Bool} {l a b : ℝ} (hl : Allowed l)
    (ha : 0≤a) (hb : b≤Real.pi/2)
    (hleft : 0≤(sign j*u+v)*Real.sin a-(v-sign j*u)*Real.cos a) :
    MonotoneOn (N j l) (Icc a b) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun x _ => (N_deriv hl x).continuousAt.continuousWithinAt
  · exact fun x _ => N_deriv hl x
  · intro x hx
    have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [Real.pi_pos] : -(Real.pi/2)≤a) (hx.2.le.trans hb) hx.1.le
    have hc := Real.cos_le_cos_of_nonneg_of_le_pi ha
      (by linarith [hx.2,hb,Real.pi_pos] : x≤Real.pi) hx.1.le
    have hsp := mul_le_mul_of_nonneg_left hs (signed_coefficients j).1.le
    have hcp := mul_le_mul_of_nonneg_left hc (signed_coefficients j).2.le
    rw [N1_formula]
    exact div_nonneg (mul_nonneg (allowed_bounds hl).1.le (by linarith)) (N_pos hl x).le

theorem norm_monotone_second {j : Bool} {l : ℝ} (hl : Allowed l) :
    MonotoneOn (N j l) (Icc (Real.pi/2) Real.pi) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun x _ => (N_deriv hl x).continuousAt.continuousWithinAt
  · exact fun x _ => N_deriv hl x
  · intro x hx
    have ht := second_signs (Ioo_subset_Icc_self hx)
    rw [N1_formula]
    apply div_nonneg _ (N_pos hl x).le
    apply mul_nonneg (allowed_bounds hl).1.le
    exact sub_nonneg.mpr ((mul_nonpos_of_nonneg_of_nonpos
      (signed_coefficients j).2.le ht.2).trans
      (mul_nonneg (signed_coefficients j).1.le ht.1))

theorem curvature_from_norm {j : Bool} {l a b n x : ℝ} (hl : Allowed l)
    (ha : 0≤a) (hb : b≤Real.pi/2) (hx : x∈Icc a b)
    (hn : N j l x≤n)
    (hreserve : (9/100)*Real.cos a+(139921407/50000000:ℝ)*n/4<
      (2*l-9/100)*Real.sin a) (hn0 : 0≤n) : Fdd j l x<0 := by
  have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [Real.pi_pos] : -(Real.pi/2)≤a) (hx.2.trans hb) hx.1
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi ha
    (by linarith [hx.2,hb,Real.pi_pos] : x≤Real.pi) hx.1
  have hsp := mul_le_mul_of_nonneg_left hs (by linarith [(allowed_bounds hl).2] : 0≤2*l-9/100)
  have hnp := mul_le_mul_of_nonneg_left (norm_curvature hl x) R_pos.le
  have hR := mul_le_mul R_precise.2.le hn (N_pos hl x).le
    (by norm_num : (0:ℝ)≤139921407/50000000)
  dsimp [Fdd]
  linarith

theorem positive_norm_bounds {x : ℝ} (hx : x∈Icc (7/10:ℝ) (93/100)) :
    N true (7/20) x<(17/100:ℝ) := by
  have htrigL := FrameMidHighConstantScalars.trigonometric_reference
    (show (0:ℝ)≤7/10 by norm_num)
  have htrigU := FrameMidHighConstantScalars.trigonometric_reference
    (show (0:ℝ)≤93/100 by norm_num)
  norm_num [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,
    SecondWord.ReferenceTrig.cos12,Arithmetic.cos10,Arithmetic.cos8] at htrigL htrigU
  have hm := norm_monotone_first (j := true) (l := (7/20:ℝ)) (Or.inl rfl)
    (a := (7/10:ℝ)) (b := (93/100:ℝ)) (by norm_num)
    (by linarith [FrameLowPair.pi_lower]) (by norm_num [sign,u,v]; nlinarith)
  have hh := hm hx ⟨by norm_num,le_rfl⟩ hx.2
  have hn := N_pos (j := true) (Or.inl (rfl : (7/20:ℝ)=7/20)) (93/100)
  have hs := N_sq (j := true) (Or.inl (rfl : (7/20:ℝ)=7/20)) (93/100)
  norm_num [energyA,energyB,energyC,sign,u,v] at hs
  have he : N true (7/20) (93/100)<(17/100:ℝ) := by nlinarith
  exact hh.trans_lt he

theorem negative_norm_bounds {x : ℝ} (hx : x∈Icc (6/5:ℝ) (71/50)) :
    N false (2/5) x<(3/10:ℝ) := by
  have htrigL := FrameMidHighConstantScalars.trigonometric_reference
    (show (0:ℝ)≤6/5 by norm_num)
  have htrigU := FrameMidHighConstantScalars.trigonometric_reference
    (show (0:ℝ)≤71/50 by norm_num)
  norm_num [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,
    SecondWord.ReferenceTrig.cos12,Arithmetic.cos10,Arithmetic.cos8] at htrigL htrigU
  have hm := norm_monotone_first (j := false) (l := (2/5:ℝ)) (Or.inr rfl)
    (a := (6/5:ℝ)) (b := (71/50:ℝ)) (by norm_num)
    (by linarith [FrameLowPair.pi_lower]) (by norm_num [sign,u,v]; nlinarith)
  have hh := hm hx ⟨by norm_num,le_rfl⟩ hx.2
  have hn := N_pos (j := false) (Or.inr (rfl : (2/5:ℝ)=2/5)) (71/50)
  have hs := N_sq (j := false) (Or.inr (rfl : (2/5:ℝ)=2/5)) (71/50)
  norm_num [energyA,energyB,energyC,sign,u,v] at hs
  have he : N false (2/5) (71/50)<(3/10:ℝ) := by nlinarith
  exact hh.trans_lt he

theorem opposite_norm_bounds {x : ℝ} (hx : x∈Icc (13/10:ℝ) (Real.pi/2)) :
    N true (2/5) x<(497/1000:ℝ) := by
  have ht := FrameMidHighConstantScalars.trigonometric_reference
    (show (0:ℝ)≤13/10 by norm_num)
  norm_num [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,
    SecondWord.ReferenceTrig.cos12,Arithmetic.cos10,Arithmetic.cos8] at ht
  have hm := norm_monotone_first (j := true) (l := (2/5:ℝ)) (Or.inr rfl)
    (a := (13/10:ℝ)) (b := Real.pi/2) (by norm_num) le_rfl
    (by norm_num [sign,u,v]; nlinarith)
  have hh := hm hx ⟨by linarith [FrameLowPair.pi_lower],le_rfl⟩ hx.2
  have hn := N_pos (j := true) (Or.inr (rfl : (2/5:ℝ)=2/5)) (Real.pi/2)
  have hs := N_sq (j := true) (Or.inr (rfl : (2/5:ℝ)=2/5)) (Real.pi/2)
  norm_num [energyA,energyB,energyC,sign,u,v] at hs
  have he : N true (2/5) (Real.pi/2)<(497/1000:ℝ) := by nlinarith
  exact hh.trans_lt he

theorem positive_concave :
    ConcaveOn ℝ (Icc (7/10:ℝ) (93/100)) (F true true (7/20)) := by
  apply concave_of_deriv2 (fun x _ => F_deriv true true (Or.inl rfl) x)
    (fun x _ => Fd_deriv true (Or.inl rfl) x)
  intro x hx
  have ht := FrameMidHighConstantScalars.trigonometric_reference
    (show (0:ℝ)≤7/10 by norm_num)
  norm_num [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,
    SecondWord.ReferenceTrig.cos12,Arithmetic.cos10,Arithmetic.cos8] at ht
  exact (curvature_from_norm (Or.inl rfl) (by norm_num)
    (by linarith [FrameLowPair.pi_lower]) hx (positive_norm_bounds hx).le
    (by nlinarith) (by norm_num)).le

theorem negative_concave :
    ConcaveOn ℝ (Icc (6/5:ℝ) (71/50)) (F false false (2/5)) := by
  apply concave_of_deriv2 (fun x _ => F_deriv false false (Or.inr rfl) x)
    (fun x _ => Fd_deriv false (Or.inr rfl) x)
  intro x hx
  have ht := FrameMidHighConstantScalars.trigonometric_reference
    (show (0:ℝ)≤6/5 by norm_num)
  norm_num [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,
    SecondWord.ReferenceTrig.cos12,Arithmetic.cos10,Arithmetic.cos8] at ht
  exact (curvature_from_norm (Or.inr rfl) (by norm_num)
    (by linarith [FrameLowPair.pi_lower]) hx (negative_norm_bounds hx).le
    (by nlinarith) (by norm_num)).le

theorem opposite_concave :
    ConcaveOn ℝ (Icc (13/10:ℝ) (Real.pi/2-1/50)) (F false true (2/5)) := by
  apply concave_of_deriv2 (fun x _ => F_deriv false true (Or.inr rfl) x)
    (fun x _ => Fd_deriv true (Or.inr rfl) x)
  intro x hx
  have ht := FrameMidHighConstantScalars.trigonometric_reference
    (show (0:ℝ)≤13/10 by norm_num)
  norm_num [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,
    SecondWord.ReferenceTrig.cos12,Arithmetic.cos10,Arithmetic.cos8] at ht
  exact (curvature_from_norm (Or.inr rfl) (by norm_num) (by linarith) hx
    (opposite_norm_bounds ⟨hx.1,by linarith [hx.2]⟩).le
    (by nlinarith) (by norm_num)).le

theorem after_norm_lower {x : ℝ} (hx : x∈Icc (Real.pi/2) (171/100:ℝ)) :
    (2479/5000:ℝ)<N true (2/5) x := by
  have hn := N_pos (j := true) (Or.inr (rfl : (2/5:ℝ)=2/5)) (Real.pi/2)
  have hs := N_sq (j := true) (Or.inr (rfl : (2/5:ℝ)=2/5)) (Real.pi/2)
  norm_num [energyA,energyB,energyC,sign,u,v] at hs
  have he : (2479/5000:ℝ)<N true (2/5) (Real.pi/2) := by nlinarith
  exact he.trans_le (norm_monotone_second (Or.inr rfl)
    ⟨le_rfl,by linarith [Real.pi_pos]⟩
    ⟨hx.1,by linarith [hx.2,FrameLowPair.pi_lower]⟩ hx.1)

theorem after_cos_lower {x : ℝ} (hx : x∈Icc (Real.pi/2) (171/100:ℝ)) :
    -(7/50:ℝ)<Real.cos x := by
  let e : ℝ := x-Real.pi/2
  have he : e∈Icc (0:ℝ) (7/50) :=
    ⟨by dsimp [e]; linarith [hx.1],by dsimp [e]; linarith [hx.2,Arithmetic.pi_hand_enclosure.1]⟩
  have hu : e<(7/50:ℝ) := by dsimp [e]; linarith [hx.2,Arithmetic.pi_hand_enclosure.1]
  have hs := Real.sin_le_self he.1
  have hxid : x=Real.pi/2+e := by dsimp [e]; ring
  rw [hxid,Real.cos_add]
  simp only [Real.cos_pi_div_two,Real.sin_pi_div_two,zero_mul,one_mul,zero_sub]
  linarith

theorem after_derivative_positive {x : ℝ}
    (hx : x∈Icc (Real.pi/2) (171/100:ℝ)) : 0<afterD true (2/5) x := by
  have ht := second_signs (show x∈Icc (Real.pi/2) Real.pi from
    ⟨hx.1,by linarith [hx.2,FrameLowPair.pi_lower]⟩)
  have hsum := FrameDiagonalGeometry.late_sum_lower hx
  have hc := after_cos_lower hx
  have hn := after_norm_lower hx
  let cap : ℝ := (2/5)*((v-u)*(7/50)+u+v)
  have hcap : 0≤cap := by norm_num [cap,u,v]
  have hnum : 0≤(2/5:ℝ)*((u+v)*Real.sin x-(v-u)*Real.cos x) := by
    have h1 := mul_nonneg (show 0≤u+v by norm_num [u,v]) ht.1
    have h2 := mul_nonpos_of_nonneg_of_nonpos (show 0≤v-u by norm_num [u,v]) ht.2
    nlinarith
  have hnumU : (2/5:ℝ)*((u+v)*Real.sin x-(v-u)*Real.cos x)≤cap := by
    dsimp [cap,u,v]
    nlinarith [Real.sin_le_one x]
  have hNpos := N_pos (j := true) (Or.inr (rfl : (2/5:ℝ)=2/5)) x
  have hderiv : N1 true (2/5) x≤cap/(2479/5000:ℝ) := by
    rw [N1_formula]
    simp only [sign,ite_true,one_mul]
    calc
      _ ≤ cap/N true (2/5) x := div_le_div_of_nonneg_right hnumU hNpos.le
      _ ≤ cap/(2479/5000:ℝ) := div_le_div_of_nonneg_left hcap (by norm_num) hn.le
  have hderiv0 : 0≤N1 true (2/5) x := by
    rw [N1_formula]
    simp only [sign,ite_true,one_mul]
    exact div_nonneg hnum hNpos.le
  have hprod := mul_le_mul R_precise.2.le hderiv hderiv0
    (by norm_num : (0:ℝ)≤139921407/50000000)
  have hreserve : (139921407/50000000:ℝ)*(cap/(2479/5000))<1+(71/100)*(17/20) := by
    norm_num [cap,u,v]
  dsimp [afterD]
  nlinarith

theorem after_monotone :
    MonotoneOn (after false true (2/5)) (Icc (Real.pi/2+1/50) (171/100:ℝ)) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun x _ => (after_deriv false true (Or.inr rfl) x).continuousAt.continuousWithinAt
  · exact fun x _ => after_deriv false true (Or.inr rfl) x
  · exact fun x hx => (after_derivative_positive
      ⟨by linarith [hx.1],hx.2.le⟩).le

end SquaresInCircles.Eight.TableFree.FrameMidHighTargetCalculus

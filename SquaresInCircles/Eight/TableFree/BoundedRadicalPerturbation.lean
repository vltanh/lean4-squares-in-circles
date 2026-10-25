module

public import SquaresInCircles.Eight.TableFree.ScalarRadicalTransfer

/-!
# Uniform algebraic perturbation of bounded radical rows

Uncompiled source. These estimates concern two actual real inputs, not
samples. The lower square-root bound is needed only on the comparison
radicand; the other radicand may be zero. The constants are deliberately
coarse so that the same proof can transfer several endpoint families.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree.BoundedRadicalPerturbation

theorem product_difference {a a' b b' A B ea eb : ℝ}
    (ha : |a|≤A) (hb : |b'|≤B)
    (hda : |a-a'|≤ea) (hdb : |b-b'|≤eb) :
    |a*b-a'*b'|≤A*eb+ea*B := by
  have hA : 0≤A := (abs_nonneg a).trans ha
  have hea : 0≤ea := (abs_nonneg (a-a')).trans hda
  calc
    |a*b-a'*b'|=|a*(b-b')+(a-a')*b'| := by congr 1; ring
    _≤|a*(b-b')|+|(a-a')*b'| := abs_add_le _ _
    _=|a| * |b-b'|+|a-a'| * |b'| := by rw [abs_mul,abs_mul]
    _≤A*eb+ea*B := add_le_add
      (mul_le_mul ha hdb (abs_nonneg _) hA)
      (mul_le_mul hda hb (abs_nonneg _) hea)

theorem square_difference {a a' A e : ℝ}
    (ha : |a|≤A) (ha' : |a'|≤A) (hda : |a-a'|≤e) :
    |a^2-a'^2|≤2*A*e := by
  have hh := product_difference ha ha' hda hda
  have heq : a^2-a'^2=a*a-a'*a' := by ring
  rw [heq]
  linarith

theorem sub_abs_bound (a b : ℝ) : |a-b|≤|a|+|b| := by
  simpa only [sub_eq_add_neg,abs_neg] using abs_add_le a (-b)

theorem constant_product_difference {a x y A e : ℝ}
    (ha : |a|≤A) (hxy : |x-y|≤e) : |a*x-a*y|≤A*e := by
  rw [← mul_sub,abs_mul]
  exact mul_le_mul ha hxy (abs_nonneg _) ((abs_nonneg _).trans ha)

theorem linear_difference {a b x x' y y' A B e : ℝ}
    (ha : |a|≤A) (hb : |b|≤B) (hx : |x-x'|≤e) (hy : |y-y'|≤e) :
    |(a*x+b*y)-(a*x'+b*y')|≤(A+B)*e := by
  have h1 := constant_product_difference ha hx
  have h2 := constant_product_difference hb hy
  have heq : (a*x+b*y)-(a*x'+b*y')=(a*x-a*x')+(b*y-b*y') := by ring
  rw [heq]
  have hh := abs_add_le (a*x-a*x') (b*y-b*y')
  linarith

theorem negative_pair_difference {a a' b b' s s' e : ℝ}
    (he : 0≤e)
    (ha : |a|≤2) (ha' : |a'|≤2) (hb : |b|≤2) (hb' : |b'|≤2)
    (hs' : |s'|≤1)
    (hda : |a-a'|≤3*e) (hdb : |b-b'|≤3*e) (hds : |s-s'|≤e) :
    |(a^2+b^2-2*a*b*s)-(a'^2+b'^2-2*a'*b'*s')|≤100*e := by
  have hA := square_difference ha ha' hda
  have hB := square_difference hb hb' hdb
  have hprod := product_difference ha hb' hda hdb
  have hab : |a*b|≤4 := by
    rw [abs_mul]
    nlinarith [mul_le_mul ha hb (abs_nonneg b) (by norm_num : (0:ℝ)≤2)]
  have hprod' : |a*b-a'*b'|≤12*e := by linarith
  have htriple := product_difference hab hs' hprod' hds
  have heq : (a^2+b^2-2*a*b*s)-(a'^2+b'^2-2*a'*b'*s')=
      ((a^2-a'^2)+(b^2-b'^2))-2*(a*b*s-a'*b'*s') := by ring
  rw [heq]
  have hsum := abs_add_le (a^2-a'^2) (b^2-b'^2)
  have hsub := sub_abs_bound ((a^2-a'^2)+(b^2-b'^2))
    (2*(a*b*s-a'*b'*s'))
  rw [abs_mul] at hsub
  norm_num at hsub
  linarith

theorem positive_pair_difference {a a' b b' e : ℝ}
    (he : 0≤e)
    (ha : |a|≤2) (ha' : |a'|≤2) (hb : |b|≤2) (hb' : |b'|≤2)
    (hda : |a-a'|≤3*e) (hdb : |b-b'|≤3*e) :
    |(a^2+b^2)-(a'^2+b'^2)|≤100*e := by
  have hA := square_difference ha ha' hda
  have hB := square_difference hb hb' hdb
  have heq : (a^2+b^2)-(a'^2+b'^2)=(a^2-a'^2)+(b^2-b'^2) := by ring
  rw [heq]
  have hsum := abs_add_le (a^2-a'^2) (b^2-b'^2)
  linarith

theorem sqrt_difference {v w : ℝ} (hv : 0≤v) (hw : 1/4≤w) :
    |Real.sqrt v-Real.sqrt w|≤2*|v-w| := by
  have hw0 : 0≤w := by linarith
  have hvq := Real.sq_sqrt hv
  have hwq := Real.sq_sqrt hw0
  have hv0 := Real.sqrt_nonneg v
  have hw0' := Real.sqrt_nonneg w
  have hwlo : 1/2≤Real.sqrt w := by nlinarith
  have hsum : 1/2≤Real.sqrt v+Real.sqrt w := by linarith
  have heq : (Real.sqrt v-Real.sqrt w)*(Real.sqrt v+Real.sqrt w)=v-w := by
    nlinarith
  have hab : |Real.sqrt v-Real.sqrt w| * (Real.sqrt v+Real.sqrt w)=|v-w| := by
    rw [← abs_of_nonneg (add_nonneg hv0 hw0'),← abs_mul,heq]
  have hh := mul_le_mul_of_nonneg_left hsum
    (abs_nonneg (Real.sqrt v-Real.sqrt w))
  rw [hab] at hh
  linarith

theorem sqrt_upper {v w e : ℝ}
    (hv : 0≤v) (hw : w≤6) (he : 0≤e) (he1 : e≤1/100)
    (hd : |v-w|≤100*e) : Real.sqrt v≤3 := by
  have hvw : v-w≤100*e := (le_abs_self _).trans hd
  have hvq := Real.sq_sqrt hv
  have hv0 := Real.sqrt_nonneg v
  nlinarith

theorem weighted_root_difference {v w a b e : ℝ}
    (hv : 0≤v) (hw : 1/4≤w) (hw6 : w≤6)
    (he : 0≤e) (he1 : e≤1/100)
    (ha : a∈Set.Icc 0 2) (hb : b∈Set.Icc 0 2)
    (hd : |v-w|≤100*e) (hab : |a-b|≤3*e) :
    |a*Real.sqrt v-b*Real.sqrt w|≤500*e := by
  have hv3 := sqrt_upper hv hw6 he he1 hd
  have hr0 := Real.sqrt_nonneg v
  have hr := sqrt_difference hv hw
  have hr' : |Real.sqrt v-Real.sqrt w|≤200*e := by linarith
  have hR : |Real.sqrt v|≤3 := by rwa [abs_of_nonneg hr0]
  have hB : |b|≤2 := by rw [abs_of_nonneg hb.1]; exact hb.2
  have hm := product_difference hR hB hr' hab
  have hcomm : |a*Real.sqrt v-b*Real.sqrt w|=
      |Real.sqrt v*a-Real.sqrt w*b| := by congr 1; ring
  rw [hcomm]
  linarith

end SquaresInCircles.Eight.TableFree.BoundedRadicalPerturbation

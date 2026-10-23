module

public import SquaresInCircles.Eight.TableFree.ShortOuterOneEdgeFiveBPrimary

/-!
# The prescribed A-secondary circle supports

Uncompiled transcription of Section 3, equations (16)--(18). These are
the two original A tuples, with the stated multiplier on each complete
angle half. The moving norm and both derivatives remain explicit.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterOne.EdgeFive.ASecondary
open CommonQuarter CorePairGeometry Arithmetic

def weight (r : Row) (upper : Bool) : ℝ :=
  if upper then 3/4 else if r=0 then q r else 439/500
def source (r : Row) (upper : Bool) : ℝ :=
  if upper then p r*outerAxial else if r=0 then 0 else
    -(p r+q r-weight r upper)/2-radius*Real.sqrt (p r^2+(q r-weight r upper)^2)
def normA (r : Row) (upper : Bool) : ℝ := P r^2+t r^2+weight r upper^2
def normB (r : Row) (upper : Bool) : ℝ := 2*weight r upper*P r
def normC (r : Row) (upper : Bool) : ℝ := 2*direction upper*weight r upper*t r
def N (r : Row) (upper : Bool) (x : ℝ) : ℝ :=
  CircularNorm.norm (normA r upper) (normB r upper) (normC r upper) x
def F (r : Row) (upper : Bool) (x : ℝ) : ℝ :=
  angle upper x+c r+source r upper+(weight r upper+P r+t r)/2+
    weight r upper*Real.cos x+(1+direction upper)/2*weight r upper*Real.sin x-radius*N r upper x
def first (r : Row) (upper : Bool) (x : ℝ) : ℝ :=
  direction upper-weight r upper*Real.sin x+(1+direction upper)/2*weight r upper*Real.cos x-
    radius*CircularNorm.d1 (normA r upper) (normB r upper) (normC r upper) x
def second (r : Row) (upper : Bool) (x : ℝ) : ℝ :=
  -weight r upper*Real.cos x-(1+direction upper)/2*weight r upper*Real.sin x-
    radius*CircularNorm.d2 (normA r upper) (normB r upper) (normC r upper) x

theorem weight_bounds (r : Row) (hr : ARows r) (upper : Bool) :
    (3/4:ℝ)≤weight r upper ∧ weight r upper≤439/500 := by
  rcases hr with rfl|rfl <;> cases upper <;> norm_num [weight,q]
theorem weight_positive (r : Row) (hr : ARows r) (upper : Bool) : 0<weight r upper := by
  linarith [(weight_bounds r hr upper).1]
theorem lower_weight (r : Row) (hr : ARows r) :
    (21721/25000:ℝ)≤weight r false ∧ (20762/25000:ℝ)≤t r := by
  rcases hr with rfl|rfl <;> norm_num [weight,q,t]
theorem energy_identity (r : Row) (upper : Bool) (x : ℝ) :
    CircularNorm.energy (normA r upper) (normB r upper) (normC r upper) x=
      (P r+weight r upper*Real.cos x)^2+(t r+direction upper*weight r upper*Real.sin x)^2 := by
  cases upper
  · dsimp [CircularNorm.energy,normA,normB,normC,direction]
    linear_combination -(weight r false)^2*(Real.sin_sq_add_cos_sq x)
  · dsimp [CircularNorm.energy,normA,normB,normC,direction]
    linear_combination -(weight r true)^2*(Real.sin_sq_add_cos_sq x)
theorem energy_positive (r : Row) (hr : ARows r) (upper : Bool) {x : ℝ}
    (hx : x∈Icc 0 (7/10)) :
    0<CircularNorm.energy (normA r upper) (normB r upper) (normC r upper) x := by
  have hP := (A_bounds r hr).1
  have hw := weight_positive r hr upper
  have hc : 0<Real.cos x := by linarith [(positive_trig hx).1]
  have hh : 0<P r+weight r upper*Real.cos x := by nlinarith [mul_pos hw hc]
  rw [energy_identity]
  nlinarith [sq_nonneg (t r+direction upper*weight r upper*Real.sin x)]
theorem norm_positive (r : Row) (hr : ARows r) (upper : Bool) {x : ℝ}
    (hx : x∈Icc 0 (7/10)) : 0<N r upper x :=
  CircularNorm.norm_pos (energy_positive r hr upper hx)
theorem norm_sq (r : Row) (hr : ARows r) (upper : Bool) {x : ℝ}
    (hx : x∈Icc 0 (7/10)) :
    (N r upper x)^2=normA r upper+normB r upper*Real.cos x+normC r upper*Real.sin x :=
  CircularNorm.norm_sq (energy_positive r hr upper hx).le
theorem norm_initial (r : Row) (upper : Bool) :
    (N r upper 0)^2=(P r+weight r upper)^2+t r^2 := by
  have he : CircularNorm.energy (normA r upper) (normB r upper) (normC r upper) 0=
      (P r+weight r upper)^2+t r^2 := by
    simp [CircularNorm.energy,normA,normB,normC]
    ring
  dsimp [N,CircularNorm.norm]
  rw [he,Real.sq_sqrt (by positivity)]
theorem norm_hasDerivAt (r : Row) (hr : ARows r) (upper : Bool) {x : ℝ}
    (hx : x∈Icc 0 (7/10)) :
    HasDerivAt (N r upper) (CircularNorm.d1 (normA r upper) (normB r upper) (normC r upper) x) x :=
  CircularNorm.norm_hasDerivAt (energy_positive r hr upper hx)
theorem norm_first (r : Row) (hr : ARows r) (upper : Bool) {x : ℝ}
    (hx : x∈Icc 0 (7/10)) :
    CircularNorm.d1 (normA r upper) (normB r upper) (normC r upper) x=
      weight r upper*(-P r*Real.sin x+direction upper*t r*Real.cos x)/N r upper x := by
  have hn := (norm_positive r hr upper hx).ne'
  dsimp [CircularNorm.d1,CircularNorm.slope,normB,normC]
  change _=_/N r upper x
  field_simp [hn]
  ring
theorem F_hasDerivAt (r : Row) (hr : ARows r) (upper : Bool) {x : ℝ}
    (hx : x∈Icc 0 (7/10)) : HasDerivAt (F r upper) (first r upper x) x := by
  convert (((((hasDerivAt_id x).const_mul (direction upper)).const_add
    (Real.pi/2+c r+source r upper+(weight r upper+P r+t r)/2)).add
      ((Real.hasDerivAt_cos x).const_mul (weight r upper))).add
        ((Real.hasDerivAt_sin x).const_mul ((1+direction upper)/2*weight r upper))).sub
          ((norm_hasDerivAt r hr upper hx).const_mul radius) using 1 <;>
    dsimp [F,first,angle] <;> ring
theorem first_hasDerivAt (r : Row) (hr : ARows r) (upper : Bool) {x : ℝ}
    (hx : x∈Icc 0 (7/10)) : HasDerivAt (first r upper) (second r upper x) x := by
  convert ((((Real.hasDerivAt_sin x).const_mul (-weight r upper)).const_add (direction upper)).add
    ((Real.hasDerivAt_cos x).const_mul ((1+direction upper)/2*weight r upper))).sub
      ((CircularNorm.d1_hasDerivAt (energy_positive r hr upper hx)).const_mul radius) using 1 <;>
    dsimp [first,second] <;> ring

theorem source_lower (r : Row) (hr : ARows r) (upper : Bool) {a b : ℝ}
    (hs : OuterState a b) : source r upper≤p r*a+(q r-weight r upper)*b := by
  cases upper
  · rcases hr with rfl|rfl
    · norm_num [source,weight,p,q]
    · exact outer_circle_lower (X:=p 1) (Y:=q 1-weight 1 false) hs
  · have hp := (coefficient_bounds r).1
    have hq : 0≤q r-weight r true := by
      dsimp [weight]
      linarith [(coefficient_bounds r).2.2.1]
    exact ShortWord.MixedQuarter.outer_axial_lower hs hp hq
theorem original_lower (r : Row) (hr : ARows r) (upper : Bool) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : Secondary r upper a b A B x) : F r upper x≤cost r upper a b A B x := by
  let X := -P r-weight r upper*Real.cos x
  let Y := -direction upper*weight r upper*Real.sin x-t r
  have he : Real.sqrt (X^2+Y^2)=N r upper x := by
    dsimp [N,CircularNorm.norm]
    congr 1
    rw [energy_identity]
    dsimp [X,Y]
    ring
  have htarg := outer_circle_lower (X:=X) (Y:=Y) ht
  rw [he] at htarg
  have hh := secondary_support r upper (λ:=weight r upper) (weight_positive r hr upper).le hm
    (S:=source r upper) (T:= -(X+Y)/2-radius*N r upper x)
    (by rw [A_sign hr]; nlinarith [source_lower r hr upper hs])
    (by rw [A_sign hr]; exact htarg)
  dsimp [F,width,X,Y] at *
  nlinarith

end SquaresInCircles.Eight.TableFree.ShortOuterOne.EdgeFive.ASecondary

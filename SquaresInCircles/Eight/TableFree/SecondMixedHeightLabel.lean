module

public import SquaresInCircles.Eight.TableFree.SecondMixedEdgeThreeLabels
public import SquaresInCircles.Eight.TableFree.HighOrderTaylor

/-!
# Exact height coordinates for the mixed outer labels

The height radical is differentiated on its full positive domain.
One four-coefficient expression gives the negative P, T and L labels
and their first five derivatives.  All circle identities are equalities
at the unchanged original outer point.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree.SecondWord
open CommonQuarter CorePairGeometry Arithmetic

structure HeightLabel where
  c : ℝ
  v : ℝ
  k : ℝ
  w : ℝ

namespace HeightLabel

def root (u : ℝ) : ℝ := Real.sqrt (Q0-u^2)

lemma root_pos {u : ℝ} (hu : 0<Q0-u^2) : 0<root u := Real.sqrt_pos.mpr hu
lemma root_sq {u : ℝ} (hu : 0<Q0-u^2) : (root u)^2=Q0-u^2 := Real.sq_sqrt hu.le

lemma root_even {u : ℝ} (hu : 0<Q0-u^2) (n : ℕ) :
    (root u)^(2*n)=(Q0-u^2)^n := by rw [pow_mul,root_sq hu]

lemma root_odd {u : ℝ} (hu : 0<Q0-u^2) (n : ℕ) :
    (root u)^(2*n+1)=(Q0-u^2)^n*root u := by rw [pow_succ,root_even hu]

lemma root_cage {u l r : ℝ} (hl : 0≤l) (hr : 0<r)
    (hlo : l^2<Q0-u^2) (hhi : Q0-u^2<r^2) : l<root u ∧ root u<r := by
  have hu : 0<Q0-u^2 := by nlinarith [sq_nonneg l]
  have hp := root_pos hu
  have hs := root_sq hu
  constructor <;> nlinarith

lemma root_hasDerivAt {u : ℝ} (hu : 0<Q0-u^2) : HasDerivAt root (-u/root u) u := by
  convert (((hasDerivAt_id u).pow 2).const_sub Q0).sqrt hu.ne' using 1
  · rfl
  · dsimp [root]
    ring

def eval (H : HeightLabel) (u : ℝ) : ℝ :=
  H.c-H.v*u^2-H.k*u/2-(H.w-H.k*u)*root u
def d1 (H : HeightLabel) (u : ℝ) : ℝ :=
  -2*H.v*u-H.k/2+(H.k*Q0+H.w*u-2*H.k*u^2)/root u
def d2 (H : HeightLabel) (u : ℝ) : ℝ :=
  -2*H.v+(H.w*Q0-3*H.k*Q0*u+2*H.k*u^3)/(root u)^3
def d3 (H : HeightLabel) (u : ℝ) : ℝ :=
  3*Q0*(H.w*u-H.k*Q0)/(root u)^5
def d4 (H : HeightLabel) (u : ℝ) : ℝ :=
  3*Q0*(H.w*(Q0+4*u^2)-5*H.k*Q0*u)/(root u)^7
def d5 (H : HeightLabel) (u : ℝ) : ℝ :=
  15*Q0*(H.w*u*(3*Q0+4*u^2)-H.k*Q0*(Q0+6*u^2))/(root u)^9

local macro "height_algebra" h:term : tactic => `(tactic|
  (field_simp [(root_pos $h).ne']
   ring_nf
   simp only [root_even $h 1,root_even $h 2,root_even $h 3,root_even $h 4,
     root_even $h 5,root_even $h 6,root_even $h 7,root_even $h 8,
     root_odd $h 1,root_odd $h 2,root_odd $h 3,root_odd $h 4,
     root_odd $h 5,root_odd $h 6,root_odd $h 7,root_odd $h 8]
   ring))

lemma eval_hasDerivAt (H : HeightLabel) {u : ℝ} (hu : 0<Q0-u^2) :
    HasDerivAt H.eval (H.d1 u) u := by
  have hd := ((((hasDerivAt_const u H.c).sub (((hasDerivAt_id u).pow 2).const_mul H.v)).sub
    (((hasDerivAt_id u).const_mul H.k).div_const 2)).sub
      ((((hasDerivAt_id u).const_mul H.k).const_sub H.w).mul (root_hasDerivAt hu)))
  convert hd using 1
  · rfl
  · dsimp [d1]
    height_algebra hu

lemma d1_hasDerivAt (H : HeightLabel) {u : ℝ} (hu : 0<Q0-u^2) :
    HasDerivAt H.d1 (H.d2 u) u := by
  have hn := (((hasDerivAt_id u).const_mul H.w).const_add (H.k*Q0)).sub
    (((hasDerivAt_id u).pow 2).const_mul (2*H.k))
  have hd := (((hasDerivAt_id u).const_mul (-2*H.v)).sub_const (H.k/2)).add
    (hn.div (root_hasDerivAt hu) (root_pos hu).ne')
  convert hd using 1
  · ext x
    dsimp [d1]
    ring
  · dsimp [d2]
    height_algebra hu

lemma d2_hasDerivAt (H : HeightLabel) {u : ℝ} (hu : 0<Q0-u^2) :
    HasDerivAt H.d2 (H.d3 u) u := by
  have hn := ((((hasDerivAt_id u).const_mul (3*H.k*Q0)).const_sub (H.w*Q0)).add
    (((hasDerivAt_id u).pow 3).const_mul (2*H.k)))
  have hd := (hn.div ((root_hasDerivAt hu).pow 3) (pow_ne_zero 3 (root_pos hu).ne')).const_add (-2*H.v)
  convert hd using 1
  · rfl
  · dsimp [d3]
    height_algebra hu

lemma d3_hasDerivAt (H : HeightLabel) {u : ℝ} (hu : 0<Q0-u^2) :
    HasDerivAt H.d3 (H.d4 u) u := by
  have hn := (((hasDerivAt_id u).const_mul H.w).sub_const (H.k*Q0)).const_mul (3*Q0)
  have hd := hn.div ((root_hasDerivAt hu).pow 5) (pow_ne_zero 5 (root_pos hu).ne')
  convert hd using 1
  · rfl
  · dsimp [d4]
    height_algebra hu

lemma d4_hasDerivAt (H : HeightLabel) {u : ℝ} (hu : 0<Q0-u^2) :
    HasDerivAt H.d4 (H.d5 u) u := by
  have hn := ((((((hasDerivAt_id u).pow 2).const_mul 4).const_add Q0).const_mul H.w).sub
    ((hasDerivAt_id u).const_mul (5*H.k*Q0))).const_mul (3*Q0)
  have hd := hn.div ((root_hasDerivAt hu).pow 7) (pow_ne_zero 7 (root_pos hu).ne')
  convert hd using 1
  · rfl
  · dsimp [d5]
    height_algebra hu

lemma d1_mul (H : HeightLabel) {u : ℝ} (hu : 0<Q0-u^2) :
    H.d1 u*root u=(-2*H.v*u-H.k/2)*root u+H.k*Q0+H.w*u-2*H.k*u^2 := by
  dsimp [d1]
  field_simp [(root_pos hu).ne']
  ring

lemma d2_mul (H : HeightLabel) {u : ℝ} (hu : 0<Q0-u^2) :
    H.d2 u*(root u)^3= -2*H.v*(root u)^3+H.w*Q0-3*H.k*Q0*u+2*H.k*u^3 := by
  dsimp [d2]
  field_simp [(root_pos hu).ne']
  ring

lemma d3_mul (H : HeightLabel) {u : ℝ} (hu : 0<Q0-u^2) :
    H.d3 u*(root u)^5=3*Q0*(H.w*u-H.k*Q0) := by
  dsimp [d3]
  field_simp [(root_pos hu).ne']

lemma d4_mul (H : HeightLabel) {u : ℝ} (hu : 0<Q0-u^2) :
    H.d4 u*(root u)^7=3*Q0*(H.w*(Q0+4*u^2)-5*H.k*Q0*u) := by
  dsimp [d4]
  field_simp [(root_pos hu).ne']

lemma fourth_growth_identity (H : HeightLabel) {u : ℝ} (hu : 0<Q0-u^2) (r : ℝ) :
    (H.d4 u-r*H.d3 u)*(root u)^7=
      3*Q0*(H.w*(Q0-u^2)+(5*u-r*(Q0-u^2))*(H.w*u-H.k*Q0)) := by
  dsimp [d3,d4]
  height_algebra hu

lemma actual_root {a b : ℝ} (hs : OuterState a b) : root (a+1/2)=b+1/2 := by
  have hrad : Q0-(a+1/2)^2=(b+1/2)^2 := by linarith [hs.2.2]
  dsimp [root]
  rw [hrad,Real.sqrt_sq_eq_abs,abs_of_nonneg (by linarith [hs.1])]

end HeightLabel

def LHeight : HeightLabel := ⟨1074925961/125000000,37437/25000,94721/50000,629979/100000⟩

lemma LHeight_actual {a b : ℝ} (hs : OuterState a b) : LHeight.eval (a+1/2)= -L b := by
  have hc := hs.2.2
  norm_num [Q0] at hc
  rw [HeightLabel.eval,HeightLabel.actual_root hs,
    show L b=LLabel.eval a b from LLabel.outer_actual hs]
  norm_num [LHeight,LLabel,RoleLabel.eval]
  linear_combination -(37437/25000)*hc

end SquaresInCircles.Eight.TableFree.SecondWord

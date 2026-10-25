module

public import SquaresInCircles.Eight.TableFree.FrameDiagonalSupport

/-!
# Complete initial-angle barriers on the folded arcs

The maximum of the retained central margin is attained at the specified
actual source and target endpoints, uniformly on the first quadrant.
One rational Taylor comparison at the final angle of each sign case
therefore excludes the entire initial interval.  The twelve cases are
the two ordered M/H pairs and H/H, including endpoint ties.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameDiagonalCuts
open FramePair FrameDiagonalArc FrameDiagonalLabels FrameDiagonalTransport
open FramePairCalculus

def first (m : Bool) : ℝ := if m then b1 else 0
def last (m : Bool) : ℝ := if m then b2 else b1
def sourceEnd (m i : Bool) : ℝ := if i then last m else first m
def targetEnd (n j : Bool) : ℝ := if j then first n else last n
def sourcePart (i : Bool) (b : ℝ) : ℝ := A b+sign i*b
def targetPart (j : Bool) (x B : ℝ) : ℝ :=
  (Real.sin x-Real.cos x)*A B-sign j*(Real.sin x+Real.cos x)*B
def K (m i : Bool) : ℝ := sourcePart i (sourceEnd m i)-1
def S (n j : Bool) : ℝ := A (targetEnd n j)-sign j*targetEnd n j-1
def C (n j : Bool) : ℝ := A (targetEnd n j)+sign j*targetEnd n j+1
def barrier (m n i j : Bool) (x : ℝ) : ℝ :=
  K m i+S n j*Real.sin x-C n j*Real.cos x
def cut (m n i j : Bool) : ℝ :=
  if m then
    if n then 0 else if i then (if j then 7/10 else 1/10)
      else (if j then 6/5 else 9/10)
  else if n then
    if i then (if j then 11/10 else 1/10) else (if j then 13/10 else 2/5)
  else if i then 7/20 else (if j then 1 else 3/5)

theorem arc_eq (m : Bool) : arc m=Icc (first m) (last m) := by cases m <;> rfl

theorem first_mem (m : Bool) : first m∈arc m := by
  cases m
  · show (0:ℝ)∈Icc 0 b1
    exact ⟨le_rfl,by linarith [b1_bounds.1]⟩
  · show b1∈Icc b1 b2
    exact ⟨le_rfl,b1_lt_b2.le⟩

theorem last_mem (m : Bool) : last m∈arc m := by
  cases m
  · show b1∈Icc 0 b1
    exact ⟨by linarith [b1_bounds.1],le_rfl⟩
  · show b2∈Icc b1 b2
    exact ⟨b1_lt_b2.le,le_rfl⟩

theorem sourceEnd_mem (m i : Bool) : sourceEnd m i∈arc m := by
  cases i
  · exact first_mem m
  · exact last_mem m

theorem targetEnd_mem (n j : Bool) : targetEnd n j∈arc n := by
  cases j
  · exact last_mem n
  · exact first_mem n

theorem source_upper (m i : Bool) {b : ℝ} (hb : b∈arc m) :
    sourcePart i b≤ sourcePart i (sourceEnd m i) := by
  have hi : b∈Icc (first m) (last m) := by simpa only [arc_eq] using hb
  cases i
  · have h : A b-b≤A (first m)-first m :=
      minus_antitone (arc_subset (first_mem m)) (arc_subset hb) hi.1
    show A b+sign false*b≤A (first m)+sign false*first m
    rw [show sign false=-1 from rfl]
    linarith
  · have h : A b+b≤A (last m)+last m :=
      plus_monotone (arc_subset hb) (arc_subset (last_mem m)) hi.2
    show A b+sign true*b≤A (last m)+sign true*last m
    rw [show sign true=1 from rfl]
    linarith

theorem target_deriv (j : Bool) (x : ℝ) {B : ℝ} (hB : B∈Icc 0 b2) :
    HasDerivAt (targetPart j x)
      (-(Real.sin x-Real.cos x)*slope B-sign j*(Real.sin x+Real.cos x)) B := by
  have hd := ((A_hasDerivAt hB).const_mul (Real.sin x-Real.cos x)).fun_sub
    ((hasDerivAt_id' B).const_mul (sign j*(Real.sin x+Real.cos x)))
  refine hd.congr_deriv ?_
  have hAd : Ad B=-FrameDiagonalArc.slope B := by
    simp only [Ad,FrameDiagonalArc.slope,neg_div]
  rw [hAd]
  ring

theorem quadrant_slope_bounds {x B : ℝ} (hx : x∈Icc 0 (Real.pi/2))
    (hB : B∈Icc 0 b2) :
    -(Real.sin x+Real.cos x)≤(Real.sin x-Real.cos x)*slope B ∧
      (Real.sin x-Real.cos x)*slope B≤Real.sin x+Real.cos x := by
  have ht := FrameLowPair.quadrant hx
  have hr := slope_bounds hB
  have hw := FrameCoreArc.width_one_le x
  rw [(first_width hx).1] at hw
  have hlo := mul_le_mul_of_nonneg_right
    (show -(1:ℝ)≤Real.sin x-Real.cos x by linarith) hr.1
  have hhi := mul_le_mul_of_nonneg_right
    (show Real.sin x-Real.cos x≤1 by linarith) hr.1
  constructor <;> linarith

theorem target_positive_antitone {x : ℝ} (hx : x∈Icc 0 (Real.pi/2)) :
    AntitoneOn (targetPart true x) (Icc 0 b2) := by
  apply antiOn_of_hasDeriv_nonpos
  · exact fun B hB => (target_deriv true x hB).continuousAt.continuousWithinAt
  · exact fun B hB => target_deriv true x (Ioo_subset_Icc_self hB)
  · intro B hB
    have hh := (quadrant_slope_bounds hx (Ioo_subset_Icc_self hB)).1
    norm_num [sign]
    linarith

theorem target_negative_monotone {x : ℝ} (hx : x∈Icc 0 (Real.pi/2)) :
    MonotoneOn (targetPart false x) (Icc 0 b2) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun B hB => (target_deriv false x hB).continuousAt.continuousWithinAt
  · exact fun B hB => target_deriv false x (Ioo_subset_Icc_self hB)
  · intro B hB
    have hh := (quadrant_slope_bounds hx (Ioo_subset_Icc_self hB)).2
    norm_num [sign]
    linarith

theorem target_upper (n j : Bool) {B x : ℝ} (hB : B∈arc n)
    (hx : x∈Icc 0 (Real.pi/2)) :
    targetPart j x B≤targetPart j x (targetEnd n j) := by
  have hi : B∈Icc (first n) (last n) := by simpa only [arc_eq] using hB
  cases j
  · exact target_negative_monotone hx (arc_subset hB) (arc_subset (last_mem n)) hi.2
  · exact target_positive_antitone hx (arc_subset (first_mem n)) (arc_subset hB) hi.1

theorem central_upper (m n i j : Bool) {b B x : ℝ}
    (hb : b∈arc m) (hB : B∈arc n) (hx : x∈Icc 0 (Real.pi/2)) :
    central i j (A b) b (A B) B x≤barrier m n i j x := by
  have hs := source_upper m i hb
  have ht := target_upper n j hB hx
  dsimp [sourcePart,targetPart] at hs ht
  dsimp [central,barrier,K,S,C,sourcePart]
  rw [(first_width hx).1]
  nlinarith

theorem coefficients_positive (n j : Bool) : 0<S n j ∧ 0<C n j := by
  have h0 := a0_precise
  have h1 := a1_precise
  have h2 := a2_precise
  have e1 := b1_eq
  have e2 := b2_eq
  cases n <;> cases j <;>
    simp only [S,C,targetEnd,first,last,sign,Bool.false_eq_true,↓reduceIte,
      A_zero,A_b1,A_b2] <;>
    constructor <;> linarith

theorem barrier_deriv (m n i j : Bool) (x : ℝ) :
    HasDerivAt (barrier m n i j)
      (S n j*Real.cos x+C n j*Real.sin x) x := by
  have h := (((Real.hasDerivAt_sin x).const_mul (S n j)).const_add (K m i)).fun_sub
    ((Real.hasDerivAt_cos x).const_mul (C n j))
  refine h.congr_deriv ?_
  ring

theorem barrier_monotone (m n i j : Bool) :
    MonotoneOn (barrier m n i j) (Icc 0 (Real.pi/2)) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun x _ => (barrier_deriv m n i j x).continuousAt.continuousWithinAt
  · exact fun x _ => barrier_deriv m n i j x
  · intro x hx
    have ht := FrameLowPair.quadrant (Ioo_subset_Icc_self hx)
    have hc := coefficients_positive n j
    exact add_nonneg (mul_nonneg hc.1.le ht.2.2.1) (mul_nonneg hc.2.le ht.1)

theorem cut_quadrant (m n i j : Bool) : cut m n i j∈Icc 0 (Real.pi/2) := by
  cases m <;> cases n <;> cases i <;> cases j <;> norm_num [cut]
  all_goals linarith [Arithmetic.pi_hand_enclosure.1]

theorem cut_negative (m n i j : Bool) (hhigh : m=false ∨ n=false) :
    barrier m n i j (cut m n i j)<0 := by
  have ht := Arithmetic.trig_taylor_bounds (cut_quadrant m n i j).1
  have hc := coefficients_positive n j
  have hs := mul_le_mul_of_nonneg_left ht.2.1 hc.1.le
  have hcos := mul_le_mul_of_nonneg_left ht.2.2.1 hc.2.le
  have hp : K m i+S n j*Arithmetic.sin9 (cut m n i j)-
      C n j*Arithmetic.cos10 (cut m n i j)<0 := by
    have h0 := a0_precise
    have h1 := a1_precise
    have h2 := a2_precise
    have e1 := b1_eq
    have e2 := b2_eq
    cases m
    · cases n <;> cases i <;> cases j <;>
        simp only [cut,K,S,C,sourcePart,sourceEnd,targetEnd,first,last,sign,
          Bool.false_eq_true,↓reduceIte,A_zero,A_b1,A_b2] <;>
        norm_num [e1,e2,Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8] <;>
        linarith
    · rcases hhigh with h | rfl
      · exact absurd h (by decide)
      · cases i <;> cases j <;>
          simp only [cut,K,S,C,sourcePart,sourceEnd,targetEnd,first,last,sign,
            Bool.false_eq_true,↓reduceIte,A_zero,A_b1,A_b2] <;>
          norm_num [e1,e2,Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8] <;>
          linarith
  dsimp only [barrier]
  linarith

theorem central_cut (m n i j : Bool) (hhigh : m=false ∨ n=false)
    {b B x : ℝ} (hb : b∈arc m) (hB : B∈arc n) (hx : 0≤x)
    (hm : 0≤central i j (A b) b (A B) B x) : cut m n i j<x := by
  by_contra! hsmall
  have hxq : x∈Icc 0 (Real.pi/2) := ⟨hx,hsmall.trans (cut_quadrant m n i j).2⟩
  have hmax := central_upper m n i j hb hB hxq
  have hmono := barrier_monotone m n i j hxq (cut_quadrant m n i j) hsmall
  linarith [cut_negative m n i j hhigh]

end SquaresInCircles.Eight.TableFree.FrameDiagonalCuts

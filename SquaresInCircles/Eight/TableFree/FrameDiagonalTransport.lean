module

public import SquaresInCircles.Eight.TableFree.FrameDiagonalLabels
public import SquaresInCircles.Eight.TableFree.FramePairCalculus

/-!
# Original witnesses in the diagonal chart

The chart rotates each original signed frame toward its diagonal.  Its
quarter shift preserves the width and its complementary marker preserves
the actual pair cost.  The identities below carry the original source
axes, including a zero margin, rather than selecting a new separator.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameDiagonalTransport
open FramePair FrameDiagonalArc FrameDiagonalLabels

def kind (middle : Bool) : Branch := if middle then .middle else .high
def angle (i j : Bool) (x : ℝ) : ℝ := x+(sign i-sign j)*(Real.pi/4)
def turn (s : FramePair.State) : ℝ := Real.pi/4-Real.arctan (s.b/s.a)
def offset (s : FramePair.State) : ℝ := s.offset-sign s.positive*(Real.pi/4)
def cap (middle : Bool) : ℝ := if middle then 541/1000 else 381/1000
def cost (m n i j : Bool) (b B x : ℝ) : ℝ :=
  x-(9/50)*periodicFrameCost x+sign i*marker m b-sign j*marker n B
def central (i j : Bool) (a b A B x : ℝ) : ℝ :=
  a+sign i*b+(Real.sin x-Real.cos x)*A-
    sign j*(Real.sin x+Real.cos x)*B-2*pairWidth x
def extra (j : Bool) (a b A B x : ℝ) : ℝ :=
  a+b-(Real.sin x+Real.cos x)*A-
    sign j*(Real.sin x-Real.cos x)*B-2*pairWidth x
def centralAxis (i : Bool) : Fin 4 := if i then 0 else 3

@[simp] theorem angle_false_false (x : ℝ) : angle false false x=x := by
  simp [angle,sign]
@[simp] theorem angle_true_true (x : ℝ) : angle true true x=x := by
  simp [angle,sign]
@[simp] theorem angle_false_true (x : ℝ) : angle false true x=x-Real.pi/2 := by
  dsimp [angle,sign]
  ring
@[simp] theorem angle_true_false (x : ℝ) : angle true false x=x+Real.pi/2 := by
  dsimp [angle,sign]
  ring

theorem angle_width (i j : Bool) (x : ℝ) : pairWidth (angle i j x)=pairWidth x := by
  cases i <;> cases j <;> simp [pairWidth,Real.sin_add,Real.cos_add,
    Real.sin_sub,Real.cos_sub,abs_neg,add_comm,add_left_comm,add_assoc]

theorem angle_charge (i j : Bool) (x : ℝ) :
    periodicFrameCost (angle i j x)=periodicFrameCost x := by
  cases i <;> cases j <;> simp [periodicFrameCost,Real.sin_add,Real.cos_add,
    Real.sin_sub,Real.cos_sub,abs_neg,add_comm]

theorem central_identity (i j : Bool) (a b A B x : ℝ) :
    central (!i) (!j) (a+b) (a-b) (A+B) (A-B) (angle i j x)=
      2*forwardMargin (centralAxis i) a b A B (sign i) (sign j) x := by
  dsimp only [central]
  rw [angle_width]
  cases i <;> cases j
  all_goals (simp [centralAxis,sign,forwardMargin,Real.sin_add,Real.cos_add,
    Real.sin_sub,Real.cos_sub]; ring)

theorem extra_identity (j : Bool) (a b A B x : ℝ) :
    extra (!j) (a+b) (a-b) (A+B) (A-B) (angle true j x)=
      2*forwardMargin 3 a b A B 1 (sign j) x := by
  dsimp only [extra]
  rw [angle_width]
  cases j
  all_goals (simp [sign,forwardMargin,Real.sin_add,Real.cos_add]; ring)

theorem offset_turn (s : FramePair.State) : offset s=sign (!s.positive)*turn s := by
  rw [sign_not]
  dsimp [offset,turn,State.offset]
  ring

theorem gap_identity (s t : FramePair.State) (x : ℝ) :
    angle s.positive t.positive x+offset s-offset t=s.gap t x := by
  dsimp [angle,offset,State.gap]
  ring

theorem turn_nonneg (s : FramePair.State) : 0≤turn s := by
  have hr : s.b/s.a≤1 := (div_le_one s.a_pos).2 s.canonical
  have hh : Real.arctan (s.b/s.a)≤Real.pi/4 := by
    simpa [Real.arctan_one] using Real.arctan_mono hr
  exact sub_nonneg.mpr hh

theorem high_turn_upper (s : FramePair.State) (hs : s.branch=.high) :
    turn s<(381/1000:ℝ) := by
  have ht : 3*s.a≤7*s.b := by simpa [hs,TypeMem] using s.type_mem
  have hr : (3/7:ℝ) ≤ s.b/s.a := (le_div_iff₀ s.a_pos).2 (by linarith)
  have hl := Arithmetic.atanLower_le (show (0:ℝ)≤3/7 by norm_num)
  have hn : (1011/2500:ℝ)<Arithmetic.atanLower (3/7:ℝ) := by
    norm_num [Arithmetic.atanLower]
  have ha := hl.trans (Real.arctan_mono hr)
  dsimp [turn]
  linarith [Arithmetic.pi_hand_enclosure.2]

theorem mid_turn_upper (s : FramePair.State) (hs : s.branch=.middle) :
    turn s<(541/1000:ℝ) := by
  have ht : s.a≤4*s.b ∧ 7*s.b≤3*s.a := by simpa [hs,TypeMem] using s.type_mem
  have hr : (1/4:ℝ) ≤ s.b/s.a := (le_div_iff₀ s.a_pos).2 (by linarith [ht.1])
  have hl := Arithmetic.atanLower_le (show (0:ℝ)≤1/4 by norm_num)
  have hn : (489/2000:ℝ)<Arithmetic.atanLower (1/4:ℝ) := by
    norm_num [Arithmetic.atanLower]
  have ha := hl.trans (Real.arctan_mono hr)
  dsimp [turn]
  linarith [Arithmetic.pi_hand_enclosure.2]

theorem turn_bounds (m : Bool) (s : FramePair.State) (hs : s.branch=kind m) :
    0≤turn s ∧ turn s<cap m := by
  refine ⟨turn_nonneg s,?_⟩
  cases m
  · exact high_turn_upper s hs
  · exact mid_turn_upper s hs

theorem offset_bounds (m : Bool) (s : FramePair.State) (hs : s.branch=kind m) :
    -cap m<offset s ∧ offset s<cap m := by
  have ht := turn_bounds m s hs
  rw [offset_turn]
  cases hi : s.positive <;> simp [sign] <;> constructor <;>
    linarith [show 0<cap m by cases m <;> norm_num [cap]]

theorem angle_lower (m n : Bool) (s t : FramePair.State)
    (hs : s.branch=kind m) (ht : t.branch=kind n) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) :
    19/25-cap m-cap n<angle s.positive t.positive x := by
  have hso := offset_bounds m s hs
  have hto := offset_bounds n t ht
  have hid := gap_identity s t x
  linarith

/-- A nonpositive folded angle can only have folded signs `(+,-)`. -/
theorem nonpositive_signs (m n : Bool) (s t : FramePair.State)
    (hs : s.branch=kind m) (ht : t.branch=kind n) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x)
    (hx : angle s.positive t.positive x≤0) :
    s.positive=false ∧ t.positive=true := by
  have hso := turn_bounds m s hs
  have hto := turn_bounds n t ht
  have hmc : cap m<(19/25:ℝ) := by cases m <;> norm_num [cap]
  have hnc : cap n<(19/25:ℝ) := by cases n <;> norm_num [cap]
  have hid := gap_identity s t x
  rw [offset_turn,offset_turn] at hid
  cases hi : s.positive <;> cases hj : t.positive
  all_goals simp only [hi,hj,Bool.not_false,Bool.not_true,sign,Bool.false_eq_true,
    ↓reduceIte,one_mul,neg_one_mul] at hid hx
  all_goals first | exact ⟨rfl,rfl⟩ | linarith

theorem state_fold (m : Bool) (s : FramePair.State) (hs : s.branch=kind m) :
    s.a-s.b∈arc m ∧ A (s.a-s.b)=s.a+s.b := by
  cases m
  · exact FrameDiagonalArc.state_high_fold s hs
  · exact FrameDiagonalArc.state_mid_fold s hs

theorem state_label (m : Bool) (s : FramePair.State) (hs : s.branch=kind m) :
    sign (!s.positive)*marker m (s.a-s.b)=
      s.signedLabel-sign s.positive*(Real.pi/4) := by
  cases m
  · exact FrameDiagonalLabels.state_high_label s hs
  · exact FrameDiagonalLabels.state_mid_label s hs

theorem state_cost (m n : Bool) (s t : FramePair.State)
    (hs : s.branch=kind m) (ht : t.branch=kind n) (x : ℝ) :
    cost m n (!s.positive) (!t.positive) (s.a-s.b) (t.a-t.b)
        (angle s.positive t.positive x)=s.cost t x := by
  rw [cost,angle_charge,state_label m s hs,state_label n t ht]
  dsimp [angle,State.cost]
  ring

theorem state_central (m n : Bool) (s t : FramePair.State)
    (hs : s.branch=kind m) (ht : t.branch=kind n) (x : ℝ) :
    central (!s.positive) (!t.positive) (A (s.a-s.b)) (s.a-s.b)
        (A (t.a-t.b)) (t.a-t.b) (angle s.positive t.positive x)=
      2*forwardMargin (centralAxis s.positive) s.a s.b t.a t.b
        (sign s.positive) (sign t.positive) x := by
  rw [(state_fold m s hs).2,(state_fold n t ht).2]
  exact central_identity s.positive t.positive s.a s.b t.a t.b x

theorem state_central_feasible (m n : Bool) (s t : FramePair.State)
    (hs : s.branch=kind m) (ht : t.branch=kind n) {x : ℝ}
    (hm : s.Feasible t (centralAxis s.positive) x) :
    0≤central (!s.positive) (!t.positive) (A (s.a-s.b)) (s.a-s.b)
      (A (t.a-t.b)) (t.a-t.b) (angle s.positive t.positive x) := by
  rw [state_central m n s t hs ht]
  exact mul_nonneg (by norm_num) hm

theorem state_extra (m n : Bool) (s t : FramePair.State)
    (hs : s.branch=kind m) (ht : t.branch=kind n)
    (hi : s.positive=true) (x : ℝ) :
    extra (!t.positive) (A (s.a-s.b)) (s.a-s.b)
        (A (t.a-t.b)) (t.a-t.b) (angle s.positive t.positive x)=
      2*forwardMargin 3 s.a s.b t.a t.b (sign s.positive) (sign t.positive) x := by
  rw [(state_fold m s hs).2,(state_fold n t ht).2,hi]
  simpa [sign] using extra_identity t.positive s.a s.b t.a t.b x

end SquaresInCircles.Eight.TableFree.FrameDiagonalTransport

module

public import SquaresInCircles.Eight.TableFree.FrameLowMidArc

/-!
# Original signed low/middle coordinates and angular tails

The angle floors use only the ordered physical center gap and the
intrinsic low/middle cuts.  Both circle endpoints and every weak
separating-axis equality remain in the domain.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameLowMidGeometry
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc

def lowMidCost (i k : Bool) (b B x : ℝ) : ℝ :=
  x-(9/50)*periodicFrameCost x+sign i*L b-sign k*M B
def midLowCost (i k : Bool) (b B x : ℝ) : ℝ :=
  x-(9/50)*periodicFrameCost x+sign i*M b-sign k*L B
def secondary (i k : Bool) (b B x : ℝ) : ℝ :=
  sign i*b+A B*Real.sin x-sign k*B*Real.cos x-pairWidth x
def primary (k : Bool) (b B x : ℝ) : ℝ :=
  A b-A B*Real.cos x-sign k*B*Real.sin x-pairWidth x

def lowMidFloor (i k : Bool) : ℝ :=
  if i then (if k then 19/25 else 11/100) else (if k then 1 else 7/20)
def midLowFloor (i k : Bool) : ℝ :=
  if i then (if k then 7/20 else 11/100) else (if k then 1 else 19/25)
def lowMidTail (i k : Bool) : ℝ :=
  if i then (if k then 7/5 else 16/25) else (if k then 171/100 else 19/20)
def midLowTail (i k : Bool) : ℝ :=
  if i then (if k then 19/20 else 16/25) else (if k then 171/100 else 7/5)

theorem low_intrinsic (s : FramePair.State) (hs : s.branch=.low) :
    0≤Real.arctan (s.b/s.a) ∧
      Real.arctan (s.b/s.a)≤Real.arctan (1/4:ℝ) ∧
      Real.arctan (s.b/s.a)<49/200 := by
  have ht : 4*s.b≤ s.a := by simpa [hs,TypeMem] using s.type_mem
  have hlo : 0≤ s.b/s.a := div_nonneg s.b_nonneg s.a_pos.le
  have hhi : s.b/s.a≤1/4 := (div_le_iff₀ s.a_pos).2 (by linarith)
  have ha0 : 0≤Real.arctan (s.b/s.a) := Real.arctan_nonneg.2 hlo
  have hau := Arithmetic.arctan_le_atanUpper (show (0:ℝ)≤1/4 by norm_num)
  have hnum : Arithmetic.atanUpper (1/4:ℝ)<49/200 := by
    norm_num [Arithmetic.atanUpper]
  exact ⟨ha0,Real.arctan_mono hhi,
    (Real.arctan_mono hhi).trans_lt (hau.trans_lt hnum)⟩

theorem middle_intrinsic (s : FramePair.State) (hs : s.branch=.middle) :
    (6/25:ℝ)<Real.arctan (s.b/s.a) ∧
      Real.arctan (1/4:ℝ)≤Real.arctan (s.b/s.a) ∧
      Real.arctan (s.b/s.a)<81/200 := by
  have ht : s.a≤4*s.b ∧ 7*s.b≤3*s.a := by simpa [hs,TypeMem] using s.type_mem
  have hlo : (1/4:ℝ)≤ s.b/s.a := (le_div_iff₀ s.a_pos).2 (by linarith [ht.1])
  have hhi : s.b/s.a≤3/7 := (div_le_iff₀ s.a_pos).2 (by linarith [ht.2])
  have hal := Arithmetic.atanLower_le (show (0:ℝ)≤1/4 by norm_num)
  have hau := Arithmetic.arctan_le_atanUpper (show (0:ℝ)≤3/7 by norm_num)
  have hnumL : (6/25:ℝ)<Arithmetic.atanLower (1/4:ℝ) := by
    norm_num [Arithmetic.atanLower]
  have hnumU : Arithmetic.atanUpper (3/7:ℝ)<81/200 := by
    norm_num [Arithmetic.atanUpper]
  exact ⟨hnumL.trans_le (hal.trans (Real.arctan_mono hlo)),
    Real.arctan_mono hlo,
    (Real.arctan_mono hhi).trans_lt (hau.trans_lt hnumU)⟩

theorem low_mid_angle (s t : FramePair.State) (hs : s.branch=.low)
    (ht : t.branch=.middle) {x : ℝ} (hgap : (19/25:ℝ)≤ s.gap t x) :
    lowMidFloor s.positive t.positive≤x := by
  have hso := low_intrinsic s hs
  have hto := middle_intrinsic t ht
  have hord := hso.2.1.trans hto.2.1
  dsimp [State.gap,State.offset] at hgap
  cases hi : s.positive <;> cases hk : t.positive
  all_goals simp only [hi,hk,sign,Bool.false_eq_true,↓reduceIte,one_mul,neg_one_mul] at hgap
  all_goals simp only [lowMidFloor,Bool.false_eq_true,↓reduceIte]
  all_goals linarith

theorem mid_low_angle (s t : FramePair.State) (hs : s.branch=.middle)
    (ht : t.branch=.low) {x : ℝ} (hgap : (19/25:ℝ)≤ s.gap t x) :
    midLowFloor s.positive t.positive≤x := by
  have hso := middle_intrinsic s hs
  have hto := low_intrinsic t ht
  have hord := hto.2.1.trans hso.2.1
  dsimp [State.gap,State.offset] at hgap
  cases hi : s.positive <;> cases hk : t.positive
  all_goals simp only [hi,hk,sign,Bool.false_eq_true,↓reduceIte,one_mul,neg_one_mul] at hgap
  all_goals simp only [midLowFloor,Bool.false_eq_true,↓reduceIte]
  all_goals linarith

theorem low_mid_tail (i k : Bool) {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc b1 b2) (hx : lowMidTail i k≤x) :
    (1801/2000:ℝ)<lowMidCost i k b B x := by
  have hs := L_bounds hb
  have ht := M_bounds hB
  have hch := CorePairGeometry.charge_upper x
  cases i <;> cases k <;> dsimp [lowMidTail,lowMidCost,sign] at *
  all_goals linarith [L1_precise.2,M_endpoints.1,M_endpoints.2.2.2]

theorem mid_low_tail (i k : Bool) {b B x : ℝ}
    (hb : b∈Icc b1 b2) (hB : B∈Icc 0 b1) (hx : midLowTail i k≤x) :
    (1801/2000:ℝ)< midLowCost i k b B x := by
  have hs := M_bounds hb
  have ht := L_bounds hB
  have hch := CorePairGeometry.charge_upper x
  cases i <;> cases k <;> dsimp [midLowTail,midLowCost,sign] at *
  all_goals linarith [L1_precise.2,M_endpoints.1,M_endpoints.2.2.2]

theorem low_mid_weaken_source (i k : Bool) {b B x : ℝ} (hb : b∈Icc 0 b1) :
    lowMidCost false k b B x≤lowMidCost i k b B x := by
  have hp := (L_bounds hb).1
  cases i <;> dsimp [lowMidCost,sign] <;> linarith

theorem mid_low_weaken_source (i k : Bool) {b B x : ℝ} (hb : b∈Icc b1 b2) :
    midLowCost false k b B x≤ midLowCost i k b B x := by
  have hp : 0≤M b := by linarith [(M_bounds hb).1,M_endpoints.1]
  cases i <;> dsimp [midLowCost,sign] <;> linarith

theorem state_low_mid_cost (s t : FramePair.State) (hs : s.branch=.low)
    (ht : t.branch=.middle) (x : ℝ) :
    s.cost t x=lowMidCost s.positive t.positive s.b t.b x := by
  rw [State.cost,state_low_label s hs,state_mid_label t ht]
  rfl

theorem state_mid_low_cost (s t : FramePair.State) (hs : s.branch=.middle)
    (ht : t.branch=.low) (x : ℝ) :
    s.cost t x=midLowCost s.positive t.positive s.b t.b x := by
  rw [State.cost,state_mid_label s hs,state_low_label t ht]
  rfl

theorem state_secondary (s t : FramePair.State)
    (ht : t.branch.type≠0) (x : ℝ) :
    s.Feasible t 0 x ↔ 0≤ secondary s.positive t.positive s.b t.b x := by
  simp only [State.Feasible,forwardMargin,Matrix.cons_val_zero,(state_outer_chart t ht).1]
  rfl

theorem state_primary (s t : FramePair.State)
    (hs : s.branch.type≠0) (ht : t.branch.type≠0) (x : ℝ) :
    s.Feasible t 3 x ↔ 0≤primary t.positive s.b t.b x := by
  simp only [State.Feasible,forwardMargin,Matrix.cons_val_succ,Matrix.cons_val_zero,
    (state_outer_chart s hs).1,(state_outer_chart t ht).1]
  rfl

end SquaresInCircles.Eight.TableFree.FrameLowMidGeometry

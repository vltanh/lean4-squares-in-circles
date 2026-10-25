module

public import Mathlib.Algebra.Order.Star.Real
public import SquaresInCircles.Eight.Frames.Pair.TransportAssembly
public import SquaresInCircles.Eight.Owners.GA.Owners
public import SquaresInCircles.Eight.Owners.GA.EZero

/-!
# Eight squares: the T primary-pair reduction inside a high-GA source domain

`reduce` moves T alone. The primary-pair theorems at the same radius give the new point of T and
both neighboring separators; the source domain gives their local hypotheses (`tPair`), with no
assumption on the GA owner. The order of the moved cycle (`TTransport.ordered`) then allows the
diagonal exclusion at the new point (`no_diagonal`), and the moved cycle is again a source domain
(`domain`). Every point, frame, owner and primary total of A and E is unchanged.
-/

section
/-!
## The high-GA boundary order after a primary-pair move of T

The five unchanged gaps keep their positive lifts. The two changed gaps are checked on the BT and
TD projections, and the two-square central-band theorem `positive_gap` selects the positive lift
(`ordered`). No normal GA owner is assumed.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.TTransport
open Candidate SignedCycle

/-- Only the feasible axis `j` on this edge is needed for the central band; it need not belong to
an owner family. -/
theorem direction_separation {q : ℝ} {C : SignedCycle}
    (hn : C.Necessary q) (hq : q≤qCap) (i : Vertex) (j : Fin 4)
    (hf : C.Feasible i j) :
    19/25<dist (C.polarAngle i : Direction) (C.polarAngle (next i) : Direction) := by
  have hr (k : Vertex) : 0<Real.sqrt ((C.point k).a^2+|(C.point k).y|^2) := by
    apply Real.sqrt_pos.mpr
    nlinarith [(hn.sorted k).1,sq_nonneg |(C.point k).y|]
  have hcore (k : Vertex) : CoreAvoiding (C.actualSquare k) :=
    (SignedPoint.square_core_iff (hn.sorted k) (C.actualAngle k)).2 (hn.core k)
  have haxis : (forwardAxis j).Feasible (C.actualSquare i) (C.actualSquare (next i)) :=
    (C.actualSquare_feasible i j).2 hf
  exact exterior_pair_gap (by simpa [qCap,Q0] using hq)
    (actualSquare_contained hn.sorted hn.contained i)
    (actualSquare_contained hn.sorted hn.contained (next i))
    (hcore i) (hcore (next i)) (hr i) (hr (next i))
    (actualSquare_polar hn.sorted i).1 (actualSquare_polar hn.sorted i).2
    (actualSquare_polar hn.sorted (next i)).1
    (actualSquare_polar hn.sorted (next i)).2 (SignedAxis.disjoint haxis)

private theorem negative_gap_distance (β : Vertex → ℝ) (i : Vertex)
    (hp : angleGap β i≤0) (hu : -angleGap β i≤Real.pi) :
    dist (β i : Direction) (β (next i) : Direction)= -angleGap β i := by
  have he : ((angleGap β i : ℝ) : Direction)=
      (β (next i) : Direction)-(β i : Direction) := by
    by_cases hi : i=6 <;>
      simp [angleGap,hi,Real.Angle.coe_add,Real.Angle.coe_sub,Real.Angle.coe_two_pi]
  have hn : ((-angleGap β i : ℝ) : Direction)=
      (β i : Direction)-(β (next i) : Direction) := by
    rw [Real.Angle.coe_neg,he,neg_sub]
  rw [direction_dist,←hn]
  exact Real.Angle.abs_toReal_coe_eq_self_iff.2 ⟨neg_nonneg.mpr hp,hu⟩

/-- A gap above the negative central band lies on the positive branch when the neighboring squares
are separated by a feasible axis. -/
theorem positive_gap {q : ℝ} {C : SignedCycle}
    (hn : C.Necessary q) (hq : q≤qCap) (i : Vertex) (j : Fin 4)
    (hf : C.Feasible i j) (hl : -(19/25:ℝ)<C.physicalGap i) :
    19/25<C.physicalGap i := by
  have hsep := direction_separation hn hq i j hf
  have hp : 0<C.physicalGap i := by
    by_contra! hnp
    have hg : angleGap C.polarAngle i≤0 := by rwa [polarAngle_gap]
    have hu : -angleGap C.polarAngle i≤Real.pi := by
      rw [polarAngle_gap]
      linarith [Real.pi_gt_three]
    rw [negative_gap_distance C.polarAngle i hg hu,polarAngle_gap] at hsep
    linarith
  by_contra! hsmall
  have hg : 0≤angleGap C.polarAngle i := by rw [polarAngle_gap]; exact hp.le
  have hu : angleGap C.polarAngle i≤Real.pi := by
    rw [polarAngle_gap]
    linarith [Real.pi_gt_three]
  rw [angleGap_direction_distance C.polarAngle i hg hu,polarAngle_gap] at hsep
  linarith

def owner {q : ℝ} {C : SignedCycle} (w : Vertex → Fin 4)
    (O : TPairOutput q (C.point B) (C.point D) (C.theta B) (C.theta T) (C.theta D)) :
    Vertex → Fin 4 := ![w H,w G,w A,O.btOwner,O.tdOwner,w D,w E]

theorem feasible {q : ℝ} {C : SignedCycle} (w : Vertex → Fin 4)
    (hf : ∀i,C.Feasible i (w i))
    (O : TPairOutput q (C.point B) (C.point D) (C.theta B) (C.theta T) (C.theta D)) :
    ∀i,(O.cycle C).Feasible i (owner w O i) := by
  intro i
  fin_cases i
  · simpa [owner,TPairOutput.cycle,replacePoint,Feasible,slack,edge,
      word,delta,next,H,G,T] using hf H
  · simpa [owner,TPairOutput.cycle,replacePoint,Feasible,slack,edge,
      word,delta,next,G,A,T] using hf G
  · simpa [owner,TPairOutput.cycle,replacePoint,Feasible,slack,edge,
      word,delta,next,A,B,T] using hf A
  · simpa [owner,TPairOutput.cycle,replacePoint,Feasible,slack,edge,
      word,delta,next,B,T,D,quarterFeasible] using sub_nonneg.mpr O.BT
  · simpa [owner,TPairOutput.cycle,replacePoint,Feasible,slack,edge,
      word,delta,next,B,T,D,zeroFeasible] using sub_nonneg.mpr O.TD
  · simpa [owner,TPairOutput.cycle,replacePoint,Feasible,slack,edge,
      word,delta,next,T,D,E] using hf D
  · simpa [owner,TPairOutput.cycle,replacePoint,Feasible,slack,edge,
      word,delta,next,H,T,E] using hf E

theorem allowed {q : ℝ} {C : SignedCycle} (w : Vertex → Fin 4)
    (hw : ∀i,w i∈highGAOwners i)
    (O : TPairOutput q (C.point B) (C.point D) (C.theta B) (C.theta T) (C.theta D)) :
    ∀i,owner w O i∈highGAOwners i := by
  intro i
  fin_cases i
  · simpa [owner,H] using hw H
  · simpa [owner,G] using hw G
  · simpa [owner,A] using hw A
  · rcases O.bt_allowed with h|h <;> simp [owner,h,highGAOwners,B]
  · rcases O.td_allowed with h|h <;> simp [owner,h,highGAOwners,T]
  · simpa [owner,D] using hw D
  · simpa [owner,E] using hw E

/-- The order of the cycle before the move is used only for the unchanged gaps. The changing TD
gap uses the TD owner after the move and its canceling-sign implication. -/
theorem ordered {q : ℝ} {C : SignedCycle}
    (hn : C.Necessary q) (ho : C.Ordered) (hq : q≤qCap)
    (hDy : (C.point D).y≤0) (w : Vertex → Fin 4)
    (hf : ∀i,C.Feasible i (w i))
    (O : TPairOutput q (C.point B) (C.point D) (C.theta B) (C.theta T) (C.theta D)) :
    (O.cycle C).Ordered := by
  let C' := O.cycle C
  have hn' : C'.Necessary q := O.necessary hn
  have hf' := feasible w hf O
  have hD' : (C'.point D).y≤0 := by
    simpa [C',TPairOutput.cycle,replacePoint,T,D] using hDy
  have hang := localAngle_mem hn'.sorted
  have hDangle := localAngle_nonpos (hn'.sorted D) hD'
  have hdelta (i : Vertex) : -(7/10:ℝ)≤delta C'.theta i :=
    (abs_le.mp (hn'.spread (next i) i)).1
  have hlow (i : Vertex) : -(19/25:ℝ)<C'.physicalGap i := by
    by_cases hiB : i=B
    · subst i
      have he : C'.physicalGap B=Real.pi/2+delta C'.theta B+
          C'.localAngle B-C'.localAngle T := by simp [physicalGap,word,next,B,T]
      rw [he]
      linarith [(hang B).1,(hang T).2,hdelta B]
    by_cases hiT : i=T
    · subst i
      have he : C'.physicalGap T=delta C'.theta T+C'.localAngle T-C'.localAngle D := by
        simp [physicalGap,word,next,T,D]
      rw [he]
      by_cases hy : 0≤(C'.point T).y
      · have hTangle := localAngle_nonneg (hn'.sorted T) hy
        linarith [hdelta T]
      · have hyneg : (C'.point T).y<0 := lt_of_not_ge hy
        have hj : O.tdOwner=2 := by
          rcases O.td_allowed with h|h
          · have hpos := O.canceling_normal h
            have hyO : O.point.y<0 := by
              simpa [C',TPairOutput.cycle,replacePoint] using hyneg
            linarith
          · exact h
        have hTD : zeroFeasible (C'.point T) (C'.point D) (delta C'.theta T) 2 := by
          simpa [C',TPairOutput.cycle,replacePoint,delta,next,T,D,hj] using O.TD
        have hDb := (SignedPoint.coordinate_bounds (hn'.sorted D)
          (hn'.core D) (hn'.contained D) hq).2.2
        have hTu := (SignedPoint.coordinate_bounds (hn'.sorted T)
          (hn'.core T) (hn'.contained T) hq).2.1
        have hd := td2_nonpositive_tangent_error_lower
          ((neg_le_abs _).trans_lt hDb) (hn'.sorted T).1 hTu hyneg.le
          (hn'.spread D T) hTD
        have hδ : delta C'.theta T=C'.theta D-C'.theta T := by simp [delta,next,T,D]
        linarith [(hang T).1,pi_lt_22_over_7]
    · have he : C'.physicalGap i=C.physicalGap i := by
        fin_cases i <;>
          simp [C',TPairOutput.cycle,replacePoint,physicalGap,localAngle,
            word,delta,next,B,T] at hiB hiT ⊢
      rw [he]
      linarith [ho.gap_pos i]
  have hlower (i : Vertex) : 19/25<C'.physicalGap i :=
    positive_gap hn' hq i (owner w O i) (hf' i) (hlow i)
  have hupper := seven_gaps_three_quarters C'.polarAngle (fun i => by
    rw [polarAngle_gap]
    exact hlower i)
  constructor
  · intro i
    linarith [hlower i]
  · intro i
    have hh := hupper i
    rw [polarAngle_gap] at hh
    linarith [Real.pi_pos]

end SquaresInCircles.Eight.GlobalGA.TTransport
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA
open Candidate SignedCycle

namespace SourceDomain

theorem TD0_positive {q : ℝ} {C : SignedCycle} (I : SourceDomain q C)
    (hq : q∈Icc (5/2:ℝ) qCap) (hTD : C.Feasible T 0) : 0<(C.point T).y := by
  have h := C.zero_owner_classification hq I.necessary I.ordered
    I.strict_spread I.radial I.owner I.feasible T (by norm_num [word,T]) 0 hTD
  rcases h with ⟨_,hy⟩|⟨hj,_⟩
  · exact hy
  · norm_num at hj

/-- The reflected local input uses only B, T and D; the high GA separator stays in the source
domain. -/
def tPair {q : ℝ} {C : SignedCycle} (I : SourceDomain q C)
    (hq : q∈Icc (5/2:ℝ) qCap) (hBT : C.Feasible B 3) :
    TPairInput q (C.point B) (C.point T) (C.point D)
      (C.theta B) (C.theta T) (C.theta D) where
  H_sorted := by simpa using I.necessary.sorted D
  G_sorted := by simpa using I.necessary.sorted T
  A_sorted := by simpa using I.necessary.sorted B
  H_contained := by simpa using I.necessary.contained D
  G_contained := by simpa using I.necessary.contained T
  A_contained := by simpa using I.necessary.contained B
  H_core := by simpa using I.necessary.core D
  G_core := by simpa using I.necessary.core T
  A_core := by simpa using I.necessary.core B
  G_boundary := by simpa using I.radial T
  A_outer := by simpa using I.outer B (by simp [H,G,B,D])
  H_normal := by simpa [SignedPoint.reflect] using neg_nonneg.mpr I.D_negative.le
  A_normal := by simpa [SignedPoint.reflect] using neg_nonneg.mpr I.B_negative.le
  HG_error := by simpa only [neg_sub_neg] using I.necessary.spread D T
  GA_error := by simpa only [neg_sub_neg] using I.necessary.spread T B
  HA_error := by simpa only [neg_sub_neg] using I.necessary.spread D B
  owner := reflectedOwner (I.owner T)
  owner_allowed := by
    have h : I.owner T=0 ∨ I.owner T=2 := by simpa [highGAOwners,T] using I.allowed T
    rcases h with h|h <;> simp [h,reflectedOwner]
  HG := by
    have h : zeroFeasible (C.point T) (C.point D)
        (C.theta D-C.theta T) (I.owner T) := by
      simpa [Feasible,slack,edge,word,delta,next,T,D,zeroFeasible,sub_nonneg]
        using I.feasible T
    simpa only [neg_sub_neg] using (zeroFeasible_reflect _ _ _ _).2 h
  GA := by
    have h : quarterFeasible (C.point B) (C.point T) (C.theta T-C.theta B) 3 := by
      simpa [Feasible,slack,edge,word,delta,next,B,T,quarterFeasible,sub_nonneg] using hBT
    have h2 := (quarterFeasible_reflect _ _ _ 3).2 h
    rw [show (-C.theta B)-(-C.theta T)=C.theta T-C.theta B by ring]
    exact h2
  canceling_normal := by
    intro h
    have hj : I.owner T=0 := by
      have ha : I.owner T=0 ∨ I.owner T=2 := by simpa [highGAOwners,T] using I.allowed T
      rcases ha with hj|hj
      · exact hj
      · simp [hj,reflectedOwner] at h
    have hpos := I.TD0_positive hq (by simpa [hj] using I.feasible T)
    simpa [SignedPoint.reflect] using neg_neg_of_pos hpos

def hardT {q : ℝ} {C : SignedCycle} (I : SourceDomain q C)
    (hq : q∈Icc (5/2:ℝ) qCap) (hBT : C.Feasible B 2) :
    TPairOutput q (C.point B) (C.point D) (C.theta B) (C.theta T) (C.theta D) where
  point := C.point T
  theta := C.theta T
  btOwner := 2
  tdOwner := I.owner T
  bt_allowed := Or.inl rfl
  td_allowed := by simpa [highGAOwners,T] using I.allowed T
  sorted := I.necessary.sorted T
  contained := I.necessary.contained T
  avoids := I.necessary.core T
  boundary := I.radial T
  BT := by
    simpa [Feasible,slack,edge,word,delta,next,B,T,quarterFeasible,sub_nonneg] using hBT
  TD := by
    simpa [Feasible,slack,edge,word,delta,next,T,D,zeroFeasible,sub_nonneg] using I.feasible T
  canceling_normal := fun h => I.TD0_positive hq (by simpa [h] using I.feasible T)
  frame_range := Or.inl rfl
  terminal := Or.inl rfl

end SourceDomain

namespace TTransport

/-- All high-GA data hold on the moved cycle; in particular the strict internal sorting comes from
the boundary geometry. -/
def domain {q : ℝ} {C : SignedCycle} (I : SourceDomain q C)
    (hq : q∈Icc (5/2:ℝ) qCap)
    (O : TPairOutput q (C.point B) (C.point D) (C.theta B) (C.theta T) (C.theta D)) :
    SourceDomain q (O.cycle C) := by
  have hn := O.necessary I.necessary
  have ho := ordered I.necessary I.ordered hq.2 I.D_negative.le I.owner I.feasible O
  have hs : (O.cycle C).StrictSpread :=
    strictSpread_replace_clamped (v:=T) (a:=B) (b:=D) I.strict_spread O.frame_range
  have hr : ∀i,((O.cycle C).point i).Boundary q :=
    radial_replace (v:=T) (t:=O.theta) I.radial O.boundary
  have hf := feasible I.owner I.feasible O
  have hsort := ((O.cycle C).nearest_axis_tie_locations hq hn ho hs hr
    (owner I.owner O) hf).1
  refine {
    owner := owner I.owner O
    feasible := hf
    allowed := allowed I.owner I.allowed O
    necessary := hn
    ordered := ho
    strict_spread := hs
    positive_variation := O.variations.1.trans_lt I.positive_variation
    negative_variation := O.variations.2.trans_lt I.negative_variation
    radial := hr
    outer := ?_
    H_positive := by simpa [TPairOutput.cycle,replacePoint,T,H] using I.H_positive
    G_negative := by simpa [TPairOutput.cycle,replacePoint,T,G] using I.G_negative
    B_negative := by simpa [TPairOutput.cycle,replacePoint,T,B] using I.B_negative
    D_negative := by simpa [TPairOutput.cycle,replacePoint,T,D] using I.D_negative
    E_nonpos := by simpa [TPairOutput.cycle,replacePoint,T,E] using I.E_nonpos
    A_upper := by simpa [TPairOutput.cycle,replacePoint,T,A] using I.A_upper
    A_nonpos_outer := ?_
    internal_sorted := hsort }
  · intro i hi
    have hiT : i≠T := by
      simp only [Finset.mem_insert,Finset.mem_singleton] at hi
      rcases hi with rfl|rfl|rfl|rfl <;> decide
    simpa [TPairOutput.cycle,replacePoint,hiT] using I.outer i hi
  · intro h
    have hh : (C.point A).y≤0 := by simpa [TPairOutput.cycle,replacePoint,T,A] using h
    simpa [TPairOutput.cycle,replacePoint,T,A] using I.A_nonpos_outer hh

theorem point_other {q : ℝ} {C : SignedCycle}
    (O : TPairOutput q (C.point B) (C.point D) (C.theta B) (C.theta T) (C.theta D))
    (i : Vertex) (hi : i≠T) : (O.cycle C).point i=C.point i := by
  simp [TPairOutput.cycle,replacePoint,hi]

theorem theta_other {q : ℝ} {C : SignedCycle}
    (O : TPairOutput q (C.point B) (C.point D) (C.theta B) (C.theta T) (C.theta D))
    (i : Vertex) (hi : i≠T) : (O.cycle C).theta i=C.theta i := by
  simp [TPairOutput.cycle,replacePoint,hi]

theorem owner_other {q : ℝ} {C : SignedCycle} (w : Vertex → Fin 4)
    (O : TPairOutput q (C.point B) (C.point D) (C.theta B) (C.theta T) (C.theta D))
    (i : Vertex) (hi : i≠B ∧ i≠T) : owner w O i=w i := by
  fin_cases i <;> simp [owner,B,T,H,G,A,D,E] at hi ⊢

theorem no_diagonal {q : ℝ} {C : SignedCycle} (I : SourceDomain q C)
    (hq : q∈Icc (5/2:ℝ) qCap)
    (O : TPairOutput q (C.point B) (C.point D) (C.theta B) (C.theta T) (C.theta D)) :
    O.point.y≠O.point.a := by
  intro hd
  have hs := (domain I hq O).internal_sorted T (by simp)
  have hh : |O.point.y|<O.point.a := by
    simpa [TPairOutput.cycle,replacePoint] using hs
  rw [hd,abs_of_pos O.sorted.1] at hh
  exact lt_irrefl _ hh

/-- At a TD alignment the two weak zero owners tie; this changes only the selected index, once both
projections are equal. -/
def selectTD0 {q : ℝ} {C : SignedCycle}
    (O : TPairOutput q (C.point B) (C.point D) (C.theta B) (C.theta T) (C.theta D))
    (ht : O.theta=C.theta D) (hy : 0<O.point.y) :
    TPairOutput q (C.point B) (C.point D) (C.theta B) (C.theta T) (C.theta D) :=
  { O with
    tdOwner := 0
    td_allowed := Or.inl rfl
    TD := by
      have h := O.TD
      rw [ht,sub_self] at h ⊢
      rcases O.td_allowed with hj|hj
      · simpa [hj] using h
      · exact (zero_owner_tie _ _).2 (by simpa [hj] using h)
    canceling_normal := fun _ => hy
    terminal := by
      rcases O.terminal with h|⟨hb,_,hp⟩|⟨hb,he,hn,hp⟩|h
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨hb,rfl,hp⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨hb,he,hn,hp⟩))
      · exact Or.inr (Or.inr (Or.inr h)) }

structure Result (q : ℝ) (C : SignedCycle) where
  output : TPairOutput q (C.point B) (C.point D) (C.theta B) (C.theta T) (C.theta D)
  source : SourceDomain q (output.cycle C)
  terminal : output.btOwner=2 ∨
    (output.btOwner=3 ∧ output.tdOwner=0 ∧ 0<output.theta-C.theta B) ∨
    (output.btOwner=3 ∧ output.tdOwner=0 ∧ output.theta=C.theta D ∧
      output.theta-C.theta B<0 ∧ 0<output.point.y)

/-- The T dispatch: BT2, a single positive BT3, or a single negative BT3 at the frame of D. The
local primary-pair reduction covers both signed-cancellation orders and weak ties. -/
theorem reduce {q : ℝ} {C : SignedCycle} (I : SourceDomain q C)
    (hqL : qLow≤q) (hqU : q≤qCap) : Nonempty (Result q C) := by
  have hq : q∈Icc (5/2:ℝ) qCap := ⟨by norm_num [qLow] at hqL ⊢; linarith,hqU⟩
  by_cases hBT : C.Feasible B 2
  · let O := I.hardT hq hBT
    exact ⟨⟨O,domain I hq O,Or.inl rfl⟩⟩
  have hprimary : C.Feasible B 3 := by
    have hh : I.owner B=2 ∨ I.owner B=3 := by simpa [highGAOwners,B] using I.allowed B
    rcases hh with hh|hh
    · exact (hBT (by simpa [hh] using I.feasible B)).elim
    · simpa [hh] using I.feasible B
  obtain ⟨O⟩ := preprocess_T_pair hqL hqU (I.tPair hq hprimary)
  rcases O.terminal with hb|⟨hb,ht,hp⟩|⟨hb,he,hn,hy⟩|hd
  · exact ⟨⟨O,domain I hq O,Or.inl hb⟩⟩
  · exact ⟨⟨O,domain I hq O,Or.inr (Or.inl ⟨hb,ht,hp⟩)⟩⟩
  · let P := selectTD0 O he hy
    exact ⟨⟨P,domain I hq P,Or.inr (Or.inr ⟨hb,rfl,he,hn,hy⟩)⟩⟩
  · exact (no_diagonal I hq O hd).elim

end TTransport
end SquaresInCircles.Eight.GlobalGA
end
end
end

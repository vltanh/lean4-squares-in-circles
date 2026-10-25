module

public import SquaresInCircles.Eight.Owners.GA.SourceDomain
public import SquaresInCircles.Eight.Owners.GA.Transport.Order

/-!
# Eight squares: the T primary-pair reduction inside a high-GA source domain

`reduce` moves T alone. The primary-pair theorems at the same radius give the new point of T and
both neighboring separators; the source domain gives their local hypotheses (`tPair`), with no
assumption on the GA owner. The order of the moved cycle (`TTransport.ordered`) then allows the
diagonal exclusion at the new point (`no_diagonal`), and the moved cycle is again a source domain
(`domain`). Every point, frame, owner and primary total of A and E is unchanged.
-/

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

module
public import SquaresInCircles.Six.Stress.FixedData.Checks

@[expose] public section

/-!
# Exact coverage of unions of fixed-row domains

This checker proves only domain coverage, not positivity. Leaves refer to the
separately proved fixed rows. Splits occur at exact row endpoints, so shared
non-dyadic boundaries cannot fall between mesh cells. Real coverage follows
from the total order on each coordinate; no sampled rectangle union is used.
-/

namespace SquaresInCircles.Six.Stress
open ProofTools FixedData

namespace PiBound

def upperDifference (a b : PiBound) : ℚ :=
  a.rational-b.rational+(a.piCoeff-b.piCoeff)*
    (if 0≤a.piCoeff-b.piCoeff then RInterval.piInterval.hi else RInterval.piInterval.lo)

def leCheck (a b : PiBound) : Bool := decide (upperDifference a b≤0)
def ltCheck (a b : PiBound) : Bool := decide (upperDifference a b<0)

lemma value_sub_le_upperDifference (a b : PiBound) :
    a.value-b.value≤(upperDifference a b:ℝ) := by
  have hpi := RInterval.mem_piInterval
  unfold upperDifference
  split_ifs with h
  · have hc : (0:ℝ)≤(a.piCoeff:ℝ)-b.piCoeff := by exact_mod_cast h
    have hm := mul_le_mul_of_nonneg_left hpi.2 hc
    dsimp [value]
    push_cast
    linarith
  · have hc : (a.piCoeff:ℝ)-b.piCoeff≤0 := by exact_mod_cast (le_of_not_ge h)
    have hm := mul_le_mul_of_nonpos_left hpi.1 hc
    dsimp [value]
    push_cast
    linarith

lemma leCheck_sound {a b : PiBound} (h : a.leCheck b=true) : a.value≤b.value := by
  have hc : upperDifference a b≤0 := of_decide_eq_true h
  have hc' : (upperDifference a b:ℝ)≤0 := by exact_mod_cast hc
  linarith [value_sub_le_upperDifference a b]

lemma ltCheck_sound {a b : PiBound} (h : a.ltCheck b=true) : a.value<b.value := by
  have hc : upperDifference a b<0 := of_decide_eq_true h
  have hc' : (upperDifference a b:ℝ)<0 := by exact_mod_cast hc
  linarith [value_sub_le_upperDifference a b]
end PiBound

abbrev PiBox := Fin 3 → PiBound × PiBound

namespace PiBox
noncomputable def Mem (B : PiBox) (x : Fin 3 → ℝ) : Prop :=
  ∀ i,(B i).1.value≤x i ∧ x i≤(B i).2.value

def within (outer inner : PiBox) : Bool :=
  decide (∀ i : Fin 3, (outer i).1.leCheck (inner i).1=true ∧
    (inner i).2.leCheck (outer i).2=true)

lemma within_sound {outer inner : PiBox} (h : within outer inner=true)
    {x : Fin 3 → ℝ} (hx : inner.Mem x) : outer.Mem x := by
  have hh : ∀ i : Fin 3, (outer i).1.leCheck (inner i).1=true ∧
      (inner i).2.leCheck (outer i).2=true := of_decide_eq_true h
  intro i
  exact ⟨(PiBound.leCheck_sound (hh i).1).trans (hx i).1,
    (hx i).2.trans (PiBound.leCheck_sound (hh i).2)⟩

def lower (B : PiBox) (i : Fin 3) (cut : PiBound) : PiBox :=
  Function.update B i ((B i).1,cut)
def upper (B : PiBox) (i : Fin 3) (cut : PiBound) : PiBox :=
  Function.update B i (cut,(B i).2)

lemma mem_lower {B : PiBox} {x : Fin 3 → ℝ} (hx : B.Mem x) {i : Fin 3} {cut : PiBound}
    (hi : x i≤cut.value) : (lower B i cut).Mem x := by
  intro j
  by_cases h : j=i
  · subst j
    simpa [lower] using And.intro (hx i).1 hi
  · simpa [lower,h] using hx j

lemma mem_upper {B : PiBox} {x : Fin 3 → ℝ} (hx : B.Mem x) {i : Fin 3} {cut : PiBound}
    (hi : cut.value≤x i) : (upper B i cut).Mem x := by
  intro j
  by_cases h : j=i
  · subst j
    simpa [upper] using And.intro hi (hx i).2
  · simpa [upper,h] using hx j
end PiBox

structure GraphChoice where
  westOwn : Bool
  southOwn : Bool
  wdAxis : Fin 8
  dsAxis : Fin 8
  deriving DecidableEq

namespace GraphChoice

def Matches (g : GraphChoice) (s : FixedSpec) : Prop :=
  (s.weight 0≠0 → g.westOwn=(!s.westCardinal)) ∧
  (s.weight 1≠0 → g.southOwn=(!s.southCardinal)) ∧
  (s.weight 3≠0 → s.wdAxis=g.wdAxis) ∧
  (s.weight 4≠0 → s.dsAxis=g.dsAxis)

instance (g : GraphChoice) (s : FixedSpec) : Decidable (g.Matches s) := by
  unfold Matches
  infer_instance

lemma realized_of_matches {g : GraphChoice} {s : FixedSpec} (h : g.Matches s)
    {R : ℝ} (P : Normalization.NormalizedPacking R)
    (hW : P.ownBits 2=g.westOwn) (hS : P.ownBits 4=g.southOwn)
    (hwd : Seven.SAT.threshold (P.square 2) (P.square 3) ≤
      dot (Stress.pairNormal g.wdAxis (P.square 2) (P.square 3))
        (sub (P.square 3).center (P.square 2).center))
    (hds : Seven.SAT.threshold (P.square 3) (P.square 4) ≤
      dot (Stress.pairNormal g.dsAxis (P.square 3) (P.square 4))
        (sub (P.square 4).center (P.square 3).center)) : s.Realized P := by
  refine ⟨fun hz => hW.trans (h.1 hz),fun hz => hS.trans (h.2.1 hz),?_,?_⟩
  · intro hz
    simpa only [h.2.2.1 hz] using hwd
  · intro hz
    simpa only [h.2.2.2 hz] using hds
end GraphChoice

namespace ExactCover

def rows : List RowId :=
  (List.finRange 59).map RowId.main ++ (List.finRange 53).map RowId.hard ++
    (List.finRange 3).map RowId.tail ++ (List.finRange 99).map RowId.app

def qualifies (g : GraphChoice) (B : PiBox) (i : RowId) : Bool :=
  decide (g.Matches i.row.spec) && PiBox.within i.row.limits B

def pick (g : GraphChoice) (B : PiBox) : List RowId → Option RowId
  | [] => none
  | i::is => if qualifies g B i then some i else pick g B is

lemma pick_sound {g : GraphChoice} {B : PiBox} {is : List RowId} {i : RowId}
    (h : pick g B is=some i) : g.Matches i.row.spec ∧ PiBox.within i.row.limits B=true := by
  induction is with
  | nil => cases h
  | cons j js ih =>
    simp only [pick] at h
    split_ifs at h with hj
    · cases h
      have hh := Bool.and_eq_true.mp hj
      exact ⟨of_decide_eq_true hh.1,hh.2⟩
    · exact ih h

/-- All possible row boundaries; duplicate cuts affect speed, never soundness. -/
def cuts : List (Fin 3 × PiBound) := rows.flatMap (fun r =>
  (List.finRange 3).flatMap (fun i => [(i,(r.row.limits i).1),(i,(r.row.limits i).2)]))

def interiorCut (B : PiBox) (c : Fin 3 × PiBound) : Bool :=
  (B c.1).1.ltCheck c.2 && c.2.ltCheck (B c.1).2

def pickCut (B : PiBox) : List (Fin 3 × PiBound) → Option (Fin 3 × PiBound)
  | [] => none
  | c::cs => if interiorCut B c then some c else pickCut B cs

def certify (g : GraphChoice) : ℕ → PiBox → Bool
  | 0, B => (pick g B rows).isSome
  | fuel+1, B =>
      match pick g B rows with
      | some _ => true
      | none => match pickCut B cuts with
        | none => false
        | some (i,c) => certify g fuel (PiBox.lower B i c) && certify g fuel (PiBox.upper B i c)

/-- Successful coverage returns a genuinely applicable row for every real point. -/
theorem certify_sound (g : GraphChoice) (fuel : ℕ) {B : PiBox}
    (h : certify g fuel B=true) {x : Fin 3 → ℝ} (hx : B.Mem x) (horder : x 0≤x 2) :
    ∃ i : RowId, g.Matches i.row.spec ∧ i.row.InDomain (x 0) (x 1) (x 2) := by
  have selected {i : RowId} (hp : pick g B rows=some i) :
      g.Matches i.row.spec ∧ i.row.InDomain (x 0) (x 1) (x 2) := by
    have hh := pick_sound hp
    have hm := PiBox.within_sound hh.2 hx
    refine ⟨hh.1,?_,fun _ => horder⟩
    intro j
    fin_cases j
    · exact hm 0
    · exact hm 1
    · exact hm 2
  induction fuel generalizing B with
  | zero =>
    cases hp : pick g B rows with
    | none => simp [certify,hp] at h
    | some i => exact ⟨i,selected hp⟩
  | succ fuel ih =>
    cases hp : pick g B rows with
    | some i => exact ⟨i,selected hp⟩
    | none =>
      cases hc : pickCut B cuts with
      | none => simp [certify,hp,hc] at h
      | some c =>
        have hh : certify g fuel (PiBox.lower B c.1 c.2)=true ∧
            certify g fuel (PiBox.upper B c.1 c.2)=true := by
          simpa only [certify,hp,hc,Bool.and_eq_true] using h
        by_cases hl : x c.1≤c.2.value
        · exact ih hh.1 (PiBox.mem_lower hx hl)
        · exact ih hh.2 (PiBox.mem_upper hx (le_of_not_ge hl))

/-- The coverage checker never supplies a new geometric premise. -/
theorem excludes (g : GraphChoice) (fuel : ℕ) (B : PiBox)
    (h : certify g fuel B=true) {R : ℝ} (P : Normalization.NormalizedPacking R)
    (hW : P.ownBits 2=g.westOwn) (hS : P.ownBits 4=g.southOwn)
    (hwd : Seven.SAT.threshold (P.square 2) (P.square 3) ≤
      dot (Stress.pairNormal g.wdAxis (P.square 2) (P.square 3))
        (sub (P.square 3).center (P.square 2).center))
    (hds : Seven.SAT.threshold (P.square 3) (P.square 4) ≤
      dot (Stress.pairNormal g.dsAxis (P.square 3) (P.square 4))
        (sub (P.square 4).center (P.square 3).center))
    (hx : B.Mem ![P.helperAngle 2,P.helperAngle 4,P.diagonalAngle])
    (horder : P.helperAngle 2≤P.diagonalAngle) : False := by
  obtain ⟨i,hm,hd⟩ := certify_sound g fuel h hx horder
  exact i.excludes P (g.realized_of_matches hm P hW hS hwd hds) hd

end ExactCover
end SquaresInCircles.Six.Stress

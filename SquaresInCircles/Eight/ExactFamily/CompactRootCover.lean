module

public import SquaresInCircles.Eight.ExactFamily.RootCover
public import SquaresInCircles.Eight.ExactFamily.IntervalEnclosure

/-!
# Historical stationary-cover search

The active stationary proof uses `GeometricStationary.stationary_chain_unique`.
This generic search is retained only for the historical generator. It is
not imported by the active Eight proof, and no stationary-cover decision
is instantiated here. Fixed adaptive bounds use `IntervalEnclosure` directly.
This source remains uncompiled.
-/

@[expose] public section
namespace SquaresInCircles.Eight.ExactFamily.CompactRootCover
open Arithmetic

export IntervalEnclosure (precision denominator outward rootProposal proposeAt
  checkedRangeAt checkedRange boundedAt checkedRangeAt_sound checkedRange_sound boundedAt_sound)

/-- The inclusion test uses weak endpoints in every coordinate. -/
def inside (B target : QBox 3) : Bool :=
  decide (∀ i, (target i).lo ≤ (B i).lo ∧ (B i).hi ≤ (target i).hi)

def excludes (B : QBox 3) (f : Formula 3) : Bool :=
  match checkedRange B f with
  | none => false
  | some I => decide (I.hi < 0 ∨ 0 < I.lo)

/-- Dimension weights are the original generator's coordinate scaling. -/
def scale : Fin 3 → ℚ := ![8, 1, 3]

def splitAxis (B : QBox 3) : Fin 3 :=
  (List.finRange 3).foldl (fun i j =>
    if ((B i).hi - (B i).lo) * scale i < ((B j).hi - (B j).lo) * scale j
    then j else i) 0

def midpoint (B : QBox 3) (i : Fin 3) : ℚ := ((B i).lo + (B i).hi) / 2

/-- A failed leaf returns false. Both closed children must succeed. -/
def certify (targets : Fin 3 → Formula 3) (target : QBox 3) : ℕ → QBox 3 → Bool
  | fuel, B =>
      if inside B target then true
      else if (List.finRange 3).any (fun i => excludes B (targets i)) then true
      else match fuel with
        | 0 => false
        | fuel + 1 =>
            let i := splitAxis B
            let c := midpoint B i
            certify targets target fuel (B.left i c) &&
              certify targets target fuel (B.right i c)

noncomputable section

theorem excluded_not_zero {B : QBox 3} {f : Formula 3}
    (hc : excludes B f = true) {env : Fin 3 → ℝ} (he : B.Mem env) :
    f.eval env ≠ 0 := by
  cases hI : checkedRange B f with
  | none => simp [excludes, hI] at hc
  | some I =>
      have hs : I.hi < 0 ∨ 0 < I.lo := by simpa [excludes, hI] using hc
      have hb := checkedRange_sound hI he
      intro hz
      rw [hz] at hb
      rcases hs with hs | hs
      · have hn : (I.hi : ℝ) < 0 := by exact_mod_cast hs
        linarith [hb.2]
      · have hn : (0 : ℝ) < I.lo := by exact_mod_cast hs
        linarith [hb.1]

/-- The entire localization proof, independent of the number of boxes. -/
theorem sound (targets : Fin 3 → Formula 3) (target : QBox 3) (fuel : ℕ)
    (B : QBox 3) (hc : certify targets target fuel B = true)
    (env : Fin 3 → ℝ) (he : B.Mem env) (hz : SimultaneousZeros targets env) :
    target.Mem env := by
  induction fuel generalizing B env with
  | zero =>
      by_cases hi : inside B target = true
      · exact box_mem_of_subset (by simpa [inside] using hi) he
      · have hx : (List.finRange 3).any (fun i => excludes B (targets i)) = true := by
          simpa [certify, hi] using hc
        obtain ⟨i, _, hxi⟩ := List.any_eq_true.mp hx
        exact False.elim (excluded_not_zero hxi he (hz i))
  | succ fuel ih =>
      by_cases hi : inside B target = true
      · exact box_mem_of_subset (by simpa [inside] using hi) he
      · by_cases hx : (List.finRange 3).any (fun i => excludes B (targets i)) = true
        · obtain ⟨i, _, hxi⟩ := List.any_eq_true.mp hx
          exact False.elim (excluded_not_zero hxi he (hz i))
        · have hchildren :
              certify targets target fuel (B.left (splitAxis B) (midpoint B (splitAxis B))) = true ∧
              certify targets target fuel (B.right (splitAxis B) (midpoint B (splitAxis B))) = true := by
            simpa [certify, hi, hx] using hc
          exact closed_box_split B (splitAxis B) (midpoint B (splitAxis B))
            (P := fun x => SimultaneousZeros targets x → target.Mem x)
            (fun x hx hxz => ih _ hchildren.1 x hx hxz)
            (fun x hx hxz => ih _ hchildren.2 x hx hxz) env he hz

end
end SquaresInCircles.Eight.ExactFamily.CompactRootCover

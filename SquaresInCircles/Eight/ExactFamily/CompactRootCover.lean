module

public import SquaresInCircles.Eight.ExactFamily.RootCover

/-!
# A single interval argument for the stationary cover

The old source printed the same radical expressions and closed-box argument
at 22,601 nodes. Here the expressions are written once, interval endpoints
are computed by one exact rational routine, and soundness is proved once.

The rounding and search code are not trusted: `checkedRange` accepts an
expression only after `FormulaCertificate.Valid` checks its complete syntax
and interval arithmetic. No floating-point operation or external success flag
is used. This source has not been compiled.
-/

@[expose] public section
namespace SquaresInCircles.Eight.ExactFamily.CompactRootCover
open Arithmetic

/-- The dyadic precision used by the original stationary-cover generator. -/
def precision : ℕ := 40

def denominator : ℕ := 2 ^ precision

private def floorRat (x : ℚ) : ℤ := x.num / (x.den : ℤ)

private def roundDown (x : ℚ) : ℚ :=
  (floorRat (x * denominator) : ℚ) / denominator

private def roundUp (x : ℚ) : ℚ := -roundDown (-x)

def outward (I : QInterval) : QInterval := ⟨roundDown I.lo, roundUp I.hi⟩

private def rootFloor (x : ℚ) : ℕ :=
  Nat.sqrt ((x.num.toNat * denominator ^ 2) / x.den)

/-- An untrusted proposed bracket; the scalar certificate checks it. -/
def rootProposal (I : QInterval) : QInterval :=
  let lo := rootFloor I.lo
  let hi := rootFloor I.hi
  let upper := if (hi : ℚ) ^ 2 / (denominator : ℚ) ^ 2 < I.hi then hi + 1 else hi
  ⟨(lo : ℚ) / denominator, (upper : ℚ) / denominator⟩

private def enclose {n : ℕ} (B : QBox n) (e : ScalarExpr n) : ScalarExpr n :=
  .enclose e (outward (e.range B))

/-- Translate a formula without printing its algebraic expansion at every box.
Failed positive-denominator or real-radical tests reject the proposal. -/
def propose {n : ℕ} (B : QBox n) : Formula n → Option (ScalarExpr n)
  | .const q => some (.const q)
  | .var i => some (.var i)
  | .add a b => do return enclose B (.add (← propose B a) (← propose B b))
  | .neg a => do return enclose B (.neg (← propose B a))
  | .mul a b => do return enclose B (.mul (← propose B a) (← propose B b))
  | .inv a => do
      let e ← propose B a
      if 0 < (e.range B).lo then some (enclose B (.inv e)) else none
  | .sqrt a => do
      let e ← propose B a
      if 0 ≤ (e.range B).lo then some (.sqrt e (rootProposal (e.range B))) else none
  | .pow a k => do return enclose B (.pow (← propose B a) k)

/-- The guard includes expression identity as well as interval validity.
A mistake in `propose`, rounding, or branch selection cannot become a premise. -/
def checkedRange {n : ℕ} (B : QBox n) (f : Formula n) : Option QInterval :=
  match propose B f with
  | none => none
  | some e =>
      if (FormulaCertificate.mk e).Valid B f then some (e.range B) else none

noncomputable section

theorem checkedRange_sound {n : ℕ} {B : QBox n} {f : Formula n} {I : QInterval}
    (hc : checkedRange B f = some I) {env : Fin n → ℝ} (he : B.Mem env) :
    I.Mem (f.eval env) := by
  unfold checkedRange at hc
  cases hp : propose B f with
  | none => simp [hp] at hc
  | some e =>
      rw [hp] at hc
      split_ifs at hc with hv
      · cases Option.some.inj hc
        exact (FormulaCertificate.mk e).sound hv he
      · simp at hc

end

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

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

def denominator (bits : ℕ) : ℕ := 2 ^ bits

private def floorRat (x : ℚ) : ℤ := x.num / (x.den : ℤ)

private def roundDown (bits : ℕ) (x : ℚ) : ℚ :=
  (floorRat (x * denominator bits) : ℚ) / denominator bits

private def roundUp (bits : ℕ) (x : ℚ) : ℚ := -roundDown bits (-x)

def outward (bits : ℕ) (I : QInterval) : QInterval :=
  ⟨roundDown bits I.lo, roundUp bits I.hi⟩

private def rootFloor (bits : ℕ) (x : ℚ) : ℕ :=
  Nat.sqrt ((x.num.toNat * denominator bits ^ 2) / x.den)

/-- An untrusted proposed bracket; the scalar certificate checks it. -/
def rootProposal (bits : ℕ) (I : QInterval) : QInterval :=
  let lo := rootFloor bits I.lo
  let hi := rootFloor bits I.hi
  let upper := if (hi : ℚ) ^ 2 / (denominator bits : ℚ) ^ 2 < I.hi then hi + 1 else hi
  ⟨(lo : ℚ) / denominator bits, (upper : ℚ) / denominator bits⟩

private def enclose {n : ℕ} (bits : ℕ) (B : QBox n) (e : ScalarExpr n) : ScalarExpr n :=
  .enclose e (outward bits (e.range B))

/-- One translator for the root cover and all adaptive boxes. Failed
positive-denominator or real-radical tests reject the proposal. -/
def proposeAt {n : ℕ} (bits : ℕ) (B : QBox n) : Formula n → Option (ScalarExpr n)
  | .const q => some (.const q)
  | .var i => some (.var i)
  | .add a b => do return enclose bits B (.add (← proposeAt bits B a) (← proposeAt bits B b))
  | .neg a => do return enclose bits B (.neg (← proposeAt bits B a))
  | .mul a b => do return enclose bits B (.mul (← proposeAt bits B a) (← proposeAt bits B b))
  | .inv a => do
      let e ← proposeAt bits B a
      if 0 < (e.range B).lo then some (enclose bits B (.inv e)) else none
  | .sqrt a => do
      let e ← proposeAt bits B a
      if 0 ≤ (e.range B).lo then some (.sqrt e (rootProposal bits (e.range B))) else none
  | .pow a k => do return enclose bits B (.pow (← proposeAt bits B a) k)

/-- The guard checks the whole formula identity and every interval operation.
Changing precision does not change the proposition being proved. -/
def checkedRangeAt {n : ℕ} (bits : ℕ) (B : QBox n) (f : Formula n) : Option QInterval :=
  match proposeAt bits B f with
  | none => none
  | some e =>
      if (FormulaCertificate.mk e).Valid B f then some (e.range B) else none

def checkedRange {n : ℕ} (B : QBox n) (f : Formula n) : Option QInterval :=
  checkedRangeAt precision B f

/-- A bound is accepted only when the checked interval is inside it. -/
def boundedAt {n : ℕ} (bits : ℕ) (B : QBox n) (f : Formula n) (target : QInterval) : Bool :=
  match checkedRangeAt bits B f with
  | none => false
  | some I => decide (target.lo ≤ I.lo ∧ I.hi ≤ target.hi)

noncomputable section

theorem checkedRangeAt_sound {n bits : ℕ} {B : QBox n} {f : Formula n} {I : QInterval}
    (hc : checkedRangeAt bits B f = some I) {env : Fin n → ℝ} (he : B.Mem env) :
    I.Mem (f.eval env) := by
  cases hp : proposeAt bits B f with
  | none => simp [checkedRangeAt,hp] at hc
  | some e =>
      have hh : (if (FormulaCertificate.mk e).Valid B f then some (e.range B) else none) = some I := by
        simpa only [checkedRangeAt,hp] using hc
      split_ifs at hh with hv
      · cases Option.some.inj hh
        exact FormulaCertificate.sound hv he
      · simp at hh

theorem checkedRange_sound {n : ℕ} {B : QBox n} {f : Formula n} {I : QInterval}
    (hc : checkedRange B f = some I) {env : Fin n → ℝ} (he : B.Mem env) :
    I.Mem (f.eval env) := checkedRangeAt_sound hc he

theorem boundedAt_sound {n bits : ℕ} {B : QBox n} {f : Formula n} {target : QInterval}
    (hc : boundedAt bits B f target = true) {env : Fin n → ℝ} (he : B.Mem env) :
    target.Mem (f.eval env) := by
  cases hI : checkedRangeAt bits B f with
  | none => simp [boundedAt,hI] at hc
  | some I =>
      have hb : target.lo ≤ I.lo ∧ I.hi ≤ target.hi := by
        simpa [boundedAt,hI] using hc
      exact QInterval.mem_mono (checkedRangeAt_sound hI he) hb.1 hb.2

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

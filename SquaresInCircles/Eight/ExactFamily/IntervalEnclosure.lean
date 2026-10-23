module

public import SquaresInCircles.Eight.ExactFamily.Expression

/-!
# Checked interval bounds on a fixed box

This module proposes an exact rational enclosure for one formula on one
specified box and checks every arithmetic operation against that formula.
Its soundness theorem is independent of rounding precision. There is no
root localization or recursive box search here.

The retained adaptive estimates use this utility on their original 256
boxes. Those finite decision obligations remain; extracting the utility
is dependency cleanup, not a geometric replacement of those estimates.
This source remains uncompiled.
-/

@[expose] public section
namespace SquaresInCircles.Eight.ExactFamily.IntervalEnclosure
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

/-- Translate a formula on one fixed box. Failed positive-denominator
or real-radical tests reject the proposal. No box subdivision occurs. -/
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

end SquaresInCircles.Eight.ExactFamily.IntervalEnclosure

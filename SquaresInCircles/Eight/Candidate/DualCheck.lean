module

public import SquaresInCircles.Eight.Candidate.Dual

/-!
# Eight squares: checking dual rows by evaluation

A row of `Candidate/Dual.lean` is valid when its multipliers have the right signs and the
quartic `Row.quartic` is positive on its interval, which is shown by Bernstein coefficients.
In the tables every multiplier is an integer multiple of `10⁻⁸` and every interval is
`[a / d, b / d]` with integers `a < b` and `d > 0`. A table row is therefore stored as a
`Line` of natural numbers, and `Line.row` is its `Row`.

The quartic is computed from the line with natural-number arithmetic, which the kernel
evaluates fastest: an integer is a pair `pos - neg` (`SNat`), the polynomials of degree two and
four are `P2` and `P4`, and their operations call `Nat.add` and `Nat.mul` directly rather than
through the instances of `+` and `*`. A line keeps the multipliers of each vertex in one record
(`VRow`), so that the kernel looks a vertex up once, and only the edges `j` and `prev j` enter
the forces at the vertex `j` (`sum_edges`). Clearing denominators, the computed forces,
right-hand side and quartic are those of the row times `forceScale = 2·10¹²`,
`rhsScale = 2.4·10¹⁸` and `Line.M = 12 forceScale² ∏ᵢ 10⁸ μᵢ` (`Line.quarticN_toPoly`), and the
computed Bernstein coefficients are those of the row's quartic on `[a / d, b / d]` times
`12 d⁴ Line.M`. `Line.check_sound` reduces the validity of `Line.row` to a Boolean test of
natural-number inequalities, and `OwnerTable.ofLines` and `TiltBundle.ofLines` build a table and
a bundle from lines whose tests the kernel evaluates.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
open Polynomial (C X)
namespace SquaresInCircles.Eight.Candidate.Dual

open Arithmetic

@[simp] theorem listPoly_nil : listPoly [] = 0 := rfl

@[simp] theorem listPoly_cons (a : ℚ) (p : List ℚ) :
    listPoly (a :: p) = C a + X * listPoly p := rfl

theorem listPoly_map_div (M : ℚ) : ∀ p : List ℚ,
    listPoly (p.map (· / M)) = C M⁻¹ * listPoly p
  | [] => by simp
  | a :: p => by
    simp only [List.map_cons, listPoly_cons]
    rw [listPoly_map_div M p, div_eq_mul_inv, map_mul]
    ring

/-! ### Integers as differences of natural numbers -/

/-- The integer `pos - neg`. -/
structure SNat where
  pos : ℕ
  neg : ℕ
  deriving Inhabited

namespace SNat

def val (x : SNat) : ℚ := x.pos - x.neg

def ofNat (n : ℕ) : SNat := ⟨n, 0⟩
def add (x y : SNat) : SNat := ⟨Nat.add x.pos y.pos, Nat.add x.neg y.neg⟩
def sub (x y : SNat) : SNat := ⟨Nat.add x.pos y.neg, Nat.add x.neg y.pos⟩
def negate (x : SNat) : SNat := ⟨x.neg, x.pos⟩
def mul (x y : SNat) : SNat :=
  ⟨Nat.add (Nat.mul x.pos y.pos) (Nat.mul x.neg y.neg),
    Nat.add (Nat.mul x.pos y.neg) (Nat.mul x.neg y.pos)⟩
def nsmul (c : ℕ) (x : SNat) : SNat := ⟨Nat.mul c x.pos, Nat.mul c x.neg⟩

/-- `0 < x`. -/
def isPos (x : SNat) : Bool := Nat.blt x.neg x.pos

@[simp] theorem val_mk (p n : ℕ) : (SNat.mk p n).val = p - n := rfl
@[simp] theorem val_ofNat (n : ℕ) : (ofNat n).val = n := by simp [ofNat, val]
@[simp] theorem val_add (x y : SNat) : (x.add y).val = x.val + y.val := by
  simp only [add, val, Nat.add_eq]; push_cast; ring
@[simp] theorem val_sub (x y : SNat) : (x.sub y).val = x.val - y.val := by
  simp only [sub, val, Nat.add_eq]; push_cast; ring
@[simp] theorem val_negate (x : SNat) : x.negate.val = -x.val := by
  simp only [negate, val]; ring
@[simp] theorem val_mul (x y : SNat) : (x.mul y).val = x.val * y.val := by
  simp only [mul, val, Nat.add_eq, Nat.mul_eq]; push_cast; ring
@[simp] theorem val_nsmul (c : ℕ) (x : SNat) : (x.nsmul c).val = c * x.val := by
  simp only [nsmul, val, Nat.mul_eq]; push_cast; ring

theorem isPos_iff (x : SNat) : x.isPos = true ↔ 0 < x.val := by
  simp only [isPos, Nat.blt_eq, val, sub_pos, Nat.cast_lt]

end SNat

/-! ### Polynomials of degree two and four -/

/-- `c0 + c1 X + c2 X²`. -/
structure P2 where
  c0 : SNat
  c1 : SNat
  c2 : SNat

/-- `c0 + c1 X + c2 X² + c3 X³ + c4 X⁴`. -/
structure P4 where
  c0 : SNat
  c1 : SNat
  c2 : SNat
  c3 : SNat
  c4 : SNat

def P2.toPoly (p : P2) : Poly := listPoly [p.c0.val, p.c1.val, p.c2.val]
def P4.toList (p : P4) : List ℚ := [p.c0.val, p.c1.val, p.c2.val, p.c3.val, p.c4.val]
def P4.toPoly (p : P4) : Poly := listPoly p.toList

namespace P2

def add (p q : P2) : P2 := ⟨p.c0.add q.c0, p.c1.add q.c1, p.c2.add q.c2⟩
def sub (p q : P2) : P2 := ⟨p.c0.sub q.c0, p.c1.sub q.c1, p.c2.sub q.c2⟩
def neg (p : P2) : P2 := ⟨p.c0.negate, p.c1.negate, p.c2.negate⟩
def nsmul (c : ℕ) (p : P2) : P2 := ⟨p.c0.nsmul c, p.c1.nsmul c, p.c2.nsmul c⟩
def smul (s : SNat) (p : P2) : P2 := ⟨s.mul p.c0, s.mul p.c1, s.mul p.c2⟩
/-- `x (1 + X²)`. -/
def ofD (x : SNat) : P2 := ⟨x, ⟨0, 0⟩, x⟩
/-- `(1 + X²) p`. -/
def mulD (p : P2) : P4 := ⟨p.c0, p.c1, p.c0.add p.c2, p.c1, p.c2⟩
/-- `p²`. -/
def sq (p : P2) : P4 :=
  ⟨p.c0.mul p.c0, (p.c0.mul p.c1).nsmul 2, (p.c1.mul p.c1).add ((p.c0.mul p.c2).nsmul 2),
    (p.c1.mul p.c2).nsmul 2, p.c2.mul p.c2⟩

section
attribute [local simp] toPoly P4.toPoly P4.toList Polynomial.C_ofNat

@[simp] theorem add_toPoly (p q : P2) : (p.add q).toPoly = p.toPoly + q.toPoly := by
  simp [add]; ring
@[simp] theorem sub_toPoly (p q : P2) : (p.sub q).toPoly = p.toPoly - q.toPoly := by
  simp [sub]; ring
@[simp] theorem neg_toPoly (p : P2) : p.neg.toPoly = -p.toPoly := by
  simp [neg]; ring
@[simp] theorem nsmul_toPoly (c : ℕ) (p : P2) : (p.nsmul c).toPoly = C (c : ℚ) * p.toPoly := by
  simp [nsmul]; ring
@[simp] theorem smul_toPoly (s : SNat) (p : P2) : (p.smul s).toPoly = C s.val * p.toPoly := by
  simp [smul]; ring
@[simp] theorem ofD_toPoly (x : SNat) : (ofD x).toPoly = C x.val * Dpoly := by
  simp [ofD, Dpoly]; ring
@[simp] theorem mulD_toPoly (p : P2) : p.mulD.toPoly = Dpoly * p.toPoly := by
  simp [mulD, Dpoly]; ring
@[simp] theorem sq_toPoly (p : P2) : p.sq.toPoly = p.toPoly ^ 2 := by
  simp [sq]; ring

end

/-- All coefficients vanish. -/
def isZero (p : P2) : Bool :=
  Nat.beq p.c0.pos p.c0.neg && Nat.beq p.c1.pos p.c1.neg && Nat.beq p.c2.pos p.c2.neg
/-- `p + q`, computed only when `b`. -/
def addIf (b : Bool) (p q : P2) : P2 := bif b then p.add q else p
/-- `p - q`, computed only when `b`. -/
def subIf (b : Bool) (p q : P2) : P2 := bif b then p.sub q else p

theorem toPoly_eq_zero {p : P2} (h : p.isZero = true) : p.toPoly = 0 := by
  simp only [isZero, Bool.and_eq_true, Nat.beq_eq] at h
  simp [toPoly, SNat.val, h.1.1, h.1.2, h.2]

theorem addIf_toPoly {b : Bool} (p q : P2) (h : b = false → q.toPoly = 0) :
    (p.addIf b q).toPoly = p.toPoly + q.toPoly := by
  cases b <;> simp [addIf, h]

theorem subIf_toPoly {b : Bool} (p q : P2) (h : b = false → q.toPoly = 0) :
    (p.subIf b q).toPoly = p.toPoly - q.toPoly := by
  cases b <;> simp [subIf, h]

/-- Adding `c q` is skipped when `q` vanishes. -/
theorem nsmul_toPoly_of_isZero {q : P2} (c : ℕ) (h : (!q.isZero) = false) :
    (q.nsmul c).toPoly = 0 := by
  rw [nsmul_toPoly, toPoly_eq_zero (by simpa using h), mul_zero]

end P2

namespace P4

def add (p q : P4) : P4 :=
  ⟨p.c0.add q.c0, p.c1.add q.c1, p.c2.add q.c2, p.c3.add q.c3, p.c4.add q.c4⟩
def sub (p q : P4) : P4 :=
  ⟨p.c0.sub q.c0, p.c1.sub q.c1, p.c2.sub q.c2, p.c3.sub q.c3, p.c4.sub q.c4⟩
def nsmul (c : ℕ) (p : P4) : P4 :=
  ⟨p.c0.nsmul c, p.c1.nsmul c, p.c2.nsmul c, p.c3.nsmul c, p.c4.nsmul c⟩

section
attribute [local simp] toPoly toList

@[simp] theorem add_toPoly (p q : P4) : (p.add q).toPoly = p.toPoly + q.toPoly := by
  simp [add]; ring
@[simp] theorem sub_toPoly (p q : P4) : (p.sub q).toPoly = p.toPoly - q.toPoly := by
  simp [sub]; ring
@[simp] theorem nsmul_toPoly (c : ℕ) (p : P4) : (p.nsmul c).toPoly = C (c : ℚ) * p.toPoly := by
  simp [nsmul]; ring

end

end P4

/-- `f 0 + ⋯ + f 6`. -/
def sum7 (f : Vertex → P2) : P2 :=
  ((((((f 0).add (f 1)).add (f 2)).add (f 3)).add (f 4)).add (f 5)).add (f 6)
/-- `f 0 + ⋯ + f 6`. -/
def sum7' (f : Vertex → P4) : P4 :=
  ((((((f 0).add (f 1)).add (f 2)).add (f 3)).add (f 4)).add (f 5)).add (f 6)

@[simp] theorem sum7_toPoly (f : Vertex → P2) : (sum7 f).toPoly = ∑ i, (f i).toPoly := by
  simp [sum7, Fin.sum_univ_seven]
@[simp] theorem sum7'_toPoly (f : Vertex → P4) : (sum7' f).toPoly = ∑ i, (f i).toPoly := by
  simp [sum7', Fin.sum_univ_seven]

/-- `f 0 + ⋯ + f 6`. -/
def SNat.sum7 (f : Vertex → SNat) : SNat :=
  ((((((f 0).add (f 1)).add (f 2)).add (f 3)).add (f 4)).add (f 5)).add (f 6)

@[simp] theorem SNat.val_sum7 (f : Vertex → SNat) : (SNat.sum7 f).val = ∑ i, (f i).val := by
  simp [SNat.sum7, Fin.sum_univ_seven]

/-! ### The polynomials of the projections -/

/-- `Dpoly = 1 + X²`. -/
def D2 : P2 := ⟨⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩⟩
/-- `Cpoly = 1 - X²`. -/
def C2 : P2 := ⟨⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩⟩
/-- `Spoly = 2 X`. -/
def S2 : P2 := ⟨⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩⟩
/-- `0`. -/
def Z2 : P2 := ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩
/-- `Dpoly ^ 2`. -/
def DD4 : P4 := ⟨⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩⟩

@[simp] theorem D2_toPoly : D2.toPoly = Dpoly := by simp [D2, P2.toPoly, Dpoly]; ring
@[simp] theorem C2_toPoly : C2.toPoly = Cpoly := by simp [C2, P2.toPoly, Cpoly]; ring
@[simp] theorem S2_toPoly : S2.toPoly = Spoly := by
  simp [S2, P2.toPoly, Spoly, Polynomial.C_ofNat]; ring
@[simp] theorem Z2_toPoly : Z2.toPoly = 0 := by simp [Z2, P2.toPoly]
@[simp] theorem DD4_toPoly : DD4.toPoly = Dpoly ^ 2 := by
  simp [DD4, P4.toPoly, P4.toList, Dpoly, Polynomial.C_ofNat]; ring

/-- `sinNumerator`. -/
def sinN (i : Vertex) : P2 :=
  if i ∈ zeroEdges then Z2 else if i ∈ otherQuarterEdges then D2 else C2
/-- `cosNumerator`. -/
def cosN (i : Vertex) : P2 :=
  if i ∈ zeroEdges then D2 else if i ∈ otherQuarterEdges then Z2 else if i = G then S2 else S2.neg
/-- `coefficient`. -/
def coefficientN (j r : Vertex) (p : P2) : P2 := if j = r then p else Z2
/-- `signs`. -/
def signN : Vertex → SNat := ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩]

@[simp] theorem sinN_toPoly (i : Vertex) : (sinN i).toPoly = sinNumerator i := by
  unfold sinN sinNumerator; split_ifs <;> simp
@[simp] theorem cosN_toPoly (i : Vertex) : (cosN i).toPoly = cosNumerator i := by
  unfold cosN cosNumerator; split_ifs <;> simp
@[simp] theorem coefficientN_toPoly (j r : Vertex) (p : P2) :
    (coefficientN j r p).toPoly = coefficient j r p.toPoly := by
  unfold coefficientN coefficient; split_ifs <;> simp
@[simp] theorem signN_val (i : Vertex) : (signN i).val = signs i := by
  fin_cases i <;> simp [signN, signs]

/-- `nominalA`. -/
def nominalAN (i : Vertex) (owner : Fin 4) (r : Vertex) : P2 :=
  ![coefficientN (next i) r (sinN i),
    (coefficientN i r (cosN i)).neg.add (coefficientN (next i) r D2),
    coefficientN i r (sinN i),
    (coefficientN i r D2).sub (coefficientN (next i) r (cosN i))] owner

/-- `nominalB`. -/
def nominalBN (i : Vertex) (owner : Fin 4) (r : Vertex) : P2 :=
  ![(coefficientN i r (D2.smul (signN i))).sub
      (coefficientN (next i) r ((cosN i).smul (signN (next i)))),
    coefficientN i r ((sinN i).smul (signN i)),
    (coefficientN i r ((cosN i).smul (signN i))).sub
      (coefficientN (next i) r (D2.smul (signN (next i)))),
    (coefficientN (next i) r ((sinN i).smul (signN (next i)))).neg] owner

/-- `derivativeA`. -/
def derivativeAN (i : Vertex) (owner : Fin 4) (r : Vertex) : P2 :=
  ![coefficientN (next i) r (cosN i), coefficientN i r (sinN i), coefficientN i r (cosN i),
    coefficientN (next i) r (sinN i)] owner

/-- `derivativeB`. -/
def derivativeBN (i : Vertex) (owner : Fin 4) (r : Vertex) : P2 :=
  ![coefficientN (next i) r ((sinN i).smul (signN (next i))),
    coefficientN i r ((cosN i).smul (signN i)),
    (coefficientN i r ((sinN i).smul (signN i))).neg,
    (coefficientN (next i) r ((cosN i).smul (signN (next i)))).neg] owner

@[simp] theorem nominalAN_toPoly (i : Vertex) (o : Fin 4) (r : Vertex) :
    (nominalAN i o r).toPoly = nominalA i o r := by
  fin_cases o <;> simp [nominalAN, nominalA]
@[simp] theorem nominalBN_toPoly (i : Vertex) (o : Fin 4) (r : Vertex) :
    (nominalBN i o r).toPoly = nominalB i o r := by
  fin_cases o <;> simp [nominalBN, nominalB]
@[simp] theorem derivativeAN_toPoly (i : Vertex) (o : Fin 4) (r : Vertex) :
    (derivativeAN i o r).toPoly = derivativeA i o r := by
  fin_cases o <;> simp [derivativeAN, derivativeA]
@[simp] theorem derivativeBN_toPoly (i : Vertex) (o : Fin 4) (r : Vertex) :
    (derivativeBN i o r).toPoly = derivativeB i o r := by
  fin_cases o <;> simp [derivativeBN, derivativeB]

/-- `2.4 · 10¹⁰ · edgeWidth`. -/
def widthN (positive : Bool) (i : Vertex) : P2 :=
  if i ∈ mixedEdges then ((D2.add C2).add (if positive then S2 else S2.neg)).nsmul 12000000000
  else D2.nsmul 24000000000
/-- `2 · lastWidthDerivative`. -/
def lastWidthN (positive : Bool) : P2 := if positive then C2.sub S2 else (C2.add S2).neg

theorem widthN_toPoly (positive : Bool) (i : Vertex) :
    (widthN positive i).toPoly = C 24000000000 * edgeWidth positive i := by
  by_cases h : i ∈ mixedEdges <;> cases positive <;>
    simp only [widthN, edgeWidth, widthNumerator, h, ite_true, ite_false, signValue,
      Bool.false_eq_true, P2.nsmul_toPoly, P2.add_toPoly, P2.neg_toPoly, D2_toPoly, C2_toPoly,
      S2_toPoly, ← mul_assoc, ← map_mul] <;> norm_num

theorem lastWidthN_toPoly (positive : Bool) :
    (lastWidthN positive).toPoly = C 2 * lastWidthDerivative positive := by
  cases positive <;>
    simp only [lastWidthN, lastWidthDerivative, ite_true, ite_false, Bool.false_eq_true,
      P2.sub_toPoly, P2.add_toPoly, P2.neg_toPoly, C2_toPoly, S2_toPoly, ← mul_assoc,
      ← map_mul] <;> norm_num

/-- `widthN positive i`, testing the sign first, so that both widths are closed terms. -/
def widthOf (positive : Bool) (i : Vertex) : P2 :=
  bif positive then widthN true i else widthN false i

@[simp] theorem widthOf_eq (positive : Bool) (i : Vertex) :
    widthOf positive i = widthN positive i := by
  cases positive <;> rfl

/-! ### The edges at a vertex -/

theorem ne_prev (j : Vertex) : j ≠ prev j := by
  revert j; decide

/-- Only the edges `j` and `prev j` contain the vertex `j`. -/
theorem sum_edges {f : Vertex → Poly} (j : Vertex) (h : ∀ i, i ≠ j → next i ≠ j → f i = 0) :
    ∑ i, f i = f j + f (prev j) := by
  refine Fintype.sum_eq_add j (prev j) (ne_prev j) fun i hi => h i hi.1 ?_
  rintro rfl
  exact hi.2 (by simp [next, prev])

theorem nominalA_eq_zero {i r : Vertex} (o : Fin 4) (h₁ : i ≠ r) (h₂ : next i ≠ r) :
    nominalA i o r = 0 := by
  fin_cases o <;> simp [nominalA, coefficient, h₁, h₂]

theorem nominalB_eq_zero {i r : Vertex} (o : Fin 4) (h₁ : i ≠ r) (h₂ : next i ≠ r) :
    nominalB i o r = 0 := by
  fin_cases o <;> simp [nominalB, coefficient, h₁, h₂]

theorem derivativeA_eq_zero {i r : Vertex} (o : Fin 4) (h₁ : i ≠ r) (h₂ : next i ≠ r) :
    derivativeA i o r = 0 := by
  fin_cases o <;> simp [derivativeA, coefficient, h₁, h₂]

theorem derivativeB_eq_zero {i r : Vertex} (o : Fin 4) (h₁ : i ≠ r) (h₂ : next i ≠ r) :
    derivativeB i o r = 0 := by
  fin_cases o <;> simp [derivativeB, coefficient, h₁, h₂]

/-- The vertex `j` lies on the edge `i`: `j = i` or `j = next i`. -/
def onEdge (i j : Vertex) : Bool := (j == i) || (j == next i)

theorem derivativeAN_off (i j : Vertex) (o : Fin 4) (c : ℕ) (h : onEdge i j = false) :
    ((derivativeAN i o j).nsmul c).toPoly = 0 := by
  simp only [onEdge, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h
  simp [derivativeA_eq_zero o (Ne.symm h.1) (Ne.symm h.2)]

theorem derivativeBN_off (i j : Vertex) (o : Fin 4) (c : ℕ) (h : onEdge i j = false) :
    ((derivativeBN i o j).nsmul c).toPoly = 0 := by
  simp only [onEdge, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h
  simp [derivativeB_eq_zero o (Ne.symm h.1) (Ne.symm h.2)]

theorem sum_nominalA (c : Vertex → ℚ) (o : Vertex → Fin 4) (j : Vertex) :
    ∑ i, C (c i) * nominalA i (o i) j =
      C (c j) * nominalA j (o j) j + C (c (prev j)) * nominalA (prev j) (o (prev j)) j :=
  sum_edges j fun i h₁ h₂ => by simp only [nominalA_eq_zero _ h₁ h₂, mul_zero]

theorem sum_nominalB (c : Vertex → ℚ) (o : Vertex → Fin 4) (j : Vertex) :
    ∑ i, C (c i) * nominalB i (o i) j =
      C (c j) * nominalB j (o j) j + C (c (prev j)) * nominalB (prev j) (o (prev j)) j :=
  sum_edges j fun i h₁ h₂ => by simp only [nominalB_eq_zero _ h₁ h₂, mul_zero]

/-! ### Bernstein coefficients of degree four -/

/-- The Bernstein coefficients of degree four of `t ↦ p (lo + (hi - lo) t)` on `[0, 1]`,
for a coefficient list `p` of at most five entries: first the Taylor coefficients `c k`
of `p` at `lo`, scaled by `(hi - lo) ^ k`, then `b i = ∑ k ≤ i, c k * C(i, k) / C(4, k)`. -/
def bernstein4 (p : List ℚ) (I : QInterval) : List ℚ :=
  let lo := I.lo
  let w := I.hi - I.lo
  let p0 := p.getD 0 0
  let p1 := p.getD 1 0
  let p2 := p.getD 2 0
  let p3 := p.getD 3 0
  let p4 := p.getD 4 0
  let c0 := p0 + lo * (p1 + lo * (p2 + lo * (p3 + lo * p4)))
  let c1 := w * (p1 + lo * (2 * p2 + lo * (3 * p3 + lo * (4 * p4))))
  let c2 := w * w * (p2 + lo * (3 * p3 + lo * (6 * p4)))
  let c3 := w * w * w * (p3 + lo * (4 * p4))
  let c4 := w * w * w * w * p4
  [c0, c0 + c1 / 4, c0 + c1 / 2 + c2 / 6, c0 + 3 * c1 / 4 + c2 / 2 + c3 / 4,
    c0 + c1 + c2 + c3 + c4]

theorem QPoly.eval_of_length_le_five (p : List ℚ) (hp : p.length ≤ 5) (x : ℝ) :
    QPoly.eval p x = (p.getD 0 0 : ℝ) + x * ((p.getD 1 0 : ℝ) + x * ((p.getD 2 0 : ℝ) +
      x * ((p.getD 3 0 : ℝ) + x * (p.getD 4 0 : ℝ)))) := by
  match p, hp with
  | [], _ => simp [QPoly.eval]
  | [_], _ => simp [QPoly.eval]
  | [_, _], _ => simp [QPoly.eval]
  | [_, _, _], _ => simp [QPoly.eval]
  | [_, _, _, _], _ => simp [QPoly.eval]
  | [_, _, _, _, _], _ => simp [QPoly.eval]
  | _ :: _ :: _ :: _ :: _ :: _ :: _, h => simp only [List.length_cons] at h; omega

theorem bernstein4_expansion (p : List ℚ) (hp : p.length ≤ 5) (I : QInterval) (t : ℝ) :
    QPoly.eval p ((I.lo : ℝ) + ((I.hi - I.lo : ℚ) : ℝ) * t) =
      bernsteinEval 4 (fun i => (bernstein4 p I).getD i 0) t := by
  rw [QPoly.eval_of_length_le_five p hp]
  simp only [bernstein4, bernsteinEval, bernsteinBasis, Finset.sum_range_succ,
    Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
  norm_num [Nat.choose]
  ring

/-- The least entry of a list. -/
def minList : List ℚ → ℚ
  | [] => 0
  | [a] => a
  | a :: b :: l => min a (minList (b :: l))

theorem minList_le : ∀ {l : List ℚ} {x : ℚ}, x ∈ l → minList l ≤ x
  | [_], _, h => by simp_all [minList]
  | a :: b :: l, x, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (minList_le h)

/-- `p i` for every vertex `i`. -/
def all7 (p : Vertex → Bool) : Bool := p 0 && p 1 && p 2 && p 3 && p 4 && p 5 && p 6

theorem all7_eq_true {p : Vertex → Bool} : all7 p = true ↔ ∀ i, p i = true := by
  refine ⟨fun h i => ?_, fun h => by simp [all7, h]⟩
  simp only [all7, Bool.and_eq_true] at h
  fin_cases i <;> simp_all

/-- Alternatives are numbered `0` for `.zero` and `1 + 4 j + 2 second + positive`. -/
def Alternative.index : Alternative → ℕ
  | .zero => 0
  | .spike j second positive => 1 + 4 * j + 2 * second.toNat + positive.toNat

def Alternative.ofIndex (k : ℕ) : Alternative :=
  if k = 0 then .zero
  else .spike (Fin.ofNat 5 ((k - 1) / 4)) ((k - 1) / 2 % 2 == 1) ((k - 1) % 2 == 1)

theorem Alternative.ofIndex_index (a : Alternative) : Alternative.ofIndex a.index = a := by
  rcases a with _ | ⟨j, s, p⟩
  · rfl
  · fin_cases j <;> cases s <;> cases p <;> rfl

theorem Alternative.index_lt (a : Alternative) : a.index < 21 := by
  rcases a with _ | ⟨j, s, p⟩
  · decide
  · have := j.isLt
    cases s <;> cases p <;> simp [Alternative.index] <;> omega

/-- The 21 alternatives, in the order of their numbers. -/
def Alternative.all : List Alternative := (List.range 21).map Alternative.ofIndex

theorem Alternative.mem_all (a : Alternative) : a ∈ Alternative.all :=
  List.mem_map.2 ⟨a.index, List.mem_range.2 a.index_lt, a.ofIndex_index⟩

/-! ### The cone sums -/

theorem Row.coneA_sum (r : Row) (j : Vertex) :
    ∑ k, r.cone k * coneA k j = r.cone (j, 0) - r.cone (j, 1) - lowerRatio j * r.cone (j, 2) +
      upperRatio j * r.cone (j, 3) := by
  fin_cases j <;> simp [coneA, Fintype.sum_prod_type, Fin.sum_univ_five] <;> ring

theorem Row.coneB_sum (r : Row) (j : Vertex) :
    ∑ k, r.cone k * coneB k j = r.cone (j, 2) - r.cone (j, 3) - r.cone (j, 4) := by
  fin_cases j <;> simp [coneB, Fintype.sum_prod_type, Fin.sum_univ_five] <;> ring

theorem Row.coneRhs_sum (r : Row) :
    ∑ k, r.cone k * coneRhs k = ∑ i : Vertex, (r.cone (i, 0) * lowerPrimary i -
      r.cone (i, 1) * upperPrimary i - r.cone (i, 4) * (9 / 10) : ℚ) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [coneRhs, Fin.sum_univ_five]
  ring

/-! ### Lines -/

/-- The multipliers of the tables are integer multiples of `1 / ten8`. -/
def ten8 : ℕ := 100000000
/-- The scale of the forces. -/
def forceScale : ℕ := 2000000000000
/-- The scale of the right-hand side. -/
def rhsScale : ℕ := 2400000000000000000

/-- The multipliers of one vertex of a table row, in units of `1 / ten8`: `lam`, the five cone
multipliers `k0, …, k4` and `mu`. -/
structure VRow where
  lam : ℕ
  k0 : ℕ
  k1 : ℕ
  k2 : ℕ
  k3 : ℕ
  k4 : ℕ
  mu : ℕ
  deriving Inhabited

/-- The cone multiplier `k` of a vertex. -/
def VRow.cone (v : VRow) : Fin 5 → ℕ
  | 0 => v.k0
  | 1 => v.k1
  | 2 => v.k2
  | 3 => v.k3
  | _ => v.k4

/-- A table row: the sign of its interval `[a / d, b / d]`, and the multipliers of its seven
vertices. -/
structure Line where
  positive : Bool
  a : SNat
  b : SNat
  d : ℕ
  v0 : VRow
  v1 : VRow
  v2 : VRow
  v3 : VRow
  v4 : VRow
  v5 : VRow
  v6 : VRow
  deriving Inhabited

/-- The line of the 55 entries `positive a⁺ a⁻ b⁺ b⁻ d lam[7] cone[35] mu[7]`, where
`a = a⁺ - a⁻`, `b = b⁺ - b⁻`, `positive` is `1` or `0`, and the five cone multipliers of a vertex
are consecutive. -/
def Line.ofNats (p a₀ a₁ b₀ b₁ d l0 l1 l2 l3 l4 l5 l6
    k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 k15 k16 k17 k18 k19 k20 k21 k22 k23 k24
    k25 k26 k27 k28 k29 k30 k31 k32 k33 k34 u0 u1 u2 u3 u4 u5 u6 : ℕ) : Line :=
  ⟨Nat.beq p 1, ⟨a₀, a₁⟩, ⟨b₀, b₁⟩, d, ⟨l0, k0, k1, k2, k3, k4, u0⟩, ⟨l1, k5, k6, k7, k8, k9, u1⟩,
    ⟨l2, k10, k11, k12, k13, k14, u2⟩, ⟨l3, k15, k16, k17, k18, k19, u3⟩,
    ⟨l4, k20, k21, k22, k23, k24, u4⟩, ⟨l5, k25, k26, k27, k28, k29, u5⟩,
    ⟨l6, k30, k31, k32, k33, k34, u6⟩⟩

namespace Line

/-- The record of the vertex `i`. -/
def vrow (L : Line) : Vertex → VRow
  | 0 => L.v0
  | 1 => L.v1
  | 2 => L.v2
  | 3 => L.v3
  | 4 => L.v4
  | 5 => L.v5
  | _ => L.v6

def lam (L : Line) (i : Vertex) : ℕ := (L.vrow i).lam
def cone (L : Line) (k : ConeIndex) : ℕ := (L.vrow k.1).cone k.2
def mu (L : Line) (i : Vertex) : ℕ := (L.vrow i).mu

@[simp] theorem cone_k0 (L : Line) (j : Vertex) : L.cone (j, 0) = (L.vrow j).k0 := rfl
@[simp] theorem cone_k1 (L : Line) (j : Vertex) : L.cone (j, 1) = (L.vrow j).k1 := rfl
@[simp] theorem cone_k2 (L : Line) (j : Vertex) : L.cone (j, 2) = (L.vrow j).k2 := rfl
@[simp] theorem cone_k3 (L : Line) (j : Vertex) : L.cone (j, 3) = (L.vrow j).k3 := rfl
@[simp] theorem cone_k4 (L : Line) (j : Vertex) : L.cone (j, 4) = (L.vrow j).k4 := rfl

variable (mode : Mode) (owners : Vertex → Fin 4) (alt : Alternative) (L : Line)

def interval : QInterval := ⟨L.a.val / L.d, L.b.val / L.d⟩

/-- `20000 · lowerRatio` and `20000 · upperRatio`. -/
def lowerRatioN : Vertex → ℕ := ![10000, 1000, 0, 0, 1000, 10000, 0]
def upperRatioN : Vertex → ℕ := ![20000, 16000, 20000, 20000, 16000, 20000, 20000]
/-- `2.4 · 10¹⁰ · lowerPrimary` and `2.4 · 10¹⁰ · upperPrimary`. -/
def lowerPrimaryN (i : Vertex) : ℕ := if i = G ∨ i = T then 14000000000 else 13410000000
def upperPrimaryN (i : Vertex) : ℕ := if i = G ∨ i = T then 33504000000 else 33960000000

/-- `20000 · epsilon`. -/
def epsilonN : ℕ := 20
/-- `1.2 · 10¹⁰ · epsilon`. -/
def halfN : ℕ := 12000000
/-- `12 · forceScale² · Q / ten8`. -/
def QN : ℕ := if mode = .tilt then 1879456386240000000 else 1879488000000000000

/-- `forceScale · ∑ k, cone k * coneA k j`. -/
def coneAN (j : Vertex) : SNat :=
  ⟨Nat.add (Nat.mul 20000 (L.vrow j).k0) (Nat.mul (upperRatioN j) (L.vrow j).k3),
    Nat.add (Nat.mul 20000 (L.vrow j).k1) (Nat.mul (lowerRatioN j) (L.vrow j).k2)⟩
/-- `forceScale · ∑ k, cone k * coneB k j`. -/
def coneBN (j : Vertex) : SNat :=
  ⟨Nat.mul 20000 (L.vrow j).k2,
    Nat.add (Nat.mul 20000 (L.vrow j).k3) (Nat.mul 20000 (L.vrow j).k4)⟩
/-- `rhsScale` times the cone terms of the vertex `i` in `∑ k, cone k * coneRhs k`. -/
def coneRhsAt (i : Vertex) : SNat :=
  ⟨Nat.mul (lowerPrimaryN i) (L.vrow i).k0,
    Nat.add (Nat.mul (upperPrimaryN i) (L.vrow i).k1) (Nat.mul 21600000000 (L.vrow i).k4)⟩
/-- `rhsScale · ∑ k, cone k * coneRhs k`. -/
def coneRhsN : SNat := SNat.sum7 L.coneRhsAt

/-- `ten8 · maxLambda`. -/
def maxLambdaN : ℕ := max (L.lam 0) (max (L.lam 2) (max (L.lam 3) (max (L.lam 4) (L.lam 5))))

/-- `rhsScale · loss`. -/
def lossN : ℕ :=
  match mode with
  | .mixed => 24024000 * L.maxLambdaN + 48000000 * L.lam E
  | .tilt => 24024 * L.maxLambdaN + 27000 * L.lam E

/-- `forceScale · errorA`. -/
def errorAN (i : Vertex) : P2 :=
  match alt with
  | .zero => Z2
  | .spike j second positive =>
    let t := ((derivativeAN (alignedEdge j) (Alternative.owner j second) i).nsmul
        (Nat.mul epsilonN (L.lam (alignedEdge j)))).sub
      ((derivativeAN E 1 i).nsmul (Nat.mul epsilonN (L.lam E)))
    bif positive then t else t.neg

/-- `forceScale · errorB`. -/
def errorBN (i : Vertex) : P2 :=
  match alt with
  | .zero => Z2
  | .spike j second positive =>
    let t := ((derivativeBN (alignedEdge j) (Alternative.owner j second) i).nsmul
        (Nat.mul epsilonN (L.lam (alignedEdge j)))).sub
      ((derivativeBN E 1 i).nsmul (Nat.mul epsilonN (L.lam E)))
    bif positive then t else t.neg

/-- `rhsScale · errorRhs`. -/
def errorRhsN : P2 :=
  match alt with
  | .zero => Z2
  | .spike j _ positive =>
    let w := (lastWidthN L.positive).nsmul (L.lam E)
    ((D2.nsmul (L.lam (alignedEdge j))).add (bif positive then w.neg else w)).nsmul halfN

/-- `forceScale · forceA` without the error term: the cone term, and the terms of the edges `j`
and `prev j` that do not vanish. -/
def baseAN (j : Vertex) : P2 :=
  ((P2.ofD (L.coneAN j)).addIf (!(nominalAN j (owners j) j).isZero)
      ((nominalAN j (owners j) j).nsmul (Nat.mul 20000 (L.lam j)))).addIf
    (!(nominalAN (prev j) (owners (prev j)) j).isZero)
    ((nominalAN (prev j) (owners (prev j)) j).nsmul (Nat.mul 20000 (L.lam (prev j))))

/-- `forceScale · forceB` without the error term. -/
def baseBN (j : Vertex) : P2 :=
  ((P2.ofD (L.coneBN j)).addIf (!(nominalBN j (owners j) j).isZero)
      ((nominalBN j (owners j) j).nsmul (Nat.mul 20000 (L.lam j)))).addIf
    (!(nominalBN (prev j) (owners (prev j)) j).isZero)
    ((nominalBN (prev j) (owners (prev j)) j).nsmul (Nat.mul 20000 (L.lam (prev j))))

/-- `forceScale · forceA`: each part of the error term enters only at the vertices of its edge. -/
def forceAN (j : Vertex) : P2 :=
  match alt with
  | .zero => L.baseAN owners j
  | .spike s second positive =>
    let t := (derivativeAN (alignedEdge s) (Alternative.owner s second) j).nsmul
      (Nat.mul epsilonN (L.lam (alignedEdge s)))
    let u := (derivativeAN E 1 j).nsmul (Nat.mul epsilonN (L.lam E))
    bif positive then ((L.baseAN owners j).addIf (onEdge (alignedEdge s) j) t).subIf (onEdge E j) u
    else ((L.baseAN owners j).subIf (onEdge (alignedEdge s) j) t).addIf (onEdge E j) u

/-- `forceScale · forceB`: each part of the error term enters only at the vertices of its edge. -/
def forceBN (j : Vertex) : P2 :=
  match alt with
  | .zero => L.baseBN owners j
  | .spike s second positive =>
    let t := (derivativeBN (alignedEdge s) (Alternative.owner s second) j).nsmul
      (Nat.mul epsilonN (L.lam (alignedEdge s)))
    let u := (derivativeBN E 1 j).nsmul (Nat.mul epsilonN (L.lam E))
    bif positive then ((L.baseBN owners j).addIf (onEdge (alignedEdge s) j) t).subIf (onEdge E j) u
    else ((L.baseBN owners j).subIf (onEdge (alignedEdge s) j) t).addIf (onEdge E j) u

/-- `rhsScale · rhs`. -/
def rhsN : P2 :=
  ((sum7 fun i => (widthOf L.positive i).nsmul (L.lam i)).add
    (P2.ofD (L.coneRhsN.sub (.ofNat (L.lossN mode))))).add (L.errorRhsN alt)

/-- `rhsScale · L`. -/
def LN : P2 :=
  (L.rhsN mode alt).add
    ((sum7 fun i => (L.forceAN owners alt i).add (L.forceBN owners alt i)).nsmul 600000)

def prodMu : ℕ :=
  Nat.mul (Nat.mul (Nat.mul (Nat.mul (Nat.mul (Nat.mul (L.mu 0) (L.mu 1)) (L.mu 2)) (L.mu 3))
    (L.mu 4)) (L.mu 5)) (L.mu 6)
def sumMu : ℕ :=
  Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (L.mu 0) (L.mu 1)) (L.mu 2)) (L.mu 3))
    (L.mu 4)) (L.mu 5)) (L.mu 6)

/-- `M · quartic`. -/
def quarticN : P4 :=
  ((((L.LN mode owners alt).mulD).nsmul (Nat.mul 20000000 L.prodMu)).sub
    (DD4.nsmul (Nat.mul (Nat.mul (QN mode) L.sumMu) L.prodMu))).sub
    (sum7' fun i => ((L.forceAN owners alt i).sq.add (L.forceBN owners alt i).sq).nsmul
      (Nat.mul 300000000 (L.prodMu / L.mu i)))

/-- `M = 12 forceScale² ∏ᵢ μᵢ ten8⁷`. -/
def M : ℚ := 48000000000000000000000000 * L.prodMu

/-- The quartic of the row, `quarticN / M`. -/
def polynomial : List ℚ := (L.quarticN mode owners alt).toList.map (· / L.M)

/-- The row of a line, with its quartic, the Bernstein coefficients of degree four and their
minimum as reserve. -/
def row : Row where
  mode := mode
  positive := L.positive
  interval := L.interval
  owners := owners
  lambda i := L.lam i / ten8
  cone k := L.cone k / ten8
  mu i := L.mu i / ten8
  alternative := alt
  polynomial := L.polynomial mode owners alt
  bernstein := bernstein4 (L.polynomial mode owners alt) L.interval
  reserve := minList (bernstein4 (L.polynomial mode owners alt) L.interval)

@[simp] theorem row_mode : (L.row mode owners alt).mode = mode := rfl
@[simp] theorem row_positive : (L.row mode owners alt).positive = L.positive := rfl
@[simp] theorem row_owners : (L.row mode owners alt).owners = owners := rfl
@[simp] theorem row_lambda (i : Vertex) : (L.row mode owners alt).lambda i = L.lam i / ten8 := rfl
@[simp] theorem row_cone (k : ConeIndex) : (L.row mode owners alt).cone k = L.cone k / ten8 := rfl
@[simp] theorem row_mu (i : Vertex) : (L.row mode owners alt).mu i = L.mu i / ten8 := rfl
@[simp] theorem row_alternative : (L.row mode owners alt).alternative = alt := rfl

/-! ### The forces, right-hand side and quartic of a line -/

theorem upperRatioN_eq (j : Vertex) : (upperRatioN j : ℚ) = 20000 * upperRatio j := by
  fin_cases j <;> norm_num [upperRatioN, upperRatio]
theorem lowerRatioN_eq (j : Vertex) : (lowerRatioN j : ℚ) = 20000 * lowerRatio j := by
  fin_cases j <;> norm_num [lowerRatioN, lowerRatio]
theorem lowerPrimaryN_eq (i : Vertex) :
    (lowerPrimaryN i : ℚ) = 24000000000 * lowerPrimary i := by
  unfold lowerPrimaryN lowerPrimary; split_ifs <;> norm_num
theorem upperPrimaryN_eq (i : Vertex) :
    (upperPrimaryN i : ℚ) = 24000000000 * upperPrimary i := by
  unfold upperPrimaryN upperPrimary; split_ifs <;> norm_num

theorem errorAN_toPoly (i : Vertex) :
    (L.errorAN alt i).toPoly = C (forceScale : ℚ) * (L.row mode owners alt).errorA i := by
  apply Polynomial.funext; intro z
  cases alt with
  | zero => simp [errorAN, Row.errorA]
  | spike j second positive =>
    cases positive <;>
      simp [errorAN, Row.errorA, Row.epsilon, epsilonN, signValue, forceScale, ten8] <;> ring

theorem errorBN_toPoly (i : Vertex) :
    (L.errorBN alt i).toPoly = C (forceScale : ℚ) * (L.row mode owners alt).errorB i := by
  apply Polynomial.funext; intro z
  cases alt with
  | zero => simp [errorBN, Row.errorB]
  | spike j second positive =>
    cases positive <;>
      simp [errorBN, Row.errorB, Row.epsilon, epsilonN, signValue, forceScale, ten8] <;> ring

theorem errorRhsN_toPoly :
    (L.errorRhsN alt).toPoly = C (rhsScale : ℚ) * (L.row mode owners alt).errorRhs := by
  apply Polynomial.funext; intro z
  have hw := congrArg (Polynomial.eval z) (lastWidthN_toPoly L.positive)
  simp only [Polynomial.eval_mul, Polynomial.eval_C] at hw
  cases alt with
  | zero => simp [errorRhsN, Row.errorRhs]
  | spike j second positive =>
    cases positive <;>
      simp [errorRhsN, Row.errorRhs, Row.epsilon, halfN, signValue, rhsScale, ten8, hw] <;> ring

theorem baseAN_toPoly (j : Vertex) :
    (L.baseAN owners j).toPoly = (P2.ofD (L.coneAN j)).toPoly +
      ((nominalAN j (owners j) j).nsmul (Nat.mul 20000 (L.lam j))).toPoly +
      ((nominalAN (prev j) (owners (prev j)) j).nsmul (Nat.mul 20000 (L.lam (prev j)))).toPoly := by
  rw [baseAN, P2.addIf_toPoly _ _ (P2.nsmul_toPoly_of_isZero _),
    P2.addIf_toPoly _ _ (P2.nsmul_toPoly_of_isZero _)]

theorem baseBN_toPoly (j : Vertex) :
    (L.baseBN owners j).toPoly = (P2.ofD (L.coneBN j)).toPoly +
      ((nominalBN j (owners j) j).nsmul (Nat.mul 20000 (L.lam j))).toPoly +
      ((nominalBN (prev j) (owners (prev j)) j).nsmul (Nat.mul 20000 (L.lam (prev j)))).toPoly := by
  rw [baseBN, P2.addIf_toPoly _ _ (P2.nsmul_toPoly_of_isZero _),
    P2.addIf_toPoly _ _ (P2.nsmul_toPoly_of_isZero _)]

theorem forceAN_eq (j : Vertex) :
    (L.forceAN owners alt j).toPoly =
      (L.baseAN owners j).toPoly + (L.errorAN alt j).toPoly := by
  cases alt with
  | zero => simp [forceAN, errorAN]
  | spike s second positive =>
    cases positive <;>
      simp only [forceAN, errorAN, Bool.cond_true, Bool.cond_false, P2.addIf_toPoly _ _
        (derivativeAN_off _ _ _ _), P2.subIf_toPoly _ _ (derivativeAN_off _ _ _ _),
        P2.sub_toPoly, P2.neg_toPoly] <;> ring

theorem forceBN_eq (j : Vertex) :
    (L.forceBN owners alt j).toPoly =
      (L.baseBN owners j).toPoly + (L.errorBN alt j).toPoly := by
  cases alt with
  | zero => simp [forceBN, errorBN]
  | spike s second positive =>
    cases positive <;>
      simp only [forceBN, errorBN, Bool.cond_true, Bool.cond_false, P2.addIf_toPoly _ _
        (derivativeBN_off _ _ _ _), P2.subIf_toPoly _ _ (derivativeBN_off _ _ _ _),
        P2.sub_toPoly, P2.neg_toPoly] <;> ring

theorem forceAN_toPoly (j : Vertex) :
    (L.forceAN owners alt j).toPoly =
      C (forceScale : ℚ) * (L.row mode owners alt).forceA j := by
  apply Polynomial.funext; intro z
  have he := congrArg (Polynomial.eval z) (L.errorAN_toPoly mode owners alt j)
  simp only [Polynomial.eval_mul, Polynomial.eval_C] at he
  simp only [Row.forceA, Row.coneA_sum, sum_nominalA]
  simp only [forceAN_eq, baseAN_toPoly, P2.nsmul_toPoly, nominalAN_toPoly,
    P2.ofD_toPoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    he, row_lambda, row_cone, row_owners, coneAN, SNat.val_mk, cone_k0, cone_k1, cone_k2,
    cone_k3, Nat.add_eq, Nat.mul_eq]
  push_cast
  simp only [upperRatioN_eq, lowerRatioN_eq, forceScale, ten8]
  ring

theorem forceBN_toPoly (j : Vertex) :
    (L.forceBN owners alt j).toPoly =
      C (forceScale : ℚ) * (L.row mode owners alt).forceB j := by
  apply Polynomial.funext; intro z
  have he := congrArg (Polynomial.eval z) (L.errorBN_toPoly mode owners alt j)
  simp only [Polynomial.eval_mul, Polynomial.eval_C] at he
  simp only [Row.forceB, Row.coneB_sum, sum_nominalB]
  simp only [forceBN_eq, baseBN_toPoly, P2.nsmul_toPoly, nominalBN_toPoly,
    P2.ofD_toPoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    he, row_lambda, row_cone, row_owners, coneBN, SNat.val_mk, cone_k2, cone_k3, cone_k4,
    Nat.add_eq, Nat.mul_eq]
  push_cast
  simp only [forceScale, ten8]
  ring

theorem lossN_eq : (L.lossN mode : ℚ) = rhsScale * (L.row mode owners alt).loss := by
  have h8 : (0 : ℚ) ≤ 100000000 := by norm_num
  cases mode <;>
    simp [lossN, Row.loss, Row.epsilon, Row.maxLambda, maxLambdaN, rhsScale, ten8,
      max_div_div_right h8] <;> ring

theorem rhsN_toPoly :
    (L.rhsN mode alt).toPoly = C (rhsScale : ℚ) * (L.row mode owners alt).rhs := by
  apply Polynomial.funext; intro z
  have he := congrArg (Polynomial.eval z) (L.errorRhsN_toPoly mode owners alt)
  have hw := fun i => congrArg (Polynomial.eval z) (widthN_toPoly L.positive i)
  simp only [Polynomial.eval_mul, Polynomial.eval_C] at he hw
  simp only [Row.rhs, Row.coneRhs_sum]
  simp only [rhsN, P2.add_toPoly, sum7_toPoly, P2.nsmul_toPoly, P2.ofD_toPoly, widthOf_eq,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Fin.sum_univ_seven, he, hw, row_lambda, row_cone, row_positive, coneRhsN, coneRhsAt,
    SNat.val_sum7, SNat.val_sub, SNat.val_mk, SNat.val_ofNat, L.lossN_eq mode owners alt,
    cone_k0, cone_k1, cone_k4, Nat.add_eq, Nat.mul_eq]
  push_cast
  simp only [lowerPrimaryN_eq, upperPrimaryN_eq, rhsScale, ten8]
  ring

theorem LN_toPoly :
    (L.LN mode owners alt).toPoly = C (rhsScale : ℚ) * (L.row mode owners alt).L := by
  apply Polynomial.funext; intro z
  have hr := congrArg (Polynomial.eval z) (L.rhsN_toPoly mode owners alt)
  have hA := fun i => congrArg (Polynomial.eval z) (L.forceAN_toPoly mode owners alt i)
  have hB := fun i => congrArg (Polynomial.eval z) (L.forceBN_toPoly mode owners alt i)
  simp only [Polynomial.eval_mul, Polynomial.eval_C] at hr hA hB
  simp only [LN, Row.L, P2.add_toPoly, sum7_toPoly, P2.nsmul_toPoly, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Fin.sum_univ_seven, hr, hA, hB]
  simp only [rhsScale, forceScale]
  push_cast
  ring

theorem prodMu_eq : L.prodMu = ∏ i, L.mu i := by
  simp [prodMu, Fin.prod_univ_seven, Nat.mul_assoc]

theorem weight_eq (hmu : ∀ i, 0 < L.mu i) (i : Vertex) :
    ((300000000 * (L.prodMu / L.mu i) : ℕ) : ℚ) * (forceScale : ℚ) ^ 2 =
      L.M * (1 / (4 * (L.mu i / ten8 : ℚ))) := by
  have hd : L.mu i ∣ L.prodMu := L.prodMu_eq ▸ Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  have hne : (L.mu i : ℚ) ≠ 0 := by exact_mod_cast (hmu i).ne'
  push_cast [Nat.cast_div_charZero hd]
  simp only [M, forceScale, ten8]
  field_simp
  ring

theorem quarticN_toPoly (hmu : ∀ i, 0 < L.mu i) :
    (L.quarticN mode owners alt).toPoly = C L.M * (L.row mode owners alt).quartic := by
  apply Polynomial.funext; intro z
  have hL := congrArg (Polynomial.eval z) (L.LN_toPoly mode owners alt)
  have hA := fun i => congrArg (Polynomial.eval z) (L.forceAN_toPoly mode owners alt i)
  have hB := fun i => congrArg (Polynomial.eval z) (L.forceBN_toPoly mode owners alt i)
  simp only [Polynomial.eval_mul, Polynomial.eval_C] at hL hA hB
  have hsum : ∑ i, (((300000000 * (L.prodMu / L.mu i) : ℕ) : ℚ) *
        ((L.forceAN owners alt i).toPoly.eval z ^ 2 +
          (L.forceBN owners alt i).toPoly.eval z ^ 2)) =
      L.M * ∑ i, 1 / (4 * (L.row mode owners alt).mu i) *
        (((L.row mode owners alt).forceA i).eval z ^ 2 +
          ((L.row mode owners alt).forceB i).eval z ^ 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hA i, hB i, row_mu, ← mul_assoc L.M, ← L.weight_eq hmu i]
    ring
  simp only [quarticN, Row.quartic, P4.sub_toPoly, P4.nsmul_toPoly, P2.mulD_toPoly, DD4_toPoly,
    sum7'_toPoly, P4.add_toPoly, P2.sq_toPoly, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_finsetSum, hL,
    Nat.mul_eq, hsum, Polynomial.eval_pow]
  simp only [M, rhsScale, QN, Row.Q, row_mode, row_mu, sumMu, Fin.sum_univ_seven, ten8,
    Nat.add_eq]
  cases mode <;> simp <;> ring

/-! ### Bernstein coefficients in natural numbers -/

/-- Five integers. -/
structure B5 where
  b0 : SNat
  b1 : SNat
  b2 : SNat
  b3 : SNat
  b4 : SNat

def B5.toList (x : B5) : List ℚ := [x.b0.val, x.b1.val, x.b2.val, x.b3.val, x.b4.val]
def B5.allPos (x : B5) : Bool := x.b0.isPos && x.b1.isPos && x.b2.isPos && x.b3.isPos && x.b4.isPos

/-- `12 d⁴` times the Bernstein coefficients of degree four of `p` on `[a / d, b / d]`. -/
def bernsteinN (p : P4) (a b : SNat) (d : ℕ) : B5 :=
  let e := b.sub a
  let d2 := Nat.mul d d
  let d3 := Nat.mul d2 d
  let d4 := Nat.mul d3 d
  let c0 := (p.c0.nsmul d4).add (a.mul ((p.c1.nsmul d3).add (a.mul ((p.c2.nsmul d2).add
    (a.mul ((p.c3.nsmul d).add (a.mul p.c4)))))))
  let c1 := e.mul ((p.c1.nsmul d3).add (a.mul ((p.c2.nsmul (Nat.mul 2 d2)).add
    (a.mul ((p.c3.nsmul (Nat.mul 3 d)).add (a.mul (p.c4.nsmul 4)))))))
  let c2 := (e.mul e).mul ((p.c2.nsmul d2).add (a.mul ((p.c3.nsmul (Nat.mul 3 d)).add
    (a.mul (p.c4.nsmul 6)))))
  let c3 := ((e.mul e).mul e).mul ((p.c3.nsmul d).add (a.mul (p.c4.nsmul 4)))
  let c4 := ((e.mul e).mul (e.mul e)).mul p.c4
  ⟨c0.nsmul 12, (c0.nsmul 12).add (c1.nsmul 3), ((c0.nsmul 12).add (c1.nsmul 6)).add (c2.nsmul 2),
    (((c0.nsmul 12).add (c1.nsmul 9)).add (c2.nsmul 6)).add (c3.nsmul 3),
    ((((c0.add c1).add c2).add c3).add c4).nsmul 12⟩

theorem bernsteinN_spec (p : P4) (a b : SNat) {d : ℕ} (hd : d ≠ 0) {M : ℚ} (hM : M ≠ 0) :
    bernstein4 (p.toList.map (· / M)) ⟨a.val / d, b.val / d⟩ =
      (bernsteinN p a b d).toList.map (· / (12 * d ^ 4 * M)) := by
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  simp only [bernstein4, bernsteinN, B5.toList, P4.toList, List.map_cons, List.map_nil,
    List.getD_cons_zero, List.getD_cons_succ, SNat.val_add, SNat.val_sub, SNat.val_mul,
    SNat.val_nsmul, List.cons.injEq, and_true, Nat.mul_eq]
  push_cast
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> field_simp <;> ring

theorem minList_pos : ∀ {l : List ℚ}, l ≠ [] → (∀ x ∈ l, 0 < x) → 0 < minList l
  | [_], _, h => by simpa [minList] using h
  | _ :: _ :: _, _, h => lt_min (h _ List.mem_cons_self)
      (minList_pos (List.cons_ne_nil _ _) fun x hx => h x (List.mem_cons_of_mem _ hx))

/-! ### The test of a line -/

/-- Positive `μ`, a positive denominator, the sign and order of the interval, and positive
Bernstein coefficients. -/
def check : Bool :=
  all7 (fun i => Nat.blt 0 (L.mu i)) && Nat.blt 0 L.d &&
  (bif L.positive then Nat.ble L.a.neg L.a.pos else Nat.ble L.b.pos L.b.neg) &&
  Nat.blt (Nat.add L.a.pos L.b.neg) (Nat.add L.b.pos L.a.neg) &&
  (bernsteinN (L.quarticN mode owners alt) L.a L.b L.d).allPos

theorem check_sound (h : L.check mode owners alt = true) : (L.row mode owners alt).Valid := by
  simp only [check, Bool.and_eq_true, all7_eq_true, Nat.blt_eq, B5.allPos,
    SNat.isPos_iff, Nat.add_eq] at h
  obtain ⟨⟨⟨⟨hmu, hd⟩, hsign⟩, horder⟩, ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩⟩ := h
  have hd' : (0 : ℚ) < L.d := by exact_mod_cast hd
  have hM : 0 < L.M := by
    have : 0 < L.prodMu := L.prodMu_eq ▸ Finset.prod_pos fun i _ => hmu i
    exact mul_pos (by norm_num) (by exact_mod_cast this)
  have hval : L.a.val < L.b.val := by
    have : ((L.a.pos + L.b.neg : ℕ) : ℚ) < ((L.b.pos + L.a.neg : ℕ) : ℚ) := by exact_mod_cast horder
    simp only [SNat.val]; push_cast at this; linarith
  have hb : bernstein4 (L.polynomial mode owners alt) L.interval =
      (bernsteinN (L.quarticN mode owners alt) L.a L.b L.d).toList.map
        (· / (12 * L.d ^ 4 * L.M)) :=
    bernsteinN_spec _ _ _ hd.ne' hM.ne'
  have hden : 0 < 12 * (L.d : ℚ) ^ 4 * L.M := mul_pos (mul_pos (by norm_num) (pow_pos hd' 4)) hM
  have hpos : ∀ x ∈ bernstein4 (L.polynomial mode owners alt) L.interval, 0 < x := by
    rw [hb]
    simp only [B5.toList, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
    intro x hx
    rcases hx with h | h | h | h | h <;> rw [h]
    exacts [div_pos h0 hden, div_pos h1 hden, div_pos h2 hden, div_pos h3 hden, div_pos h4 hden]
  have hlen : (L.polynomial mode owners alt).length ≤ 5 := by
    simp only [polynomial, P4.toList, List.length_map, List.length_cons, List.length_nil]; omega
  have hcount : (bernstein4 (L.polynomial mode owners alt) L.interval).length = 4 + 1 := rfl
  have hsign' : if L.positive then 0 ≤ L.interval.lo else L.interval.hi ≤ 0 := by
    simp only [interval]
    cases hp : L.positive <;> simp only [hp, ite_true, ite_false, Bool.false_eq_true,
      Bool.cond_true, Bool.cond_false, Nat.ble_eq] at hsign ⊢
    · have : ((L.b.pos : ℕ) : ℚ) ≤ ((L.b.neg : ℕ) : ℚ) := by exact_mod_cast hsign
      apply div_nonpos_of_nonpos_of_nonneg _ hd'.le
      simp only [SNat.val]; linarith
    · have : ((L.a.neg : ℕ) : ℚ) ≤ ((L.a.pos : ℕ) : ℚ) := by exact_mod_cast hsign
      apply div_nonneg _ hd'.le
      simp only [SNat.val]; linarith
  have hid : (L.row mode owners alt).quartic = listPoly (L.polynomial mode owners alt) := by
    rw [polynomial, listPoly_map_div, ← P4.toPoly, L.quarticN_toPoly mode owners alt hmu,
      ← mul_assoc, ← map_mul, inv_mul_cancel₀ hM.ne', map_one, one_mul]
  have hlower : ∀ i, i ≤ 4 → minList (bernstein4 (L.polynomial mode owners alt) L.interval) ≤
      (bernstein4 (L.polynomial mode owners alt) L.interval).getD i 0 := by
    intro i hi
    have hi' : i < (bernstein4 (L.polynomial mode owners alt) L.interval).length := by
      rw [hcount]; exact Nat.lt_succ_of_le hi
    rw [List.getD_eq_getElem _ _ hi']
    exact minList_le (List.getElem_mem hi')
  exact
    { lambda_nonneg := fun i => by simp only [row_lambda]; positivity
      cone_nonneg := fun k => by simp only [row_cone]; positivity
      mu_pos := fun i => by simp only [row_mu, ten8]; have := hmu i; positivity
      interval_sign := hsign'
      polynomial_identity := hid
      bernstein_valid :=
        { interval_order := div_lt_div_of_pos_right hval hd'
          expansion := bernstein4_expansion (L.polynomial mode owners alt) hlen L.interval
          coefficient_lower := hlower }
      reserve_pos := minList_pos (by simp [bernstein4]) hpos }

end Line

/-! ### Tables of lines -/

/-- `x / d ≤ y / e`, for `d, e > 0`. -/
def SNat.leFrac (x : SNat) (d : ℕ) (y : SNat) (e : ℕ) : Bool :=
  Nat.ble (Nat.add (Nat.mul x.pos e) (Nat.mul y.neg d)) (Nat.add (Nat.mul y.pos d) (Nat.mul x.neg e))

theorem SNat.leFrac_iff {x y : SNat} {d e : ℕ} (hd : 0 < d) (he : 0 < e) :
    SNat.leFrac x d y e = true ↔ x.val / d ≤ y.val / e := by
  rw [div_le_div_iff₀ (by exact_mod_cast hd) (by exact_mod_cast he)]
  simp only [leFrac, Nat.ble_eq, Nat.add_eq, Nat.mul_eq, val]
  constructor
  · intro h
    have h' : ((x.pos * e + y.neg * d : ℕ) : ℚ) ≤ ((y.pos * d + x.neg * e : ℕ) : ℚ) := by
      exact_mod_cast h
    push_cast at h'
    linarith
  · intro h
    have h' : ((x.pos * e + y.neg * d : ℕ) : ℚ) ≤ ((y.pos * d + x.neg * e : ℕ) : ℚ) := by
      push_cast; linarith
    exact_mod_cast h'

/-- `ClosedChain (lo / dlo) (hi / dhi)` for the intervals of the lines, in natural numbers. -/
def chainCheck (hi : SNat) (dhi : ℕ) : SNat → ℕ → List Line → Bool
  | lo, dlo, [] => !SNat.leFrac lo dlo hi dhi
  | lo, dlo, L :: rest => Nat.blt 0 L.d && SNat.leFrac L.a L.d lo dlo &&
      (SNat.leFrac hi dhi L.b L.d || (SNat.leFrac lo dlo L.b L.d && chainCheck hi dhi L.b L.d rest))

theorem chainCheck_sound {hi : SNat} {dhi : ℕ} (hhi : 0 < dhi) :
    ∀ {lo : SNat} {dlo : ℕ} {lines : List Line}, 0 < dlo → chainCheck hi dhi lo dlo lines = true →
      ClosedChain (lo.val / dlo) (hi.val / dhi) (lines.map Line.interval)
  | lo, dlo, [], hlo, h => by
    simp only [chainCheck, Bool.not_eq_eq_eq_not, Bool.not_true] at h
    simp only [List.map_nil, ClosedChain]
    exact lt_of_not_ge fun h' => by simp [(SNat.leFrac_iff hlo hhi).2 h'] at h
  | lo, dlo, L :: rest, hlo, h => by
    simp only [chainCheck, Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq] at h
    obtain ⟨⟨hd, h₁⟩, h₂⟩ := h
    simp only [List.map_cons, ClosedChain, Line.interval]
    refine ⟨(SNat.leFrac_iff hd hlo).1 h₁, ?_⟩
    rcases h₂ with h₂ | ⟨h₃, h₄⟩
    · exact Or.inl ((SNat.leFrac_iff hhi hd).1 h₂)
    · exact Or.inr ⟨(SNat.leFrac_iff hlo hd).1 h₃, chainCheck_sound hhi hd h₄⟩

/-- The intervals of the lines cover the half-angle chart `[-3/8, 3/8]`. -/
def coverCheck (lines : List Line) : Bool := chainCheck ⟨3, 0⟩ 8 ⟨0, 3⟩ 8 lines

theorem coverCheck_sound {lines : List Line} (h : coverCheck lines = true) :
    ClosedChain (-3 / 8) (3 / 8) (lines.map Line.interval) := by
  have := chainCheck_sound (by norm_num) (by norm_num) h
  norm_num [SNat.val] at this
  rwa [neg_div]

/-- The owner table of lines: every line passes `Line.check`, and their intervals cover the
half-angle chart `[-3/8, 3/8]`. -/
def OwnerTable.ofLines (mode : Mode) (owners : Vertex → Fin 4) (lines : List Line)
    (hrows : lines.all (Line.check mode owners .zero) = true)
    (hcover : coverCheck lines = true) : OwnerTable where
  mode := mode
  owners := owners
  rows := lines.map (Line.row mode owners .zero)
  valid r hr := by
    obtain ⟨L, hL, rfl⟩ := List.mem_map.1 hr
    exact L.check_sound mode owners .zero (List.all_eq_true.1 hrows L hL)
  same_mode r hr := by
    obtain ⟨L, _, rfl⟩ := List.mem_map.1 hr
    rfl
  same_owners r hr := by
    obtain ⟨L, _, rfl⟩ := List.mem_map.1 hr
    rfl
  no_error r hr := by
    obtain ⟨L, _, rfl⟩ := List.mem_map.1 hr
    rfl
  cover := by
    rw [List.map_map]
    exact coverCheck_sound hcover

/-- `L` has the sign, interval and weights of `L₀`. -/
def Line.sameHead (L L₀ : Line) : Bool :=
  (L.positive == L₀.positive) && (L.a.pos == L₀.a.pos) && (L.a.neg == L₀.a.neg) &&
    (L.b.pos == L₀.b.pos) && (L.b.neg == L₀.b.neg) && (L.d == L₀.d) &&
    all7 fun i => L.lam i == L₀.lam i

theorem Line.sameHead_spec {L L₀ : Line} (h : L.sameHead L₀ = true) :
    L.positive = L₀.positive ∧ L.interval = L₀.interval ∧ L.lam = L₀.lam := by
  simp only [sameHead, Bool.and_eq_true, beq_iff_eq, all7_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hp, ha₀⟩, ha₁⟩, hb₀⟩, hb₁⟩, hd⟩, hl⟩ := h
  refine ⟨hp, ?_, funext hl⟩
  simp only [interval, SNat.val, ha₀, ha₁, hb₀, hb₁, hd]

/-- The lines of a tilt bundle: line `a.index` is the row of the alternative `a`; it passes
`Line.check` for `a`, and has the sign, interval and weights of the first line. -/
def bundleCheck (lines : List Line) : Bool :=
  (lines.length == 21) && Alternative.all.all fun a =>
    (lines.getD a.index default).check .tilt nominalOwner a &&
      (lines.getD a.index default).sameHead (lines.getD 0 default)

theorem bundleCheck_spec {lines : List Line} (h : bundleCheck lines = true) (a : Alternative) :
    (lines.getD a.index default).check .tilt nominalOwner a = true ∧
      (lines.getD a.index default).sameHead (lines.getD 0 default) = true := by
  simp only [bundleCheck, Bool.and_eq_true, List.all_eq_true] at h
  exact h.2 a (Alternative.mem_all a)

/-- The tilt bundle of the 21 lines of `bundleCheck`. -/
def TiltBundle.ofLines (lines : List Line) (h : bundleCheck lines = true) : TiltBundle where
  interval := (lines.getD 0 default).interval
  lambda i := (lines.getD 0 default).lam i / ten8
  row a := (lines.getD a.index default).row .tilt nominalOwner a
  valid a := Line.check_sound _ _ _ _ (bundleCheck_spec h a).1
  same_interval a := (Line.sameHead_spec (bundleCheck_spec h a).2).2.1
  same_lambda a := by
    funext i
    simp only [Line.row_lambda, (Line.sameHead_spec (bundleCheck_spec h a).2).2.2]
  same_mode _ := rfl
  same_owners _ := rfl
  same_alternative _ := rfl
  same_sign a := (Line.sameHead_spec (bundleCheck_spec h a).2).1.trans
    (Line.sameHead_spec (bundleCheck_spec h .zero).2).1.symm

end SquaresInCircles.Eight.Candidate.Dual

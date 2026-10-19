module

public import SquaresInCircles.Eight.Arithmetic.Arctangent
public import SquaresInCircles.Eight.Arithmetic.PreparedRow

/-!
# Eight squares: the state chains of a table

Each square of a boundary cycle is given one arc of its role that contains its state, and so one
label for both of its edges. For each vertex and each curve, the table lists the arcs of that role
on that curve (`StateChains`); `StateChains.NumericValid` checks that they have the right role and
curve and are well formed, and that their intervals of the signed tangent `σ b / a` form a closed
chain over the cut of the vertex (`ClosedChain`, `ClosedCover.lean`). Then every square of a cycle
whose signed tangent lies in the cut lies on an arc of its chain (`StateChains.covers`); the sign
of the arc gives the same product `σ b` as the square, also at the tangent zero, where `b = 0`.
The margins depend on the signs only through these products.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Arithmetic

/-- `P` holds at every element of a list, as a decidable conjunction. -/
def Every {α : Type*} (P : α→ Prop) : List α→ Prop
  | [] => True | a::xs => P a ∧ Every P xs
instance everyDecidable {α : Type*} (P : α→ Prop) [DecidablePred P] (xs : List α) :
    Decidable (Every P xs) := by
  induction xs <;> simp only [Every] <;> infer_instance
theorem Every.of_mem {α : Type*} {P : α→ Prop} {xs : List α}
    (h : Every P xs) {x : α} (hx : x∈xs) : P x := by
  induction xs with
  | nil => simp at hx
  | cons a xs ih =>
      rcases List.mem_cons.mp hx with rfl | hx
      · exact h.1
      · exact ih h.2 hx

/-- The interval of the signed tangent `σ b / a` on the arc. -/
def ArcData.signedInterval (a : ArcData) : QInterval :=
  if a.positive then a.tangent else a.tangent.neg

/-- Whether a radial kind is the outer curve. -/
def radialOuter : RadialKind→ Bool | .outer => true | .coreSide => false | .coreCorner => false
/-- The arc `i` of a table (a default arc for an index out of range). -/
def arcAt (M : AffineTableMeta) (i : ℕ) : ArcData := M.arcs.getD i default

/-- A signed tangent in the signed interval of a well-formed arc has its absolute value in the
tangent interval and the sign of the arc. -/
theorem signed_interval_absolute {a : ArcData} (ha : a.WellFormed) {t : ℝ}
    (ht : a.signedInterval.Mem t) : a.tangent.Mem |t| ∧ t=a.sign*|t| := by
  have hlo : (0:ℝ)≤a.tangent.lo := by exact_mod_cast ha.1
  cases hs : a.positive with
  | true =>
      have hi : a.tangent.Mem t := by simpa [ArcData.signedInterval,hs] using ht
      have h0 : 0≤t := hlo.trans hi.1
      simpa [ArcData.sign,hs,abs_of_nonneg h0] using And.intro hi (rfl : t=t)
  | false =>
      have hi : (-(a.tangent.hi : ℝ)≤t) ∧ t≤-(a.tangent.lo : ℝ) := by
        simpa [ArcData.signedInterval,QInterval.Mem,QInterval.neg,hs] using ht
      have h0 : t≤0 := by linarith
      constructor
      · rw [abs_of_nonpos h0]
        exact ⟨by linarith,by linarith⟩
      · simp [ArcData.sign,hs,abs_of_nonpos h0]

theorem boundary_tangent_absolute {q : ℝ} (C : BoundaryCycle q) (i : Vertex) :
    |C.tangent i|=C.b i/C.a i := by
  rcases C.sigma_sign i with hs | hs <;>
    simp [BoundaryCycle.tangent,hs,abs_div,abs_of_pos (C.a_pos i),
      abs_of_nonneg (C.b_nonneg i)]

/-- A square of the cycle on the curve of a well-formed arc, with its tangent in the tangent
interval of the arc, lies on the curve of the arc (`ArcData.OnCurve`): the core side and the core
corner meet at the tangent `6/7`. -/
theorem boundary_on_arc_curve {q : ℝ} (C : BoundaryCycle q) (i : Vertex)
    {a : ArcData} (ha : a.WellFormed) (hout : a.outer=radialOuter (C.kind i))
    (ht : a.tangent.Mem (C.b i/C.a i)) : a.OnCurve q (C.a i) (C.b i) := by
  have hb := C.boundary i
  have hA := C.a_pos i
  have hB := C.b_nonneg i
  have hBA := C.b_le_a i
  cases hk : C.kind i with
  | outer =>
      have ho : a.outer=true := by simpa [radialOuter,hk] using hout
      rw [hk] at hb
      simpa [ArcData.OnCurve,ho,BoundaryState,SquaresInCircles.phi] using hb
  | coreSide =>
      have ho : a.outer=false := by simpa [radialOuter,hk] using hout
      rw [hk] at hb
      have hb' : C.a i=7/12 ∧ C.b i≤1/2 := by simpa [BoundaryState] using hb
      by_cases hhi : a.tangent.hi≤6/7
      · simpa [ArcData.OnCurve,ho,hhi] using hb'
      · have hlo : (6/7:ℝ)≤a.tangent.lo := by
          have h := (Rat.cast_le (K := ℝ)).mpr ((ha.2.2.2 ho).resolve_left hhi)
          rw [Rat.cast_div,Rat.cast_ofNat,Rat.cast_ofNat] at h
          exact h
        have hratio : (6/7:ℝ)≤C.b i/C.a i := hlo.trans ht.1
        have hcross := (le_div_iff₀ hA).mp hratio
        have he : C.b i=1/2 := by
          rw [hb'.1] at hcross
          linarith [hb'.2]
        simp only [ArcData.OnCurve,ho,hhi,Bool.false_eq_true,ite_false]
        rw [hb'.1,he]
        norm_num
  | coreCorner =>
      have ho : a.outer=false := by simpa [radialOuter,hk] using hout
      rw [hk] at hb
      have hb' : 1/2≤C.b i ∧ (C.a i-1/2)^2+(C.b i-1/2)^2=(1/12:ℝ)^2 := by
        simpa [BoundaryState] using hb
      by_cases hhi : a.tangent.hi≤6/7
      · have haU : C.a i≤7/12 := by nlinarith [sq_nonneg (C.b i-1/2)]
        have hhi' : (a.tangent.hi : ℝ)≤6/7 := by
          have h := (Rat.cast_le (K := ℝ)).mpr hhi
          rw [Rat.cast_div,Rat.cast_ofNat,Rat.cast_ofNat] at h
          exact h
        have hratio : C.b i/C.a i≤(6/7:ℝ) := ht.2.trans hhi'
        have hcross := (div_le_iff₀ hA).mp hratio
        have heA : C.a i=7/12 := by linarith [hb'.1]
        have heB : C.b i=1/2 := by linarith [hb'.1]
        simp only [ArcData.OnCurve,ho,hhi,Bool.false_eq_true,ite_false,ite_true]
        rw [heA,heB]
        norm_num
      · simpa [ArcData.OnCurve,ho,hhi] using hb'

/-- A square of the cycle whose signed tangent lies in the signed interval of a well-formed arc
of its curve lies on the arc, and the sign of the arc gives the same product `σ b`. -/
theorem boundary_arc_contains {q : ℝ} (C : BoundaryCycle q) (i : Vertex)
    {a : ArcData} (ha : a.WellFormed) (hout : a.outer=radialOuter (C.kind i))
    (ht : a.signedInterval.Mem (C.tangent i)) :
    a.Contains q (C.a i) (C.b i) ∧ a.sign*C.b i=C.sigma i*C.b i := by
  have hs := signed_interval_absolute ha ht
  rw [boundary_tangent_absolute] at hs
  have hc := boundary_on_arc_curve C i ha hout hs.1
  refine ⟨⟨C.a_pos i,C.b_nonneg i,C.b_le_a i,hs.1,hc⟩,?_⟩
  have he := congrArg (fun z : ℝ => z*C.a i) hs.2
  have ha0 := ne_of_gt (C.a_pos i)
  dsimp [BoundaryCycle.tangent] at he
  field_simp [ha0] at he
  nlinarith only [he]

/-- For each vertex and each curve (outer or core), a list of indices of arcs. -/
def StateChains := Vertex→ Bool→ List ℕ
/-- The checks of the state chains: every index names a well-formed arc of the vertex on the
curve, and the signed intervals of each chain form a closed chain over the cut of the vertex. -/
def StateChains.NumericValid (M : AffineTableMeta) (S : StateChains) : Prop :=
  ∀ i : Vertex, ∀ outer : Bool,
    Every (fun k => k<M.arcs.length ∧ (arcAt M k).role=i ∧
      (arcAt M k).outer=outer ∧ (arcAt M k).WellFormed) (S i outer) ∧
    ClosedChain (M.cuts i).lo (M.cuts i).hi
      ((S i outer).map (fun k => (arcAt M k).signedInterval))
instance (M : AffineTableMeta) (S : StateChains) : Decidable (S.NumericValid M) := by
  unfold StateChains.NumericValid
  refine @Fintype.decidableForallFintype _ _ (fun i => ?_) _
  unfold ArcData.WellFormed
  infer_instance

/-- Every square of a cycle whose signed tangents lie in the cuts lies on an arc of its role,
whose sign gives the same product `σ b`. -/
theorem StateChains.covers {M : AffineTableMeta} {S : StateChains}
    (hS : S.NumericValid M) (C : BoundaryCycle (M.radius : ℝ))
    (hc : ∀ i, (M.cuts i).Mem (C.tangent i)) (i : Vertex) :
    ∃ k : Fin M.arcs.length, (arcAt M k).role=i ∧
      (arcAt M k).Contains M.radius (C.a i) (C.b i) ∧
      (arcAt M k).sign*C.b i=C.sigma i*C.b i := by
  let outer := radialOuter (C.kind i)
  obtain ⟨I,hI,hIx⟩ := (hS i outer).2.covers (hc i)
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hI
  have hn := (hS i outer).1.of_mem hk
  have hcontain := boundary_arc_contains C i hn.2.2.2 hn.2.2.1 hIx
  exact ⟨⟨k,hn.1⟩,hn.2.1,hcontain.1,hcontain.2⟩

end SquaresInCircles.Eight.Arithmetic

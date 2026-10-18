module

public import SquaresInCircles.Eight.Arithmetic.Arctangent
public import SquaresInCircles.Eight.Arithmetic.PreparedRow

/-!
# Closed state coverage and consistent labels

Coverage is in the signed tangent coordinate.  At tangent zero either sign
represents the same state; the resulting theorem preserves the signed product
σb, which is exactly what occurs in every original separating margin.
-/

@[expose] public section
namespace SquaresInCircles.Eight.Arithmetic

def Every {α : Type*} (P : α→Prop) : List α→Prop
  | [] => True | a::xs => P a ∧ Every P xs
instance everyDecidable {α : Type*} (P : α→Prop) [DecidablePred P] (xs : List α) :
    Decidable (Every P xs) := by
  induction xs <;> simp only [Every] <;> infer_instance
theorem Every.of_mem {α : Type*} {P : α→Prop} {xs : List α}
    (h : Every P xs) {x : α} (hx : x∈xs) : P x := by
  induction xs with
  | nil => simp at hx
  | cons a xs ih =>
      rcases List.mem_cons.mp hx with rfl | hx
      · exact h.1
      · exact ih h.2 hx

theorem list_getD_mem {α : Type*} {xs : List α} {d : α} {i : ℕ}
    (hi : i<xs.length) : xs.getD i d∈xs := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
      cases i with
      | zero => simp
      | succ i =>
          have hii : i<xs.length := by simpa using hi
          simpa using List.mem_cons_of_mem a (ih hii)

def ArcData.signedInterval (a : ArcData) : QInterval :=
  if a.positive then a.tangent else a.tangent.neg

def radialOuter : RadialKind→Bool | .outer => true | .coreSide => false | .coreCorner => false
def arcAt (M : AffineTableMeta) (i : ℕ) : ArcData := M.arcs.getD i default

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
      simpa [ArcData.OnCurve,ho,BoundaryState,hk,SquaresInCircles.phi] using hb
  | coreSide =>
      have ho : a.outer=false := by simpa [radialOuter,hk] using hout
      have hb' : C.a i=7/12 ∧ C.b i≤1/2 := by simpa [BoundaryState,hk] using hb
      by_cases hhi : a.tangent.hi≤6/7
      · simpa [ArcData.OnCurve,ho,hhi] using hb'
      · have hlo : (6/7:ℝ)≤a.tangent.lo := by
          exact_mod_cast (ha.2.2.2 ho).resolve_left hhi
        have hratio : (6/7:ℝ)≤C.b i/C.a i := hlo.trans ht.1
        have hcross := (le_div_iff₀ hA).mp hratio
        have he : C.b i=1/2 := by nlinarith [hb'.1,hb'.2]
        simp [ArcData.OnCurve,ho,hhi,hb'.1,he]
        norm_num
  | coreCorner =>
      have ho : a.outer=false := by simpa [radialOuter,hk] using hout
      have hb' : 1/2≤C.b i ∧ (C.a i-1/2)^2+(C.b i-1/2)^2=(1/12:ℝ)^2 := by
        simpa [BoundaryState,hk] using hb
      by_cases hhi : a.tangent.hi≤6/7
      · have haU : C.a i≤7/12 := by nlinarith [sq_nonneg (C.b i-1/2)]
        have hratio : C.b i/C.a i≤(6/7:ℝ) := ht.2.trans (by exact_mod_cast hhi)
        have hcross := (div_le_iff₀ hA).mp hratio
        have heA : C.a i=7/12 := by nlinarith [hb'.1]
        have heB : C.b i=1/2 := by nlinarith [hb'.1]
        simp [ArcData.OnCurve,ho,hhi,heA,heB]
      · simpa [ArcData.OnCurve,ho,hhi] using hb'

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

def StateChains := Vertex→Bool→List ℕ
def StateChains.NumericValid (M : AffineTableMeta) (S : StateChains) : Prop :=
  ∀ i : Vertex, ∀ outer : Bool,
    Every (fun k => k<M.arcs.length ∧ (arcAt M k).role=i ∧
      (arcAt M k).outer=outer ∧ (arcAt M k).WellFormed) (S i outer) ∧
    ClosedChain (M.cuts i).lo (M.cuts i).hi
      ((S i outer).map (fun k => (arcAt M k).signedInterval))
instance (M : AffineTableMeta) (S : StateChains) : Decidable (S.NumericValid M) := by
  unfold StateChains.NumericValid ArcData.WellFormed
  infer_instance

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

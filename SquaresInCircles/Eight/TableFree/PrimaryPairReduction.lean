module

public import SquaresInCircles.Eight.TableFree.PositivePairEndpoints
public import SquaresInCircles.Eight.TableFree.NegativeContactGeometry

/-!
# Same-radius positive-total primary-pair reduction, with all error signs

Uncompiled draft. The scalar endpoint theorem combines nonnegative errors
with both signed-cancellation orders. The G and T adapters retain actual
signed tangent coordinates and both original projected inequalities.

The sole local alternative not an alignment is an actual nearest-axis tie.
It is returned explicitly, rather than discarded by a local bound. Its
exclusion belongs to the global quarter-word argument.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
open Candidate
namespace PairedPrimary

theorem positive_total_endpoint {q B D u v : ℝ} {p : SignedPoint}
    (hqL : qLow≤q) (hqU : q≤qCap)
    (hB : diagonalCoordinate q≤B ∧ B≤axisCoordinate q)
    (hD : 0≤D ∧ D≤diagonalCoordinate q)
    (hu : |u|≤7/10) (hv : |v|≤7/10)
    (ht0 : 0<u+v) (ht : u+v≤7/10)
    (hs : p.Sorted) (hcore : p.AvoidsCore) (hc : p.Contained q)
    (h₁ : edgeWidth u≤B+p.a*Real.sin u-p.y*Real.cos u)
    (h₂ : edgeWidth v≤p.a*Real.sin v+p.y*Real.cos v+D) :
    Nonempty (Endpoint q B D (u+v)) := by
  by_cases hu0 : 0≤u
  · by_cases hv0 : 0≤v
    · exact nonnegative_pair_endpoint hqL hqU hB hD.2 hu0 hv0 ht0 ht hs hc h₁ h₂
    · have hvneg : v<0 := lt_of_not_ge hv0
      have huPos : 0<u := by linarith
      have hDa : D≤axisCoordinate q := by
        have hdiag : diagonalCoordinate q≤axisCoordinate q := by
          have hp := SignedPoint.outerAt_spec hqL
            (show |(0:ℝ)|≤diagonalCoordinate q by
              have h := (uniform_circle_reserves hqL hqU).1
              norm_num; linarith)
          exact (SignedPoint.outer_bounds hp.1 hp.2.1).1.trans
            (SignedPoint.outer_bounds hp.1 hp.2.1).2.2
        exact hD.2.trans hdiag
      obtain ⟨p',hps,hpo,hpc,hsecond,hfirst⟩ := NegativeContact.second_negative_alignment
        hqL hqU ⟨hD.1,hDa⟩ ⟨huPos,(abs_le.mp hu).2⟩
        ⟨(abs_le.mp hv).1,hvneg⟩ ht0 hs hcore hc h₁ h₂
      refine ⟨⟨p',u+v,⟨ht0.le,le_rfl⟩,hps,hpo,hpc,hfirst,?_,Or.inr (Or.inl rfl)⟩⟩
      simpa using hsecond.ge
  · have huneg : u<0 := lt_of_not_ge hu0
    have hvpos : 0<v := by linarith
    have hB0 : 0≤B := by
      have hdiag := (uniform_circle_reserves hqL hqU).1
      linarith [hB.1]
    obtain ⟨p',hps,hpo,hpc,hfirst,hsecond⟩ := NegativeContact.first_negative_alignment
      hqL hqU ⟨hB0,hB.2⟩ ⟨(abs_le.mp hu).1,huneg⟩
      ⟨hvpos,(abs_le.mp hv).2⟩ ht0 hs hcore hc h₁ h₂
    refine ⟨⟨p',0,⟨le_rfl,ht0.le⟩,hps,hpo,hpc,?_,?_,Or.inl rfl⟩⟩
    · simpa using hfirst.ge
    · simpa using hsecond

/-- Positive and negative variation cannot increase under the endpoint
replacement, including either original signed-cancellation order. -/
theorem endpoint_variation {q B D u v : ℝ} (E : Endpoint q B D (u+v)) :
    max E.firstError 0+max (u+v-E.firstError) 0≤max u 0+max v 0 ∧
      max (-E.firstError) 0+max (-(u+v-E.firstError)) 0≤max (-u) 0+max (-v) 0 := by
  have hx := E.first_mem
  have hsecond : 0≤u+v-E.firstError := by linarith
  rw [max_eq_left hx.1,max_eq_left hsecond,
    max_eq_right (neg_nonpos.mpr hx.1),max_eq_right (neg_nonpos.mpr hsecond)]
  constructor
  · linarith [le_max_left u 0,le_max_left v 0]
  · positivity

/-- The new frame remains between the two unchanged endpoint frames. -/
theorem endpoint_frame {q B D t l : ℝ} (E : Endpoint q B D t) :
    l≤l+E.firstError ∧ l+E.firstError≤l+t := by
  constructor <;> linarith [E.first_mem.1,E.first_mem.2]

end PairedPrimary

/-- G-only positive-total output, stated on its actual neighboring squares. -/
structure GPositiveEndpoint (q : ℝ) (H A : SignedPoint) (θH θA : ℝ) where
  G : SignedPoint
  theta : ℝ
  theta_mem : θH≤theta ∧ theta≤θA
  sorted : G.Sorted
  outer : G.Outer q
  core : G.AvoidsCore
  HG : zeroFeasible H G (theta-θH) 0
  GA : quarterFeasible G A (θA-theta) 1
  endpoint : theta=θA ∨ theta=θH ∨ G.y= -G.a

theorem positive_GA_HG_pair {q θH θG θA : ℝ} {H G A : SignedPoint}
    (hqL : qLow≤q) (hqU : q≤qCap)
    (hH : H.Sorted) (hA : A.Sorted) (hG : G.Sorted)
    (hHnormal : 0≤H.y) (hHcircle : H.Contained q) (hAouter : A.Outer q)
    (hGcircle : G.Contained q) (hGcore : G.AvoidsCore)
    (hHG : zeroFeasible H G (θG-θH) 0)
    (hGA : quarterFeasible G A (θA-θG) 1)
    (hfirst : |θA-θG|≤7/10) (hsecond : |θG-θH|≤7/10)
    (ht : 0<θA-θH ∧ θA-θH≤7/10) :
    Nonempty (GPositiveEndpoint q H A θH θA) := by
  have hAs := SignedPoint.outer_bounds hA hAouter
  have hHs := SignedPoint.contained_minor_le_diagonal hH hHcircle
  have hsum : (θA-θG)+(θG-θH)=θA-θH := by ring
  obtain ⟨E⟩ := PairedPrimary.positive_total_endpoint
    (p := G.reflect) (B := A.a) (D := H.y)
    hqL hqU ⟨hAs.1,hAs.2.2⟩
    ⟨hHnormal,by simpa [abs_of_nonneg hHnormal] using hHs⟩
    hfirst hsecond (by rwa [hsum]) (by rwa [hsum])
    ((SignedPoint.reflect_sorted G).mpr hG)
    ((SignedPoint.reflect_avoidsCore G).mpr hGcore)
    ((SignedPoint.reflect_contained G q).mpr hGcircle)
    (by simpa [quarterFeasible,quarterProjection,SignedPoint.reflect] using hGA)
    (by simpa [zeroFeasible,zeroProjection,SignedPoint.reflect,add_comm,add_left_comm,add_assoc] using hHG)
  let G' := E.point.reflect
  let θ' := θA-E.firstError
  have hmem : θH≤θ' ∧ θ'≤θA := by
    dsimp [θ']
    constructor <;> linarith [E.first_mem.1,E.first_mem.2]
  have hsum' : (θA-θG)+(θG-θH)-E.firstError=θ'-θH := by dsimp [θ']; ring
  refine ⟨⟨G',θ',hmem,(SignedPoint.reflect_sorted E.point).mpr E.sorted,
    (SignedPoint.reflect_outer E.point q).mpr E.outer,
    (SignedPoint.reflect_avoidsCore E.point).mpr E.avoids_core,?_,?_,?_⟩⟩
  · have h := E.second_feasible
    rw [hsum'] at h
    simpa [G',zeroFeasible,zeroProjection,SignedPoint.reflect,add_comm,add_left_comm,add_assoc] using h
  · have h := E.first_feasible
    have he : θA-θ'=E.firstError := by dsimp [θ']; ring
    rw [he]
    simpa [G',quarterFeasible,quarterProjection,SignedPoint.reflect] using h
  · rcases E.endpoint with he | he | he
    · left
      dsimp [θ']
      linarith
    · right; left
      dsimp [θ']
      rw [hsum] at he
      linarith
    · right; right
      dsimp [G',SignedPoint.reflect]
      linarith

structure TPositiveEndpoint (q : ℝ) (B D : SignedPoint) (θB θD : ℝ) where
  T : SignedPoint
  theta : ℝ
  theta_mem : θB≤theta ∧ theta≤θD
  sorted : T.Sorted
  outer : T.Outer q
  core : T.AvoidsCore
  BT : quarterFeasible B T (theta-θB) 3
  TD : zeroFeasible T D (θD-theta) 2
  endpoint : theta=θB ∨ theta=θD ∨ T.y=T.a

theorem positive_BT_TD_pair {q θB θT θD : ℝ} {B T D : SignedPoint}
    (hqL : qLow≤q) (hqU : q≤qCap)
    (hB : B.Sorted) (hD : D.Sorted) (hT : T.Sorted)
    (hDnormal : D.y≤0) (hBouter : B.Outer q) (hDcircle : D.Contained q)
    (hTcircle : T.Contained q) (hTcore : T.AvoidsCore)
    (hBT : quarterFeasible B T (θT-θB) 3)
    (hTD : zeroFeasible T D (θD-θT) 2)
    (hfirst : |θT-θB|≤7/10) (hsecond : |θD-θT|≤7/10)
    (ht : 0<θD-θB ∧ θD-θB≤7/10) :
    Nonempty (TPositiveEndpoint q B D θB θD) := by
  have hBs := SignedPoint.outer_bounds hB hBouter
  have hDs := SignedPoint.contained_minor_le_diagonal hD hDcircle
  have hsum : (θT-θB)+(θD-θT)=θD-θB := by ring
  obtain ⟨E⟩ := PairedPrimary.positive_total_endpoint
    (p := T) (B := B.a) (D := -D.y)
    hqL hqU ⟨hBs.1,hBs.2.2⟩
    ⟨by linarith,by simpa [abs_of_nonpos hDnormal] using hDs⟩
    hfirst hsecond (by rwa [hsum]) (by rwa [hsum])
    hT hTcore hTcircle
    (by simpa [quarterFeasible,quarterProjection] using hBT)
    (by simpa [zeroFeasible,zeroProjection,sub_eq_add_neg,add_assoc] using hTD)
  let θ' := θB+E.firstError
  have hmem : θB≤θ' ∧ θ'≤θD := by
    dsimp [θ']
    constructor <;> linarith [E.first_mem.1,E.first_mem.2]
  have hsum' : (θT-θB)+(θD-θT)-E.firstError=θD-θ' := by dsimp [θ']; ring
  refine ⟨⟨E.point,θ',hmem,E.sorted,E.outer,E.avoids_core,?_,?_,?_⟩⟩
  · have he : θ'-θB=E.firstError := by dsimp [θ']; ring
    rw [he]
    simpa [quarterFeasible,quarterProjection] using E.first_feasible
  · have h := E.second_feasible
    rw [hsum'] at h
    simpa [zeroFeasible,zeroProjection,sub_eq_add_neg,add_assoc] using h
  · rcases E.endpoint with he | he | he
    · left
      dsimp [θ']
      linarith
    · right; left
      dsimp [θ']
      rw [hsum] at he
      linarith
    · exact Or.inr (Or.inr he)

end SquaresInCircles.Eight.TableFree
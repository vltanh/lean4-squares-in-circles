module

public import SquaresInCircles.Eight.Arithmetic.AffineCertificate
public import SquaresInCircles.Eight.Candidate.GeometricPrimaryExclusion

/-!
# Affine coverage with proved core-primary exclusions

Only zero-quarter target-core/target-primary and source-core/source-primary
domains are omitted.  Their infeasibility follows from the actual frame
geometry below.  All retained domains use exactly the original endpoint,
state, row-matching, and closed angle-chain predicates.  No exclusion list
or computed replacement coverage table is embedded.
-/

@[expose] public section
open scoped BigOperators
namespace SquaresInCircles.Eight.Candidate.GeometricAffine
open Arithmetic

def Excluded (M : AffineTableMeta) (s t : ℕ) (axis : ForwardAxis) : Prop :=
  (arcAt M s).role ∈ zeroEdges ∧
    ((axis=.two ∧ (arcAt M t).outer=false) ∨
     (axis=.four ∧ (arcAt M s).outer=false))

instance (M : AffineTableMeta) (s t : ℕ) (axis : ForwardAxis) :
    Decidable (Excluded M s t axis) := by unfold Excluded; infer_instance

/-- The original angle validity predicate, restricted only by a geometric
infeasibility theorem.  Retained chain and row checks are unchanged. -/
def AngleValid (K : AffineCover) (M : AffineTableMeta) (rows : List AffineTableRow) : Prop :=
  ∀ s t : Fin M.arcs.length,
    (arcAt M t).role=(arcAt M s).role+1 →
    ∀ axis : ForwardAxis, axis∈M.allowedAxes (arcAt M s).role →
      ¬ Excluded M s t axis → ∀ r : Bool,
      Every (fun k => k<rows.length ∧
        (rows.getD k default).source=s.val ∧ (rows.getD k default).target=t.val ∧
        (rows.getD k default).edge=(arcAt M s).role ∧ (rows.getD k default).axis=axis ∧
        (rows.getD k default).quarter=M.word (arcAt M s).role ∧
        (rows.getD k default).positiveHalf=r ∧
        M.target (arcAt M s).role≤(rows.getD k default).lowerTarget)
        (K.angleRows s t axis r) ∧
      ClosedChain (K.required M s t r).lo (K.required M s t r).hi
        ((K.angleRows s t axis r).map (fun k => (rows.getD k default).angle))

def NumericValid (K : AffineCover) (M : AffineTableMeta) (rows : List AffineTableRow) : Prop :=
  K.EndpointsValid M ∧ K.states.NumericValid M ∧ AngleValid K M rows

instance (K : AffineCover) (M : AffineTableMeta) (rows : List AffineTableRow) :
    Decidable (AngleValid K M rows) := by unfold AngleValid; infer_instance

instance (K : AffineCover) (M : AffineTableMeta) (rows : List AffineTableRow) :
    Decidable (NumericValid K M rows) := by unfold NumericValid; infer_instance

theorem arc_core_primary_upper {s : ArcData} {Q a b : ℝ}
    (hs : s.Contains Q a b) (hcore : s.outer=false) : a ≤ 7/12 := by
  have hc := hs.2.2.2.2
  by_cases hside : s.tangent.hi ≤ 6/7
  · simp [ArcData.OnCurve, hcore, hside] at hc
    exact hc.1.le
  · simp [ArcData.OnCurve, hcore, hside] at hc
    by_contra! ha
    nlinarith [sq_nonneg (a-7/12), sq_nonneg (b-1/2)]

/-- This is the soundness of the exclusion predicate, for original actual
axes. Arc membership, rather than a choice of radial label at a junction,
supplies the core primary-coordinate bound. -/
theorem feasible_not_excluded {M : AffineTableMeta}
    (C : BoundaryCycle (M.radius:ℝ)) (F : Frame C)
    {i : Vertex} {s t : Fin M.arcs.length}
    (hsi : (arcAt M s).role=i)
    (hs : (arcAt M s).Contains M.radius (C.a i) (C.b i))
    (ht : (arcAt M t).Contains M.radius (C.a (next i)) (C.b (next i)))
    (j : Fin 4) (hj : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    ¬ Excluded M s t (ForwardAxis.ofIndex j) := by
  rintro ⟨hi, ⟨haxis,hcore⟩ | ⟨haxis,hcore⟩⟩
  · have hi' : i∈zeroEdges := by simpa [hsi] using hi
    have hji : j=1 := by fin_cases j <;> norm_num [ForwardAxis.ofIndex] at haxis ⊢
    subst j
    have hlarge := (Geometric.zero_target_primary_requires_outer F hi' hj).2
    have hsmall := arc_core_primary_upper ht hcore
    linarith
  · have hi' : i∈zeroEdges := by simpa [hsi] using hi
    have hji : j=3 := by fin_cases j <;> norm_num [ForwardAxis.ofIndex] at haxis ⊢
    subst j
    have hlarge := (Geometric.zero_source_primary_requires_outer F hi' hj).2
    have hsmall := arc_core_primary_upper hs hcore
    linarith

theorem row_cover {K : AffineCover} {M : AffineTableMeta} {rows : List AffineTableRow}
    (hK : AngleValid K M rows) {s t : Fin M.arcs.length}
    (hst : (arcAt M t).role=(arcAt M s).role+1)
    {axis : ForwardAxis} (haxis : axis∈M.allowedAxes (arcAt M s).role)
    (hkeep : ¬ Excluded M s t axis)
    {r : Bool} {u : ℝ} (hu : (K.required M s t r).Mem u) :
    ∃ row ∈ rows,
      row.source=s.val ∧ row.target=t.val ∧ row.edge=(arcAt M s).role ∧
      row.axis=axis ∧ row.quarter=M.word (arcAt M s).role ∧
      row.positiveHalf=r ∧ row.angle.Mem u ∧ M.target (arcAt M s).role≤row.lowerTarget := by
  have hh := hK s t hst axis haxis hkeep r
  obtain ⟨I,hI,hIu⟩ := hh.2.covers hu
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hI
  have hp := hh.1.of_mem hk
  exact ⟨rows.getD k default,list_getD_mem hp.1,hp.2.1,hp.2.2.1,hp.2.2.2.1,
    hp.2.2.2.2.1,hp.2.2.2.2.2.1,hp.2.2.2.2.2.2.1,hIu,hp.2.2.2.2.2.2.2⟩

/-- The original assembly with one proved feasibility check before looking
up a retained angle chain. Labels are still selected once per vertex. -/
noncomputable def chargedBound {K : AffineCover} {M : AffineTableMeta} {rows : List AffineTableRow}
    (hK : NumericValid K M rows) (hrows : ∀ r∈rows, r.Claim M)
    (C : BoundaryCycle (M.radius:ℝ)) (F : Frame C) (β : ℝ)
    (hword : ∀ i, (M.word i:ℝ)=(Candidate.word i:ℝ))
    (hcharge : ∀ i, (M.charge i:ℝ)=Candidate.charge β i)
    (hcuts : ∀ i, (M.cuts i).Mem (C.tangent i))
    (hdiff : ∀ i, (M.differenceRange i).Mem (Candidate.delta F.theta i))
    (haxes : ∀ i j, (forwardAxis j).Feasible (C.square i) (C.square (next i)) →
      ForwardAxis.ofIndex j∈M.allowedAxes i) :
    ChargedBound C F β (fun i => (M.target i:ℝ)) := by
  choose selected hrole hcontains hproducts using fun i => K.states.covers hK.2.1 C hcuts i
  refine {label:=fun i => (arcAt M (selected i)).label.eval (C.a i) (C.b i),pair_bound:=?_}
  intro i j hj
  let axis := ForwardAxis.ofIndex j
  let d := Candidate.delta F.theta i
  let r : Bool := decide (0≤d)
  let u := |d|
  have hdu : Candidate.delta F.theta i=(AnglePolynomial.signQ r:ℝ)*u := by
    dsimp [r,u,d]
    by_cases hd : 0≤Candidate.delta F.theta i <;>
      simp [hd,AnglePolynomial.signQ,abs_of_nonneg,abs_of_neg]
  have hu := K.required_mem hK.1 C F hword hdiff (hrole i) (hcontains i)
    (hcontains (next i)) (hproducts i) (hproducts (next i)) (r:=r) (u:=u) rfl hdu
  have hallowed : axis∈M.allowedAxes (arcAt M (selected i)).role := by
    simpa [axis,hrole] using haxes i j hj
  have hkeep : ¬ Excluded M (selected i) (selected (next i)) axis :=
    feasible_not_excluded C F (hrole i) (hcontains i) (hcontains (next i)) j hj
  obtain ⟨row,hrow,hs,ht,he,ha,hk,hr,hru,hγ⟩ := row_cover hK.2.2
    (by rw [hrole,hrole]; rfl) hallowed hkeep hu
  have hsdata : row.sourceArc M=arcAt M (selected i) := by simp [AffineTableRow.sourceArc,arcAt,hs]
  have htdata : row.targetArc M=arcAt M (selected (next i)) := by simp [AffineTableRow.targetArc,arcAt,ht]
  have he' : row.edge=i := he.trans (hrole i)
  have hphi : row.phi u=Candidate.phi F.theta i := by
    rw [AffineTableRow.phi,hk,hrole]
    rw [show row.sign=(AnglePolynomial.signQ r:ℝ) by cases r <;> simp [AffineTableRow.sign,hr,AnglePolynomial.signQ]]
    rw [← hdu,hword]
    rfl
  have hdom : row.Domain M (C.a i) (C.b i) (C.a (next i)) (C.b (next i)) u :=
    ⟨by simpa [hsdata] using hcontains i,by simpa [htdata] using hcontains (next i),hru⟩
  have hactual := (F.margin_nonneg_iff i j).mp hj
  have horiginal : 0≤Arithmetic.forwardMargin axis (C.sigma i) (C.sigma (next i))
      (C.a i) (C.b i) (C.a (next i)) (C.b (next i)) (Candidate.phi F.theta i) := by
    simpa [forwardMargin_actual,axis,Candidate.margin] using hactual
  have hselected : 0≤Arithmetic.forwardMargin row.axis (row.sourceArc M).sign (row.targetArc M).sign
      (C.a i) (C.b i) (C.a (next i)) (C.b (next i)) (row.phi u) := by
    rw [ha,hsdata,htdata,hphi,
      forwardMargin_congr_products axis (hproducts i) (hproducts (next i))]
    exact horiginal
  have hp := hrows row hrow _ _ _ _ _ hdom hselected
  have htarget : (M.target i:ℝ)≤row.lowerTarget := by
    simpa [hrole] using
      (show (M.target (arcAt M (selected i)).role:ℝ)≤row.lowerTarget by exact_mod_cast hγ)
  have hh := htarget.trans_lt hp
  simpa [chargedCost,frameCharge,Candidate.h,hsdata,htdata,he',hphi,hcharge,
    sub_eq_add_neg,add_assoc,add_comm,add_left_comm] using hh

end SquaresInCircles.Eight.Candidate.GeometricAffine

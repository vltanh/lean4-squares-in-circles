module

public import SquaresInCircles.Eight.Candidate.GeometricCoreMarker

/-!
# Coarse affine coverage with coherent selected labels

Core/core pairs use center separation and whole-arc marker bounds. Other
pairs retain the original closed angle chains. The two explicit selected-
arc interfaces allow a cyclic proof to strengthen one edge without
changing either adjacent vertex label. Uncompiled source.
-/

@[expose] public section
open scoped BigOperators
namespace SquaresInCircles.Eight.Candidate.GeometricCoreCoverage
open Arithmetic

def AngleValid (K : AffineCover) (M : AffineTableMeta) (rows : List AffineTableRow) : Prop :=
  ∀ s t : Fin M.arcs.length,
    (arcAt M t).role = (arcAt M s).role+1 →
    ∀ axis : ForwardAxis, axis ∈ M.allowedAxes (arcAt M s).role →
      ¬ GeometricAffine.Excluded M s t axis →
      ((arcAt M s).outer = true ∨ (arcAt M t).outer = true) → ∀ r : Bool,
      Every (fun k => k < rows.length ∧
        (rows.getD k default).source = s.val ∧ (rows.getD k default).target = t.val ∧
        (rows.getD k default).edge = (arcAt M s).role ∧ (rows.getD k default).axis = axis ∧
        (rows.getD k default).quarter = M.word (arcAt M s).role ∧
        (rows.getD k default).positiveHalf = r ∧
        M.target (arcAt M s).role ≤ (rows.getD k default).lowerTarget)
        (K.angleRows s t axis r) ∧
      ClosedChain (K.required M s t r).lo (K.required M s t r).hi
        ((K.angleRows s t axis r).map (fun k => (rows.getD k default).angle))

def NumericValid (K : AffineCover) (M : AffineTableMeta) (rows : List AffineTableRow) : Prop :=
  K.EndpointsValid M ∧ K.states.NumericValid M ∧
    GeometricCoreMarker.MarkersValid K M ∧ GeometricCoreMarker.BudgetsValid M ∧
    AngleValid K M rows

instance (K : AffineCover) (M : AffineTableMeta) (rows : List AffineTableRow) :
    Decidable (AngleValid K M rows) := by unfold AngleValid; infer_instance

instance (K : AffineCover) (M : AffineTableMeta) (rows : List AffineTableRow) :
    Decidable (NumericValid K M rows) := by unfold NumericValid; infer_instance

theorem row_cover {K : AffineCover} {M : AffineTableMeta} {rows : List AffineTableRow}
    (hK : AngleValid K M rows) {s t : Fin M.arcs.length}
    (hst : (arcAt M t).role = (arcAt M s).role+1)
    {axis : ForwardAxis} (haxis : axis ∈ M.allowedAxes (arcAt M s).role)
    (hkeep : ¬ GeometricAffine.Excluded M s t axis)
    (houter : (arcAt M s).outer = true ∨ (arcAt M t).outer = true)
    {r : Bool} {u : ℝ} (hu : (K.required M s t r).Mem u) :
    ∃ row ∈ rows,
      row.source = s.val ∧ row.target = t.val ∧ row.edge = (arcAt M s).role ∧
      row.axis = axis ∧ row.quarter = M.word (arcAt M s).role ∧
      row.positiveHalf = r ∧ row.angle.Mem u ∧ M.target (arcAt M s).role ≤ row.lowerTarget := by
  have hh := hK s t hst axis haxis hkeep houter r
  obtain ⟨I,hI,hIu⟩ := hh.2.covers hu
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hI
  have hp := hh.1.of_mem hk
  exact ⟨rows.getD k default, list_getD_mem hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1,
    hp.2.2.2.2.1, hp.2.2.2.2.2.1, hp.2.2.2.2.2.2.1, hIu, hp.2.2.2.2.2.2.2⟩

theorem outer_pair_bound {K : AffineCover} {M : AffineTableMeta} {rows : List AffineTableRow}
    (hK : K.EndpointsValid M) (hangle : AngleValid K M rows)
    (hrows : ∀ r ∈ rows, r.Claim M)
    (C : BoundaryCycle (M.radius:ℝ)) (F : Frame C)
    (hword : ∀ i, (M.word i:ℝ) = (Candidate.word i:ℝ))
    (hdiff : ∀ i, (M.differenceRange i).Mem (Candidate.delta F.theta i))
    (haxes : ∀ i j, (forwardAxis j).Feasible (C.square i) (C.square (next i)) →
      ForwardAxis.ofIndex j ∈ M.allowedAxes i)
    {i : Vertex} {s t : Fin M.arcs.length}
    (hsi : (arcAt M s).role = i) (hti : (arcAt M t).role = next i)
    (hs : (arcAt M s).Contains M.radius (C.a i) (C.b i))
    (ht : (arcAt M t).Contains M.radius (C.a (next i)) (C.b (next i)))
    (hσ : (arcAt M s).sign*C.b i = C.sigma i*C.b i)
    (hτ : (arcAt M t).sign*C.b (next i) = C.sigma (next i)*C.b (next i))
    (houter : (arcAt M s).outer = true ∨ (arcAt M t).outer = true)
    (j : Fin 4) (hj : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    (M.target i:ℝ) < chargedCost (arcAt M s).label (arcAt M t).label
      (M.charge i) (C.a i) (C.b i) (C.a (next i)) (C.b (next i)) (phi F.theta i) := by
  let axis := ForwardAxis.ofIndex j
  let d := Candidate.delta F.theta i
  let r : Bool := decide (0 ≤ d)
  let u := |d|
  have hdu : Candidate.delta F.theta i = (AnglePolynomial.signQ r:ℝ)*u := by
    dsimp [r,u,d]
    by_cases hd : 0 ≤ Candidate.delta F.theta i <;>
      simp [hd,AnglePolynomial.signQ,abs_of_nonneg,abs_of_neg]
  have hu := K.required_mem hK C F hword hdiff hsi hs ht hσ hτ
    (r := r) (u := u) rfl hdu
  have hallowed : axis ∈ M.allowedAxes (arcAt M s).role := by
    simpa [axis,hsi] using haxes i j hj
  have hkeep : ¬ GeometricAffine.Excluded M s t axis :=
    GeometricAffine.feasible_not_excluded C F hsi hs ht hσ hτ j hj
  obtain ⟨row,hrow,hsource,htarget,he,ha,hk,hr,hru,hγ⟩ := row_cover hangle
    (by rw [hsi,hti]; rfl) hallowed hkeep houter hu
  have hsdata : row.sourceArc M = arcAt M s := by
    simp [AffineTableRow.sourceArc,arcAt,hsource]
  have htdata : row.targetArc M = arcAt M t := by
    simp [AffineTableRow.targetArc,arcAt,htarget]
  have he' : row.edge = i := he.trans hsi
  have hphi : row.phi u = Candidate.phi F.theta i := by
    rw [AffineTableRow.phi,hk,hsi]
    rw [show row.sign = (AnglePolynomial.signQ r:ℝ) by
      cases r <;> simp [AffineTableRow.sign,hr,AnglePolynomial.signQ]]
    rw [← hdu,hword]
    rfl
  have hdom : row.Domain M (C.a i) (C.b i) (C.a (next i)) (C.b (next i)) u :=
    ⟨by simpa [hsdata] using hs, by simpa [htdata] using ht, hru⟩
  have hactual := (F.margin_nonneg_iff i j).mp hj
  have horiginal : 0 ≤ Arithmetic.forwardMargin axis (C.sigma i) (C.sigma (next i))
      (C.a i) (C.b i) (C.a (next i)) (C.b (next i)) (Candidate.phi F.theta i) := by
    simpa [forwardMargin_actual,axis,Candidate.margin] using hactual
  have hselected : 0 ≤ Arithmetic.forwardMargin row.axis (row.sourceArc M).sign
      (row.targetArc M).sign (C.a i) (C.b i) (C.a (next i)) (C.b (next i)) (row.phi u) := by
    rw [ha,hsdata,htdata,hphi,forwardMargin_congr_products axis hσ hτ]
    exact horiginal
  have hp := hrows row hrow _ _ _ _ _ hdom hselected
  have htarget' : (M.target i:ℝ) ≤ row.lowerTarget := by
    simpa [hsi] using
      (show (M.target (arcAt M s).role:ℝ) ≤ row.lowerTarget by exact_mod_cast hγ)
  simpa [hsdata,htdata,he',hphi] using htarget'.trans_lt hp

theorem pair_bound {K : AffineCover} {M : AffineTableMeta} {rows : List AffineTableRow}
    (hK : NumericValid K M rows) (hrows : ∀ r ∈ rows, r.Claim M)
    (C : BoundaryCycle (M.radius:ℝ)) (F : Frame C)
    (hword : ∀ i, (M.word i:ℝ) = (Candidate.word i:ℝ))
    (hdiff : ∀ i, (M.differenceRange i).Mem (Candidate.delta F.theta i))
    (haxes : ∀ i j, (forwardAxis j).Feasible (C.square i) (C.square (next i)) →
      ForwardAxis.ofIndex j ∈ M.allowedAxes i)
    {i : Vertex} {s t : Fin M.arcs.length}
    (hsi : (arcAt M s).role = i) (hti : (arcAt M t).role = next i)
    (hs : (arcAt M s).Contains M.radius (C.a i) (C.b i))
    (ht : (arcAt M t).Contains M.radius (C.a (next i)) (C.b (next i)))
    (hσ : (arcAt M s).sign*C.b i = C.sigma i*C.b i)
    (hτ : (arcAt M t).sign*C.b (next i) = C.sigma (next i)*C.b (next i))
    (j : Fin 4) (hj : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    (M.target i:ℝ) < chargedCost (arcAt M s).label (arcAt M t).label
      (M.charge i) (C.a i) (C.b i) (C.a (next i)) (C.b (next i)) (phi F.theta i) := by
  by_cases hcore : (arcAt M s).outer = false ∧ (arcAt M t).outer = false
  · exact GeometricCoreMarker.pair_bound hK.1 hK.2.2.1 hK.2.2.2.1 C F
      hsi hti hs ht hσ hτ hcore.1 hcore.2 j hj
  · have houter : (arcAt M s).outer = true ∨ (arcAt M t).outer = true := by
      cases hs' : (arcAt M s).outer <;> cases ht' : (arcAt M t).outer <;> simp_all
    exact outer_pair_bound hK.1 hK.2.2.2.2 hrows C F hword hdiff haxes
      hsi hti hs ht hσ hτ houter j hj

noncomputable def chargedBound {K : AffineCover} {M : AffineTableMeta}
    {rows : List AffineTableRow} (hK : NumericValid K M rows)
    (hrows : ∀ r ∈ rows, r.Claim M)
    (C : BoundaryCycle (M.radius:ℝ)) (F : Frame C) (β : ℝ)
    (hword : ∀ i, (M.word i:ℝ) = (Candidate.word i:ℝ))
    (hcharge : ∀ i, (M.charge i:ℝ) = Candidate.charge β i)
    (hcuts : ∀ i, (M.cuts i).Mem (C.tangent i))
    (hdiff : ∀ i, (M.differenceRange i).Mem (Candidate.delta F.theta i))
    (haxes : ∀ i j, (forwardAxis j).Feasible (C.square i) (C.square (next i)) →
      ForwardAxis.ofIndex j ∈ M.allowedAxes i) :
    ChargedBound C F β (fun i => (M.target i:ℝ)) := by
  choose selected hrole hcontains hproducts using fun i => K.states.covers hK.2.1 C hcuts i
  refine {label := fun i => (arcAt M (selected i)).label.eval (C.a i) (C.b i), pair_bound := ?_}
  intro i j hj
  have hp := pair_bound hK hrows C F hword hdiff haxes
    (hrole i) (hrole (next i)) (hcontains i) (hcontains (next i))
    (hproducts i) (hproducts (next i)) j hj
  simpa [chargedCost,frameCharge,Candidate.h,hcharge,
    sub_eq_add_neg,add_assoc,add_comm,add_left_comm] using hp

end SquaresInCircles.Eight.Candidate.GeometricCoreCoverage

module

public import SquaresInCircles.Eight.TableFree.SignedStress
public import SquaresInCircles.Eight.TableFree.NecessaryCycle

/-!
# A concrete four-circle obstruction to an actual high GA witness

Uncompiled source draft. The exact zero-error stress is the one in
HAND_G3_HIGH_GA_LOW_EH_SECONDARY_OWNER_FOUR_CIRCLE_EXCLUSION.md, Section 2.
The perturbation estimate below applies to every owner in the full high-GA
necessary owner domain, including both owners of every weak tie. It gives
an explicit necessary error budget, and excludes high GA when every actual
edge error is at most 1/225.

No outer equality, tangent sign, frame order, core endpoint, or selected
low GA witness is an input. A, T, and E cancel in the exact linear sum.
The sorted D support is essential and is proved directly from its circle.

This is one proved region of the global GA theorem. The full interval
`positiveVariation < 7/10` still requires the signed primary-total and
angular concentration arguments in HAND_G3_GLOBAL_GA_OWNER_RIGIDITY.md;
that conclusion is neither asserted nor assumed here.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA
open Candidate SignedStress

def highGAOwners : Vertex → Finset (Fin 4) :=
  ![{0,2},{2,3},{0,2},{2,3},{0,2},{2,3},{0,1}]

theorem highGAOwners_eq_normal {i : Vertex} (hi : i≠G) :
    highGAOwners i=SignedCycle.normalOwners i := by
  fin_cases i <;> norm_num [G] at hi <;>
    simp [highGAOwners,SignedCycle.normalOwners]

def fourCircleWeights : Vertex → ℝ := ![31/40,31/20,31/20,2,2,1,1]

def alignedHighEdge (C : SignedCycle) : Vertex → ℝ :=
  ![(C.point H).y-(C.point G).y,
    (C.point G).a-(C.point A).y,
    (C.point A).y-(C.point B).y,
    (C.point B).a-(C.point T).y,
    (C.point T).y-(C.point D).y,
    (C.point D).a-(C.point E).y,
    (C.point E).y+(C.point H).a]

theorem fourCircleWeights_nonneg (i : Vertex) : 0≤fourCircleWeights i := by
  fin_cases i <;> norm_num [fourCircleWeights]

theorem fourCircleWeights_sum : (∑ i,fourCircleWeights i)=79/8 := by
  norm_num [fourCircleWeights,Fin.sum_univ_succ]

/-- The cancellation is an identity on the original seven points. -/
theorem alignedHighEdge_sum (C : SignedCycle) :
    (∑ i,fourCircleWeights i*alignedHighEdge C i)=
      ((C.point H).a+(31/40)*(C.point H).y)+
      ((31/20)*(C.point G).a-(31/40)*(C.point G).y)+
      (2*(C.point B).a-(31/20)*(C.point B).y)+
      ((C.point D).a-2*(C.point D).y) := by
  simp [fourCircleWeights,alignedHighEdge,Fin.sum_univ_succ,H,G,A,B,T,D,E]
  ring

/-- On the sorted part of the shifted circle, the D force `(1,-2)` has
its maximum at the diagonal. No sign assumption about D is needed. -/
theorem sorted_D_support {q : ℝ} {p : SignedPoint}
    (hs : p.Sorted) (hc : p.Contained q) (hq : q≤qCap) :
    p.a-2*p.y≤3*diagonalCoordinate qCap := by
  have hb := abs_nonneg p.y
  have hroot := Real.sqrt_nonneg (qCap/2)
  have hroot2 := Real.sq_sqrt (show 0≤qCap/2 by norm_num [qCap])
  have hcircle : (p.a+1/2)^2+(|p.y|+1/2)^2≤qCap := hc.trans hq
  have hsum : p.a+|p.y|+1≤2*Real.sqrt (qCap/2) := by
    nlinarith [sq_nonneg (p.a-|p.y|),hs.1]
  unfold diagonalCoordinate
  linarith [hs.2,neg_le_abs p.y]

/-- Three positive square comparisons prove the strict zero-error reserve.
These are exact radical bounds, not an accepted numerical certificate. -/
theorem fourCircle_radical_reserve :
    Real.sqrt qCap*Real.sqrt (1+(31/40 : ℝ)^2)+
      Real.sqrt qCap*Real.sqrt ((31/20 : ℝ)^2+(31/40 : ℝ)^2)+
      Real.sqrt qCap*Real.sqrt (4+(31/20 : ℝ)^2)+
      3*diagonalCoordinate qCap < 137/10-627/10000 := by
  have hQ := Real.sq_sqrt (show 0≤qCap by norm_num [qCap])
  have hH := Real.sq_sqrt (show (0:ℝ)≤1+(31/40 : ℝ)^2 by norm_num)
  have hG := Real.sq_sqrt
    (show (0:ℝ)≤(31/20 : ℝ)^2+(31/40 : ℝ)^2 by norm_num)
  have hB := Real.sq_sqrt (show (0:ℝ)≤4+(31/20 : ℝ)^2 by norm_num)
  have hD := Real.sq_sqrt (show 0≤qCap/2 by norm_num [qCap])
  have hHsq : (Real.sqrt qCap*Real.sqrt (1+(31/40 : ℝ)^2))^2=
      qCap*(1+(31/40 : ℝ)^2) := by rw [mul_pow,hQ,hH]
  have hGsq :
      (Real.sqrt qCap*Real.sqrt ((31/20 : ℝ)^2+(31/40 : ℝ)^2))^2=
        qCap*((31/20 : ℝ)^2+(31/40 : ℝ)^2) := by rw [mul_pow,hQ,hG]
  have hBsq : (Real.sqrt qCap*Real.sqrt (4+(31/20 : ℝ)^2))^2=
      qCap*(4+(31/20 : ℝ)^2) := by rw [mul_pow,hQ,hB]
  have hHbound : Real.sqrt qCap*Real.sqrt (1+(31/40 : ℝ)^2)<25034791/10000000 := by
    norm_num [qCap] at hHsq
    nlinarith [mul_nonneg (Real.sqrt_nonneg qCap)
      (Real.sqrt_nonneg (1+(31/40 : ℝ)^2))]
  have hGbound :
      Real.sqrt qCap*Real.sqrt ((31/20 : ℝ)^2+(31/40 : ℝ)^2)<34291452/10000000 := by
    norm_num [qCap] at hGsq
    nlinarith [mul_nonneg (Real.sqrt_nonneg qCap)
      (Real.sqrt_nonneg ((31/20 : ℝ)^2+(31/40 : ℝ)^2))]
  have hBbound : Real.sqrt qCap*Real.sqrt (4+(31/20 : ℝ)^2)<50069582/10000000 := by
    norm_num [qCap] at hBsq
    nlinarith [mul_nonneg (Real.sqrt_nonneg qCap)
      (Real.sqrt_nonneg (4+(31/20 : ℝ)^2))]
  have hDbound : Real.sqrt (qCap/2)<13992141/10000000 := by
    norm_num [qCap] at hD
    nlinarith [Real.sqrt_nonneg (qCap/2)]
  dsimp [diagonalCoordinate]
  linarith

/-- The exact four-circle upper bound remains valid at every actual radius
below the cap. The source points are not expanded or relabeled. -/
theorem alignedHighEdge_sum_lt {q : ℝ} {C : SignedCycle}
    (hs : ∀ i,(C.point i).Sorted)
    (hc : ∀ i,(C.point i).Contained q) (hq : q≤qCap) :
    (∑ i,fourCircleWeights i*alignedHighEdge C i)<79/8-627/10000 := by
  have hcontain (i : Vertex) : (C.point i).Contained ((Real.sqrt qCap)^2) := by
    rw [Real.sq_sqrt (show 0≤qCap by norm_num [qCap])]
    exact (hc i).trans hq
  have hH := work_le_circleSupport (Real.sqrt_nonneg qCap) (hs H)
    (hcontain H) (1,31/40)
  have hG := work_le_circleSupport (Real.sqrt_nonneg qCap) (hs G)
    (hcontain G) (31/20,-31/40)
  have hB := work_le_circleSupport (Real.sqrt_nonneg qCap) (hs B)
    (hcontain B) (2,-31/20)
  have hD := sorted_D_support (hs D) (hc D) hq
  norm_num [work,circleSupport] at hH hG hB
  have hreserve := fourCircle_radical_reserve
  norm_num at hreserve
  rw [alignedHighEdge_sum]
  linarith

def projectionError (r : ℝ) : ℝ := (283/200 : ℝ)*(r+r^2/2)

/-- Sorting and containment suffice for this upper coordinate bound; no
core or outer-boundary hypothesis is used in the perturbation estimate. -/
theorem primary_upper {q : ℝ} {p : SignedPoint}
    (hs : p.Sorted) (hc : p.Contained q) (hq : q≤qCap) : p.a≤283/200 := by
  have hcircle : (p.a+1/2)^2+(|p.y|+1/2)^2≤qCap := hc.trans hq
  dsimp [qCap] at hcircle
  nlinarith [abs_nonneg p.y,sq_nonneg |p.y|,hs.1]

/-- Both signs and both rotation coordinates are covered simultaneously.
The error is quadratic in the original absolute angle bound. -/
theorem rotation_component_error {q d r : ℝ} {p : SignedPoint}
    (hs : p.Sorted) (hc : p.Contained q) (hq : q≤qCap) (hd : |d|≤r) :
    p.a*Real.sin d+p.y*(Real.cos d-1)≤projectionError r ∧
    p.a*Real.sin d-p.y*(Real.cos d-1)≤projectionError r ∧
    p.a*(Real.cos d-1)+p.y*Real.sin d≤projectionError r ∧
    p.a*(Real.cos d-1)-p.y*Real.sin d≤projectionError r := by
  have hr : 0≤r := (abs_nonneg d).trans hd
  have htrig := small_angle hd
  have hcos : 0≤1-Real.cos d := sub_nonneg.mpr (Real.cos_le_one d)
  have habsCos : |Real.cos d-1|=1-Real.cos d := by
    rw [abs_of_nonpos (by linarith [Real.cos_le_one d])]
    ring
  have hasin : |p.a*Real.sin d|≤p.a*r := by
    rw [abs_mul,abs_of_pos hs.1]
    exact mul_le_mul_of_nonneg_left htrig.2 hs.1.le
  have hysin : |p.y*Real.sin d|≤p.a*r := by
    rw [abs_mul]
    exact mul_le_mul hs.2 htrig.2 (abs_nonneg _) hs.1.le
  have hacos : |p.a*(Real.cos d-1)|≤p.a*(r^2/2) := by
    rw [abs_mul,abs_of_pos hs.1,habsCos]
    exact mul_le_mul_of_nonneg_left (by linarith [htrig.1]) hs.1.le
  have hycos : |p.y*(Real.cos d-1)|≤p.a*(r^2/2) := by
    rw [abs_mul,habsCos]
    exact mul_le_mul hs.2 (by linarith [htrig.1]) hcos hs.1.le
  have hup := mul_le_mul_of_nonneg_right (primary_upper hs hc hq)
    (show 0≤r+r^2/2 by positivity)
  have hbound : p.a*r+p.a*(r^2/2)≤projectionError r := by
    dsimp [projectionError]
    nlinarith only [hup]
  have ha := abs_le.mp hasin
  have hb := abs_le.mp hysin
  have hcc := abs_le.mp hacos
  have he := abs_le.mp hycos
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

/-- Every actual high-domain owner has the same aligned edge value, with
the stated uniform error. Primaries are not silently reselected. -/
theorem edge_le_alignedHighEdge {q r : ℝ} {C : SignedCycle}
    (hs : ∀ i,(C.point i).Sorted)
    (hc : ∀ i,(C.point i).Contained q) (hq : q≤qCap)
    (hd : ∀ i,|delta C.theta i|≤r)
    (i : Vertex) (j : Fin 4) (hj : j∈highGAOwners i) :
    C.edge i j≤alignedHighEdge C i+projectionError r := by
  have hp := rotation_component_error (hs i) (hc i) hq (hd i)
  have ht := rotation_component_error (hs (next i)) (hc (next i)) hq (hd i)
  fin_cases i <;> fin_cases j <;>
    norm_num [highGAOwners] at hj <;>
    simp [SignedCycle.edge,zeroProjection,quarterProjection,word,
      alignedHighEdge,H,G,A,B,T,D,E,next] at hp ht ⊢ <;>
    rcases hp with ⟨hp₀,hp₁,hp₂,hp₃⟩ <;>
    rcases ht with ⟨ht₀,ht₁,ht₂,ht₃⟩ <;> linarith

/-- A global necessary consequence of any actual selected high-GA witness.
The seven selected axes are kept throughout the proof, including ties. -/
theorem highGA_error_budget {q r : ℝ} {C : SignedCycle}
    (hs : ∀ i,(C.point i).Sorted)
    (hc : ∀ i,(C.point i).Contained q) (hq : q≤qCap)
    (hd : ∀ i,|delta C.theta i|≤r)
    (owner : Vertex → Fin 4) (ho : ∀ i,owner i∈highGAOwners i)
    (hf : ∀ i,C.Feasible i (owner i)) :
    (627/10000 : ℝ)<(79/8)*projectionError r := by
  have he (i : Vertex) : 1-projectionError r≤alignedHighEdge C i := by
    have h := hf i
    change 0≤C.edge i (owner i)-edgeWidth (delta C.theta i) at h
    have hupper := edge_le_alignedHighEdge hs hc hq hd i (owner i) (ho i)
    have hwidth := edgeWidth_ge_one (delta C.theta i)
    linarith
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => mul_le_mul_of_nonneg_left (he i) (fourCircleWeights_nonneg i))
  have hsumleft : (∑ i,fourCircleWeights i*(1-projectionError r))=
      (79/8)*(1-projectionError r) := by
    rw [← Finset.sum_mul,fourCircleWeights_sum]
  rw [hsumleft] at hsum
  have hupper := alignedHighEdge_sum_lt hs hc hq
  linarith

/-- The source data on the six other edges makes no GA-owner assumption. -/
def OtherNormalWitnesses (C : SignedCycle) : Prop :=
  ∀ i,i≠G → ∃ j,j∈SignedCycle.normalOwners i ∧ C.Feasible i j

/-- Concrete actual-witness restriction on a full neighborhood of the
aligned frames. In particular a high weak tie is excluded as well. -/
theorem GA_owner_low_of_small_errors {q : ℝ} {C : SignedCycle}
    (hs : ∀ i,(C.point i).Sorted)
    (hc : ∀ i,(C.point i).Contained q) (hq : q≤qCap)
    (hd : ∀ i,|delta C.theta i|≤1/225)
    (hother : OtherNormalWitnesses C) (j : Fin 4) (hf : C.Feasible G j) :
    j=0 ∨ j=1 := by
  classical
  by_contra hbad
  have hj : j=2 ∨ j=3 := by fin_cases j <;> simp_all
  let owner (i : Vertex) : Fin 4 := if h : i=G then j else (hother i h).choose
  have ho (i : Vertex) : owner i∈highGAOwners i := by
    by_cases hi : i=G
    · subst i
      rcases hj with rfl | rfl <;> simp [owner,highGAOwners,G]
    · rw [highGAOwners_eq_normal hi]
      simpa only [owner,dif_neg hi] using (hother i hi).choose_spec.1
  have hfeasible (i : Vertex) : C.Feasible i (owner i) := by
    by_cases hi : i=G
    · subst i
      simpa only [owner,dif_pos rfl] using hf
    · simpa only [owner,dif_neg hi] using (hother i hi).choose_spec.2
  have h := highGA_error_budget hs hc hq hd owner ho hfeasible
  norm_num [projectionError] at h

theorem GA_owner_low_of_aligned {q : ℝ} {C : SignedCycle}
    (hs : ∀ i,(C.point i).Sorted)
    (hc : ∀ i,(C.point i).Contained q) (hq : q≤qCap)
    (hd : ∀ i,delta C.theta i=0)
    (hother : OtherNormalWitnesses C) (j : Fin 4) (hf : C.Feasible G j) :
    j=0 ∨ j=1 :=
  GA_owner_low_of_small_errors hs hc hq
    (fun i => by rw [hd i]; norm_num) hother j hf

/-- Application to a boundary source uses all its actual feasible GA axes,
not just the particular low axis stored among its witnesses. -/
theorem boundaryInput_GA_owner_low {q : ℝ} (I : SignedCycle.BoundaryInput q)
    (hq : q≤qCap) (hd : ∀ i,|delta I.cycle.theta i|≤1/225)
    (j : Fin 4) (hf : I.cycle.Feasible G j) : j=0 ∨ j=1 := by
  apply GA_owner_low_of_small_errors I.necessary.sorted I.necessary.contained hq hd _ j hf
  intro i hi
  exact ⟨I.witnesses.owner i,I.witnesses.allowed i,I.witnesses.feasible i⟩

end SquaresInCircles.Eight.TableFree.GlobalGA

module

public import SquaresInCircles.Eight.TableFree.OneNegativeBarrierState

/-!
# Genuine local states for the negative-T order obstruction

Uncompiled source. The two attained transport endpoints are converted to
complete local barrier data with actual BT3, unavailable BT2, aligned TD,
and retained original mixed owners. The points are the explicit original
circle constructions, not abstract states postulated by an exclusion.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
namespace DirectNegativeT
open AlignedNegative PrimaryCap

theorem path_BT3 {q t x : ℝ} {D T B : SignedPoint}
    (I : Source q t D T B) (hx : x∈Icc 0 t) :
    quarterFeasible B (Tpath (B.a-1/2) x) (-x) 3 := by
  have hp : quarterFeasible (point (B.a-1/2) x) B.reflect (-x) 1 := by
    exact (actual_primary_contact
      (show B.reflect.a=(B.a-1/2)+1/2 by simp [SignedPoint.reflect])
      ⟨hx.1,hx.2.trans I.tilt_cap⟩).ge
  apply (quarterFeasible_reflect B (Tpath (B.a-1/2) x) (-x) 3).1
  simpa [Tpath,reflectedOwner] using hp

theorem path_BT2_unavailable {B : SignedPoint} {x : ℝ}
    (hnot : ¬quarterFeasible (point (B.a-1/2) x) B.reflect (-x) 0) :
    ¬quarterFeasible B (Tpath (B.a-1/2) x) (-x) 2 := by
  intro hf
  apply hnot
  simpa [Tpath,reflectedOwner] using
    (quarterFeasible_reflect B (Tpath (B.a-1/2) x) (-x) 2).2 hf

def FullCoupledStop.local_barrier {q t h : ℝ} {D T B E H : SignedPoint}
    {kind : FullE.ArcKind} {I : Source q t D T B} {jDE jEH : Fin 4}
    (O : FullCoupledStop I kind E H h jEH) (J : FullE.ArcSource q E kind)
    (hqL : qLow≤q) (hqU : q≤qCap)
    (hjDE : jDE=2 ∨ jDE=3) (hjEH : jEH=0 ∨ jEH=1)
    (hnot : ¬quarterFeasible (point (B.a-1/2) O.angle) B.reflect (-O.angle) 0) :
    LocalBarrier I E H (-t) h jDE jEH := by
  have hg := I.path_data hqU O.angle_mem
  have hEg := J.geometry hqL O.tangent_mem
  have hEH : quarterFeasible (fullCoupledPoint kind q D.circle (B.a-1/2) O.angle)
      H (h+O.angle) jEH := by
    have hh := O.mixed_strict.le
    rw [fullCoupledSlack_actual kind H jEH hjEH
      ⟨O.error_mem.1,by linarith [O.error_mem.2]⟩] at hh
    exact sub_nonneg.mp hh
  exact {
    angle := O.angle
    angle_mem := O.angle_mem
    Dpoint := Dpath D.circle (B.a-1/2) O.angle
    Tpoint := Tpath (B.a-1/2) O.angle
    Epoint := fullCoupledPoint kind q D.circle (B.a-1/2) O.angle
    Etheta := -O.angle
    E_frame := Or.inr ⟨by linarith [O.angle_mem.2],neg_nonpos.mpr O.angle_mem.1⟩
    E_advance := by linarith [O.angle_mem.2]
    D_sorted := hg.D_sorted
    T_sorted := hg.T_sorted
    E_sorted := hEg.1
    D_core := hg.D_core
    T_core := hg.T_core
    E_core := hEg.2.2.1
    D_circle_nonincrease := hg.D_circle.le
    T_inside := hg.T_inside
    E_contained := hEg.2.1
    E_radial := hEg.2.2.2.1
    E_circle_nonincrease := hEg.2.2.2.2.1
    D_negative := hg.D_negative
    T_positive := hg.T_positive
    E_nonpos := by
      dsimp [fullCoupledPoint,FullE.ArcKind.point]
      linarith [O.tangent_mem.1]
    TD0 := hg.TD0
    BT3 := I.path_BT3 ⟨O.angle_mem.1,O.angle_mem.2.le⟩
    BT_unavailable := path_BT2_unavailable hnot
    DE := by
      simpa using (fullCoupled_DE_contact kind q D.circle (B.a-1/2) O.angle jDE hjDE).ge
    EH := by simpa using hEH
    bad_order := (O.terminal.resolve_left hnot).le }

def PositiveDEStop.local_barrier {q t e h : ℝ} {D T B E H : SignedPoint}
    {I : Source q t D T B} {jDE jEH : Fin 4}
    (O : PositiveDEStop I E e jDE) (hqU : q≤qCap)
    (hEs : E.Sorted) (hEc : E.Contained q) (hEcore : E.AvoidsCore)
    (hEr : E.Boundary q) (hEy : E.y≤0)
    (hjDE : jDE=2 ∨ jDE=3)
    (hEH : quarterFeasible E H (h-e) jEH)
    (hnot : ¬quarterFeasible (point (B.a-1/2) O.angle) B.reflect (-O.angle) 0)
    (hbad : h+O.angle≤0) : LocalBarrier I E H e h jDE jEH := by
  have hg := I.path_data hqU O.angle_mem
  have hDE : quarterFeasible (Dpath D.circle (B.a-1/2) O.angle) E (e+O.angle) jDE := by
    have hh := O.mixed_strict.le
    rw [positiveDESlack_actual E jDE hjDE ⟨O.error_mem.1,by linarith [O.error_mem.2]⟩] at hh
    exact sub_nonneg.mp hh
  exact {
    angle := O.angle
    angle_mem := O.angle_mem
    Dpoint := Dpath D.circle (B.a-1/2) O.angle
    Tpoint := Tpath (B.a-1/2) O.angle
    Epoint := E
    Etheta := e
    E_frame := Or.inl rfl
    E_advance := le_rfl
    D_sorted := hg.D_sorted
    T_sorted := hg.T_sorted
    E_sorted := hEs
    D_core := hg.D_core
    T_core := hg.T_core
    E_core := hEcore
    D_circle_nonincrease := hg.D_circle.le
    T_inside := hg.T_inside
    E_contained := hEc
    E_radial := hEr
    E_circle_nonincrease := le_rfl
    D_negative := hg.D_negative
    T_positive := hg.T_positive
    E_nonpos := hEy
    TD0 := hg.TD0
    BT3 := I.path_BT3 ⟨O.angle_mem.1,O.angle_mem.2.le⟩
    BT_unavailable := path_BT2_unavailable hnot
    DE := hDE
    EH := hEH
    bad_order := hbad }

end DirectNegativeT
end SquaresInCircles.Eight.TableFree

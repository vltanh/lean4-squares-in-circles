module

public import SquaresInCircles.Eight.Words.One.NegativeBarrierState

/-!
# Eight squares: composition of the actual negative-T stages

These constructors pull local endpoints back through
the already proved E-only alignment and same-circle D/T contact. Original
circle comparisons and frame intervals are composed explicitly; no loss
at T is substituted for the strict loss at D.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
namespace DirectNegativeT

def LocalEndpoint.prepend_E_motion {q t e h : ℝ} {D T B E E' H : SignedPoint}
    {I : Source q t D T B} {jDE jEH : Fin 4}
    (K : LocalEndpoint I E' H (-t) h jDE jEH)
    (he : e≤ -t) (hcircle : E'.circle≤E.circle) :
    LocalEndpoint I E H e h jDE jEH where
  angle := K.angle
  angle_mem := K.angle_mem
  Dpoint := K.Dpoint
  Tpoint := K.Tpoint
  Epoint := K.Epoint
  Etheta := K.Etheta
  E_frame := by
    right
    rcases K.E_frame with hh | hh
    · rw [hh]; exact ⟨le_rfl,neg_nonpos.mpr I.tilt_pos.le⟩
    · exact hh
  E_advance := he.trans K.E_advance
  D_sorted := K.D_sorted
  T_sorted := K.T_sorted
  E_sorted := K.E_sorted
  D_core := K.D_core
  T_core := K.T_core
  E_core := K.E_core
  D_circle_loss := K.D_circle_loss
  T_inside := K.T_inside
  E_contained := K.E_contained
  E_radial := K.E_radial
  E_circle_nonincrease := K.E_circle_nonincrease.trans hcircle
  D_negative := K.D_negative
  T_positive := K.T_positive
  E_nonpos := K.E_nonpos
  D_nondiagonal := K.D_nondiagonal
  T_nondiagonal := K.T_nondiagonal
  D_tangent_decreases := K.D_tangent_decreases
  TD0 := K.TD0
  TD2 := K.TD2
  BT2 := K.BT2
  DE := K.DE
  EH := K.EH

def LocalBarrier.prepend_E_motion {q t e h : ℝ} {D T B E E' H : SignedPoint}
    {I : Source q t D T B} {jDE jEH : Fin 4}
    (K : LocalBarrier I E' H (-t) h jDE jEH)
    (he : e≤ -t) (hcircle : E'.circle≤E.circle) :
    LocalBarrier I E H e h jDE jEH where
  angle := K.angle
  angle_mem := K.angle_mem
  Dpoint := K.Dpoint
  Tpoint := K.Tpoint
  Epoint := K.Epoint
  Etheta := K.Etheta
  E_frame := by
    right
    rcases K.E_frame with hh | hh
    · rw [hh]; exact ⟨le_rfl,neg_nonpos.mpr I.tilt_pos.le⟩
    · exact hh
  E_advance := he.trans K.E_advance
  D_sorted := K.D_sorted
  T_sorted := K.T_sorted
  E_sorted := K.E_sorted
  D_core := K.D_core
  T_core := K.T_core
  E_core := K.E_core
  D_circle_nonincrease := K.D_circle_nonincrease
  T_inside := K.T_inside
  E_contained := K.E_contained
  E_radial := K.E_radial
  E_circle_nonincrease := K.E_circle_nonincrease.trans hcircle
  D_negative := K.D_negative
  T_positive := K.T_positive
  E_nonpos := K.E_nonpos
  TD0 := K.TD0
  BT3 := K.BT3
  BT_unavailable := K.BT_unavailable
  DE := K.DE
  EH := K.EH
  bad_order := K.bad_order

def LocalEndpoint.prepend_contact {q t m e h : ℝ} {D T D' T' B E H : SignedPoint}
    (I : Source q t D T B) {J : Source q m D' T' B} {jDE jEH : Fin 4}
    (K : LocalEndpoint J E H e h jDE jEH)
    (hmt : m<t) (hcircle : D'.circle=D.circle) (htangent : |D'.y|≤|D.y|) :
    LocalEndpoint I E H e h jDE jEH where
  angle := K.angle
  angle_mem := ⟨K.angle_mem.1,K.angle_mem.2.trans hmt⟩
  Dpoint := K.Dpoint
  Tpoint := K.Tpoint
  Epoint := K.Epoint
  Etheta := K.Etheta
  E_frame := by
    rcases K.E_frame with hh | hh
    · exact Or.inl hh
    · exact Or.inr ⟨by linarith [hh.1],hh.2⟩
  E_advance := K.E_advance
  D_sorted := K.D_sorted
  T_sorted := K.T_sorted
  E_sorted := K.E_sorted
  D_core := K.D_core
  T_core := K.T_core
  E_core := K.E_core
  D_circle_loss := K.D_circle_loss.trans_eq hcircle
  T_inside := K.T_inside
  E_contained := K.E_contained
  E_radial := K.E_radial
  E_circle_nonincrease := K.E_circle_nonincrease
  D_negative := K.D_negative
  T_positive := K.T_positive
  E_nonpos := K.E_nonpos
  D_nondiagonal := K.D_nondiagonal
  T_nondiagonal := K.T_nondiagonal
  D_tangent_decreases := K.D_tangent_decreases.trans_le htangent
  TD0 := K.TD0
  TD2 := K.TD2
  BT2 := K.BT2
  DE := K.DE
  EH := K.EH

def LocalBarrier.prepend_contact {q t m e h : ℝ} {D T D' T' B E H : SignedPoint}
    (I : Source q t D T B) {J : Source q m D' T' B} {jDE jEH : Fin 4}
    (K : LocalBarrier J E H e h jDE jEH)
    (hmt : m<t) (hcircle : D'.circle=D.circle) :
    LocalBarrier I E H e h jDE jEH where
  angle := K.angle
  angle_mem := ⟨K.angle_mem.1,K.angle_mem.2.trans hmt⟩
  Dpoint := K.Dpoint
  Tpoint := K.Tpoint
  Epoint := K.Epoint
  Etheta := K.Etheta
  E_frame := by
    rcases K.E_frame with hh | hh
    · exact Or.inl hh
    · exact Or.inr ⟨by linarith [hh.1],hh.2⟩
  E_advance := K.E_advance
  D_sorted := K.D_sorted
  T_sorted := K.T_sorted
  E_sorted := K.E_sorted
  D_core := K.D_core
  T_core := K.T_core
  E_core := K.E_core
  D_circle_nonincrease := K.D_circle_nonincrease.trans_eq hcircle
  T_inside := K.T_inside
  E_contained := K.E_contained
  E_radial := K.E_radial
  E_circle_nonincrease := K.E_circle_nonincrease
  D_negative := K.D_negative
  T_positive := K.T_positive
  E_nonpos := K.E_nonpos
  TD0 := K.TD0
  BT3 := K.BT3
  BT_unavailable := K.BT_unavailable
  DE := K.DE
  EH := K.EH
  bad_order := K.bad_order

end DirectNegativeT
end SquaresInCircles.Eight

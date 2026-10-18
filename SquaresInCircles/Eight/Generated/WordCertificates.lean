module

public import SquaresInCircles.Eight.Arithmetic.WordProblems

/-!
# Whole-domain finite proof scripts for the six excluded words

These are complete rational closed-box decisions, with their continuous
meaning supplied by `RealBox.certify_sound`. They are deliberately left
uncompiled and unevaluated in this draft. No external Boolean report,
opaque arithmetic record, or numerical optimizer is consumed here.

Each statement carries the actual branch/sign/axis expression. A failed
leaf will make its `by decide` proof fail during the later requested audit.
The common core/core block has been removed: WordGeometry supplies its
whole-domain geometric proof before calling the retained dispatcher.
Both dispatchers also omit the five impossible core separator classes;
WordGeometry proves this exclusion for every actual feasible axis.
-/

@[expose] public section
namespace SquaresInCircles.Eight.WordProblems
open Arithmetic.RealBox
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
theorem common_0_outer_outer_00_0 :
    certify 96 (commonProblem 0 .outer .outer false false 0) (pairBox .outer .outer)=true := by decide
theorem common_0_outer_outer_00_1 :
    certify 96 (commonProblem 0 .outer .outer false false 1) (pairBox .outer .outer)=true := by decide
theorem common_0_outer_outer_00_2 :
    certify 96 (commonProblem 0 .outer .outer false false 2) (pairBox .outer .outer)=true := by decide
theorem common_0_outer_outer_00_3 :
    certify 96 (commonProblem 0 .outer .outer false false 3) (pairBox .outer .outer)=true := by decide
theorem common_0_outer_outer_01_0 :
    certify 96 (commonProblem 0 .outer .outer false true 0) (pairBox .outer .outer)=true := by decide
theorem common_0_outer_outer_01_1 :
    certify 96 (commonProblem 0 .outer .outer false true 1) (pairBox .outer .outer)=true := by decide
theorem common_0_outer_outer_01_2 :
    certify 96 (commonProblem 0 .outer .outer false true 2) (pairBox .outer .outer)=true := by decide
theorem common_0_outer_outer_01_3 :
    certify 96 (commonProblem 0 .outer .outer false true 3) (pairBox .outer .outer)=true := by decide
theorem common_0_outer_outer_10_0 :
    certify 96 (commonProblem 0 .outer .outer true false 0) (pairBox .outer .outer)=true := by decide
theorem common_0_outer_outer_10_1 :
    certify 96 (commonProblem 0 .outer .outer true false 1) (pairBox .outer .outer)=true := by decide
theorem common_0_outer_outer_10_2 :
    certify 96 (commonProblem 0 .outer .outer true false 2) (pairBox .outer .outer)=true := by decide
theorem common_0_outer_outer_10_3 :
    certify 96 (commonProblem 0 .outer .outer true false 3) (pairBox .outer .outer)=true := by decide
theorem common_0_outer_outer_11_0 :
    certify 96 (commonProblem 0 .outer .outer true true 0) (pairBox .outer .outer)=true := by decide
theorem common_0_outer_outer_11_1 :
    certify 96 (commonProblem 0 .outer .outer true true 1) (pairBox .outer .outer)=true := by decide
theorem common_0_outer_outer_11_2 :
    certify 96 (commonProblem 0 .outer .outer true true 2) (pairBox .outer .outer)=true := by decide
theorem common_0_outer_outer_11_3 :
    certify 96 (commonProblem 0 .outer .outer true true 3) (pairBox .outer .outer)=true := by decide
theorem common_0_outer_coreSide_00_2 :
    certify 96 (commonProblem 0 .outer .coreSide false false 2) (pairBox .outer .coreSide)=true := by decide
theorem common_0_outer_coreSide_00_3 :
    certify 96 (commonProblem 0 .outer .coreSide false false 3) (pairBox .outer .coreSide)=true := by decide
theorem common_0_outer_coreSide_01_2 :
    certify 96 (commonProblem 0 .outer .coreSide false true 2) (pairBox .outer .coreSide)=true := by decide
theorem common_0_outer_coreSide_01_3 :
    certify 96 (commonProblem 0 .outer .coreSide false true 3) (pairBox .outer .coreSide)=true := by decide
theorem common_0_outer_coreSide_10_0 :
    certify 96 (commonProblem 0 .outer .coreSide true false 0) (pairBox .outer .coreSide)=true := by decide
theorem common_0_outer_coreSide_10_2 :
    certify 96 (commonProblem 0 .outer .coreSide true false 2) (pairBox .outer .coreSide)=true := by decide
theorem common_0_outer_coreSide_10_3 :
    certify 96 (commonProblem 0 .outer .coreSide true false 3) (pairBox .outer .coreSide)=true := by decide
theorem common_0_outer_coreSide_11_0 :
    certify 96 (commonProblem 0 .outer .coreSide true true 0) (pairBox .outer .coreSide)=true := by decide
theorem common_0_outer_coreSide_11_2 :
    certify 96 (commonProblem 0 .outer .coreSide true true 2) (pairBox .outer .coreSide)=true := by decide
theorem common_0_outer_coreSide_11_3 :
    certify 96 (commonProblem 0 .outer .coreSide true true 3) (pairBox .outer .coreSide)=true := by decide
theorem common_0_outer_coreCorner_00_2 :
    certify 96 (commonProblem 0 .outer .coreCorner false false 2) (pairBox .outer .coreCorner)=true := by decide
theorem common_0_outer_coreCorner_00_3 :
    certify 96 (commonProblem 0 .outer .coreCorner false false 3) (pairBox .outer .coreCorner)=true := by decide
theorem common_0_outer_coreCorner_01_2 :
    certify 96 (commonProblem 0 .outer .coreCorner false true 2) (pairBox .outer .coreCorner)=true := by decide
theorem common_0_outer_coreCorner_01_3 :
    certify 96 (commonProblem 0 .outer .coreCorner false true 3) (pairBox .outer .coreCorner)=true := by decide
theorem common_0_outer_coreCorner_10_0 :
    certify 96 (commonProblem 0 .outer .coreCorner true false 0) (pairBox .outer .coreCorner)=true := by decide
theorem common_0_outer_coreCorner_10_2 :
    certify 96 (commonProblem 0 .outer .coreCorner true false 2) (pairBox .outer .coreCorner)=true := by decide
theorem common_0_outer_coreCorner_10_3 :
    certify 96 (commonProblem 0 .outer .coreCorner true false 3) (pairBox .outer .coreCorner)=true := by decide
theorem common_0_outer_coreCorner_11_0 :
    certify 96 (commonProblem 0 .outer .coreCorner true true 0) (pairBox .outer .coreCorner)=true := by decide
theorem common_0_outer_coreCorner_11_2 :
    certify 96 (commonProblem 0 .outer .coreCorner true true 2) (pairBox .outer .coreCorner)=true := by decide
theorem common_0_outer_coreCorner_11_3 :
    certify 96 (commonProblem 0 .outer .coreCorner true true 3) (pairBox .outer .coreCorner)=true := by decide
theorem common_0_coreSide_outer_00_0 :
    certify 96 (commonProblem 0 .coreSide .outer false false 0) (pairBox .coreSide .outer)=true := by decide
theorem common_0_coreSide_outer_00_1 :
    certify 96 (commonProblem 0 .coreSide .outer false false 1) (pairBox .coreSide .outer)=true := by decide
theorem common_0_coreSide_outer_00_2 :
    certify 96 (commonProblem 0 .coreSide .outer false false 2) (pairBox .coreSide .outer)=true := by decide
theorem common_0_coreSide_outer_01_0 :
    certify 96 (commonProblem 0 .coreSide .outer false true 0) (pairBox .coreSide .outer)=true := by decide
theorem common_0_coreSide_outer_01_1 :
    certify 96 (commonProblem 0 .coreSide .outer false true 1) (pairBox .coreSide .outer)=true := by decide
theorem common_0_coreSide_outer_10_0 :
    certify 96 (commonProblem 0 .coreSide .outer true false 0) (pairBox .coreSide .outer)=true := by decide
theorem common_0_coreSide_outer_10_1 :
    certify 96 (commonProblem 0 .coreSide .outer true false 1) (pairBox .coreSide .outer)=true := by decide
theorem common_0_coreSide_outer_10_2 :
    certify 96 (commonProblem 0 .coreSide .outer true false 2) (pairBox .coreSide .outer)=true := by decide
theorem common_0_coreSide_outer_11_0 :
    certify 96 (commonProblem 0 .coreSide .outer true true 0) (pairBox .coreSide .outer)=true := by decide
theorem common_0_coreSide_outer_11_1 :
    certify 96 (commonProblem 0 .coreSide .outer true true 1) (pairBox .coreSide .outer)=true := by decide
theorem common_0_coreCorner_outer_00_0 :
    certify 96 (commonProblem 0 .coreCorner .outer false false 0) (pairBox .coreCorner .outer)=true := by decide
theorem common_0_coreCorner_outer_00_1 :
    certify 96 (commonProblem 0 .coreCorner .outer false false 1) (pairBox .coreCorner .outer)=true := by decide
theorem common_0_coreCorner_outer_00_2 :
    certify 96 (commonProblem 0 .coreCorner .outer false false 2) (pairBox .coreCorner .outer)=true := by decide
theorem common_0_coreCorner_outer_01_0 :
    certify 96 (commonProblem 0 .coreCorner .outer false true 0) (pairBox .coreCorner .outer)=true := by decide
theorem common_0_coreCorner_outer_01_1 :
    certify 96 (commonProblem 0 .coreCorner .outer false true 1) (pairBox .coreCorner .outer)=true := by decide
theorem common_0_coreCorner_outer_10_0 :
    certify 96 (commonProblem 0 .coreCorner .outer true false 0) (pairBox .coreCorner .outer)=true := by decide
theorem common_0_coreCorner_outer_10_1 :
    certify 96 (commonProblem 0 .coreCorner .outer true false 1) (pairBox .coreCorner .outer)=true := by decide
theorem common_0_coreCorner_outer_10_2 :
    certify 96 (commonProblem 0 .coreCorner .outer true false 2) (pairBox .coreCorner .outer)=true := by decide
theorem common_0_coreCorner_outer_11_0 :
    certify 96 (commonProblem 0 .coreCorner .outer true true 0) (pairBox .coreCorner .outer)=true := by decide
theorem common_0_coreCorner_outer_11_1 :
    certify 96 (commonProblem 0 .coreCorner .outer true true 1) (pairBox .coreCorner .outer)=true := by decide
theorem common_1_outer_outer_00_0 :
    certify 96 (commonProblem 1 .outer .outer false false 0) (pairBox .outer .outer)=true := by decide
theorem common_1_outer_outer_00_1 :
    certify 96 (commonProblem 1 .outer .outer false false 1) (pairBox .outer .outer)=true := by decide
theorem common_1_outer_outer_00_2 :
    certify 96 (commonProblem 1 .outer .outer false false 2) (pairBox .outer .outer)=true := by decide
theorem common_1_outer_outer_00_3 :
    certify 96 (commonProblem 1 .outer .outer false false 3) (pairBox .outer .outer)=true := by decide
theorem common_1_outer_outer_01_0 :
    certify 96 (commonProblem 1 .outer .outer false true 0) (pairBox .outer .outer)=true := by decide
theorem common_1_outer_outer_01_1 :
    certify 96 (commonProblem 1 .outer .outer false true 1) (pairBox .outer .outer)=true := by decide
theorem common_1_outer_outer_01_2 :
    certify 96 (commonProblem 1 .outer .outer false true 2) (pairBox .outer .outer)=true := by decide
theorem common_1_outer_outer_01_3 :
    certify 96 (commonProblem 1 .outer .outer false true 3) (pairBox .outer .outer)=true := by decide
theorem common_1_outer_outer_10_0 :
    certify 96 (commonProblem 1 .outer .outer true false 0) (pairBox .outer .outer)=true := by decide
theorem common_1_outer_outer_10_1 :
    certify 96 (commonProblem 1 .outer .outer true false 1) (pairBox .outer .outer)=true := by decide
theorem common_1_outer_outer_10_2 :
    certify 96 (commonProblem 1 .outer .outer true false 2) (pairBox .outer .outer)=true := by decide
theorem common_1_outer_outer_10_3 :
    certify 96 (commonProblem 1 .outer .outer true false 3) (pairBox .outer .outer)=true := by decide
theorem common_1_outer_outer_11_0 :
    certify 96 (commonProblem 1 .outer .outer true true 0) (pairBox .outer .outer)=true := by decide
theorem common_1_outer_outer_11_1 :
    certify 96 (commonProblem 1 .outer .outer true true 1) (pairBox .outer .outer)=true := by decide
theorem common_1_outer_outer_11_2 :
    certify 96 (commonProblem 1 .outer .outer true true 2) (pairBox .outer .outer)=true := by decide
theorem common_1_outer_outer_11_3 :
    certify 96 (commonProblem 1 .outer .outer true true 3) (pairBox .outer .outer)=true := by decide
theorem common_1_outer_coreSide_00_1 :
    certify 96 (commonProblem 1 .outer .coreSide false false 1) (pairBox .outer .coreSide)=true := by decide
theorem common_1_outer_coreSide_00_2 :
    certify 96 (commonProblem 1 .outer .coreSide false false 2) (pairBox .outer .coreSide)=true := by decide
theorem common_1_outer_coreSide_00_3 :
    certify 96 (commonProblem 1 .outer .coreSide false false 3) (pairBox .outer .coreSide)=true := by decide
theorem common_1_outer_coreSide_01_1 :
    certify 96 (commonProblem 1 .outer .coreSide false true 1) (pairBox .outer .coreSide)=true := by decide
theorem common_1_outer_coreSide_01_2 :
    certify 96 (commonProblem 1 .outer .coreSide false true 2) (pairBox .outer .coreSide)=true := by decide
theorem common_1_outer_coreSide_01_3 :
    certify 96 (commonProblem 1 .outer .coreSide false true 3) (pairBox .outer .coreSide)=true := by decide
theorem common_1_outer_coreSide_10_0 :
    certify 96 (commonProblem 1 .outer .coreSide true false 0) (pairBox .outer .coreSide)=true := by decide
theorem common_1_outer_coreSide_10_1 :
    certify 96 (commonProblem 1 .outer .coreSide true false 1) (pairBox .outer .coreSide)=true := by decide
theorem common_1_outer_coreSide_10_2 :
    certify 96 (commonProblem 1 .outer .coreSide true false 2) (pairBox .outer .coreSide)=true := by decide
theorem common_1_outer_coreSide_10_3 :
    certify 96 (commonProblem 1 .outer .coreSide true false 3) (pairBox .outer .coreSide)=true := by decide
theorem common_1_outer_coreSide_11_0 :
    certify 96 (commonProblem 1 .outer .coreSide true true 0) (pairBox .outer .coreSide)=true := by decide
theorem common_1_outer_coreSide_11_1 :
    certify 96 (commonProblem 1 .outer .coreSide true true 1) (pairBox .outer .coreSide)=true := by decide
theorem common_1_outer_coreSide_11_2 :
    certify 96 (commonProblem 1 .outer .coreSide true true 2) (pairBox .outer .coreSide)=true := by decide
theorem common_1_outer_coreSide_11_3 :
    certify 96 (commonProblem 1 .outer .coreSide true true 3) (pairBox .outer .coreSide)=true := by decide
theorem common_1_outer_coreCorner_00_1 :
    certify 96 (commonProblem 1 .outer .coreCorner false false 1) (pairBox .outer .coreCorner)=true := by decide
theorem common_1_outer_coreCorner_00_2 :
    certify 96 (commonProblem 1 .outer .coreCorner false false 2) (pairBox .outer .coreCorner)=true := by decide
theorem common_1_outer_coreCorner_00_3 :
    certify 96 (commonProblem 1 .outer .coreCorner false false 3) (pairBox .outer .coreCorner)=true := by decide
theorem common_1_outer_coreCorner_01_1 :
    certify 96 (commonProblem 1 .outer .coreCorner false true 1) (pairBox .outer .coreCorner)=true := by decide
theorem common_1_outer_coreCorner_01_2 :
    certify 96 (commonProblem 1 .outer .coreCorner false true 2) (pairBox .outer .coreCorner)=true := by decide
theorem common_1_outer_coreCorner_01_3 :
    certify 96 (commonProblem 1 .outer .coreCorner false true 3) (pairBox .outer .coreCorner)=true := by decide
theorem common_1_outer_coreCorner_10_0 :
    certify 96 (commonProblem 1 .outer .coreCorner true false 0) (pairBox .outer .coreCorner)=true := by decide
theorem common_1_outer_coreCorner_10_1 :
    certify 96 (commonProblem 1 .outer .coreCorner true false 1) (pairBox .outer .coreCorner)=true := by decide
theorem common_1_outer_coreCorner_10_2 :
    certify 96 (commonProblem 1 .outer .coreCorner true false 2) (pairBox .outer .coreCorner)=true := by decide
theorem common_1_outer_coreCorner_10_3 :
    certify 96 (commonProblem 1 .outer .coreCorner true false 3) (pairBox .outer .coreCorner)=true := by decide
theorem common_1_outer_coreCorner_11_0 :
    certify 96 (commonProblem 1 .outer .coreCorner true true 0) (pairBox .outer .coreCorner)=true := by decide
theorem common_1_outer_coreCorner_11_1 :
    certify 96 (commonProblem 1 .outer .coreCorner true true 1) (pairBox .outer .coreCorner)=true := by decide
theorem common_1_outer_coreCorner_11_2 :
    certify 96 (commonProblem 1 .outer .coreCorner true true 2) (pairBox .outer .coreCorner)=true := by decide
theorem common_1_outer_coreCorner_11_3 :
    certify 96 (commonProblem 1 .outer .coreCorner true true 3) (pairBox .outer .coreCorner)=true := by decide
theorem common_1_coreSide_outer_00_0 :
    certify 96 (commonProblem 1 .coreSide .outer false false 0) (pairBox .coreSide .outer)=true := by decide
theorem common_1_coreSide_outer_00_1 :
    certify 96 (commonProblem 1 .coreSide .outer false false 1) (pairBox .coreSide .outer)=true := by decide
theorem common_1_coreSide_outer_00_2 :
    certify 96 (commonProblem 1 .coreSide .outer false false 2) (pairBox .coreSide .outer)=true := by decide
theorem common_1_coreSide_outer_00_3 :
    certify 96 (commonProblem 1 .coreSide .outer false false 3) (pairBox .coreSide .outer)=true := by decide
theorem common_1_coreSide_outer_01_0 :
    certify 96 (commonProblem 1 .coreSide .outer false true 0) (pairBox .coreSide .outer)=true := by decide
theorem common_1_coreSide_outer_01_1 :
    certify 96 (commonProblem 1 .coreSide .outer false true 1) (pairBox .coreSide .outer)=true := by decide
theorem common_1_coreSide_outer_01_3 :
    certify 96 (commonProblem 1 .coreSide .outer false true 3) (pairBox .coreSide .outer)=true := by decide
theorem common_1_coreSide_outer_10_0 :
    certify 96 (commonProblem 1 .coreSide .outer true false 0) (pairBox .coreSide .outer)=true := by decide
theorem common_1_coreSide_outer_10_1 :
    certify 96 (commonProblem 1 .coreSide .outer true false 1) (pairBox .coreSide .outer)=true := by decide
theorem common_1_coreSide_outer_10_2 :
    certify 96 (commonProblem 1 .coreSide .outer true false 2) (pairBox .coreSide .outer)=true := by decide
theorem common_1_coreSide_outer_10_3 :
    certify 96 (commonProblem 1 .coreSide .outer true false 3) (pairBox .coreSide .outer)=true := by decide
theorem common_1_coreSide_outer_11_0 :
    certify 96 (commonProblem 1 .coreSide .outer true true 0) (pairBox .coreSide .outer)=true := by decide
theorem common_1_coreSide_outer_11_1 :
    certify 96 (commonProblem 1 .coreSide .outer true true 1) (pairBox .coreSide .outer)=true := by decide
theorem common_1_coreSide_outer_11_3 :
    certify 96 (commonProblem 1 .coreSide .outer true true 3) (pairBox .coreSide .outer)=true := by decide
theorem common_1_coreCorner_outer_00_0 :
    certify 96 (commonProblem 1 .coreCorner .outer false false 0) (pairBox .coreCorner .outer)=true := by decide
theorem common_1_coreCorner_outer_00_1 :
    certify 96 (commonProblem 1 .coreCorner .outer false false 1) (pairBox .coreCorner .outer)=true := by decide
theorem common_1_coreCorner_outer_00_2 :
    certify 96 (commonProblem 1 .coreCorner .outer false false 2) (pairBox .coreCorner .outer)=true := by decide
theorem common_1_coreCorner_outer_00_3 :
    certify 96 (commonProblem 1 .coreCorner .outer false false 3) (pairBox .coreCorner .outer)=true := by decide
theorem common_1_coreCorner_outer_01_0 :
    certify 96 (commonProblem 1 .coreCorner .outer false true 0) (pairBox .coreCorner .outer)=true := by decide
theorem common_1_coreCorner_outer_01_1 :
    certify 96 (commonProblem 1 .coreCorner .outer false true 1) (pairBox .coreCorner .outer)=true := by decide
theorem common_1_coreCorner_outer_01_3 :
    certify 96 (commonProblem 1 .coreCorner .outer false true 3) (pairBox .coreCorner .outer)=true := by decide
theorem common_1_coreCorner_outer_10_0 :
    certify 96 (commonProblem 1 .coreCorner .outer true false 0) (pairBox .coreCorner .outer)=true := by decide
theorem common_1_coreCorner_outer_10_1 :
    certify 96 (commonProblem 1 .coreCorner .outer true false 1) (pairBox .coreCorner .outer)=true := by decide
theorem common_1_coreCorner_outer_10_2 :
    certify 96 (commonProblem 1 .coreCorner .outer true false 2) (pairBox .coreCorner .outer)=true := by decide
theorem common_1_coreCorner_outer_10_3 :
    certify 96 (commonProblem 1 .coreCorner .outer true false 3) (pairBox .coreCorner .outer)=true := by decide
theorem common_1_coreCorner_outer_11_0 :
    certify 96 (commonProblem 1 .coreCorner .outer true true 0) (pairBox .coreCorner .outer)=true := by decide
theorem common_1_coreCorner_outer_11_1 :
    certify 96 (commonProblem 1 .coreCorner .outer true true 1) (pairBox .coreCorner .outer)=true := by decide
theorem common_1_coreCorner_outer_11_3 :
    certify 96 (commonProblem 1 .coreCorner .outer true true 3) (pairBox .coreCorner .outer)=true := by decide
theorem common_2_outer_outer_00_0 :
    certify 96 (commonProblem 2 .outer .outer false false 0) (pairBox .outer .outer)=true := by decide
theorem common_2_outer_outer_00_1 :
    certify 96 (commonProblem 2 .outer .outer false false 1) (pairBox .outer .outer)=true := by decide
theorem common_2_outer_outer_00_2 :
    certify 96 (commonProblem 2 .outer .outer false false 2) (pairBox .outer .outer)=true := by decide
theorem common_2_outer_outer_00_3 :
    certify 96 (commonProblem 2 .outer .outer false false 3) (pairBox .outer .outer)=true := by decide
theorem common_2_outer_outer_01_0 :
    certify 96 (commonProblem 2 .outer .outer false true 0) (pairBox .outer .outer)=true := by decide
theorem common_2_outer_outer_01_1 :
    certify 96 (commonProblem 2 .outer .outer false true 1) (pairBox .outer .outer)=true := by decide
theorem common_2_outer_outer_01_2 :
    certify 96 (commonProblem 2 .outer .outer false true 2) (pairBox .outer .outer)=true := by decide
theorem common_2_outer_outer_01_3 :
    certify 96 (commonProblem 2 .outer .outer false true 3) (pairBox .outer .outer)=true := by decide
theorem common_2_outer_outer_10_0 :
    certify 96 (commonProblem 2 .outer .outer true false 0) (pairBox .outer .outer)=true := by decide
theorem common_2_outer_outer_10_1 :
    certify 96 (commonProblem 2 .outer .outer true false 1) (pairBox .outer .outer)=true := by decide
theorem common_2_outer_outer_10_2 :
    certify 96 (commonProblem 2 .outer .outer true false 2) (pairBox .outer .outer)=true := by decide
theorem common_2_outer_outer_10_3 :
    certify 96 (commonProblem 2 .outer .outer true false 3) (pairBox .outer .outer)=true := by decide
theorem common_2_outer_outer_11_0 :
    certify 96 (commonProblem 2 .outer .outer true true 0) (pairBox .outer .outer)=true := by decide
theorem common_2_outer_outer_11_1 :
    certify 96 (commonProblem 2 .outer .outer true true 1) (pairBox .outer .outer)=true := by decide
theorem common_2_outer_outer_11_2 :
    certify 96 (commonProblem 2 .outer .outer true true 2) (pairBox .outer .outer)=true := by decide
theorem common_2_outer_outer_11_3 :
    certify 96 (commonProblem 2 .outer .outer true true 3) (pairBox .outer .outer)=true := by decide
theorem common_2_outer_coreSide_00_1 :
    certify 96 (commonProblem 2 .outer .coreSide false false 1) (pairBox .outer .coreSide)=true := by decide
theorem common_2_outer_coreSide_00_2 :
    certify 96 (commonProblem 2 .outer .coreSide false false 2) (pairBox .outer .coreSide)=true := by decide
theorem common_2_outer_coreSide_00_3 :
    certify 96 (commonProblem 2 .outer .coreSide false false 3) (pairBox .outer .coreSide)=true := by decide
theorem common_2_outer_coreSide_01_1 :
    certify 96 (commonProblem 2 .outer .coreSide false true 1) (pairBox .outer .coreSide)=true := by decide
theorem common_2_outer_coreSide_01_2 :
    certify 96 (commonProblem 2 .outer .coreSide false true 2) (pairBox .outer .coreSide)=true := by decide
theorem common_2_outer_coreSide_01_3 :
    certify 96 (commonProblem 2 .outer .coreSide false true 3) (pairBox .outer .coreSide)=true := by decide
theorem common_2_outer_coreSide_10_0 :
    certify 96 (commonProblem 2 .outer .coreSide true false 0) (pairBox .outer .coreSide)=true := by decide
theorem common_2_outer_coreSide_10_1 :
    certify 96 (commonProblem 2 .outer .coreSide true false 1) (pairBox .outer .coreSide)=true := by decide
theorem common_2_outer_coreSide_10_2 :
    certify 96 (commonProblem 2 .outer .coreSide true false 2) (pairBox .outer .coreSide)=true := by decide
theorem common_2_outer_coreSide_10_3 :
    certify 96 (commonProblem 2 .outer .coreSide true false 3) (pairBox .outer .coreSide)=true := by decide
theorem common_2_outer_coreSide_11_0 :
    certify 96 (commonProblem 2 .outer .coreSide true true 0) (pairBox .outer .coreSide)=true := by decide
theorem common_2_outer_coreSide_11_1 :
    certify 96 (commonProblem 2 .outer .coreSide true true 1) (pairBox .outer .coreSide)=true := by decide
theorem common_2_outer_coreSide_11_2 :
    certify 96 (commonProblem 2 .outer .coreSide true true 2) (pairBox .outer .coreSide)=true := by decide
theorem common_2_outer_coreSide_11_3 :
    certify 96 (commonProblem 2 .outer .coreSide true true 3) (pairBox .outer .coreSide)=true := by decide
theorem common_2_outer_coreCorner_00_1 :
    certify 96 (commonProblem 2 .outer .coreCorner false false 1) (pairBox .outer .coreCorner)=true := by decide
theorem common_2_outer_coreCorner_00_2 :
    certify 96 (commonProblem 2 .outer .coreCorner false false 2) (pairBox .outer .coreCorner)=true := by decide
theorem common_2_outer_coreCorner_00_3 :
    certify 96 (commonProblem 2 .outer .coreCorner false false 3) (pairBox .outer .coreCorner)=true := by decide
theorem common_2_outer_coreCorner_01_1 :
    certify 96 (commonProblem 2 .outer .coreCorner false true 1) (pairBox .outer .coreCorner)=true := by decide
theorem common_2_outer_coreCorner_01_2 :
    certify 96 (commonProblem 2 .outer .coreCorner false true 2) (pairBox .outer .coreCorner)=true := by decide
theorem common_2_outer_coreCorner_01_3 :
    certify 96 (commonProblem 2 .outer .coreCorner false true 3) (pairBox .outer .coreCorner)=true := by decide
theorem common_2_outer_coreCorner_10_0 :
    certify 96 (commonProblem 2 .outer .coreCorner true false 0) (pairBox .outer .coreCorner)=true := by decide
theorem common_2_outer_coreCorner_10_1 :
    certify 96 (commonProblem 2 .outer .coreCorner true false 1) (pairBox .outer .coreCorner)=true := by decide
theorem common_2_outer_coreCorner_10_2 :
    certify 96 (commonProblem 2 .outer .coreCorner true false 2) (pairBox .outer .coreCorner)=true := by decide
theorem common_2_outer_coreCorner_10_3 :
    certify 96 (commonProblem 2 .outer .coreCorner true false 3) (pairBox .outer .coreCorner)=true := by decide
theorem common_2_outer_coreCorner_11_0 :
    certify 96 (commonProblem 2 .outer .coreCorner true true 0) (pairBox .outer .coreCorner)=true := by decide
theorem common_2_outer_coreCorner_11_1 :
    certify 96 (commonProblem 2 .outer .coreCorner true true 1) (pairBox .outer .coreCorner)=true := by decide
theorem common_2_outer_coreCorner_11_2 :
    certify 96 (commonProblem 2 .outer .coreCorner true true 2) (pairBox .outer .coreCorner)=true := by decide
theorem common_2_outer_coreCorner_11_3 :
    certify 96 (commonProblem 2 .outer .coreCorner true true 3) (pairBox .outer .coreCorner)=true := by decide
theorem common_2_coreSide_outer_00_0 :
    certify 96 (commonProblem 2 .coreSide .outer false false 0) (pairBox .coreSide .outer)=true := by decide
theorem common_2_coreSide_outer_00_1 :
    certify 96 (commonProblem 2 .coreSide .outer false false 1) (pairBox .coreSide .outer)=true := by decide
theorem common_2_coreSide_outer_00_2 :
    certify 96 (commonProblem 2 .coreSide .outer false false 2) (pairBox .coreSide .outer)=true := by decide
theorem common_2_coreSide_outer_00_3 :
    certify 96 (commonProblem 2 .coreSide .outer false false 3) (pairBox .coreSide .outer)=true := by decide
theorem common_2_coreSide_outer_01_0 :
    certify 96 (commonProblem 2 .coreSide .outer false true 0) (pairBox .coreSide .outer)=true := by decide
theorem common_2_coreSide_outer_01_1 :
    certify 96 (commonProblem 2 .coreSide .outer false true 1) (pairBox .coreSide .outer)=true := by decide
theorem common_2_coreSide_outer_01_3 :
    certify 96 (commonProblem 2 .coreSide .outer false true 3) (pairBox .coreSide .outer)=true := by decide
theorem common_2_coreSide_outer_10_0 :
    certify 96 (commonProblem 2 .coreSide .outer true false 0) (pairBox .coreSide .outer)=true := by decide
theorem common_2_coreSide_outer_10_1 :
    certify 96 (commonProblem 2 .coreSide .outer true false 1) (pairBox .coreSide .outer)=true := by decide
theorem common_2_coreSide_outer_10_2 :
    certify 96 (commonProblem 2 .coreSide .outer true false 2) (pairBox .coreSide .outer)=true := by decide
theorem common_2_coreSide_outer_10_3 :
    certify 96 (commonProblem 2 .coreSide .outer true false 3) (pairBox .coreSide .outer)=true := by decide
theorem common_2_coreSide_outer_11_0 :
    certify 96 (commonProblem 2 .coreSide .outer true true 0) (pairBox .coreSide .outer)=true := by decide
theorem common_2_coreSide_outer_11_1 :
    certify 96 (commonProblem 2 .coreSide .outer true true 1) (pairBox .coreSide .outer)=true := by decide
theorem common_2_coreSide_outer_11_3 :
    certify 96 (commonProblem 2 .coreSide .outer true true 3) (pairBox .coreSide .outer)=true := by decide
theorem common_2_coreCorner_outer_00_0 :
    certify 96 (commonProblem 2 .coreCorner .outer false false 0) (pairBox .coreCorner .outer)=true := by decide
theorem common_2_coreCorner_outer_00_1 :
    certify 96 (commonProblem 2 .coreCorner .outer false false 1) (pairBox .coreCorner .outer)=true := by decide
theorem common_2_coreCorner_outer_00_2 :
    certify 96 (commonProblem 2 .coreCorner .outer false false 2) (pairBox .coreCorner .outer)=true := by decide
theorem common_2_coreCorner_outer_00_3 :
    certify 96 (commonProblem 2 .coreCorner .outer false false 3) (pairBox .coreCorner .outer)=true := by decide
theorem common_2_coreCorner_outer_01_0 :
    certify 96 (commonProblem 2 .coreCorner .outer false true 0) (pairBox .coreCorner .outer)=true := by decide
theorem common_2_coreCorner_outer_01_1 :
    certify 96 (commonProblem 2 .coreCorner .outer false true 1) (pairBox .coreCorner .outer)=true := by decide
theorem common_2_coreCorner_outer_01_3 :
    certify 96 (commonProblem 2 .coreCorner .outer false true 3) (pairBox .coreCorner .outer)=true := by decide
theorem common_2_coreCorner_outer_10_0 :
    certify 96 (commonProblem 2 .coreCorner .outer true false 0) (pairBox .coreCorner .outer)=true := by decide
theorem common_2_coreCorner_outer_10_1 :
    certify 96 (commonProblem 2 .coreCorner .outer true false 1) (pairBox .coreCorner .outer)=true := by decide
theorem common_2_coreCorner_outer_10_2 :
    certify 96 (commonProblem 2 .coreCorner .outer true false 2) (pairBox .coreCorner .outer)=true := by decide
theorem common_2_coreCorner_outer_10_3 :
    certify 96 (commonProblem 2 .coreCorner .outer true false 3) (pairBox .coreCorner .outer)=true := by decide
theorem common_2_coreCorner_outer_11_0 :
    certify 96 (commonProblem 2 .coreCorner .outer true true 0) (pairBox .coreCorner .outer)=true := by decide
theorem common_2_coreCorner_outer_11_1 :
    certify 96 (commonProblem 2 .coreCorner .outer true true 1) (pairBox .coreCorner .outer)=true := by decide
theorem common_2_coreCorner_outer_11_3 :
    certify 96 (commonProblem 2 .coreCorner .outer true true 3) (pairBox .coreCorner .outer)=true := by decide

theorem common_certificates (k : Fin 3) (source target : RadialKind)
    (σ τ : Bool) (axis : Fin 4) (houter : source=.outer ∨ target=.outer)
    (hkeep : ¬ CoreSeparatorExcluded k source target σ τ axis) :
    certify 96 (commonProblem k source target σ τ axis) (pairBox source target)=true := by
  fin_cases k <;> cases source <;> cases target <;> cases σ <;> cases τ <;> fin_cases axis
  all_goals first
  | solve | simp at houter
  | solve | simp [CoreSeparatorExcluded] at hkeep
  | exact common_0_outer_outer_00_0
  | exact common_0_outer_outer_00_1
  | exact common_0_outer_outer_00_2
  | exact common_0_outer_outer_00_3
  | exact common_0_outer_outer_01_0
  | exact common_0_outer_outer_01_1
  | exact common_0_outer_outer_01_2
  | exact common_0_outer_outer_01_3
  | exact common_0_outer_outer_10_0
  | exact common_0_outer_outer_10_1
  | exact common_0_outer_outer_10_2
  | exact common_0_outer_outer_10_3
  | exact common_0_outer_outer_11_0
  | exact common_0_outer_outer_11_1
  | exact common_0_outer_outer_11_2
  | exact common_0_outer_outer_11_3
  | exact common_0_outer_coreSide_00_2
  | exact common_0_outer_coreSide_00_3
  | exact common_0_outer_coreSide_01_2
  | exact common_0_outer_coreSide_01_3
  | exact common_0_outer_coreSide_10_0
  | exact common_0_outer_coreSide_10_2
  | exact common_0_outer_coreSide_10_3
  | exact common_0_outer_coreSide_11_0
  | exact common_0_outer_coreSide_11_2
  | exact common_0_outer_coreSide_11_3
  | exact common_0_outer_coreCorner_00_2
  | exact common_0_outer_coreCorner_00_3
  | exact common_0_outer_coreCorner_01_2
  | exact common_0_outer_coreCorner_01_3
  | exact common_0_outer_coreCorner_10_0
  | exact common_0_outer_coreCorner_10_2
  | exact common_0_outer_coreCorner_10_3
  | exact common_0_outer_coreCorner_11_0
  | exact common_0_outer_coreCorner_11_2
  | exact common_0_outer_coreCorner_11_3
  | exact common_0_coreSide_outer_00_0
  | exact common_0_coreSide_outer_00_1
  | exact common_0_coreSide_outer_00_2
  | exact common_0_coreSide_outer_01_0
  | exact common_0_coreSide_outer_01_1
  | exact common_0_coreSide_outer_10_0
  | exact common_0_coreSide_outer_10_1
  | exact common_0_coreSide_outer_10_2
  | exact common_0_coreSide_outer_11_0
  | exact common_0_coreSide_outer_11_1
  | exact common_0_coreCorner_outer_00_0
  | exact common_0_coreCorner_outer_00_1
  | exact common_0_coreCorner_outer_00_2
  | exact common_0_coreCorner_outer_01_0
  | exact common_0_coreCorner_outer_01_1
  | exact common_0_coreCorner_outer_10_0
  | exact common_0_coreCorner_outer_10_1
  | exact common_0_coreCorner_outer_10_2
  | exact common_0_coreCorner_outer_11_0
  | exact common_0_coreCorner_outer_11_1
  | exact common_1_outer_outer_00_0
  | exact common_1_outer_outer_00_1
  | exact common_1_outer_outer_00_2
  | exact common_1_outer_outer_00_3
  | exact common_1_outer_outer_01_0
  | exact common_1_outer_outer_01_1
  | exact common_1_outer_outer_01_2
  | exact common_1_outer_outer_01_3
  | exact common_1_outer_outer_10_0
  | exact common_1_outer_outer_10_1
  | exact common_1_outer_outer_10_2
  | exact common_1_outer_outer_10_3
  | exact common_1_outer_outer_11_0
  | exact common_1_outer_outer_11_1
  | exact common_1_outer_outer_11_2
  | exact common_1_outer_outer_11_3
  | exact common_1_outer_coreSide_00_1
  | exact common_1_outer_coreSide_00_2
  | exact common_1_outer_coreSide_00_3
  | exact common_1_outer_coreSide_01_1
  | exact common_1_outer_coreSide_01_2
  | exact common_1_outer_coreSide_01_3
  | exact common_1_outer_coreSide_10_0
  | exact common_1_outer_coreSide_10_1
  | exact common_1_outer_coreSide_10_2
  | exact common_1_outer_coreSide_10_3
  | exact common_1_outer_coreSide_11_0
  | exact common_1_outer_coreSide_11_1
  | exact common_1_outer_coreSide_11_2
  | exact common_1_outer_coreSide_11_3
  | exact common_1_outer_coreCorner_00_1
  | exact common_1_outer_coreCorner_00_2
  | exact common_1_outer_coreCorner_00_3
  | exact common_1_outer_coreCorner_01_1
  | exact common_1_outer_coreCorner_01_2
  | exact common_1_outer_coreCorner_01_3
  | exact common_1_outer_coreCorner_10_0
  | exact common_1_outer_coreCorner_10_1
  | exact common_1_outer_coreCorner_10_2
  | exact common_1_outer_coreCorner_10_3
  | exact common_1_outer_coreCorner_11_0
  | exact common_1_outer_coreCorner_11_1
  | exact common_1_outer_coreCorner_11_2
  | exact common_1_outer_coreCorner_11_3
  | exact common_1_coreSide_outer_00_0
  | exact common_1_coreSide_outer_00_1
  | exact common_1_coreSide_outer_00_2
  | exact common_1_coreSide_outer_00_3
  | exact common_1_coreSide_outer_01_0
  | exact common_1_coreSide_outer_01_1
  | exact common_1_coreSide_outer_01_3
  | exact common_1_coreSide_outer_10_0
  | exact common_1_coreSide_outer_10_1
  | exact common_1_coreSide_outer_10_2
  | exact common_1_coreSide_outer_10_3
  | exact common_1_coreSide_outer_11_0
  | exact common_1_coreSide_outer_11_1
  | exact common_1_coreSide_outer_11_3
  | exact common_1_coreCorner_outer_00_0
  | exact common_1_coreCorner_outer_00_1
  | exact common_1_coreCorner_outer_00_2
  | exact common_1_coreCorner_outer_00_3
  | exact common_1_coreCorner_outer_01_0
  | exact common_1_coreCorner_outer_01_1
  | exact common_1_coreCorner_outer_01_3
  | exact common_1_coreCorner_outer_10_0
  | exact common_1_coreCorner_outer_10_1
  | exact common_1_coreCorner_outer_10_2
  | exact common_1_coreCorner_outer_10_3
  | exact common_1_coreCorner_outer_11_0
  | exact common_1_coreCorner_outer_11_1
  | exact common_1_coreCorner_outer_11_3
  | exact common_2_outer_outer_00_0
  | exact common_2_outer_outer_00_1
  | exact common_2_outer_outer_00_2
  | exact common_2_outer_outer_00_3
  | exact common_2_outer_outer_01_0
  | exact common_2_outer_outer_01_1
  | exact common_2_outer_outer_01_2
  | exact common_2_outer_outer_01_3
  | exact common_2_outer_outer_10_0
  | exact common_2_outer_outer_10_1
  | exact common_2_outer_outer_10_2
  | exact common_2_outer_outer_10_3
  | exact common_2_outer_outer_11_0
  | exact common_2_outer_outer_11_1
  | exact common_2_outer_outer_11_2
  | exact common_2_outer_outer_11_3
  | exact common_2_outer_coreSide_00_1
  | exact common_2_outer_coreSide_00_2
  | exact common_2_outer_coreSide_00_3
  | exact common_2_outer_coreSide_01_1
  | exact common_2_outer_coreSide_01_2
  | exact common_2_outer_coreSide_01_3
  | exact common_2_outer_coreSide_10_0
  | exact common_2_outer_coreSide_10_1
  | exact common_2_outer_coreSide_10_2
  | exact common_2_outer_coreSide_10_3
  | exact common_2_outer_coreSide_11_0
  | exact common_2_outer_coreSide_11_1
  | exact common_2_outer_coreSide_11_2
  | exact common_2_outer_coreSide_11_3
  | exact common_2_outer_coreCorner_00_1
  | exact common_2_outer_coreCorner_00_2
  | exact common_2_outer_coreCorner_00_3
  | exact common_2_outer_coreCorner_01_1
  | exact common_2_outer_coreCorner_01_2
  | exact common_2_outer_coreCorner_01_3
  | exact common_2_outer_coreCorner_10_0
  | exact common_2_outer_coreCorner_10_1
  | exact common_2_outer_coreCorner_10_2
  | exact common_2_outer_coreCorner_10_3
  | exact common_2_outer_coreCorner_11_0
  | exact common_2_outer_coreCorner_11_1
  | exact common_2_outer_coreCorner_11_2
  | exact common_2_outer_coreCorner_11_3
  | exact common_2_coreSide_outer_00_0
  | exact common_2_coreSide_outer_00_1
  | exact common_2_coreSide_outer_00_2
  | exact common_2_coreSide_outer_00_3
  | exact common_2_coreSide_outer_01_0
  | exact common_2_coreSide_outer_01_1
  | exact common_2_coreSide_outer_01_3
  | exact common_2_coreSide_outer_10_0
  | exact common_2_coreSide_outer_10_1
  | exact common_2_coreSide_outer_10_2
  | exact common_2_coreSide_outer_10_3
  | exact common_2_coreSide_outer_11_0
  | exact common_2_coreSide_outer_11_1
  | exact common_2_coreSide_outer_11_3
  | exact common_2_coreCorner_outer_00_0
  | exact common_2_coreCorner_outer_00_1
  | exact common_2_coreCorner_outer_00_2
  | exact common_2_coreCorner_outer_00_3
  | exact common_2_coreCorner_outer_01_0
  | exact common_2_coreCorner_outer_01_1
  | exact common_2_coreCorner_outer_01_3
  | exact common_2_coreCorner_outer_10_0
  | exact common_2_coreCorner_outer_10_1
  | exact common_2_coreCorner_outer_10_2
  | exact common_2_coreCorner_outer_10_3
  | exact common_2_coreCorner_outer_11_0
  | exact common_2_coreCorner_outer_11_1
  | exact common_2_coreCorner_outer_11_3
theorem short_0_outer_outer_10_0 :
    certify 96 (wrongProblem .short 0 .outer .outer true false 0) (pairBox .outer .outer)=true := by decide
theorem short_0_outer_outer_10_1 :
    certify 96 (wrongProblem .short 0 .outer .outer true false 1) (pairBox .outer .outer)=true := by decide
theorem short_0_outer_outer_10_2 :
    certify 96 (wrongProblem .short 0 .outer .outer true false 2) (pairBox .outer .outer)=true := by decide
theorem short_0_outer_outer_10_3 :
    certify 96 (wrongProblem .short 0 .outer .outer true false 3) (pairBox .outer .outer)=true := by decide
theorem short_0_outer_coreSide_10_0 :
    certify 96 (wrongProblem .short 0 .outer .coreSide true false 0) (pairBox .outer .coreSide)=true := by decide
theorem short_0_outer_coreSide_10_2 :
    certify 96 (wrongProblem .short 0 .outer .coreSide true false 2) (pairBox .outer .coreSide)=true := by decide
theorem short_0_outer_coreSide_10_3 :
    certify 96 (wrongProblem .short 0 .outer .coreSide true false 3) (pairBox .outer .coreSide)=true := by decide
theorem short_0_outer_coreCorner_10_0 :
    certify 96 (wrongProblem .short 0 .outer .coreCorner true false 0) (pairBox .outer .coreCorner)=true := by decide
theorem short_0_outer_coreCorner_10_2 :
    certify 96 (wrongProblem .short 0 .outer .coreCorner true false 2) (pairBox .outer .coreCorner)=true := by decide
theorem short_0_outer_coreCorner_10_3 :
    certify 96 (wrongProblem .short 0 .outer .coreCorner true false 3) (pairBox .outer .coreCorner)=true := by decide
theorem short_0_coreSide_outer_10_0 :
    certify 96 (wrongProblem .short 0 .coreSide .outer true false 0) (pairBox .coreSide .outer)=true := by decide
theorem short_0_coreSide_outer_10_1 :
    certify 96 (wrongProblem .short 0 .coreSide .outer true false 1) (pairBox .coreSide .outer)=true := by decide
theorem short_0_coreSide_outer_10_2 :
    certify 96 (wrongProblem .short 0 .coreSide .outer true false 2) (pairBox .coreSide .outer)=true := by decide
theorem short_0_coreSide_coreSide_10_0 :
    certify 96 (wrongProblem .short 0 .coreSide .coreSide true false 0) (pairBox .coreSide .coreSide)=true := by decide
theorem short_0_coreSide_coreSide_10_2 :
    certify 96 (wrongProblem .short 0 .coreSide .coreSide true false 2) (pairBox .coreSide .coreSide)=true := by decide
theorem short_0_coreSide_coreCorner_10_0 :
    certify 96 (wrongProblem .short 0 .coreSide .coreCorner true false 0) (pairBox .coreSide .coreCorner)=true := by decide
theorem short_0_coreSide_coreCorner_10_2 :
    certify 96 (wrongProblem .short 0 .coreSide .coreCorner true false 2) (pairBox .coreSide .coreCorner)=true := by decide
theorem short_0_coreCorner_outer_10_0 :
    certify 96 (wrongProblem .short 0 .coreCorner .outer true false 0) (pairBox .coreCorner .outer)=true := by decide
theorem short_0_coreCorner_outer_10_1 :
    certify 96 (wrongProblem .short 0 .coreCorner .outer true false 1) (pairBox .coreCorner .outer)=true := by decide
theorem short_0_coreCorner_outer_10_2 :
    certify 96 (wrongProblem .short 0 .coreCorner .outer true false 2) (pairBox .coreCorner .outer)=true := by decide
theorem short_0_coreCorner_coreSide_10_0 :
    certify 96 (wrongProblem .short 0 .coreCorner .coreSide true false 0) (pairBox .coreCorner .coreSide)=true := by decide
theorem short_0_coreCorner_coreSide_10_2 :
    certify 96 (wrongProblem .short 0 .coreCorner .coreSide true false 2) (pairBox .coreCorner .coreSide)=true := by decide
theorem short_0_coreCorner_coreCorner_10_0 :
    certify 96 (wrongProblem .short 0 .coreCorner .coreCorner true false 0) (pairBox .coreCorner .coreCorner)=true := by decide
theorem short_0_coreCorner_coreCorner_10_2 :
    certify 96 (wrongProblem .short 0 .coreCorner .coreCorner true false 2) (pairBox .coreCorner .coreCorner)=true := by decide
theorem short_0_outer_outer_11_0 :
    certify 96 (wrongProblem .short 0 .outer .outer true true 0) (pairBox .outer .outer)=true := by decide
theorem short_0_outer_outer_11_1 :
    certify 96 (wrongProblem .short 0 .outer .outer true true 1) (pairBox .outer .outer)=true := by decide
theorem short_0_outer_outer_11_2 :
    certify 96 (wrongProblem .short 0 .outer .outer true true 2) (pairBox .outer .outer)=true := by decide
theorem short_0_outer_outer_11_3 :
    certify 96 (wrongProblem .short 0 .outer .outer true true 3) (pairBox .outer .outer)=true := by decide
theorem short_0_outer_coreSide_11_0 :
    certify 96 (wrongProblem .short 0 .outer .coreSide true true 0) (pairBox .outer .coreSide)=true := by decide
theorem short_0_outer_coreSide_11_2 :
    certify 96 (wrongProblem .short 0 .outer .coreSide true true 2) (pairBox .outer .coreSide)=true := by decide
theorem short_0_outer_coreSide_11_3 :
    certify 96 (wrongProblem .short 0 .outer .coreSide true true 3) (pairBox .outer .coreSide)=true := by decide
theorem short_0_outer_coreCorner_11_0 :
    certify 96 (wrongProblem .short 0 .outer .coreCorner true true 0) (pairBox .outer .coreCorner)=true := by decide
theorem short_0_outer_coreCorner_11_2 :
    certify 96 (wrongProblem .short 0 .outer .coreCorner true true 2) (pairBox .outer .coreCorner)=true := by decide
theorem short_0_outer_coreCorner_11_3 :
    certify 96 (wrongProblem .short 0 .outer .coreCorner true true 3) (pairBox .outer .coreCorner)=true := by decide
theorem short_0_coreSide_outer_11_0 :
    certify 96 (wrongProblem .short 0 .coreSide .outer true true 0) (pairBox .coreSide .outer)=true := by decide
theorem short_0_coreSide_outer_11_1 :
    certify 96 (wrongProblem .short 0 .coreSide .outer true true 1) (pairBox .coreSide .outer)=true := by decide
theorem short_0_coreSide_coreSide_11_0 :
    certify 96 (wrongProblem .short 0 .coreSide .coreSide true true 0) (pairBox .coreSide .coreSide)=true := by decide
theorem short_0_coreSide_coreCorner_11_0 :
    certify 96 (wrongProblem .short 0 .coreSide .coreCorner true true 0) (pairBox .coreSide .coreCorner)=true := by decide
theorem short_0_coreCorner_outer_11_0 :
    certify 96 (wrongProblem .short 0 .coreCorner .outer true true 0) (pairBox .coreCorner .outer)=true := by decide
theorem short_0_coreCorner_outer_11_1 :
    certify 96 (wrongProblem .short 0 .coreCorner .outer true true 1) (pairBox .coreCorner .outer)=true := by decide
theorem short_0_coreCorner_coreSide_11_0 :
    certify 96 (wrongProblem .short 0 .coreCorner .coreSide true true 0) (pairBox .coreCorner .coreSide)=true := by decide
theorem short_0_coreCorner_coreCorner_11_0 :
    certify 96 (wrongProblem .short 0 .coreCorner .coreCorner true true 0) (pairBox .coreCorner .coreCorner)=true := by decide
theorem short_1_outer_outer_00_0 :
    certify 96 (wrongProblem .short 1 .outer .outer false false 0) (pairBox .outer .outer)=true := by decide
theorem short_1_outer_outer_00_1 :
    certify 96 (wrongProblem .short 1 .outer .outer false false 1) (pairBox .outer .outer)=true := by decide
theorem short_1_outer_outer_00_2 :
    certify 96 (wrongProblem .short 1 .outer .outer false false 2) (pairBox .outer .outer)=true := by decide
theorem short_1_outer_outer_00_3 :
    certify 96 (wrongProblem .short 1 .outer .outer false false 3) (pairBox .outer .outer)=true := by decide
theorem short_1_outer_coreSide_00_2 :
    certify 96 (wrongProblem .short 1 .outer .coreSide false false 2) (pairBox .outer .coreSide)=true := by decide
theorem short_1_outer_coreSide_00_3 :
    certify 96 (wrongProblem .short 1 .outer .coreSide false false 3) (pairBox .outer .coreSide)=true := by decide
theorem short_1_outer_coreCorner_00_2 :
    certify 96 (wrongProblem .short 1 .outer .coreCorner false false 2) (pairBox .outer .coreCorner)=true := by decide
theorem short_1_outer_coreCorner_00_3 :
    certify 96 (wrongProblem .short 1 .outer .coreCorner false false 3) (pairBox .outer .coreCorner)=true := by decide
theorem short_1_coreSide_outer_00_0 :
    certify 96 (wrongProblem .short 1 .coreSide .outer false false 0) (pairBox .coreSide .outer)=true := by decide
theorem short_1_coreSide_outer_00_1 :
    certify 96 (wrongProblem .short 1 .coreSide .outer false false 1) (pairBox .coreSide .outer)=true := by decide
theorem short_1_coreSide_outer_00_2 :
    certify 96 (wrongProblem .short 1 .coreSide .outer false false 2) (pairBox .coreSide .outer)=true := by decide
theorem short_1_coreSide_coreSide_00_2 :
    certify 96 (wrongProblem .short 1 .coreSide .coreSide false false 2) (pairBox .coreSide .coreSide)=true := by decide
theorem short_1_coreSide_coreCorner_00_2 :
    certify 96 (wrongProblem .short 1 .coreSide .coreCorner false false 2) (pairBox .coreSide .coreCorner)=true := by decide
theorem short_1_coreCorner_outer_00_0 :
    certify 96 (wrongProblem .short 1 .coreCorner .outer false false 0) (pairBox .coreCorner .outer)=true := by decide
theorem short_1_coreCorner_outer_00_1 :
    certify 96 (wrongProblem .short 1 .coreCorner .outer false false 1) (pairBox .coreCorner .outer)=true := by decide
theorem short_1_coreCorner_outer_00_2 :
    certify 96 (wrongProblem .short 1 .coreCorner .outer false false 2) (pairBox .coreCorner .outer)=true := by decide
theorem short_1_coreCorner_coreSide_00_2 :
    certify 96 (wrongProblem .short 1 .coreCorner .coreSide false false 2) (pairBox .coreCorner .coreSide)=true := by decide
theorem short_1_coreCorner_coreCorner_00_2 :
    certify 96 (wrongProblem .short 1 .coreCorner .coreCorner false false 2) (pairBox .coreCorner .coreCorner)=true := by decide
theorem short_1_outer_outer_10_0 :
    certify 96 (wrongProblem .short 1 .outer .outer true false 0) (pairBox .outer .outer)=true := by decide
theorem short_1_outer_outer_10_1 :
    certify 96 (wrongProblem .short 1 .outer .outer true false 1) (pairBox .outer .outer)=true := by decide
theorem short_1_outer_outer_10_2 :
    certify 96 (wrongProblem .short 1 .outer .outer true false 2) (pairBox .outer .outer)=true := by decide
theorem short_1_outer_outer_10_3 :
    certify 96 (wrongProblem .short 1 .outer .outer true false 3) (pairBox .outer .outer)=true := by decide
theorem short_1_outer_coreSide_10_0 :
    certify 96 (wrongProblem .short 1 .outer .coreSide true false 0) (pairBox .outer .coreSide)=true := by decide
theorem short_1_outer_coreSide_10_2 :
    certify 96 (wrongProblem .short 1 .outer .coreSide true false 2) (pairBox .outer .coreSide)=true := by decide
theorem short_1_outer_coreSide_10_3 :
    certify 96 (wrongProblem .short 1 .outer .coreSide true false 3) (pairBox .outer .coreSide)=true := by decide
theorem short_1_outer_coreCorner_10_0 :
    certify 96 (wrongProblem .short 1 .outer .coreCorner true false 0) (pairBox .outer .coreCorner)=true := by decide
theorem short_1_outer_coreCorner_10_2 :
    certify 96 (wrongProblem .short 1 .outer .coreCorner true false 2) (pairBox .outer .coreCorner)=true := by decide
theorem short_1_outer_coreCorner_10_3 :
    certify 96 (wrongProblem .short 1 .outer .coreCorner true false 3) (pairBox .outer .coreCorner)=true := by decide
theorem short_1_coreSide_outer_10_0 :
    certify 96 (wrongProblem .short 1 .coreSide .outer true false 0) (pairBox .coreSide .outer)=true := by decide
theorem short_1_coreSide_outer_10_1 :
    certify 96 (wrongProblem .short 1 .coreSide .outer true false 1) (pairBox .coreSide .outer)=true := by decide
theorem short_1_coreSide_outer_10_2 :
    certify 96 (wrongProblem .short 1 .coreSide .outer true false 2) (pairBox .coreSide .outer)=true := by decide
theorem short_1_coreSide_coreSide_10_0 :
    certify 96 (wrongProblem .short 1 .coreSide .coreSide true false 0) (pairBox .coreSide .coreSide)=true := by decide
theorem short_1_coreSide_coreSide_10_2 :
    certify 96 (wrongProblem .short 1 .coreSide .coreSide true false 2) (pairBox .coreSide .coreSide)=true := by decide
theorem short_1_coreSide_coreCorner_10_0 :
    certify 96 (wrongProblem .short 1 .coreSide .coreCorner true false 0) (pairBox .coreSide .coreCorner)=true := by decide
theorem short_1_coreSide_coreCorner_10_2 :
    certify 96 (wrongProblem .short 1 .coreSide .coreCorner true false 2) (pairBox .coreSide .coreCorner)=true := by decide
theorem short_1_coreCorner_outer_10_0 :
    certify 96 (wrongProblem .short 1 .coreCorner .outer true false 0) (pairBox .coreCorner .outer)=true := by decide
theorem short_1_coreCorner_outer_10_1 :
    certify 96 (wrongProblem .short 1 .coreCorner .outer true false 1) (pairBox .coreCorner .outer)=true := by decide
theorem short_1_coreCorner_outer_10_2 :
    certify 96 (wrongProblem .short 1 .coreCorner .outer true false 2) (pairBox .coreCorner .outer)=true := by decide
theorem short_1_coreCorner_coreSide_10_0 :
    certify 96 (wrongProblem .short 1 .coreCorner .coreSide true false 0) (pairBox .coreCorner .coreSide)=true := by decide
theorem short_1_coreCorner_coreSide_10_2 :
    certify 96 (wrongProblem .short 1 .coreCorner .coreSide true false 2) (pairBox .coreCorner .coreSide)=true := by decide
theorem short_1_coreCorner_coreCorner_10_0 :
    certify 96 (wrongProblem .short 1 .coreCorner .coreCorner true false 0) (pairBox .coreCorner .coreCorner)=true := by decide
theorem short_1_coreCorner_coreCorner_10_2 :
    certify 96 (wrongProblem .short 1 .coreCorner .coreCorner true false 2) (pairBox .coreCorner .coreCorner)=true := by decide
theorem short_2_outer_outer_00_0 :
    certify 96 (wrongProblem .short 2 .outer .outer false false 0) (pairBox .outer .outer)=true := by decide
theorem short_2_outer_outer_00_1 :
    certify 96 (wrongProblem .short 2 .outer .outer false false 1) (pairBox .outer .outer)=true := by decide
theorem short_2_outer_outer_00_2 :
    certify 96 (wrongProblem .short 2 .outer .outer false false 2) (pairBox .outer .outer)=true := by decide
theorem short_2_outer_outer_00_3 :
    certify 96 (wrongProblem .short 2 .outer .outer false false 3) (pairBox .outer .outer)=true := by decide
theorem short_2_outer_coreSide_00_1 :
    certify 96 (wrongProblem .short 2 .outer .coreSide false false 1) (pairBox .outer .coreSide)=true := by decide
theorem short_2_outer_coreSide_00_2 :
    certify 96 (wrongProblem .short 2 .outer .coreSide false false 2) (pairBox .outer .coreSide)=true := by decide
theorem short_2_outer_coreSide_00_3 :
    certify 96 (wrongProblem .short 2 .outer .coreSide false false 3) (pairBox .outer .coreSide)=true := by decide
theorem short_2_outer_coreCorner_00_1 :
    certify 96 (wrongProblem .short 2 .outer .coreCorner false false 1) (pairBox .outer .coreCorner)=true := by decide
theorem short_2_outer_coreCorner_00_2 :
    certify 96 (wrongProblem .short 2 .outer .coreCorner false false 2) (pairBox .outer .coreCorner)=true := by decide
theorem short_2_outer_coreCorner_00_3 :
    certify 96 (wrongProblem .short 2 .outer .coreCorner false false 3) (pairBox .outer .coreCorner)=true := by decide
theorem short_2_coreSide_outer_00_0 :
    certify 96 (wrongProblem .short 2 .coreSide .outer false false 0) (pairBox .coreSide .outer)=true := by decide
theorem short_2_coreSide_outer_00_1 :
    certify 96 (wrongProblem .short 2 .coreSide .outer false false 1) (pairBox .coreSide .outer)=true := by decide
theorem short_2_coreSide_outer_00_2 :
    certify 96 (wrongProblem .short 2 .coreSide .outer false false 2) (pairBox .coreSide .outer)=true := by decide
theorem short_2_coreSide_outer_00_3 :
    certify 96 (wrongProblem .short 2 .coreSide .outer false false 3) (pairBox .coreSide .outer)=true := by decide
theorem short_2_coreSide_coreSide_00_1 :
    certify 96 (wrongProblem .short 2 .coreSide .coreSide false false 1) (pairBox .coreSide .coreSide)=true := by decide
theorem short_2_coreSide_coreSide_00_2 :
    certify 96 (wrongProblem .short 2 .coreSide .coreSide false false 2) (pairBox .coreSide .coreSide)=true := by decide
theorem short_2_coreSide_coreSide_00_3 :
    certify 96 (wrongProblem .short 2 .coreSide .coreSide false false 3) (pairBox .coreSide .coreSide)=true := by decide
theorem short_2_coreSide_coreCorner_00_1 :
    certify 96 (wrongProblem .short 2 .coreSide .coreCorner false false 1) (pairBox .coreSide .coreCorner)=true := by decide
theorem short_2_coreSide_coreCorner_00_2 :
    certify 96 (wrongProblem .short 2 .coreSide .coreCorner false false 2) (pairBox .coreSide .coreCorner)=true := by decide
theorem short_2_coreSide_coreCorner_00_3 :
    certify 96 (wrongProblem .short 2 .coreSide .coreCorner false false 3) (pairBox .coreSide .coreCorner)=true := by decide
theorem short_2_coreCorner_outer_00_0 :
    certify 96 (wrongProblem .short 2 .coreCorner .outer false false 0) (pairBox .coreCorner .outer)=true := by decide
theorem short_2_coreCorner_outer_00_1 :
    certify 96 (wrongProblem .short 2 .coreCorner .outer false false 1) (pairBox .coreCorner .outer)=true := by decide
theorem short_2_coreCorner_outer_00_2 :
    certify 96 (wrongProblem .short 2 .coreCorner .outer false false 2) (pairBox .coreCorner .outer)=true := by decide
theorem short_2_coreCorner_outer_00_3 :
    certify 96 (wrongProblem .short 2 .coreCorner .outer false false 3) (pairBox .coreCorner .outer)=true := by decide
theorem short_2_coreCorner_coreSide_00_1 :
    certify 96 (wrongProblem .short 2 .coreCorner .coreSide false false 1) (pairBox .coreCorner .coreSide)=true := by decide
theorem short_2_coreCorner_coreSide_00_2 :
    certify 96 (wrongProblem .short 2 .coreCorner .coreSide false false 2) (pairBox .coreCorner .coreSide)=true := by decide
theorem short_2_coreCorner_coreSide_00_3 :
    certify 96 (wrongProblem .short 2 .coreCorner .coreSide false false 3) (pairBox .coreCorner .coreSide)=true := by decide
theorem short_2_coreCorner_coreCorner_00_1 :
    certify 96 (wrongProblem .short 2 .coreCorner .coreCorner false false 1) (pairBox .coreCorner .coreCorner)=true := by decide
theorem short_2_coreCorner_coreCorner_00_2 :
    certify 96 (wrongProblem .short 2 .coreCorner .coreCorner false false 2) (pairBox .coreCorner .coreCorner)=true := by decide
theorem short_2_coreCorner_coreCorner_00_3 :
    certify 96 (wrongProblem .short 2 .coreCorner .coreCorner false false 3) (pairBox .coreCorner .coreCorner)=true := by decide
theorem short_2_outer_outer_01_0 :
    certify 96 (wrongProblem .short 2 .outer .outer false true 0) (pairBox .outer .outer)=true := by decide
theorem short_2_outer_outer_01_1 :
    certify 96 (wrongProblem .short 2 .outer .outer false true 1) (pairBox .outer .outer)=true := by decide
theorem short_2_outer_outer_01_2 :
    certify 96 (wrongProblem .short 2 .outer .outer false true 2) (pairBox .outer .outer)=true := by decide
theorem short_2_outer_outer_01_3 :
    certify 96 (wrongProblem .short 2 .outer .outer false true 3) (pairBox .outer .outer)=true := by decide
theorem short_2_outer_coreSide_01_1 :
    certify 96 (wrongProblem .short 2 .outer .coreSide false true 1) (pairBox .outer .coreSide)=true := by decide
theorem short_2_outer_coreSide_01_2 :
    certify 96 (wrongProblem .short 2 .outer .coreSide false true 2) (pairBox .outer .coreSide)=true := by decide
theorem short_2_outer_coreSide_01_3 :
    certify 96 (wrongProblem .short 2 .outer .coreSide false true 3) (pairBox .outer .coreSide)=true := by decide
theorem short_2_outer_coreCorner_01_1 :
    certify 96 (wrongProblem .short 2 .outer .coreCorner false true 1) (pairBox .outer .coreCorner)=true := by decide
theorem short_2_outer_coreCorner_01_2 :
    certify 96 (wrongProblem .short 2 .outer .coreCorner false true 2) (pairBox .outer .coreCorner)=true := by decide
theorem short_2_outer_coreCorner_01_3 :
    certify 96 (wrongProblem .short 2 .outer .coreCorner false true 3) (pairBox .outer .coreCorner)=true := by decide
theorem short_2_coreSide_outer_01_0 :
    certify 96 (wrongProblem .short 2 .coreSide .outer false true 0) (pairBox .coreSide .outer)=true := by decide
theorem short_2_coreSide_outer_01_1 :
    certify 96 (wrongProblem .short 2 .coreSide .outer false true 1) (pairBox .coreSide .outer)=true := by decide
theorem short_2_coreSide_outer_01_3 :
    certify 96 (wrongProblem .short 2 .coreSide .outer false true 3) (pairBox .coreSide .outer)=true := by decide
theorem short_2_coreSide_coreSide_01_1 :
    certify 96 (wrongProblem .short 2 .coreSide .coreSide false true 1) (pairBox .coreSide .coreSide)=true := by decide
theorem short_2_coreSide_coreSide_01_3 :
    certify 96 (wrongProblem .short 2 .coreSide .coreSide false true 3) (pairBox .coreSide .coreSide)=true := by decide
theorem short_2_coreSide_coreCorner_01_1 :
    certify 96 (wrongProblem .short 2 .coreSide .coreCorner false true 1) (pairBox .coreSide .coreCorner)=true := by decide
theorem short_2_coreSide_coreCorner_01_3 :
    certify 96 (wrongProblem .short 2 .coreSide .coreCorner false true 3) (pairBox .coreSide .coreCorner)=true := by decide
theorem short_2_coreCorner_outer_01_0 :
    certify 96 (wrongProblem .short 2 .coreCorner .outer false true 0) (pairBox .coreCorner .outer)=true := by decide
theorem short_2_coreCorner_outer_01_1 :
    certify 96 (wrongProblem .short 2 .coreCorner .outer false true 1) (pairBox .coreCorner .outer)=true := by decide
theorem short_2_coreCorner_outer_01_3 :
    certify 96 (wrongProblem .short 2 .coreCorner .outer false true 3) (pairBox .coreCorner .outer)=true := by decide
theorem short_2_coreCorner_coreSide_01_1 :
    certify 96 (wrongProblem .short 2 .coreCorner .coreSide false true 1) (pairBox .coreCorner .coreSide)=true := by decide
theorem short_2_coreCorner_coreSide_01_3 :
    certify 96 (wrongProblem .short 2 .coreCorner .coreSide false true 3) (pairBox .coreCorner .coreSide)=true := by decide
theorem short_2_coreCorner_coreCorner_01_1 :
    certify 96 (wrongProblem .short 2 .coreCorner .coreCorner false true 1) (pairBox .coreCorner .coreCorner)=true := by decide
theorem short_2_coreCorner_coreCorner_01_3 :
    certify 96 (wrongProblem .short 2 .coreCorner .coreCorner false true 3) (pairBox .coreCorner .coreCorner)=true := by decide
theorem short_3_outer_outer_00_0 :
    certify 96 (wrongProblem .short 3 .outer .outer false false 0) (pairBox .outer .outer)=true := by decide
theorem short_3_outer_outer_00_1 :
    certify 96 (wrongProblem .short 3 .outer .outer false false 1) (pairBox .outer .outer)=true := by decide
theorem short_3_outer_outer_00_2 :
    certify 96 (wrongProblem .short 3 .outer .outer false false 2) (pairBox .outer .outer)=true := by decide
theorem short_3_outer_outer_00_3 :
    certify 96 (wrongProblem .short 3 .outer .outer false false 3) (pairBox .outer .outer)=true := by decide
theorem short_3_outer_coreSide_00_2 :
    certify 96 (wrongProblem .short 3 .outer .coreSide false false 2) (pairBox .outer .coreSide)=true := by decide
theorem short_3_outer_coreSide_00_3 :
    certify 96 (wrongProblem .short 3 .outer .coreSide false false 3) (pairBox .outer .coreSide)=true := by decide
theorem short_3_outer_coreCorner_00_2 :
    certify 96 (wrongProblem .short 3 .outer .coreCorner false false 2) (pairBox .outer .coreCorner)=true := by decide
theorem short_3_outer_coreCorner_00_3 :
    certify 96 (wrongProblem .short 3 .outer .coreCorner false false 3) (pairBox .outer .coreCorner)=true := by decide
theorem short_3_coreSide_outer_00_0 :
    certify 96 (wrongProblem .short 3 .coreSide .outer false false 0) (pairBox .coreSide .outer)=true := by decide
theorem short_3_coreSide_outer_00_1 :
    certify 96 (wrongProblem .short 3 .coreSide .outer false false 1) (pairBox .coreSide .outer)=true := by decide
theorem short_3_coreSide_outer_00_2 :
    certify 96 (wrongProblem .short 3 .coreSide .outer false false 2) (pairBox .coreSide .outer)=true := by decide
theorem short_3_coreSide_coreSide_00_2 :
    certify 96 (wrongProblem .short 3 .coreSide .coreSide false false 2) (pairBox .coreSide .coreSide)=true := by decide
theorem short_3_coreSide_coreCorner_00_2 :
    certify 96 (wrongProblem .short 3 .coreSide .coreCorner false false 2) (pairBox .coreSide .coreCorner)=true := by decide
theorem short_3_coreCorner_outer_00_0 :
    certify 96 (wrongProblem .short 3 .coreCorner .outer false false 0) (pairBox .coreCorner .outer)=true := by decide
theorem short_3_coreCorner_outer_00_1 :
    certify 96 (wrongProblem .short 3 .coreCorner .outer false false 1) (pairBox .coreCorner .outer)=true := by decide
theorem short_3_coreCorner_outer_00_2 :
    certify 96 (wrongProblem .short 3 .coreCorner .outer false false 2) (pairBox .coreCorner .outer)=true := by decide
theorem short_3_coreCorner_coreSide_00_2 :
    certify 96 (wrongProblem .short 3 .coreCorner .coreSide false false 2) (pairBox .coreCorner .coreSide)=true := by decide
theorem short_3_coreCorner_coreCorner_00_2 :
    certify 96 (wrongProblem .short 3 .coreCorner .coreCorner false false 2) (pairBox .coreCorner .coreCorner)=true := by decide
theorem short_3_outer_outer_10_0 :
    certify 96 (wrongProblem .short 3 .outer .outer true false 0) (pairBox .outer .outer)=true := by decide
theorem short_3_outer_outer_10_1 :
    certify 96 (wrongProblem .short 3 .outer .outer true false 1) (pairBox .outer .outer)=true := by decide
theorem short_3_outer_outer_10_2 :
    certify 96 (wrongProblem .short 3 .outer .outer true false 2) (pairBox .outer .outer)=true := by decide
theorem short_3_outer_outer_10_3 :
    certify 96 (wrongProblem .short 3 .outer .outer true false 3) (pairBox .outer .outer)=true := by decide
theorem short_3_outer_coreSide_10_0 :
    certify 96 (wrongProblem .short 3 .outer .coreSide true false 0) (pairBox .outer .coreSide)=true := by decide
theorem short_3_outer_coreSide_10_2 :
    certify 96 (wrongProblem .short 3 .outer .coreSide true false 2) (pairBox .outer .coreSide)=true := by decide
theorem short_3_outer_coreSide_10_3 :
    certify 96 (wrongProblem .short 3 .outer .coreSide true false 3) (pairBox .outer .coreSide)=true := by decide
theorem short_3_outer_coreCorner_10_0 :
    certify 96 (wrongProblem .short 3 .outer .coreCorner true false 0) (pairBox .outer .coreCorner)=true := by decide
theorem short_3_outer_coreCorner_10_2 :
    certify 96 (wrongProblem .short 3 .outer .coreCorner true false 2) (pairBox .outer .coreCorner)=true := by decide
theorem short_3_outer_coreCorner_10_3 :
    certify 96 (wrongProblem .short 3 .outer .coreCorner true false 3) (pairBox .outer .coreCorner)=true := by decide
theorem short_3_coreSide_outer_10_0 :
    certify 96 (wrongProblem .short 3 .coreSide .outer true false 0) (pairBox .coreSide .outer)=true := by decide
theorem short_3_coreSide_outer_10_1 :
    certify 96 (wrongProblem .short 3 .coreSide .outer true false 1) (pairBox .coreSide .outer)=true := by decide
theorem short_3_coreSide_outer_10_2 :
    certify 96 (wrongProblem .short 3 .coreSide .outer true false 2) (pairBox .coreSide .outer)=true := by decide
theorem short_3_coreSide_coreSide_10_0 :
    certify 96 (wrongProblem .short 3 .coreSide .coreSide true false 0) (pairBox .coreSide .coreSide)=true := by decide
theorem short_3_coreSide_coreSide_10_2 :
    certify 96 (wrongProblem .short 3 .coreSide .coreSide true false 2) (pairBox .coreSide .coreSide)=true := by decide
theorem short_3_coreSide_coreCorner_10_0 :
    certify 96 (wrongProblem .short 3 .coreSide .coreCorner true false 0) (pairBox .coreSide .coreCorner)=true := by decide
theorem short_3_coreSide_coreCorner_10_2 :
    certify 96 (wrongProblem .short 3 .coreSide .coreCorner true false 2) (pairBox .coreSide .coreCorner)=true := by decide
theorem short_3_coreCorner_outer_10_0 :
    certify 96 (wrongProblem .short 3 .coreCorner .outer true false 0) (pairBox .coreCorner .outer)=true := by decide
theorem short_3_coreCorner_outer_10_1 :
    certify 96 (wrongProblem .short 3 .coreCorner .outer true false 1) (pairBox .coreCorner .outer)=true := by decide
theorem short_3_coreCorner_outer_10_2 :
    certify 96 (wrongProblem .short 3 .coreCorner .outer true false 2) (pairBox .coreCorner .outer)=true := by decide
theorem short_3_coreCorner_coreSide_10_0 :
    certify 96 (wrongProblem .short 3 .coreCorner .coreSide true false 0) (pairBox .coreCorner .coreSide)=true := by decide
theorem short_3_coreCorner_coreSide_10_2 :
    certify 96 (wrongProblem .short 3 .coreCorner .coreSide true false 2) (pairBox .coreCorner .coreSide)=true := by decide
theorem short_3_coreCorner_coreCorner_10_0 :
    certify 96 (wrongProblem .short 3 .coreCorner .coreCorner true false 0) (pairBox .coreCorner .coreCorner)=true := by decide
theorem short_3_coreCorner_coreCorner_10_2 :
    certify 96 (wrongProblem .short 3 .coreCorner .coreCorner true false 2) (pairBox .coreCorner .coreCorner)=true := by decide
theorem short_3_outer_outer_11_0 :
    certify 96 (wrongProblem .short 3 .outer .outer true true 0) (pairBox .outer .outer)=true := by decide
theorem short_3_outer_outer_11_1 :
    certify 96 (wrongProblem .short 3 .outer .outer true true 1) (pairBox .outer .outer)=true := by decide
theorem short_3_outer_outer_11_2 :
    certify 96 (wrongProblem .short 3 .outer .outer true true 2) (pairBox .outer .outer)=true := by decide
theorem short_3_outer_outer_11_3 :
    certify 96 (wrongProblem .short 3 .outer .outer true true 3) (pairBox .outer .outer)=true := by decide
theorem short_3_outer_coreSide_11_0 :
    certify 96 (wrongProblem .short 3 .outer .coreSide true true 0) (pairBox .outer .coreSide)=true := by decide
theorem short_3_outer_coreSide_11_2 :
    certify 96 (wrongProblem .short 3 .outer .coreSide true true 2) (pairBox .outer .coreSide)=true := by decide
theorem short_3_outer_coreSide_11_3 :
    certify 96 (wrongProblem .short 3 .outer .coreSide true true 3) (pairBox .outer .coreSide)=true := by decide
theorem short_3_outer_coreCorner_11_0 :
    certify 96 (wrongProblem .short 3 .outer .coreCorner true true 0) (pairBox .outer .coreCorner)=true := by decide
theorem short_3_outer_coreCorner_11_2 :
    certify 96 (wrongProblem .short 3 .outer .coreCorner true true 2) (pairBox .outer .coreCorner)=true := by decide
theorem short_3_outer_coreCorner_11_3 :
    certify 96 (wrongProblem .short 3 .outer .coreCorner true true 3) (pairBox .outer .coreCorner)=true := by decide
theorem short_3_coreSide_outer_11_0 :
    certify 96 (wrongProblem .short 3 .coreSide .outer true true 0) (pairBox .coreSide .outer)=true := by decide
theorem short_3_coreSide_outer_11_1 :
    certify 96 (wrongProblem .short 3 .coreSide .outer true true 1) (pairBox .coreSide .outer)=true := by decide
theorem short_3_coreSide_coreSide_11_0 :
    certify 96 (wrongProblem .short 3 .coreSide .coreSide true true 0) (pairBox .coreSide .coreSide)=true := by decide
theorem short_3_coreSide_coreCorner_11_0 :
    certify 96 (wrongProblem .short 3 .coreSide .coreCorner true true 0) (pairBox .coreSide .coreCorner)=true := by decide
theorem short_3_coreCorner_outer_11_0 :
    certify 96 (wrongProblem .short 3 .coreCorner .outer true true 0) (pairBox .coreCorner .outer)=true := by decide
theorem short_3_coreCorner_outer_11_1 :
    certify 96 (wrongProblem .short 3 .coreCorner .outer true true 1) (pairBox .coreCorner .outer)=true := by decide
theorem short_3_coreCorner_coreSide_11_0 :
    certify 96 (wrongProblem .short 3 .coreCorner .coreSide true true 0) (pairBox .coreCorner .coreSide)=true := by decide
theorem short_3_coreCorner_coreCorner_11_0 :
    certify 96 (wrongProblem .short 3 .coreCorner .coreCorner true true 0) (pairBox .coreCorner .coreCorner)=true := by decide
theorem short_4_outer_outer_00_0 :
    certify 96 (wrongProblem .short 4 .outer .outer false false 0) (pairBox .outer .outer)=true := by decide
theorem short_4_outer_outer_00_1 :
    certify 96 (wrongProblem .short 4 .outer .outer false false 1) (pairBox .outer .outer)=true := by decide
theorem short_4_outer_outer_00_2 :
    certify 96 (wrongProblem .short 4 .outer .outer false false 2) (pairBox .outer .outer)=true := by decide
theorem short_4_outer_outer_00_3 :
    certify 96 (wrongProblem .short 4 .outer .outer false false 3) (pairBox .outer .outer)=true := by decide
theorem short_4_outer_coreSide_00_1 :
    certify 96 (wrongProblem .short 4 .outer .coreSide false false 1) (pairBox .outer .coreSide)=true := by decide
theorem short_4_outer_coreSide_00_2 :
    certify 96 (wrongProblem .short 4 .outer .coreSide false false 2) (pairBox .outer .coreSide)=true := by decide
theorem short_4_outer_coreSide_00_3 :
    certify 96 (wrongProblem .short 4 .outer .coreSide false false 3) (pairBox .outer .coreSide)=true := by decide
theorem short_4_outer_coreCorner_00_1 :
    certify 96 (wrongProblem .short 4 .outer .coreCorner false false 1) (pairBox .outer .coreCorner)=true := by decide
theorem short_4_outer_coreCorner_00_2 :
    certify 96 (wrongProblem .short 4 .outer .coreCorner false false 2) (pairBox .outer .coreCorner)=true := by decide
theorem short_4_outer_coreCorner_00_3 :
    certify 96 (wrongProblem .short 4 .outer .coreCorner false false 3) (pairBox .outer .coreCorner)=true := by decide
theorem short_4_coreSide_outer_00_0 :
    certify 96 (wrongProblem .short 4 .coreSide .outer false false 0) (pairBox .coreSide .outer)=true := by decide
theorem short_4_coreSide_outer_00_1 :
    certify 96 (wrongProblem .short 4 .coreSide .outer false false 1) (pairBox .coreSide .outer)=true := by decide
theorem short_4_coreSide_outer_00_2 :
    certify 96 (wrongProblem .short 4 .coreSide .outer false false 2) (pairBox .coreSide .outer)=true := by decide
theorem short_4_coreSide_outer_00_3 :
    certify 96 (wrongProblem .short 4 .coreSide .outer false false 3) (pairBox .coreSide .outer)=true := by decide
theorem short_4_coreSide_coreSide_00_1 :
    certify 96 (wrongProblem .short 4 .coreSide .coreSide false false 1) (pairBox .coreSide .coreSide)=true := by decide
theorem short_4_coreSide_coreSide_00_2 :
    certify 96 (wrongProblem .short 4 .coreSide .coreSide false false 2) (pairBox .coreSide .coreSide)=true := by decide
theorem short_4_coreSide_coreSide_00_3 :
    certify 96 (wrongProblem .short 4 .coreSide .coreSide false false 3) (pairBox .coreSide .coreSide)=true := by decide
theorem short_4_coreSide_coreCorner_00_1 :
    certify 96 (wrongProblem .short 4 .coreSide .coreCorner false false 1) (pairBox .coreSide .coreCorner)=true := by decide
theorem short_4_coreSide_coreCorner_00_2 :
    certify 96 (wrongProblem .short 4 .coreSide .coreCorner false false 2) (pairBox .coreSide .coreCorner)=true := by decide
theorem short_4_coreSide_coreCorner_00_3 :
    certify 96 (wrongProblem .short 4 .coreSide .coreCorner false false 3) (pairBox .coreSide .coreCorner)=true := by decide
theorem short_4_coreCorner_outer_00_0 :
    certify 96 (wrongProblem .short 4 .coreCorner .outer false false 0) (pairBox .coreCorner .outer)=true := by decide
theorem short_4_coreCorner_outer_00_1 :
    certify 96 (wrongProblem .short 4 .coreCorner .outer false false 1) (pairBox .coreCorner .outer)=true := by decide
theorem short_4_coreCorner_outer_00_2 :
    certify 96 (wrongProblem .short 4 .coreCorner .outer false false 2) (pairBox .coreCorner .outer)=true := by decide
theorem short_4_coreCorner_outer_00_3 :
    certify 96 (wrongProblem .short 4 .coreCorner .outer false false 3) (pairBox .coreCorner .outer)=true := by decide
theorem short_4_coreCorner_coreSide_00_1 :
    certify 96 (wrongProblem .short 4 .coreCorner .coreSide false false 1) (pairBox .coreCorner .coreSide)=true := by decide
theorem short_4_coreCorner_coreSide_00_2 :
    certify 96 (wrongProblem .short 4 .coreCorner .coreSide false false 2) (pairBox .coreCorner .coreSide)=true := by decide
theorem short_4_coreCorner_coreSide_00_3 :
    certify 96 (wrongProblem .short 4 .coreCorner .coreSide false false 3) (pairBox .coreCorner .coreSide)=true := by decide
theorem short_4_coreCorner_coreCorner_00_1 :
    certify 96 (wrongProblem .short 4 .coreCorner .coreCorner false false 1) (pairBox .coreCorner .coreCorner)=true := by decide
theorem short_4_coreCorner_coreCorner_00_2 :
    certify 96 (wrongProblem .short 4 .coreCorner .coreCorner false false 2) (pairBox .coreCorner .coreCorner)=true := by decide
theorem short_4_coreCorner_coreCorner_00_3 :
    certify 96 (wrongProblem .short 4 .coreCorner .coreCorner false false 3) (pairBox .coreCorner .coreCorner)=true := by decide
theorem short_4_outer_outer_01_0 :
    certify 96 (wrongProblem .short 4 .outer .outer false true 0) (pairBox .outer .outer)=true := by decide
theorem short_4_outer_outer_01_1 :
    certify 96 (wrongProblem .short 4 .outer .outer false true 1) (pairBox .outer .outer)=true := by decide
theorem short_4_outer_outer_01_2 :
    certify 96 (wrongProblem .short 4 .outer .outer false true 2) (pairBox .outer .outer)=true := by decide
theorem short_4_outer_outer_01_3 :
    certify 96 (wrongProblem .short 4 .outer .outer false true 3) (pairBox .outer .outer)=true := by decide
theorem short_4_outer_coreSide_01_1 :
    certify 96 (wrongProblem .short 4 .outer .coreSide false true 1) (pairBox .outer .coreSide)=true := by decide
theorem short_4_outer_coreSide_01_2 :
    certify 96 (wrongProblem .short 4 .outer .coreSide false true 2) (pairBox .outer .coreSide)=true := by decide
theorem short_4_outer_coreSide_01_3 :
    certify 96 (wrongProblem .short 4 .outer .coreSide false true 3) (pairBox .outer .coreSide)=true := by decide
theorem short_4_outer_coreCorner_01_1 :
    certify 96 (wrongProblem .short 4 .outer .coreCorner false true 1) (pairBox .outer .coreCorner)=true := by decide
theorem short_4_outer_coreCorner_01_2 :
    certify 96 (wrongProblem .short 4 .outer .coreCorner false true 2) (pairBox .outer .coreCorner)=true := by decide
theorem short_4_outer_coreCorner_01_3 :
    certify 96 (wrongProblem .short 4 .outer .coreCorner false true 3) (pairBox .outer .coreCorner)=true := by decide
theorem short_4_coreSide_outer_01_0 :
    certify 96 (wrongProblem .short 4 .coreSide .outer false true 0) (pairBox .coreSide .outer)=true := by decide
theorem short_4_coreSide_outer_01_1 :
    certify 96 (wrongProblem .short 4 .coreSide .outer false true 1) (pairBox .coreSide .outer)=true := by decide
theorem short_4_coreSide_outer_01_3 :
    certify 96 (wrongProblem .short 4 .coreSide .outer false true 3) (pairBox .coreSide .outer)=true := by decide
theorem short_4_coreSide_coreSide_01_1 :
    certify 96 (wrongProblem .short 4 .coreSide .coreSide false true 1) (pairBox .coreSide .coreSide)=true := by decide
theorem short_4_coreSide_coreSide_01_3 :
    certify 96 (wrongProblem .short 4 .coreSide .coreSide false true 3) (pairBox .coreSide .coreSide)=true := by decide
theorem short_4_coreSide_coreCorner_01_1 :
    certify 96 (wrongProblem .short 4 .coreSide .coreCorner false true 1) (pairBox .coreSide .coreCorner)=true := by decide
theorem short_4_coreSide_coreCorner_01_3 :
    certify 96 (wrongProblem .short 4 .coreSide .coreCorner false true 3) (pairBox .coreSide .coreCorner)=true := by decide
theorem short_4_coreCorner_outer_01_0 :
    certify 96 (wrongProblem .short 4 .coreCorner .outer false true 0) (pairBox .coreCorner .outer)=true := by decide
theorem short_4_coreCorner_outer_01_1 :
    certify 96 (wrongProblem .short 4 .coreCorner .outer false true 1) (pairBox .coreCorner .outer)=true := by decide
theorem short_4_coreCorner_outer_01_3 :
    certify 96 (wrongProblem .short 4 .coreCorner .outer false true 3) (pairBox .coreCorner .outer)=true := by decide
theorem short_4_coreCorner_coreSide_01_1 :
    certify 96 (wrongProblem .short 4 .coreCorner .coreSide false true 1) (pairBox .coreCorner .coreSide)=true := by decide
theorem short_4_coreCorner_coreSide_01_3 :
    certify 96 (wrongProblem .short 4 .coreCorner .coreSide false true 3) (pairBox .coreCorner .coreSide)=true := by decide
theorem short_4_coreCorner_coreCorner_01_1 :
    certify 96 (wrongProblem .short 4 .coreCorner .coreCorner false true 1) (pairBox .coreCorner .coreCorner)=true := by decide
theorem short_4_coreCorner_coreCorner_01_3 :
    certify 96 (wrongProblem .short 4 .coreCorner .coreCorner false true 3) (pairBox .coreCorner .coreCorner)=true := by decide
theorem short_4_outer_outer_10_0 :
    certify 96 (wrongProblem .short 4 .outer .outer true false 0) (pairBox .outer .outer)=true := by decide
theorem short_4_outer_outer_10_1 :
    certify 96 (wrongProblem .short 4 .outer .outer true false 1) (pairBox .outer .outer)=true := by decide
theorem short_4_outer_outer_10_2 :
    certify 96 (wrongProblem .short 4 .outer .outer true false 2) (pairBox .outer .outer)=true := by decide
theorem short_4_outer_outer_10_3 :
    certify 96 (wrongProblem .short 4 .outer .outer true false 3) (pairBox .outer .outer)=true := by decide
theorem short_4_outer_coreSide_10_0 :
    certify 96 (wrongProblem .short 4 .outer .coreSide true false 0) (pairBox .outer .coreSide)=true := by decide
theorem short_4_outer_coreSide_10_1 :
    certify 96 (wrongProblem .short 4 .outer .coreSide true false 1) (pairBox .outer .coreSide)=true := by decide
theorem short_4_outer_coreSide_10_2 :
    certify 96 (wrongProblem .short 4 .outer .coreSide true false 2) (pairBox .outer .coreSide)=true := by decide
theorem short_4_outer_coreSide_10_3 :
    certify 96 (wrongProblem .short 4 .outer .coreSide true false 3) (pairBox .outer .coreSide)=true := by decide
theorem short_4_outer_coreCorner_10_0 :
    certify 96 (wrongProblem .short 4 .outer .coreCorner true false 0) (pairBox .outer .coreCorner)=true := by decide
theorem short_4_outer_coreCorner_10_1 :
    certify 96 (wrongProblem .short 4 .outer .coreCorner true false 1) (pairBox .outer .coreCorner)=true := by decide
theorem short_4_outer_coreCorner_10_2 :
    certify 96 (wrongProblem .short 4 .outer .coreCorner true false 2) (pairBox .outer .coreCorner)=true := by decide
theorem short_4_outer_coreCorner_10_3 :
    certify 96 (wrongProblem .short 4 .outer .coreCorner true false 3) (pairBox .outer .coreCorner)=true := by decide
theorem short_4_coreSide_outer_10_0 :
    certify 96 (wrongProblem .short 4 .coreSide .outer true false 0) (pairBox .coreSide .outer)=true := by decide
theorem short_4_coreSide_outer_10_1 :
    certify 96 (wrongProblem .short 4 .coreSide .outer true false 1) (pairBox .coreSide .outer)=true := by decide
theorem short_4_coreSide_outer_10_2 :
    certify 96 (wrongProblem .short 4 .coreSide .outer true false 2) (pairBox .coreSide .outer)=true := by decide
theorem short_4_coreSide_outer_10_3 :
    certify 96 (wrongProblem .short 4 .coreSide .outer true false 3) (pairBox .coreSide .outer)=true := by decide
theorem short_4_coreCorner_outer_10_0 :
    certify 96 (wrongProblem .short 4 .coreCorner .outer true false 0) (pairBox .coreCorner .outer)=true := by decide
theorem short_4_coreCorner_outer_10_1 :
    certify 96 (wrongProblem .short 4 .coreCorner .outer true false 1) (pairBox .coreCorner .outer)=true := by decide
theorem short_4_coreCorner_outer_10_2 :
    certify 96 (wrongProblem .short 4 .coreCorner .outer true false 2) (pairBox .coreCorner .outer)=true := by decide
theorem short_4_coreCorner_outer_10_3 :
    certify 96 (wrongProblem .short 4 .coreCorner .outer true false 3) (pairBox .coreCorner .outer)=true := by decide
theorem short_4_outer_outer_11_0 :
    certify 96 (wrongProblem .short 4 .outer .outer true true 0) (pairBox .outer .outer)=true := by decide
theorem short_4_outer_outer_11_1 :
    certify 96 (wrongProblem .short 4 .outer .outer true true 1) (pairBox .outer .outer)=true := by decide
theorem short_4_outer_outer_11_2 :
    certify 96 (wrongProblem .short 4 .outer .outer true true 2) (pairBox .outer .outer)=true := by decide
theorem short_4_outer_outer_11_3 :
    certify 96 (wrongProblem .short 4 .outer .outer true true 3) (pairBox .outer .outer)=true := by decide
theorem short_4_outer_coreSide_11_0 :
    certify 96 (wrongProblem .short 4 .outer .coreSide true true 0) (pairBox .outer .coreSide)=true := by decide
theorem short_4_outer_coreSide_11_1 :
    certify 96 (wrongProblem .short 4 .outer .coreSide true true 1) (pairBox .outer .coreSide)=true := by decide
theorem short_4_outer_coreSide_11_2 :
    certify 96 (wrongProblem .short 4 .outer .coreSide true true 2) (pairBox .outer .coreSide)=true := by decide
theorem short_4_outer_coreSide_11_3 :
    certify 96 (wrongProblem .short 4 .outer .coreSide true true 3) (pairBox .outer .coreSide)=true := by decide
theorem short_4_outer_coreCorner_11_0 :
    certify 96 (wrongProblem .short 4 .outer .coreCorner true true 0) (pairBox .outer .coreCorner)=true := by decide
theorem short_4_outer_coreCorner_11_1 :
    certify 96 (wrongProblem .short 4 .outer .coreCorner true true 1) (pairBox .outer .coreCorner)=true := by decide
theorem short_4_outer_coreCorner_11_2 :
    certify 96 (wrongProblem .short 4 .outer .coreCorner true true 2) (pairBox .outer .coreCorner)=true := by decide
theorem short_4_outer_coreCorner_11_3 :
    certify 96 (wrongProblem .short 4 .outer .coreCorner true true 3) (pairBox .outer .coreCorner)=true := by decide
theorem short_4_coreSide_outer_11_0 :
    certify 96 (wrongProblem .short 4 .coreSide .outer true true 0) (pairBox .coreSide .outer)=true := by decide
theorem short_4_coreSide_outer_11_1 :
    certify 96 (wrongProblem .short 4 .coreSide .outer true true 1) (pairBox .coreSide .outer)=true := by decide
theorem short_4_coreSide_outer_11_3 :
    certify 96 (wrongProblem .short 4 .coreSide .outer true true 3) (pairBox .coreSide .outer)=true := by decide
theorem short_4_coreSide_coreSide_11_0 :
    certify 96 (wrongProblem .short 4 .coreSide .coreSide true true 0) (pairBox .coreSide .coreSide)=true := by decide
theorem short_4_coreSide_coreSide_11_1 :
    certify 96 (wrongProblem .short 4 .coreSide .coreSide true true 1) (pairBox .coreSide .coreSide)=true := by decide
theorem short_4_coreSide_coreSide_11_3 :
    certify 96 (wrongProblem .short 4 .coreSide .coreSide true true 3) (pairBox .coreSide .coreSide)=true := by decide
theorem short_4_coreSide_coreCorner_11_0 :
    certify 96 (wrongProblem .short 4 .coreSide .coreCorner true true 0) (pairBox .coreSide .coreCorner)=true := by decide
theorem short_4_coreSide_coreCorner_11_1 :
    certify 96 (wrongProblem .short 4 .coreSide .coreCorner true true 1) (pairBox .coreSide .coreCorner)=true := by decide
theorem short_4_coreSide_coreCorner_11_3 :
    certify 96 (wrongProblem .short 4 .coreSide .coreCorner true true 3) (pairBox .coreSide .coreCorner)=true := by decide
theorem short_4_coreCorner_outer_11_0 :
    certify 96 (wrongProblem .short 4 .coreCorner .outer true true 0) (pairBox .coreCorner .outer)=true := by decide
theorem short_4_coreCorner_outer_11_1 :
    certify 96 (wrongProblem .short 4 .coreCorner .outer true true 1) (pairBox .coreCorner .outer)=true := by decide
theorem short_4_coreCorner_outer_11_3 :
    certify 96 (wrongProblem .short 4 .coreCorner .outer true true 3) (pairBox .coreCorner .outer)=true := by decide
theorem short_4_coreCorner_coreSide_11_0 :
    certify 96 (wrongProblem .short 4 .coreCorner .coreSide true true 0) (pairBox .coreCorner .coreSide)=true := by decide
theorem short_4_coreCorner_coreSide_11_1 :
    certify 96 (wrongProblem .short 4 .coreCorner .coreSide true true 1) (pairBox .coreCorner .coreSide)=true := by decide
theorem short_4_coreCorner_coreSide_11_3 :
    certify 96 (wrongProblem .short 4 .coreCorner .coreSide true true 3) (pairBox .coreCorner .coreSide)=true := by decide
theorem short_4_coreCorner_coreCorner_11_0 :
    certify 96 (wrongProblem .short 4 .coreCorner .coreCorner true true 0) (pairBox .coreCorner .coreCorner)=true := by decide
theorem short_4_coreCorner_coreCorner_11_1 :
    certify 96 (wrongProblem .short 4 .coreCorner .coreCorner true true 1) (pairBox .coreCorner .coreCorner)=true := by decide
theorem short_4_coreCorner_coreCorner_11_3 :
    certify 96 (wrongProblem .short 4 .coreCorner .coreCorner true true 3) (pairBox .coreCorner .coreCorner)=true := by decide
theorem short_5_outer_outer_00_0 :
    certify 96 (wrongProblem .short 5 .outer .outer false false 0) (pairBox .outer .outer)=true := by decide
theorem short_5_outer_outer_00_1 :
    certify 96 (wrongProblem .short 5 .outer .outer false false 1) (pairBox .outer .outer)=true := by decide
theorem short_5_outer_outer_00_2 :
    certify 96 (wrongProblem .short 5 .outer .outer false false 2) (pairBox .outer .outer)=true := by decide
theorem short_5_outer_outer_00_3 :
    certify 96 (wrongProblem .short 5 .outer .outer false false 3) (pairBox .outer .outer)=true := by decide
theorem short_5_outer_coreSide_00_1 :
    certify 96 (wrongProblem .short 5 .outer .coreSide false false 1) (pairBox .outer .coreSide)=true := by decide
theorem short_5_outer_coreSide_00_2 :
    certify 96 (wrongProblem .short 5 .outer .coreSide false false 2) (pairBox .outer .coreSide)=true := by decide
theorem short_5_outer_coreSide_00_3 :
    certify 96 (wrongProblem .short 5 .outer .coreSide false false 3) (pairBox .outer .coreSide)=true := by decide
theorem short_5_outer_coreCorner_00_1 :
    certify 96 (wrongProblem .short 5 .outer .coreCorner false false 1) (pairBox .outer .coreCorner)=true := by decide
theorem short_5_outer_coreCorner_00_2 :
    certify 96 (wrongProblem .short 5 .outer .coreCorner false false 2) (pairBox .outer .coreCorner)=true := by decide
theorem short_5_outer_coreCorner_00_3 :
    certify 96 (wrongProblem .short 5 .outer .coreCorner false false 3) (pairBox .outer .coreCorner)=true := by decide
theorem short_5_coreSide_outer_00_0 :
    certify 96 (wrongProblem .short 5 .coreSide .outer false false 0) (pairBox .coreSide .outer)=true := by decide
theorem short_5_coreSide_outer_00_1 :
    certify 96 (wrongProblem .short 5 .coreSide .outer false false 1) (pairBox .coreSide .outer)=true := by decide
theorem short_5_coreSide_outer_00_2 :
    certify 96 (wrongProblem .short 5 .coreSide .outer false false 2) (pairBox .coreSide .outer)=true := by decide
theorem short_5_coreSide_outer_00_3 :
    certify 96 (wrongProblem .short 5 .coreSide .outer false false 3) (pairBox .coreSide .outer)=true := by decide
theorem short_5_coreSide_coreSide_00_1 :
    certify 96 (wrongProblem .short 5 .coreSide .coreSide false false 1) (pairBox .coreSide .coreSide)=true := by decide
theorem short_5_coreSide_coreSide_00_2 :
    certify 96 (wrongProblem .short 5 .coreSide .coreSide false false 2) (pairBox .coreSide .coreSide)=true := by decide
theorem short_5_coreSide_coreSide_00_3 :
    certify 96 (wrongProblem .short 5 .coreSide .coreSide false false 3) (pairBox .coreSide .coreSide)=true := by decide
theorem short_5_coreSide_coreCorner_00_1 :
    certify 96 (wrongProblem .short 5 .coreSide .coreCorner false false 1) (pairBox .coreSide .coreCorner)=true := by decide
theorem short_5_coreSide_coreCorner_00_2 :
    certify 96 (wrongProblem .short 5 .coreSide .coreCorner false false 2) (pairBox .coreSide .coreCorner)=true := by decide
theorem short_5_coreSide_coreCorner_00_3 :
    certify 96 (wrongProblem .short 5 .coreSide .coreCorner false false 3) (pairBox .coreSide .coreCorner)=true := by decide
theorem short_5_coreCorner_outer_00_0 :
    certify 96 (wrongProblem .short 5 .coreCorner .outer false false 0) (pairBox .coreCorner .outer)=true := by decide
theorem short_5_coreCorner_outer_00_1 :
    certify 96 (wrongProblem .short 5 .coreCorner .outer false false 1) (pairBox .coreCorner .outer)=true := by decide
theorem short_5_coreCorner_outer_00_2 :
    certify 96 (wrongProblem .short 5 .coreCorner .outer false false 2) (pairBox .coreCorner .outer)=true := by decide
theorem short_5_coreCorner_outer_00_3 :
    certify 96 (wrongProblem .short 5 .coreCorner .outer false false 3) (pairBox .coreCorner .outer)=true := by decide
theorem short_5_coreCorner_coreSide_00_1 :
    certify 96 (wrongProblem .short 5 .coreCorner .coreSide false false 1) (pairBox .coreCorner .coreSide)=true := by decide
theorem short_5_coreCorner_coreSide_00_2 :
    certify 96 (wrongProblem .short 5 .coreCorner .coreSide false false 2) (pairBox .coreCorner .coreSide)=true := by decide
theorem short_5_coreCorner_coreSide_00_3 :
    certify 96 (wrongProblem .short 5 .coreCorner .coreSide false false 3) (pairBox .coreCorner .coreSide)=true := by decide
theorem short_5_coreCorner_coreCorner_00_1 :
    certify 96 (wrongProblem .short 5 .coreCorner .coreCorner false false 1) (pairBox .coreCorner .coreCorner)=true := by decide
theorem short_5_coreCorner_coreCorner_00_2 :
    certify 96 (wrongProblem .short 5 .coreCorner .coreCorner false false 2) (pairBox .coreCorner .coreCorner)=true := by decide
theorem short_5_coreCorner_coreCorner_00_3 :
    certify 96 (wrongProblem .short 5 .coreCorner .coreCorner false false 3) (pairBox .coreCorner .coreCorner)=true := by decide
theorem short_5_outer_outer_01_0 :
    certify 96 (wrongProblem .short 5 .outer .outer false true 0) (pairBox .outer .outer)=true := by decide
theorem short_5_outer_outer_01_1 :
    certify 96 (wrongProblem .short 5 .outer .outer false true 1) (pairBox .outer .outer)=true := by decide
theorem short_5_outer_outer_01_2 :
    certify 96 (wrongProblem .short 5 .outer .outer false true 2) (pairBox .outer .outer)=true := by decide
theorem short_5_outer_outer_01_3 :
    certify 96 (wrongProblem .short 5 .outer .outer false true 3) (pairBox .outer .outer)=true := by decide
theorem short_5_outer_coreSide_01_1 :
    certify 96 (wrongProblem .short 5 .outer .coreSide false true 1) (pairBox .outer .coreSide)=true := by decide
theorem short_5_outer_coreSide_01_2 :
    certify 96 (wrongProblem .short 5 .outer .coreSide false true 2) (pairBox .outer .coreSide)=true := by decide
theorem short_5_outer_coreSide_01_3 :
    certify 96 (wrongProblem .short 5 .outer .coreSide false true 3) (pairBox .outer .coreSide)=true := by decide
theorem short_5_outer_coreCorner_01_1 :
    certify 96 (wrongProblem .short 5 .outer .coreCorner false true 1) (pairBox .outer .coreCorner)=true := by decide
theorem short_5_outer_coreCorner_01_2 :
    certify 96 (wrongProblem .short 5 .outer .coreCorner false true 2) (pairBox .outer .coreCorner)=true := by decide
theorem short_5_outer_coreCorner_01_3 :
    certify 96 (wrongProblem .short 5 .outer .coreCorner false true 3) (pairBox .outer .coreCorner)=true := by decide
theorem short_5_coreSide_outer_01_0 :
    certify 96 (wrongProblem .short 5 .coreSide .outer false true 0) (pairBox .coreSide .outer)=true := by decide
theorem short_5_coreSide_outer_01_1 :
    certify 96 (wrongProblem .short 5 .coreSide .outer false true 1) (pairBox .coreSide .outer)=true := by decide
theorem short_5_coreSide_outer_01_3 :
    certify 96 (wrongProblem .short 5 .coreSide .outer false true 3) (pairBox .coreSide .outer)=true := by decide
theorem short_5_coreSide_coreSide_01_1 :
    certify 96 (wrongProblem .short 5 .coreSide .coreSide false true 1) (pairBox .coreSide .coreSide)=true := by decide
theorem short_5_coreSide_coreSide_01_3 :
    certify 96 (wrongProblem .short 5 .coreSide .coreSide false true 3) (pairBox .coreSide .coreSide)=true := by decide
theorem short_5_coreSide_coreCorner_01_1 :
    certify 96 (wrongProblem .short 5 .coreSide .coreCorner false true 1) (pairBox .coreSide .coreCorner)=true := by decide
theorem short_5_coreSide_coreCorner_01_3 :
    certify 96 (wrongProblem .short 5 .coreSide .coreCorner false true 3) (pairBox .coreSide .coreCorner)=true := by decide
theorem short_5_coreCorner_outer_01_0 :
    certify 96 (wrongProblem .short 5 .coreCorner .outer false true 0) (pairBox .coreCorner .outer)=true := by decide
theorem short_5_coreCorner_outer_01_1 :
    certify 96 (wrongProblem .short 5 .coreCorner .outer false true 1) (pairBox .coreCorner .outer)=true := by decide
theorem short_5_coreCorner_outer_01_3 :
    certify 96 (wrongProblem .short 5 .coreCorner .outer false true 3) (pairBox .coreCorner .outer)=true := by decide
theorem short_5_coreCorner_coreSide_01_1 :
    certify 96 (wrongProblem .short 5 .coreCorner .coreSide false true 1) (pairBox .coreCorner .coreSide)=true := by decide
theorem short_5_coreCorner_coreSide_01_3 :
    certify 96 (wrongProblem .short 5 .coreCorner .coreSide false true 3) (pairBox .coreCorner .coreSide)=true := by decide
theorem short_5_coreCorner_coreCorner_01_1 :
    certify 96 (wrongProblem .short 5 .coreCorner .coreCorner false true 1) (pairBox .coreCorner .coreCorner)=true := by decide
theorem short_5_coreCorner_coreCorner_01_3 :
    certify 96 (wrongProblem .short 5 .coreCorner .coreCorner false true 3) (pairBox .coreCorner .coreCorner)=true := by decide
theorem short_5_outer_outer_10_0 :
    certify 96 (wrongProblem .short 5 .outer .outer true false 0) (pairBox .outer .outer)=true := by decide
theorem short_5_outer_outer_10_1 :
    certify 96 (wrongProblem .short 5 .outer .outer true false 1) (pairBox .outer .outer)=true := by decide
theorem short_5_outer_outer_10_2 :
    certify 96 (wrongProblem .short 5 .outer .outer true false 2) (pairBox .outer .outer)=true := by decide
theorem short_5_outer_outer_10_3 :
    certify 96 (wrongProblem .short 5 .outer .outer true false 3) (pairBox .outer .outer)=true := by decide
theorem short_5_outer_coreSide_10_0 :
    certify 96 (wrongProblem .short 5 .outer .coreSide true false 0) (pairBox .outer .coreSide)=true := by decide
theorem short_5_outer_coreSide_10_1 :
    certify 96 (wrongProblem .short 5 .outer .coreSide true false 1) (pairBox .outer .coreSide)=true := by decide
theorem short_5_outer_coreSide_10_2 :
    certify 96 (wrongProblem .short 5 .outer .coreSide true false 2) (pairBox .outer .coreSide)=true := by decide
theorem short_5_outer_coreSide_10_3 :
    certify 96 (wrongProblem .short 5 .outer .coreSide true false 3) (pairBox .outer .coreSide)=true := by decide
theorem short_5_outer_coreCorner_10_0 :
    certify 96 (wrongProblem .short 5 .outer .coreCorner true false 0) (pairBox .outer .coreCorner)=true := by decide
theorem short_5_outer_coreCorner_10_1 :
    certify 96 (wrongProblem .short 5 .outer .coreCorner true false 1) (pairBox .outer .coreCorner)=true := by decide
theorem short_5_outer_coreCorner_10_2 :
    certify 96 (wrongProblem .short 5 .outer .coreCorner true false 2) (pairBox .outer .coreCorner)=true := by decide
theorem short_5_outer_coreCorner_10_3 :
    certify 96 (wrongProblem .short 5 .outer .coreCorner true false 3) (pairBox .outer .coreCorner)=true := by decide
theorem short_5_coreSide_outer_10_0 :
    certify 96 (wrongProblem .short 5 .coreSide .outer true false 0) (pairBox .coreSide .outer)=true := by decide
theorem short_5_coreSide_outer_10_1 :
    certify 96 (wrongProblem .short 5 .coreSide .outer true false 1) (pairBox .coreSide .outer)=true := by decide
theorem short_5_coreSide_outer_10_2 :
    certify 96 (wrongProblem .short 5 .coreSide .outer true false 2) (pairBox .coreSide .outer)=true := by decide
theorem short_5_coreSide_outer_10_3 :
    certify 96 (wrongProblem .short 5 .coreSide .outer true false 3) (pairBox .coreSide .outer)=true := by decide
theorem short_5_coreCorner_outer_10_0 :
    certify 96 (wrongProblem .short 5 .coreCorner .outer true false 0) (pairBox .coreCorner .outer)=true := by decide
theorem short_5_coreCorner_outer_10_1 :
    certify 96 (wrongProblem .short 5 .coreCorner .outer true false 1) (pairBox .coreCorner .outer)=true := by decide
theorem short_5_coreCorner_outer_10_2 :
    certify 96 (wrongProblem .short 5 .coreCorner .outer true false 2) (pairBox .coreCorner .outer)=true := by decide
theorem short_5_coreCorner_outer_10_3 :
    certify 96 (wrongProblem .short 5 .coreCorner .outer true false 3) (pairBox .coreCorner .outer)=true := by decide
theorem short_5_outer_outer_11_0 :
    certify 96 (wrongProblem .short 5 .outer .outer true true 0) (pairBox .outer .outer)=true := by decide
theorem short_5_outer_outer_11_1 :
    certify 96 (wrongProblem .short 5 .outer .outer true true 1) (pairBox .outer .outer)=true := by decide
theorem short_5_outer_outer_11_2 :
    certify 96 (wrongProblem .short 5 .outer .outer true true 2) (pairBox .outer .outer)=true := by decide
theorem short_5_outer_outer_11_3 :
    certify 96 (wrongProblem .short 5 .outer .outer true true 3) (pairBox .outer .outer)=true := by decide
theorem short_5_outer_coreSide_11_0 :
    certify 96 (wrongProblem .short 5 .outer .coreSide true true 0) (pairBox .outer .coreSide)=true := by decide
theorem short_5_outer_coreSide_11_1 :
    certify 96 (wrongProblem .short 5 .outer .coreSide true true 1) (pairBox .outer .coreSide)=true := by decide
theorem short_5_outer_coreSide_11_2 :
    certify 96 (wrongProblem .short 5 .outer .coreSide true true 2) (pairBox .outer .coreSide)=true := by decide
theorem short_5_outer_coreSide_11_3 :
    certify 96 (wrongProblem .short 5 .outer .coreSide true true 3) (pairBox .outer .coreSide)=true := by decide
theorem short_5_outer_coreCorner_11_0 :
    certify 96 (wrongProblem .short 5 .outer .coreCorner true true 0) (pairBox .outer .coreCorner)=true := by decide
theorem short_5_outer_coreCorner_11_1 :
    certify 96 (wrongProblem .short 5 .outer .coreCorner true true 1) (pairBox .outer .coreCorner)=true := by decide
theorem short_5_outer_coreCorner_11_2 :
    certify 96 (wrongProblem .short 5 .outer .coreCorner true true 2) (pairBox .outer .coreCorner)=true := by decide
theorem short_5_outer_coreCorner_11_3 :
    certify 96 (wrongProblem .short 5 .outer .coreCorner true true 3) (pairBox .outer .coreCorner)=true := by decide
theorem short_5_coreSide_outer_11_0 :
    certify 96 (wrongProblem .short 5 .coreSide .outer true true 0) (pairBox .coreSide .outer)=true := by decide
theorem short_5_coreSide_outer_11_1 :
    certify 96 (wrongProblem .short 5 .coreSide .outer true true 1) (pairBox .coreSide .outer)=true := by decide
theorem short_5_coreSide_outer_11_3 :
    certify 96 (wrongProblem .short 5 .coreSide .outer true true 3) (pairBox .coreSide .outer)=true := by decide
theorem short_5_coreSide_coreSide_11_0 :
    certify 96 (wrongProblem .short 5 .coreSide .coreSide true true 0) (pairBox .coreSide .coreSide)=true := by decide
theorem short_5_coreSide_coreSide_11_1 :
    certify 96 (wrongProblem .short 5 .coreSide .coreSide true true 1) (pairBox .coreSide .coreSide)=true := by decide
theorem short_5_coreSide_coreSide_11_3 :
    certify 96 (wrongProblem .short 5 .coreSide .coreSide true true 3) (pairBox .coreSide .coreSide)=true := by decide
theorem short_5_coreSide_coreCorner_11_0 :
    certify 96 (wrongProblem .short 5 .coreSide .coreCorner true true 0) (pairBox .coreSide .coreCorner)=true := by decide
theorem short_5_coreSide_coreCorner_11_1 :
    certify 96 (wrongProblem .short 5 .coreSide .coreCorner true true 1) (pairBox .coreSide .coreCorner)=true := by decide
theorem short_5_coreSide_coreCorner_11_3 :
    certify 96 (wrongProblem .short 5 .coreSide .coreCorner true true 3) (pairBox .coreSide .coreCorner)=true := by decide
theorem short_5_coreCorner_outer_11_0 :
    certify 96 (wrongProblem .short 5 .coreCorner .outer true true 0) (pairBox .coreCorner .outer)=true := by decide
theorem short_5_coreCorner_outer_11_1 :
    certify 96 (wrongProblem .short 5 .coreCorner .outer true true 1) (pairBox .coreCorner .outer)=true := by decide
theorem short_5_coreCorner_outer_11_3 :
    certify 96 (wrongProblem .short 5 .coreCorner .outer true true 3) (pairBox .coreCorner .outer)=true := by decide
theorem short_5_coreCorner_coreSide_11_0 :
    certify 96 (wrongProblem .short 5 .coreCorner .coreSide true true 0) (pairBox .coreCorner .coreSide)=true := by decide
theorem short_5_coreCorner_coreSide_11_1 :
    certify 96 (wrongProblem .short 5 .coreCorner .coreSide true true 1) (pairBox .coreCorner .coreSide)=true := by decide
theorem short_5_coreCorner_coreSide_11_3 :
    certify 96 (wrongProblem .short 5 .coreCorner .coreSide true true 3) (pairBox .coreCorner .coreSide)=true := by decide
theorem short_5_coreCorner_coreCorner_11_0 :
    certify 96 (wrongProblem .short 5 .coreCorner .coreCorner true true 0) (pairBox .coreCorner .coreCorner)=true := by decide
theorem short_5_coreCorner_coreCorner_11_1 :
    certify 96 (wrongProblem .short 5 .coreCorner .coreCorner true true 1) (pairBox .coreCorner .coreCorner)=true := by decide
theorem short_5_coreCorner_coreCorner_11_3 :
    certify 96 (wrongProblem .short 5 .coreCorner .coreCorner true true 3) (pairBox .coreCorner .coreCorner)=true := by decide
theorem short_6_outer_outer_01_0 :
    certify 96 (wrongProblem .short 6 .outer .outer false true 0) (pairBox .outer .outer)=true := by decide
theorem short_6_outer_outer_01_1 :
    certify 96 (wrongProblem .short 6 .outer .outer false true 1) (pairBox .outer .outer)=true := by decide
theorem short_6_outer_outer_01_2 :
    certify 96 (wrongProblem .short 6 .outer .outer false true 2) (pairBox .outer .outer)=true := by decide
theorem short_6_outer_outer_01_3 :
    certify 96 (wrongProblem .short 6 .outer .outer false true 3) (pairBox .outer .outer)=true := by decide
theorem short_6_outer_coreSide_01_1 :
    certify 96 (wrongProblem .short 6 .outer .coreSide false true 1) (pairBox .outer .coreSide)=true := by decide
theorem short_6_outer_coreSide_01_2 :
    certify 96 (wrongProblem .short 6 .outer .coreSide false true 2) (pairBox .outer .coreSide)=true := by decide
theorem short_6_outer_coreSide_01_3 :
    certify 96 (wrongProblem .short 6 .outer .coreSide false true 3) (pairBox .outer .coreSide)=true := by decide
theorem short_6_outer_coreCorner_01_1 :
    certify 96 (wrongProblem .short 6 .outer .coreCorner false true 1) (pairBox .outer .coreCorner)=true := by decide
theorem short_6_outer_coreCorner_01_2 :
    certify 96 (wrongProblem .short 6 .outer .coreCorner false true 2) (pairBox .outer .coreCorner)=true := by decide
theorem short_6_outer_coreCorner_01_3 :
    certify 96 (wrongProblem .short 6 .outer .coreCorner false true 3) (pairBox .outer .coreCorner)=true := by decide
theorem short_6_coreSide_outer_01_0 :
    certify 96 (wrongProblem .short 6 .coreSide .outer false true 0) (pairBox .coreSide .outer)=true := by decide
theorem short_6_coreSide_outer_01_1 :
    certify 96 (wrongProblem .short 6 .coreSide .outer false true 1) (pairBox .coreSide .outer)=true := by decide
theorem short_6_coreSide_outer_01_3 :
    certify 96 (wrongProblem .short 6 .coreSide .outer false true 3) (pairBox .coreSide .outer)=true := by decide
theorem short_6_coreSide_coreSide_01_1 :
    certify 96 (wrongProblem .short 6 .coreSide .coreSide false true 1) (pairBox .coreSide .coreSide)=true := by decide
theorem short_6_coreSide_coreSide_01_3 :
    certify 96 (wrongProblem .short 6 .coreSide .coreSide false true 3) (pairBox .coreSide .coreSide)=true := by decide
theorem short_6_coreSide_coreCorner_01_1 :
    certify 96 (wrongProblem .short 6 .coreSide .coreCorner false true 1) (pairBox .coreSide .coreCorner)=true := by decide
theorem short_6_coreSide_coreCorner_01_3 :
    certify 96 (wrongProblem .short 6 .coreSide .coreCorner false true 3) (pairBox .coreSide .coreCorner)=true := by decide
theorem short_6_coreCorner_outer_01_0 :
    certify 96 (wrongProblem .short 6 .coreCorner .outer false true 0) (pairBox .coreCorner .outer)=true := by decide
theorem short_6_coreCorner_outer_01_1 :
    certify 96 (wrongProblem .short 6 .coreCorner .outer false true 1) (pairBox .coreCorner .outer)=true := by decide
theorem short_6_coreCorner_outer_01_3 :
    certify 96 (wrongProblem .short 6 .coreCorner .outer false true 3) (pairBox .coreCorner .outer)=true := by decide
theorem short_6_coreCorner_coreSide_01_1 :
    certify 96 (wrongProblem .short 6 .coreCorner .coreSide false true 1) (pairBox .coreCorner .coreSide)=true := by decide
theorem short_6_coreCorner_coreSide_01_3 :
    certify 96 (wrongProblem .short 6 .coreCorner .coreSide false true 3) (pairBox .coreCorner .coreSide)=true := by decide
theorem short_6_coreCorner_coreCorner_01_1 :
    certify 96 (wrongProblem .short 6 .coreCorner .coreCorner false true 1) (pairBox .coreCorner .coreCorner)=true := by decide
theorem short_6_coreCorner_coreCorner_01_3 :
    certify 96 (wrongProblem .short 6 .coreCorner .coreCorner false true 3) (pairBox .coreCorner .coreCorner)=true := by decide
theorem short_6_outer_outer_11_0 :
    certify 96 (wrongProblem .short 6 .outer .outer true true 0) (pairBox .outer .outer)=true := by decide
theorem short_6_outer_outer_11_1 :
    certify 96 (wrongProblem .short 6 .outer .outer true true 1) (pairBox .outer .outer)=true := by decide
theorem short_6_outer_outer_11_2 :
    certify 96 (wrongProblem .short 6 .outer .outer true true 2) (pairBox .outer .outer)=true := by decide
theorem short_6_outer_outer_11_3 :
    certify 96 (wrongProblem .short 6 .outer .outer true true 3) (pairBox .outer .outer)=true := by decide
theorem short_6_outer_coreSide_11_0 :
    certify 96 (wrongProblem .short 6 .outer .coreSide true true 0) (pairBox .outer .coreSide)=true := by decide
theorem short_6_outer_coreSide_11_1 :
    certify 96 (wrongProblem .short 6 .outer .coreSide true true 1) (pairBox .outer .coreSide)=true := by decide
theorem short_6_outer_coreSide_11_2 :
    certify 96 (wrongProblem .short 6 .outer .coreSide true true 2) (pairBox .outer .coreSide)=true := by decide
theorem short_6_outer_coreSide_11_3 :
    certify 96 (wrongProblem .short 6 .outer .coreSide true true 3) (pairBox .outer .coreSide)=true := by decide
theorem short_6_outer_coreCorner_11_0 :
    certify 96 (wrongProblem .short 6 .outer .coreCorner true true 0) (pairBox .outer .coreCorner)=true := by decide
theorem short_6_outer_coreCorner_11_1 :
    certify 96 (wrongProblem .short 6 .outer .coreCorner true true 1) (pairBox .outer .coreCorner)=true := by decide
theorem short_6_outer_coreCorner_11_2 :
    certify 96 (wrongProblem .short 6 .outer .coreCorner true true 2) (pairBox .outer .coreCorner)=true := by decide
theorem short_6_outer_coreCorner_11_3 :
    certify 96 (wrongProblem .short 6 .outer .coreCorner true true 3) (pairBox .outer .coreCorner)=true := by decide
theorem short_6_coreSide_outer_11_0 :
    certify 96 (wrongProblem .short 6 .coreSide .outer true true 0) (pairBox .coreSide .outer)=true := by decide
theorem short_6_coreSide_outer_11_1 :
    certify 96 (wrongProblem .short 6 .coreSide .outer true true 1) (pairBox .coreSide .outer)=true := by decide
theorem short_6_coreSide_outer_11_3 :
    certify 96 (wrongProblem .short 6 .coreSide .outer true true 3) (pairBox .coreSide .outer)=true := by decide
theorem short_6_coreSide_coreSide_11_0 :
    certify 96 (wrongProblem .short 6 .coreSide .coreSide true true 0) (pairBox .coreSide .coreSide)=true := by decide
theorem short_6_coreSide_coreSide_11_1 :
    certify 96 (wrongProblem .short 6 .coreSide .coreSide true true 1) (pairBox .coreSide .coreSide)=true := by decide
theorem short_6_coreSide_coreSide_11_3 :
    certify 96 (wrongProblem .short 6 .coreSide .coreSide true true 3) (pairBox .coreSide .coreSide)=true := by decide
theorem short_6_coreSide_coreCorner_11_0 :
    certify 96 (wrongProblem .short 6 .coreSide .coreCorner true true 0) (pairBox .coreSide .coreCorner)=true := by decide
theorem short_6_coreSide_coreCorner_11_1 :
    certify 96 (wrongProblem .short 6 .coreSide .coreCorner true true 1) (pairBox .coreSide .coreCorner)=true := by decide
theorem short_6_coreSide_coreCorner_11_3 :
    certify 96 (wrongProblem .short 6 .coreSide .coreCorner true true 3) (pairBox .coreSide .coreCorner)=true := by decide
theorem short_6_coreCorner_outer_11_0 :
    certify 96 (wrongProblem .short 6 .coreCorner .outer true true 0) (pairBox .coreCorner .outer)=true := by decide
theorem short_6_coreCorner_outer_11_1 :
    certify 96 (wrongProblem .short 6 .coreCorner .outer true true 1) (pairBox .coreCorner .outer)=true := by decide
theorem short_6_coreCorner_outer_11_3 :
    certify 96 (wrongProblem .short 6 .coreCorner .outer true true 3) (pairBox .coreCorner .outer)=true := by decide
theorem short_6_coreCorner_coreSide_11_0 :
    certify 96 (wrongProblem .short 6 .coreCorner .coreSide true true 0) (pairBox .coreCorner .coreSide)=true := by decide
theorem short_6_coreCorner_coreSide_11_1 :
    certify 96 (wrongProblem .short 6 .coreCorner .coreSide true true 1) (pairBox .coreCorner .coreSide)=true := by decide
theorem short_6_coreCorner_coreSide_11_3 :
    certify 96 (wrongProblem .short 6 .coreCorner .coreSide true true 3) (pairBox .coreCorner .coreSide)=true := by decide
theorem short_6_coreCorner_coreCorner_11_0 :
    certify 96 (wrongProblem .short 6 .coreCorner .coreCorner true true 0) (pairBox .coreCorner .coreCorner)=true := by decide
theorem short_6_coreCorner_coreCorner_11_1 :
    certify 96 (wrongProblem .short 6 .coreCorner .coreCorner true true 1) (pairBox .coreCorner .coreCorner)=true := by decide
theorem short_6_coreCorner_coreCorner_11_3 :
    certify 96 (wrongProblem .short 6 .coreCorner .coreCorner true true 3) (pairBox .coreCorner .coreCorner)=true := by decide
theorem second_0_outer_outer_10_0 :
    certify 96 (wrongProblem .second 0 .outer .outer true false 0) (pairBox .outer .outer)=true := by decide
theorem second_0_outer_outer_10_1 :
    certify 96 (wrongProblem .second 0 .outer .outer true false 1) (pairBox .outer .outer)=true := by decide
theorem second_0_outer_outer_10_2 :
    certify 96 (wrongProblem .second 0 .outer .outer true false 2) (pairBox .outer .outer)=true := by decide
theorem second_0_outer_outer_10_3 :
    certify 96 (wrongProblem .second 0 .outer .outer true false 3) (pairBox .outer .outer)=true := by decide
theorem second_0_outer_coreSide_10_0 :
    certify 96 (wrongProblem .second 0 .outer .coreSide true false 0) (pairBox .outer .coreSide)=true := by decide
theorem second_0_outer_coreSide_10_2 :
    certify 96 (wrongProblem .second 0 .outer .coreSide true false 2) (pairBox .outer .coreSide)=true := by decide
theorem second_0_outer_coreSide_10_3 :
    certify 96 (wrongProblem .second 0 .outer .coreSide true false 3) (pairBox .outer .coreSide)=true := by decide
theorem second_0_outer_coreCorner_10_0 :
    certify 96 (wrongProblem .second 0 .outer .coreCorner true false 0) (pairBox .outer .coreCorner)=true := by decide
theorem second_0_outer_coreCorner_10_2 :
    certify 96 (wrongProblem .second 0 .outer .coreCorner true false 2) (pairBox .outer .coreCorner)=true := by decide
theorem second_0_outer_coreCorner_10_3 :
    certify 96 (wrongProblem .second 0 .outer .coreCorner true false 3) (pairBox .outer .coreCorner)=true := by decide
theorem second_0_coreSide_outer_10_0 :
    certify 96 (wrongProblem .second 0 .coreSide .outer true false 0) (pairBox .coreSide .outer)=true := by decide
theorem second_0_coreSide_outer_10_1 :
    certify 96 (wrongProblem .second 0 .coreSide .outer true false 1) (pairBox .coreSide .outer)=true := by decide
theorem second_0_coreSide_outer_10_2 :
    certify 96 (wrongProblem .second 0 .coreSide .outer true false 2) (pairBox .coreSide .outer)=true := by decide
theorem second_0_coreSide_coreSide_10_0 :
    certify 96 (wrongProblem .second 0 .coreSide .coreSide true false 0) (pairBox .coreSide .coreSide)=true := by decide
theorem second_0_coreSide_coreSide_10_2 :
    certify 96 (wrongProblem .second 0 .coreSide .coreSide true false 2) (pairBox .coreSide .coreSide)=true := by decide
theorem second_0_coreSide_coreCorner_10_0 :
    certify 96 (wrongProblem .second 0 .coreSide .coreCorner true false 0) (pairBox .coreSide .coreCorner)=true := by decide
theorem second_0_coreSide_coreCorner_10_2 :
    certify 96 (wrongProblem .second 0 .coreSide .coreCorner true false 2) (pairBox .coreSide .coreCorner)=true := by decide
theorem second_0_coreCorner_outer_10_0 :
    certify 96 (wrongProblem .second 0 .coreCorner .outer true false 0) (pairBox .coreCorner .outer)=true := by decide
theorem second_0_coreCorner_outer_10_1 :
    certify 96 (wrongProblem .second 0 .coreCorner .outer true false 1) (pairBox .coreCorner .outer)=true := by decide
theorem second_0_coreCorner_outer_10_2 :
    certify 96 (wrongProblem .second 0 .coreCorner .outer true false 2) (pairBox .coreCorner .outer)=true := by decide
theorem second_0_coreCorner_coreSide_10_0 :
    certify 96 (wrongProblem .second 0 .coreCorner .coreSide true false 0) (pairBox .coreCorner .coreSide)=true := by decide
theorem second_0_coreCorner_coreSide_10_2 :
    certify 96 (wrongProblem .second 0 .coreCorner .coreSide true false 2) (pairBox .coreCorner .coreSide)=true := by decide
theorem second_0_coreCorner_coreCorner_10_0 :
    certify 96 (wrongProblem .second 0 .coreCorner .coreCorner true false 0) (pairBox .coreCorner .coreCorner)=true := by decide
theorem second_0_coreCorner_coreCorner_10_2 :
    certify 96 (wrongProblem .second 0 .coreCorner .coreCorner true false 2) (pairBox .coreCorner .coreCorner)=true := by decide
theorem second_0_outer_outer_11_0 :
    certify 96 (wrongProblem .second 0 .outer .outer true true 0) (pairBox .outer .outer)=true := by decide
theorem second_0_outer_outer_11_1 :
    certify 96 (wrongProblem .second 0 .outer .outer true true 1) (pairBox .outer .outer)=true := by decide
theorem second_0_outer_outer_11_2 :
    certify 96 (wrongProblem .second 0 .outer .outer true true 2) (pairBox .outer .outer)=true := by decide
theorem second_0_outer_outer_11_3 :
    certify 96 (wrongProblem .second 0 .outer .outer true true 3) (pairBox .outer .outer)=true := by decide
theorem second_0_outer_coreSide_11_0 :
    certify 96 (wrongProblem .second 0 .outer .coreSide true true 0) (pairBox .outer .coreSide)=true := by decide
theorem second_0_outer_coreSide_11_2 :
    certify 96 (wrongProblem .second 0 .outer .coreSide true true 2) (pairBox .outer .coreSide)=true := by decide
theorem second_0_outer_coreSide_11_3 :
    certify 96 (wrongProblem .second 0 .outer .coreSide true true 3) (pairBox .outer .coreSide)=true := by decide
theorem second_0_outer_coreCorner_11_0 :
    certify 96 (wrongProblem .second 0 .outer .coreCorner true true 0) (pairBox .outer .coreCorner)=true := by decide
theorem second_0_outer_coreCorner_11_2 :
    certify 96 (wrongProblem .second 0 .outer .coreCorner true true 2) (pairBox .outer .coreCorner)=true := by decide
theorem second_0_outer_coreCorner_11_3 :
    certify 96 (wrongProblem .second 0 .outer .coreCorner true true 3) (pairBox .outer .coreCorner)=true := by decide
theorem second_0_coreSide_outer_11_0 :
    certify 96 (wrongProblem .second 0 .coreSide .outer true true 0) (pairBox .coreSide .outer)=true := by decide
theorem second_0_coreSide_outer_11_1 :
    certify 96 (wrongProblem .second 0 .coreSide .outer true true 1) (pairBox .coreSide .outer)=true := by decide
theorem second_0_coreSide_coreSide_11_0 :
    certify 96 (wrongProblem .second 0 .coreSide .coreSide true true 0) (pairBox .coreSide .coreSide)=true := by decide
theorem second_0_coreSide_coreCorner_11_0 :
    certify 96 (wrongProblem .second 0 .coreSide .coreCorner true true 0) (pairBox .coreSide .coreCorner)=true := by decide
theorem second_0_coreCorner_outer_11_0 :
    certify 96 (wrongProblem .second 0 .coreCorner .outer true true 0) (pairBox .coreCorner .outer)=true := by decide
theorem second_0_coreCorner_outer_11_1 :
    certify 96 (wrongProblem .second 0 .coreCorner .outer true true 1) (pairBox .coreCorner .outer)=true := by decide
theorem second_0_coreCorner_coreSide_11_0 :
    certify 96 (wrongProblem .second 0 .coreCorner .coreSide true true 0) (pairBox .coreCorner .coreSide)=true := by decide
theorem second_0_coreCorner_coreCorner_11_0 :
    certify 96 (wrongProblem .second 0 .coreCorner .coreCorner true true 0) (pairBox .coreCorner .coreCorner)=true := by decide
theorem second_1_outer_outer_00_0 :
    certify 96 (wrongProblem .second 1 .outer .outer false false 0) (pairBox .outer .outer)=true := by decide
theorem second_1_outer_outer_00_1 :
    certify 96 (wrongProblem .second 1 .outer .outer false false 1) (pairBox .outer .outer)=true := by decide
theorem second_1_outer_outer_00_2 :
    certify 96 (wrongProblem .second 1 .outer .outer false false 2) (pairBox .outer .outer)=true := by decide
theorem second_1_outer_outer_00_3 :
    certify 96 (wrongProblem .second 1 .outer .outer false false 3) (pairBox .outer .outer)=true := by decide
theorem second_1_outer_coreSide_00_2 :
    certify 96 (wrongProblem .second 1 .outer .coreSide false false 2) (pairBox .outer .coreSide)=true := by decide
theorem second_1_outer_coreSide_00_3 :
    certify 96 (wrongProblem .second 1 .outer .coreSide false false 3) (pairBox .outer .coreSide)=true := by decide
theorem second_1_outer_coreCorner_00_2 :
    certify 96 (wrongProblem .second 1 .outer .coreCorner false false 2) (pairBox .outer .coreCorner)=true := by decide
theorem second_1_outer_coreCorner_00_3 :
    certify 96 (wrongProblem .second 1 .outer .coreCorner false false 3) (pairBox .outer .coreCorner)=true := by decide
theorem second_1_coreSide_outer_00_0 :
    certify 96 (wrongProblem .second 1 .coreSide .outer false false 0) (pairBox .coreSide .outer)=true := by decide
theorem second_1_coreSide_outer_00_1 :
    certify 96 (wrongProblem .second 1 .coreSide .outer false false 1) (pairBox .coreSide .outer)=true := by decide
theorem second_1_coreSide_outer_00_2 :
    certify 96 (wrongProblem .second 1 .coreSide .outer false false 2) (pairBox .coreSide .outer)=true := by decide
theorem second_1_coreSide_coreSide_00_2 :
    certify 96 (wrongProblem .second 1 .coreSide .coreSide false false 2) (pairBox .coreSide .coreSide)=true := by decide
theorem second_1_coreSide_coreCorner_00_2 :
    certify 96 (wrongProblem .second 1 .coreSide .coreCorner false false 2) (pairBox .coreSide .coreCorner)=true := by decide
theorem second_1_coreCorner_outer_00_0 :
    certify 96 (wrongProblem .second 1 .coreCorner .outer false false 0) (pairBox .coreCorner .outer)=true := by decide
theorem second_1_coreCorner_outer_00_1 :
    certify 96 (wrongProblem .second 1 .coreCorner .outer false false 1) (pairBox .coreCorner .outer)=true := by decide
theorem second_1_coreCorner_outer_00_2 :
    certify 96 (wrongProblem .second 1 .coreCorner .outer false false 2) (pairBox .coreCorner .outer)=true := by decide
theorem second_1_coreCorner_coreSide_00_2 :
    certify 96 (wrongProblem .second 1 .coreCorner .coreSide false false 2) (pairBox .coreCorner .coreSide)=true := by decide
theorem second_1_coreCorner_coreCorner_00_2 :
    certify 96 (wrongProblem .second 1 .coreCorner .coreCorner false false 2) (pairBox .coreCorner .coreCorner)=true := by decide
theorem second_1_outer_outer_10_0 :
    certify 96 (wrongProblem .second 1 .outer .outer true false 0) (pairBox .outer .outer)=true := by decide
theorem second_1_outer_outer_10_1 :
    certify 96 (wrongProblem .second 1 .outer .outer true false 1) (pairBox .outer .outer)=true := by decide
theorem second_1_outer_outer_10_2 :
    certify 96 (wrongProblem .second 1 .outer .outer true false 2) (pairBox .outer .outer)=true := by decide
theorem second_1_outer_outer_10_3 :
    certify 96 (wrongProblem .second 1 .outer .outer true false 3) (pairBox .outer .outer)=true := by decide
theorem second_1_outer_coreSide_10_0 :
    certify 96 (wrongProblem .second 1 .outer .coreSide true false 0) (pairBox .outer .coreSide)=true := by decide
theorem second_1_outer_coreSide_10_2 :
    certify 96 (wrongProblem .second 1 .outer .coreSide true false 2) (pairBox .outer .coreSide)=true := by decide
theorem second_1_outer_coreSide_10_3 :
    certify 96 (wrongProblem .second 1 .outer .coreSide true false 3) (pairBox .outer .coreSide)=true := by decide
theorem second_1_outer_coreCorner_10_0 :
    certify 96 (wrongProblem .second 1 .outer .coreCorner true false 0) (pairBox .outer .coreCorner)=true := by decide
theorem second_1_outer_coreCorner_10_2 :
    certify 96 (wrongProblem .second 1 .outer .coreCorner true false 2) (pairBox .outer .coreCorner)=true := by decide
theorem second_1_outer_coreCorner_10_3 :
    certify 96 (wrongProblem .second 1 .outer .coreCorner true false 3) (pairBox .outer .coreCorner)=true := by decide
theorem second_1_coreSide_outer_10_0 :
    certify 96 (wrongProblem .second 1 .coreSide .outer true false 0) (pairBox .coreSide .outer)=true := by decide
theorem second_1_coreSide_outer_10_1 :
    certify 96 (wrongProblem .second 1 .coreSide .outer true false 1) (pairBox .coreSide .outer)=true := by decide
theorem second_1_coreSide_outer_10_2 :
    certify 96 (wrongProblem .second 1 .coreSide .outer true false 2) (pairBox .coreSide .outer)=true := by decide
theorem second_1_coreSide_coreSide_10_0 :
    certify 96 (wrongProblem .second 1 .coreSide .coreSide true false 0) (pairBox .coreSide .coreSide)=true := by decide
theorem second_1_coreSide_coreSide_10_2 :
    certify 96 (wrongProblem .second 1 .coreSide .coreSide true false 2) (pairBox .coreSide .coreSide)=true := by decide
theorem second_1_coreSide_coreCorner_10_0 :
    certify 96 (wrongProblem .second 1 .coreSide .coreCorner true false 0) (pairBox .coreSide .coreCorner)=true := by decide
theorem second_1_coreSide_coreCorner_10_2 :
    certify 96 (wrongProblem .second 1 .coreSide .coreCorner true false 2) (pairBox .coreSide .coreCorner)=true := by decide
theorem second_1_coreCorner_outer_10_0 :
    certify 96 (wrongProblem .second 1 .coreCorner .outer true false 0) (pairBox .coreCorner .outer)=true := by decide
theorem second_1_coreCorner_outer_10_1 :
    certify 96 (wrongProblem .second 1 .coreCorner .outer true false 1) (pairBox .coreCorner .outer)=true := by decide
theorem second_1_coreCorner_outer_10_2 :
    certify 96 (wrongProblem .second 1 .coreCorner .outer true false 2) (pairBox .coreCorner .outer)=true := by decide
theorem second_1_coreCorner_coreSide_10_0 :
    certify 96 (wrongProblem .second 1 .coreCorner .coreSide true false 0) (pairBox .coreCorner .coreSide)=true := by decide
theorem second_1_coreCorner_coreSide_10_2 :
    certify 96 (wrongProblem .second 1 .coreCorner .coreSide true false 2) (pairBox .coreCorner .coreSide)=true := by decide
theorem second_1_coreCorner_coreCorner_10_0 :
    certify 96 (wrongProblem .second 1 .coreCorner .coreCorner true false 0) (pairBox .coreCorner .coreCorner)=true := by decide
theorem second_1_coreCorner_coreCorner_10_2 :
    certify 96 (wrongProblem .second 1 .coreCorner .coreCorner true false 2) (pairBox .coreCorner .coreCorner)=true := by decide
theorem second_2_outer_outer_00_0 :
    certify 96 (wrongProblem .second 2 .outer .outer false false 0) (pairBox .outer .outer)=true := by decide
theorem second_2_outer_outer_00_1 :
    certify 96 (wrongProblem .second 2 .outer .outer false false 1) (pairBox .outer .outer)=true := by decide
theorem second_2_outer_outer_00_2 :
    certify 96 (wrongProblem .second 2 .outer .outer false false 2) (pairBox .outer .outer)=true := by decide
theorem second_2_outer_outer_00_3 :
    certify 96 (wrongProblem .second 2 .outer .outer false false 3) (pairBox .outer .outer)=true := by decide
theorem second_2_outer_coreSide_00_1 :
    certify 96 (wrongProblem .second 2 .outer .coreSide false false 1) (pairBox .outer .coreSide)=true := by decide
theorem second_2_outer_coreSide_00_2 :
    certify 96 (wrongProblem .second 2 .outer .coreSide false false 2) (pairBox .outer .coreSide)=true := by decide
theorem second_2_outer_coreSide_00_3 :
    certify 96 (wrongProblem .second 2 .outer .coreSide false false 3) (pairBox .outer .coreSide)=true := by decide
theorem second_2_outer_coreCorner_00_1 :
    certify 96 (wrongProblem .second 2 .outer .coreCorner false false 1) (pairBox .outer .coreCorner)=true := by decide
theorem second_2_outer_coreCorner_00_2 :
    certify 96 (wrongProblem .second 2 .outer .coreCorner false false 2) (pairBox .outer .coreCorner)=true := by decide
theorem second_2_outer_coreCorner_00_3 :
    certify 96 (wrongProblem .second 2 .outer .coreCorner false false 3) (pairBox .outer .coreCorner)=true := by decide
theorem second_2_coreSide_outer_00_0 :
    certify 96 (wrongProblem .second 2 .coreSide .outer false false 0) (pairBox .coreSide .outer)=true := by decide
theorem second_2_coreSide_outer_00_1 :
    certify 96 (wrongProblem .second 2 .coreSide .outer false false 1) (pairBox .coreSide .outer)=true := by decide
theorem second_2_coreSide_outer_00_2 :
    certify 96 (wrongProblem .second 2 .coreSide .outer false false 2) (pairBox .coreSide .outer)=true := by decide
theorem second_2_coreSide_outer_00_3 :
    certify 96 (wrongProblem .second 2 .coreSide .outer false false 3) (pairBox .coreSide .outer)=true := by decide
theorem second_2_coreSide_coreSide_00_1 :
    certify 96 (wrongProblem .second 2 .coreSide .coreSide false false 1) (pairBox .coreSide .coreSide)=true := by decide
theorem second_2_coreSide_coreSide_00_2 :
    certify 96 (wrongProblem .second 2 .coreSide .coreSide false false 2) (pairBox .coreSide .coreSide)=true := by decide
theorem second_2_coreSide_coreSide_00_3 :
    certify 96 (wrongProblem .second 2 .coreSide .coreSide false false 3) (pairBox .coreSide .coreSide)=true := by decide
theorem second_2_coreSide_coreCorner_00_1 :
    certify 96 (wrongProblem .second 2 .coreSide .coreCorner false false 1) (pairBox .coreSide .coreCorner)=true := by decide
theorem second_2_coreSide_coreCorner_00_2 :
    certify 96 (wrongProblem .second 2 .coreSide .coreCorner false false 2) (pairBox .coreSide .coreCorner)=true := by decide
theorem second_2_coreSide_coreCorner_00_3 :
    certify 96 (wrongProblem .second 2 .coreSide .coreCorner false false 3) (pairBox .coreSide .coreCorner)=true := by decide
theorem second_2_coreCorner_outer_00_0 :
    certify 96 (wrongProblem .second 2 .coreCorner .outer false false 0) (pairBox .coreCorner .outer)=true := by decide
theorem second_2_coreCorner_outer_00_1 :
    certify 96 (wrongProblem .second 2 .coreCorner .outer false false 1) (pairBox .coreCorner .outer)=true := by decide
theorem second_2_coreCorner_outer_00_2 :
    certify 96 (wrongProblem .second 2 .coreCorner .outer false false 2) (pairBox .coreCorner .outer)=true := by decide
theorem second_2_coreCorner_outer_00_3 :
    certify 96 (wrongProblem .second 2 .coreCorner .outer false false 3) (pairBox .coreCorner .outer)=true := by decide
theorem second_2_coreCorner_coreSide_00_1 :
    certify 96 (wrongProblem .second 2 .coreCorner .coreSide false false 1) (pairBox .coreCorner .coreSide)=true := by decide
theorem second_2_coreCorner_coreSide_00_2 :
    certify 96 (wrongProblem .second 2 .coreCorner .coreSide false false 2) (pairBox .coreCorner .coreSide)=true := by decide
theorem second_2_coreCorner_coreSide_00_3 :
    certify 96 (wrongProblem .second 2 .coreCorner .coreSide false false 3) (pairBox .coreCorner .coreSide)=true := by decide
theorem second_2_coreCorner_coreCorner_00_1 :
    certify 96 (wrongProblem .second 2 .coreCorner .coreCorner false false 1) (pairBox .coreCorner .coreCorner)=true := by decide
theorem second_2_coreCorner_coreCorner_00_2 :
    certify 96 (wrongProblem .second 2 .coreCorner .coreCorner false false 2) (pairBox .coreCorner .coreCorner)=true := by decide
theorem second_2_coreCorner_coreCorner_00_3 :
    certify 96 (wrongProblem .second 2 .coreCorner .coreCorner false false 3) (pairBox .coreCorner .coreCorner)=true := by decide
theorem second_2_outer_outer_01_0 :
    certify 96 (wrongProblem .second 2 .outer .outer false true 0) (pairBox .outer .outer)=true := by decide
theorem second_2_outer_outer_01_1 :
    certify 96 (wrongProblem .second 2 .outer .outer false true 1) (pairBox .outer .outer)=true := by decide
theorem second_2_outer_outer_01_2 :
    certify 96 (wrongProblem .second 2 .outer .outer false true 2) (pairBox .outer .outer)=true := by decide
theorem second_2_outer_outer_01_3 :
    certify 96 (wrongProblem .second 2 .outer .outer false true 3) (pairBox .outer .outer)=true := by decide
theorem second_2_outer_coreSide_01_1 :
    certify 96 (wrongProblem .second 2 .outer .coreSide false true 1) (pairBox .outer .coreSide)=true := by decide
theorem second_2_outer_coreSide_01_2 :
    certify 96 (wrongProblem .second 2 .outer .coreSide false true 2) (pairBox .outer .coreSide)=true := by decide
theorem second_2_outer_coreSide_01_3 :
    certify 96 (wrongProblem .second 2 .outer .coreSide false true 3) (pairBox .outer .coreSide)=true := by decide
theorem second_2_outer_coreCorner_01_1 :
    certify 96 (wrongProblem .second 2 .outer .coreCorner false true 1) (pairBox .outer .coreCorner)=true := by decide
theorem second_2_outer_coreCorner_01_2 :
    certify 96 (wrongProblem .second 2 .outer .coreCorner false true 2) (pairBox .outer .coreCorner)=true := by decide
theorem second_2_outer_coreCorner_01_3 :
    certify 96 (wrongProblem .second 2 .outer .coreCorner false true 3) (pairBox .outer .coreCorner)=true := by decide
theorem second_2_coreSide_outer_01_0 :
    certify 96 (wrongProblem .second 2 .coreSide .outer false true 0) (pairBox .coreSide .outer)=true := by decide
theorem second_2_coreSide_outer_01_1 :
    certify 96 (wrongProblem .second 2 .coreSide .outer false true 1) (pairBox .coreSide .outer)=true := by decide
theorem second_2_coreSide_outer_01_3 :
    certify 96 (wrongProblem .second 2 .coreSide .outer false true 3) (pairBox .coreSide .outer)=true := by decide
theorem second_2_coreSide_coreSide_01_1 :
    certify 96 (wrongProblem .second 2 .coreSide .coreSide false true 1) (pairBox .coreSide .coreSide)=true := by decide
theorem second_2_coreSide_coreSide_01_3 :
    certify 96 (wrongProblem .second 2 .coreSide .coreSide false true 3) (pairBox .coreSide .coreSide)=true := by decide
theorem second_2_coreSide_coreCorner_01_1 :
    certify 96 (wrongProblem .second 2 .coreSide .coreCorner false true 1) (pairBox .coreSide .coreCorner)=true := by decide
theorem second_2_coreSide_coreCorner_01_3 :
    certify 96 (wrongProblem .second 2 .coreSide .coreCorner false true 3) (pairBox .coreSide .coreCorner)=true := by decide
theorem second_2_coreCorner_outer_01_0 :
    certify 96 (wrongProblem .second 2 .coreCorner .outer false true 0) (pairBox .coreCorner .outer)=true := by decide
theorem second_2_coreCorner_outer_01_1 :
    certify 96 (wrongProblem .second 2 .coreCorner .outer false true 1) (pairBox .coreCorner .outer)=true := by decide
theorem second_2_coreCorner_outer_01_3 :
    certify 96 (wrongProblem .second 2 .coreCorner .outer false true 3) (pairBox .coreCorner .outer)=true := by decide
theorem second_2_coreCorner_coreSide_01_1 :
    certify 96 (wrongProblem .second 2 .coreCorner .coreSide false true 1) (pairBox .coreCorner .coreSide)=true := by decide
theorem second_2_coreCorner_coreSide_01_3 :
    certify 96 (wrongProblem .second 2 .coreCorner .coreSide false true 3) (pairBox .coreCorner .coreSide)=true := by decide
theorem second_2_coreCorner_coreCorner_01_1 :
    certify 96 (wrongProblem .second 2 .coreCorner .coreCorner false true 1) (pairBox .coreCorner .coreCorner)=true := by decide
theorem second_2_coreCorner_coreCorner_01_3 :
    certify 96 (wrongProblem .second 2 .coreCorner .coreCorner false true 3) (pairBox .coreCorner .coreCorner)=true := by decide
theorem second_3_outer_outer_00_0 :
    certify 96 (wrongProblem .second 3 .outer .outer false false 0) (pairBox .outer .outer)=true := by decide
theorem second_3_outer_outer_00_1 :
    certify 96 (wrongProblem .second 3 .outer .outer false false 1) (pairBox .outer .outer)=true := by decide
theorem second_3_outer_outer_00_2 :
    certify 96 (wrongProblem .second 3 .outer .outer false false 2) (pairBox .outer .outer)=true := by decide
theorem second_3_outer_outer_00_3 :
    certify 96 (wrongProblem .second 3 .outer .outer false false 3) (pairBox .outer .outer)=true := by decide
theorem second_3_outer_coreSide_00_1 :
    certify 96 (wrongProblem .second 3 .outer .coreSide false false 1) (pairBox .outer .coreSide)=true := by decide
theorem second_3_outer_coreSide_00_2 :
    certify 96 (wrongProblem .second 3 .outer .coreSide false false 2) (pairBox .outer .coreSide)=true := by decide
theorem second_3_outer_coreSide_00_3 :
    certify 96 (wrongProblem .second 3 .outer .coreSide false false 3) (pairBox .outer .coreSide)=true := by decide
theorem second_3_outer_coreCorner_00_1 :
    certify 96 (wrongProblem .second 3 .outer .coreCorner false false 1) (pairBox .outer .coreCorner)=true := by decide
theorem second_3_outer_coreCorner_00_2 :
    certify 96 (wrongProblem .second 3 .outer .coreCorner false false 2) (pairBox .outer .coreCorner)=true := by decide
theorem second_3_outer_coreCorner_00_3 :
    certify 96 (wrongProblem .second 3 .outer .coreCorner false false 3) (pairBox .outer .coreCorner)=true := by decide
theorem second_3_coreSide_outer_00_0 :
    certify 96 (wrongProblem .second 3 .coreSide .outer false false 0) (pairBox .coreSide .outer)=true := by decide
theorem second_3_coreSide_outer_00_1 :
    certify 96 (wrongProblem .second 3 .coreSide .outer false false 1) (pairBox .coreSide .outer)=true := by decide
theorem second_3_coreSide_outer_00_2 :
    certify 96 (wrongProblem .second 3 .coreSide .outer false false 2) (pairBox .coreSide .outer)=true := by decide
theorem second_3_coreSide_outer_00_3 :
    certify 96 (wrongProblem .second 3 .coreSide .outer false false 3) (pairBox .coreSide .outer)=true := by decide
theorem second_3_coreSide_coreSide_00_1 :
    certify 96 (wrongProblem .second 3 .coreSide .coreSide false false 1) (pairBox .coreSide .coreSide)=true := by decide
theorem second_3_coreSide_coreSide_00_2 :
    certify 96 (wrongProblem .second 3 .coreSide .coreSide false false 2) (pairBox .coreSide .coreSide)=true := by decide
theorem second_3_coreSide_coreSide_00_3 :
    certify 96 (wrongProblem .second 3 .coreSide .coreSide false false 3) (pairBox .coreSide .coreSide)=true := by decide
theorem second_3_coreSide_coreCorner_00_1 :
    certify 96 (wrongProblem .second 3 .coreSide .coreCorner false false 1) (pairBox .coreSide .coreCorner)=true := by decide
theorem second_3_coreSide_coreCorner_00_2 :
    certify 96 (wrongProblem .second 3 .coreSide .coreCorner false false 2) (pairBox .coreSide .coreCorner)=true := by decide
theorem second_3_coreSide_coreCorner_00_3 :
    certify 96 (wrongProblem .second 3 .coreSide .coreCorner false false 3) (pairBox .coreSide .coreCorner)=true := by decide
theorem second_3_coreCorner_outer_00_0 :
    certify 96 (wrongProblem .second 3 .coreCorner .outer false false 0) (pairBox .coreCorner .outer)=true := by decide
theorem second_3_coreCorner_outer_00_1 :
    certify 96 (wrongProblem .second 3 .coreCorner .outer false false 1) (pairBox .coreCorner .outer)=true := by decide
theorem second_3_coreCorner_outer_00_2 :
    certify 96 (wrongProblem .second 3 .coreCorner .outer false false 2) (pairBox .coreCorner .outer)=true := by decide
theorem second_3_coreCorner_outer_00_3 :
    certify 96 (wrongProblem .second 3 .coreCorner .outer false false 3) (pairBox .coreCorner .outer)=true := by decide
theorem second_3_coreCorner_coreSide_00_1 :
    certify 96 (wrongProblem .second 3 .coreCorner .coreSide false false 1) (pairBox .coreCorner .coreSide)=true := by decide
theorem second_3_coreCorner_coreSide_00_2 :
    certify 96 (wrongProblem .second 3 .coreCorner .coreSide false false 2) (pairBox .coreCorner .coreSide)=true := by decide
theorem second_3_coreCorner_coreSide_00_3 :
    certify 96 (wrongProblem .second 3 .coreCorner .coreSide false false 3) (pairBox .coreCorner .coreSide)=true := by decide
theorem second_3_coreCorner_coreCorner_00_1 :
    certify 96 (wrongProblem .second 3 .coreCorner .coreCorner false false 1) (pairBox .coreCorner .coreCorner)=true := by decide
theorem second_3_coreCorner_coreCorner_00_2 :
    certify 96 (wrongProblem .second 3 .coreCorner .coreCorner false false 2) (pairBox .coreCorner .coreCorner)=true := by decide
theorem second_3_coreCorner_coreCorner_00_3 :
    certify 96 (wrongProblem .second 3 .coreCorner .coreCorner false false 3) (pairBox .coreCorner .coreCorner)=true := by decide
theorem second_3_outer_outer_01_0 :
    certify 96 (wrongProblem .second 3 .outer .outer false true 0) (pairBox .outer .outer)=true := by decide
theorem second_3_outer_outer_01_1 :
    certify 96 (wrongProblem .second 3 .outer .outer false true 1) (pairBox .outer .outer)=true := by decide
theorem second_3_outer_outer_01_2 :
    certify 96 (wrongProblem .second 3 .outer .outer false true 2) (pairBox .outer .outer)=true := by decide
theorem second_3_outer_outer_01_3 :
    certify 96 (wrongProblem .second 3 .outer .outer false true 3) (pairBox .outer .outer)=true := by decide
theorem second_3_outer_coreSide_01_1 :
    certify 96 (wrongProblem .second 3 .outer .coreSide false true 1) (pairBox .outer .coreSide)=true := by decide
theorem second_3_outer_coreSide_01_2 :
    certify 96 (wrongProblem .second 3 .outer .coreSide false true 2) (pairBox .outer .coreSide)=true := by decide
theorem second_3_outer_coreSide_01_3 :
    certify 96 (wrongProblem .second 3 .outer .coreSide false true 3) (pairBox .outer .coreSide)=true := by decide
theorem second_3_outer_coreCorner_01_1 :
    certify 96 (wrongProblem .second 3 .outer .coreCorner false true 1) (pairBox .outer .coreCorner)=true := by decide
theorem second_3_outer_coreCorner_01_2 :
    certify 96 (wrongProblem .second 3 .outer .coreCorner false true 2) (pairBox .outer .coreCorner)=true := by decide
theorem second_3_outer_coreCorner_01_3 :
    certify 96 (wrongProblem .second 3 .outer .coreCorner false true 3) (pairBox .outer .coreCorner)=true := by decide
theorem second_3_coreSide_outer_01_0 :
    certify 96 (wrongProblem .second 3 .coreSide .outer false true 0) (pairBox .coreSide .outer)=true := by decide
theorem second_3_coreSide_outer_01_1 :
    certify 96 (wrongProblem .second 3 .coreSide .outer false true 1) (pairBox .coreSide .outer)=true := by decide
theorem second_3_coreSide_outer_01_3 :
    certify 96 (wrongProblem .second 3 .coreSide .outer false true 3) (pairBox .coreSide .outer)=true := by decide
theorem second_3_coreSide_coreSide_01_1 :
    certify 96 (wrongProblem .second 3 .coreSide .coreSide false true 1) (pairBox .coreSide .coreSide)=true := by decide
theorem second_3_coreSide_coreSide_01_3 :
    certify 96 (wrongProblem .second 3 .coreSide .coreSide false true 3) (pairBox .coreSide .coreSide)=true := by decide
theorem second_3_coreSide_coreCorner_01_1 :
    certify 96 (wrongProblem .second 3 .coreSide .coreCorner false true 1) (pairBox .coreSide .coreCorner)=true := by decide
theorem second_3_coreSide_coreCorner_01_3 :
    certify 96 (wrongProblem .second 3 .coreSide .coreCorner false true 3) (pairBox .coreSide .coreCorner)=true := by decide
theorem second_3_coreCorner_outer_01_0 :
    certify 96 (wrongProblem .second 3 .coreCorner .outer false true 0) (pairBox .coreCorner .outer)=true := by decide
theorem second_3_coreCorner_outer_01_1 :
    certify 96 (wrongProblem .second 3 .coreCorner .outer false true 1) (pairBox .coreCorner .outer)=true := by decide
theorem second_3_coreCorner_outer_01_3 :
    certify 96 (wrongProblem .second 3 .coreCorner .outer false true 3) (pairBox .coreCorner .outer)=true := by decide
theorem second_3_coreCorner_coreSide_01_1 :
    certify 96 (wrongProblem .second 3 .coreCorner .coreSide false true 1) (pairBox .coreCorner .coreSide)=true := by decide
theorem second_3_coreCorner_coreSide_01_3 :
    certify 96 (wrongProblem .second 3 .coreCorner .coreSide false true 3) (pairBox .coreCorner .coreSide)=true := by decide
theorem second_3_coreCorner_coreCorner_01_1 :
    certify 96 (wrongProblem .second 3 .coreCorner .coreCorner false true 1) (pairBox .coreCorner .coreCorner)=true := by decide
theorem second_3_coreCorner_coreCorner_01_3 :
    certify 96 (wrongProblem .second 3 .coreCorner .coreCorner false true 3) (pairBox .coreCorner .coreCorner)=true := by decide
theorem second_3_outer_outer_10_0 :
    certify 96 (wrongProblem .second 3 .outer .outer true false 0) (pairBox .outer .outer)=true := by decide
theorem second_3_outer_outer_10_1 :
    certify 96 (wrongProblem .second 3 .outer .outer true false 1) (pairBox .outer .outer)=true := by decide
theorem second_3_outer_outer_10_2 :
    certify 96 (wrongProblem .second 3 .outer .outer true false 2) (pairBox .outer .outer)=true := by decide
theorem second_3_outer_outer_10_3 :
    certify 96 (wrongProblem .second 3 .outer .outer true false 3) (pairBox .outer .outer)=true := by decide
theorem second_3_outer_coreSide_10_0 :
    certify 96 (wrongProblem .second 3 .outer .coreSide true false 0) (pairBox .outer .coreSide)=true := by decide
theorem second_3_outer_coreSide_10_1 :
    certify 96 (wrongProblem .second 3 .outer .coreSide true false 1) (pairBox .outer .coreSide)=true := by decide
theorem second_3_outer_coreSide_10_2 :
    certify 96 (wrongProblem .second 3 .outer .coreSide true false 2) (pairBox .outer .coreSide)=true := by decide
theorem second_3_outer_coreSide_10_3 :
    certify 96 (wrongProblem .second 3 .outer .coreSide true false 3) (pairBox .outer .coreSide)=true := by decide
theorem second_3_outer_coreCorner_10_0 :
    certify 96 (wrongProblem .second 3 .outer .coreCorner true false 0) (pairBox .outer .coreCorner)=true := by decide
theorem second_3_outer_coreCorner_10_1 :
    certify 96 (wrongProblem .second 3 .outer .coreCorner true false 1) (pairBox .outer .coreCorner)=true := by decide
theorem second_3_outer_coreCorner_10_2 :
    certify 96 (wrongProblem .second 3 .outer .coreCorner true false 2) (pairBox .outer .coreCorner)=true := by decide
theorem second_3_outer_coreCorner_10_3 :
    certify 96 (wrongProblem .second 3 .outer .coreCorner true false 3) (pairBox .outer .coreCorner)=true := by decide
theorem second_3_coreSide_outer_10_0 :
    certify 96 (wrongProblem .second 3 .coreSide .outer true false 0) (pairBox .coreSide .outer)=true := by decide
theorem second_3_coreSide_outer_10_1 :
    certify 96 (wrongProblem .second 3 .coreSide .outer true false 1) (pairBox .coreSide .outer)=true := by decide
theorem second_3_coreSide_outer_10_2 :
    certify 96 (wrongProblem .second 3 .coreSide .outer true false 2) (pairBox .coreSide .outer)=true := by decide
theorem second_3_coreSide_outer_10_3 :
    certify 96 (wrongProblem .second 3 .coreSide .outer true false 3) (pairBox .coreSide .outer)=true := by decide
theorem second_3_coreCorner_outer_10_0 :
    certify 96 (wrongProblem .second 3 .coreCorner .outer true false 0) (pairBox .coreCorner .outer)=true := by decide
theorem second_3_coreCorner_outer_10_1 :
    certify 96 (wrongProblem .second 3 .coreCorner .outer true false 1) (pairBox .coreCorner .outer)=true := by decide
theorem second_3_coreCorner_outer_10_2 :
    certify 96 (wrongProblem .second 3 .coreCorner .outer true false 2) (pairBox .coreCorner .outer)=true := by decide
theorem second_3_coreCorner_outer_10_3 :
    certify 96 (wrongProblem .second 3 .coreCorner .outer true false 3) (pairBox .coreCorner .outer)=true := by decide
theorem second_3_outer_outer_11_0 :
    certify 96 (wrongProblem .second 3 .outer .outer true true 0) (pairBox .outer .outer)=true := by decide
theorem second_3_outer_outer_11_1 :
    certify 96 (wrongProblem .second 3 .outer .outer true true 1) (pairBox .outer .outer)=true := by decide
theorem second_3_outer_outer_11_2 :
    certify 96 (wrongProblem .second 3 .outer .outer true true 2) (pairBox .outer .outer)=true := by decide
theorem second_3_outer_outer_11_3 :
    certify 96 (wrongProblem .second 3 .outer .outer true true 3) (pairBox .outer .outer)=true := by decide
theorem second_3_outer_coreSide_11_0 :
    certify 96 (wrongProblem .second 3 .outer .coreSide true true 0) (pairBox .outer .coreSide)=true := by decide
theorem second_3_outer_coreSide_11_1 :
    certify 96 (wrongProblem .second 3 .outer .coreSide true true 1) (pairBox .outer .coreSide)=true := by decide
theorem second_3_outer_coreSide_11_2 :
    certify 96 (wrongProblem .second 3 .outer .coreSide true true 2) (pairBox .outer .coreSide)=true := by decide
theorem second_3_outer_coreSide_11_3 :
    certify 96 (wrongProblem .second 3 .outer .coreSide true true 3) (pairBox .outer .coreSide)=true := by decide
theorem second_3_outer_coreCorner_11_0 :
    certify 96 (wrongProblem .second 3 .outer .coreCorner true true 0) (pairBox .outer .coreCorner)=true := by decide
theorem second_3_outer_coreCorner_11_1 :
    certify 96 (wrongProblem .second 3 .outer .coreCorner true true 1) (pairBox .outer .coreCorner)=true := by decide
theorem second_3_outer_coreCorner_11_2 :
    certify 96 (wrongProblem .second 3 .outer .coreCorner true true 2) (pairBox .outer .coreCorner)=true := by decide
theorem second_3_outer_coreCorner_11_3 :
    certify 96 (wrongProblem .second 3 .outer .coreCorner true true 3) (pairBox .outer .coreCorner)=true := by decide
theorem second_3_coreSide_outer_11_0 :
    certify 96 (wrongProblem .second 3 .coreSide .outer true true 0) (pairBox .coreSide .outer)=true := by decide
theorem second_3_coreSide_outer_11_1 :
    certify 96 (wrongProblem .second 3 .coreSide .outer true true 1) (pairBox .coreSide .outer)=true := by decide
theorem second_3_coreSide_outer_11_3 :
    certify 96 (wrongProblem .second 3 .coreSide .outer true true 3) (pairBox .coreSide .outer)=true := by decide
theorem second_3_coreSide_coreSide_11_0 :
    certify 96 (wrongProblem .second 3 .coreSide .coreSide true true 0) (pairBox .coreSide .coreSide)=true := by decide
theorem second_3_coreSide_coreSide_11_1 :
    certify 96 (wrongProblem .second 3 .coreSide .coreSide true true 1) (pairBox .coreSide .coreSide)=true := by decide
theorem second_3_coreSide_coreSide_11_3 :
    certify 96 (wrongProblem .second 3 .coreSide .coreSide true true 3) (pairBox .coreSide .coreSide)=true := by decide
theorem second_3_coreSide_coreCorner_11_0 :
    certify 96 (wrongProblem .second 3 .coreSide .coreCorner true true 0) (pairBox .coreSide .coreCorner)=true := by decide
theorem second_3_coreSide_coreCorner_11_1 :
    certify 96 (wrongProblem .second 3 .coreSide .coreCorner true true 1) (pairBox .coreSide .coreCorner)=true := by decide
theorem second_3_coreSide_coreCorner_11_3 :
    certify 96 (wrongProblem .second 3 .coreSide .coreCorner true true 3) (pairBox .coreSide .coreCorner)=true := by decide
theorem second_3_coreCorner_outer_11_0 :
    certify 96 (wrongProblem .second 3 .coreCorner .outer true true 0) (pairBox .coreCorner .outer)=true := by decide
theorem second_3_coreCorner_outer_11_1 :
    certify 96 (wrongProblem .second 3 .coreCorner .outer true true 1) (pairBox .coreCorner .outer)=true := by decide
theorem second_3_coreCorner_outer_11_3 :
    certify 96 (wrongProblem .second 3 .coreCorner .outer true true 3) (pairBox .coreCorner .outer)=true := by decide
theorem second_3_coreCorner_coreSide_11_0 :
    certify 96 (wrongProblem .second 3 .coreCorner .coreSide true true 0) (pairBox .coreCorner .coreSide)=true := by decide
theorem second_3_coreCorner_coreSide_11_1 :
    certify 96 (wrongProblem .second 3 .coreCorner .coreSide true true 1) (pairBox .coreCorner .coreSide)=true := by decide
theorem second_3_coreCorner_coreSide_11_3 :
    certify 96 (wrongProblem .second 3 .coreCorner .coreSide true true 3) (pairBox .coreCorner .coreSide)=true := by decide
theorem second_3_coreCorner_coreCorner_11_0 :
    certify 96 (wrongProblem .second 3 .coreCorner .coreCorner true true 0) (pairBox .coreCorner .coreCorner)=true := by decide
theorem second_3_coreCorner_coreCorner_11_1 :
    certify 96 (wrongProblem .second 3 .coreCorner .coreCorner true true 1) (pairBox .coreCorner .coreCorner)=true := by decide
theorem second_3_coreCorner_coreCorner_11_3 :
    certify 96 (wrongProblem .second 3 .coreCorner .coreCorner true true 3) (pairBox .coreCorner .coreCorner)=true := by decide
theorem second_4_outer_outer_00_0 :
    certify 96 (wrongProblem .second 4 .outer .outer false false 0) (pairBox .outer .outer)=true := by decide
theorem second_4_outer_outer_00_1 :
    certify 96 (wrongProblem .second 4 .outer .outer false false 1) (pairBox .outer .outer)=true := by decide
theorem second_4_outer_outer_00_2 :
    certify 96 (wrongProblem .second 4 .outer .outer false false 2) (pairBox .outer .outer)=true := by decide
theorem second_4_outer_outer_00_3 :
    certify 96 (wrongProblem .second 4 .outer .outer false false 3) (pairBox .outer .outer)=true := by decide
theorem second_4_outer_coreSide_00_2 :
    certify 96 (wrongProblem .second 4 .outer .coreSide false false 2) (pairBox .outer .coreSide)=true := by decide
theorem second_4_outer_coreSide_00_3 :
    certify 96 (wrongProblem .second 4 .outer .coreSide false false 3) (pairBox .outer .coreSide)=true := by decide
theorem second_4_outer_coreCorner_00_2 :
    certify 96 (wrongProblem .second 4 .outer .coreCorner false false 2) (pairBox .outer .coreCorner)=true := by decide
theorem second_4_outer_coreCorner_00_3 :
    certify 96 (wrongProblem .second 4 .outer .coreCorner false false 3) (pairBox .outer .coreCorner)=true := by decide
theorem second_4_coreSide_outer_00_0 :
    certify 96 (wrongProblem .second 4 .coreSide .outer false false 0) (pairBox .coreSide .outer)=true := by decide
theorem second_4_coreSide_outer_00_1 :
    certify 96 (wrongProblem .second 4 .coreSide .outer false false 1) (pairBox .coreSide .outer)=true := by decide
theorem second_4_coreSide_outer_00_2 :
    certify 96 (wrongProblem .second 4 .coreSide .outer false false 2) (pairBox .coreSide .outer)=true := by decide
theorem second_4_coreSide_coreSide_00_2 :
    certify 96 (wrongProblem .second 4 .coreSide .coreSide false false 2) (pairBox .coreSide .coreSide)=true := by decide
theorem second_4_coreSide_coreCorner_00_2 :
    certify 96 (wrongProblem .second 4 .coreSide .coreCorner false false 2) (pairBox .coreSide .coreCorner)=true := by decide
theorem second_4_coreCorner_outer_00_0 :
    certify 96 (wrongProblem .second 4 .coreCorner .outer false false 0) (pairBox .coreCorner .outer)=true := by decide
theorem second_4_coreCorner_outer_00_1 :
    certify 96 (wrongProblem .second 4 .coreCorner .outer false false 1) (pairBox .coreCorner .outer)=true := by decide
theorem second_4_coreCorner_outer_00_2 :
    certify 96 (wrongProblem .second 4 .coreCorner .outer false false 2) (pairBox .coreCorner .outer)=true := by decide
theorem second_4_coreCorner_coreSide_00_2 :
    certify 96 (wrongProblem .second 4 .coreCorner .coreSide false false 2) (pairBox .coreCorner .coreSide)=true := by decide
theorem second_4_coreCorner_coreCorner_00_2 :
    certify 96 (wrongProblem .second 4 .coreCorner .coreCorner false false 2) (pairBox .coreCorner .coreCorner)=true := by decide
theorem second_4_outer_outer_10_0 :
    certify 96 (wrongProblem .second 4 .outer .outer true false 0) (pairBox .outer .outer)=true := by decide
theorem second_4_outer_outer_10_1 :
    certify 96 (wrongProblem .second 4 .outer .outer true false 1) (pairBox .outer .outer)=true := by decide
theorem second_4_outer_outer_10_2 :
    certify 96 (wrongProblem .second 4 .outer .outer true false 2) (pairBox .outer .outer)=true := by decide
theorem second_4_outer_outer_10_3 :
    certify 96 (wrongProblem .second 4 .outer .outer true false 3) (pairBox .outer .outer)=true := by decide
theorem second_4_outer_coreSide_10_0 :
    certify 96 (wrongProblem .second 4 .outer .coreSide true false 0) (pairBox .outer .coreSide)=true := by decide
theorem second_4_outer_coreSide_10_2 :
    certify 96 (wrongProblem .second 4 .outer .coreSide true false 2) (pairBox .outer .coreSide)=true := by decide
theorem second_4_outer_coreSide_10_3 :
    certify 96 (wrongProblem .second 4 .outer .coreSide true false 3) (pairBox .outer .coreSide)=true := by decide
theorem second_4_outer_coreCorner_10_0 :
    certify 96 (wrongProblem .second 4 .outer .coreCorner true false 0) (pairBox .outer .coreCorner)=true := by decide
theorem second_4_outer_coreCorner_10_2 :
    certify 96 (wrongProblem .second 4 .outer .coreCorner true false 2) (pairBox .outer .coreCorner)=true := by decide
theorem second_4_outer_coreCorner_10_3 :
    certify 96 (wrongProblem .second 4 .outer .coreCorner true false 3) (pairBox .outer .coreCorner)=true := by decide
theorem second_4_coreSide_outer_10_0 :
    certify 96 (wrongProblem .second 4 .coreSide .outer true false 0) (pairBox .coreSide .outer)=true := by decide
theorem second_4_coreSide_outer_10_1 :
    certify 96 (wrongProblem .second 4 .coreSide .outer true false 1) (pairBox .coreSide .outer)=true := by decide
theorem second_4_coreSide_outer_10_2 :
    certify 96 (wrongProblem .second 4 .coreSide .outer true false 2) (pairBox .coreSide .outer)=true := by decide
theorem second_4_coreSide_coreSide_10_0 :
    certify 96 (wrongProblem .second 4 .coreSide .coreSide true false 0) (pairBox .coreSide .coreSide)=true := by decide
theorem second_4_coreSide_coreSide_10_2 :
    certify 96 (wrongProblem .second 4 .coreSide .coreSide true false 2) (pairBox .coreSide .coreSide)=true := by decide
theorem second_4_coreSide_coreCorner_10_0 :
    certify 96 (wrongProblem .second 4 .coreSide .coreCorner true false 0) (pairBox .coreSide .coreCorner)=true := by decide
theorem second_4_coreSide_coreCorner_10_2 :
    certify 96 (wrongProblem .second 4 .coreSide .coreCorner true false 2) (pairBox .coreSide .coreCorner)=true := by decide
theorem second_4_coreCorner_outer_10_0 :
    certify 96 (wrongProblem .second 4 .coreCorner .outer true false 0) (pairBox .coreCorner .outer)=true := by decide
theorem second_4_coreCorner_outer_10_1 :
    certify 96 (wrongProblem .second 4 .coreCorner .outer true false 1) (pairBox .coreCorner .outer)=true := by decide
theorem second_4_coreCorner_outer_10_2 :
    certify 96 (wrongProblem .second 4 .coreCorner .outer true false 2) (pairBox .coreCorner .outer)=true := by decide
theorem second_4_coreCorner_coreSide_10_0 :
    certify 96 (wrongProblem .second 4 .coreCorner .coreSide true false 0) (pairBox .coreCorner .coreSide)=true := by decide
theorem second_4_coreCorner_coreSide_10_2 :
    certify 96 (wrongProblem .second 4 .coreCorner .coreSide true false 2) (pairBox .coreCorner .coreSide)=true := by decide
theorem second_4_coreCorner_coreCorner_10_0 :
    certify 96 (wrongProblem .second 4 .coreCorner .coreCorner true false 0) (pairBox .coreCorner .coreCorner)=true := by decide
theorem second_4_coreCorner_coreCorner_10_2 :
    certify 96 (wrongProblem .second 4 .coreCorner .coreCorner true false 2) (pairBox .coreCorner .coreCorner)=true := by decide
theorem second_4_outer_outer_11_0 :
    certify 96 (wrongProblem .second 4 .outer .outer true true 0) (pairBox .outer .outer)=true := by decide
theorem second_4_outer_outer_11_1 :
    certify 96 (wrongProblem .second 4 .outer .outer true true 1) (pairBox .outer .outer)=true := by decide
theorem second_4_outer_outer_11_2 :
    certify 96 (wrongProblem .second 4 .outer .outer true true 2) (pairBox .outer .outer)=true := by decide
theorem second_4_outer_outer_11_3 :
    certify 96 (wrongProblem .second 4 .outer .outer true true 3) (pairBox .outer .outer)=true := by decide
theorem second_4_outer_coreSide_11_0 :
    certify 96 (wrongProblem .second 4 .outer .coreSide true true 0) (pairBox .outer .coreSide)=true := by decide
theorem second_4_outer_coreSide_11_2 :
    certify 96 (wrongProblem .second 4 .outer .coreSide true true 2) (pairBox .outer .coreSide)=true := by decide
theorem second_4_outer_coreSide_11_3 :
    certify 96 (wrongProblem .second 4 .outer .coreSide true true 3) (pairBox .outer .coreSide)=true := by decide
theorem second_4_outer_coreCorner_11_0 :
    certify 96 (wrongProblem .second 4 .outer .coreCorner true true 0) (pairBox .outer .coreCorner)=true := by decide
theorem second_4_outer_coreCorner_11_2 :
    certify 96 (wrongProblem .second 4 .outer .coreCorner true true 2) (pairBox .outer .coreCorner)=true := by decide
theorem second_4_outer_coreCorner_11_3 :
    certify 96 (wrongProblem .second 4 .outer .coreCorner true true 3) (pairBox .outer .coreCorner)=true := by decide
theorem second_4_coreSide_outer_11_0 :
    certify 96 (wrongProblem .second 4 .coreSide .outer true true 0) (pairBox .coreSide .outer)=true := by decide
theorem second_4_coreSide_outer_11_1 :
    certify 96 (wrongProblem .second 4 .coreSide .outer true true 1) (pairBox .coreSide .outer)=true := by decide
theorem second_4_coreSide_coreSide_11_0 :
    certify 96 (wrongProblem .second 4 .coreSide .coreSide true true 0) (pairBox .coreSide .coreSide)=true := by decide
theorem second_4_coreSide_coreCorner_11_0 :
    certify 96 (wrongProblem .second 4 .coreSide .coreCorner true true 0) (pairBox .coreSide .coreCorner)=true := by decide
theorem second_4_coreCorner_outer_11_0 :
    certify 96 (wrongProblem .second 4 .coreCorner .outer true true 0) (pairBox .coreCorner .outer)=true := by decide
theorem second_4_coreCorner_outer_11_1 :
    certify 96 (wrongProblem .second 4 .coreCorner .outer true true 1) (pairBox .coreCorner .outer)=true := by decide
theorem second_4_coreCorner_coreSide_11_0 :
    certify 96 (wrongProblem .second 4 .coreCorner .coreSide true true 0) (pairBox .coreCorner .coreSide)=true := by decide
theorem second_4_coreCorner_coreCorner_11_0 :
    certify 96 (wrongProblem .second 4 .coreCorner .coreCorner true true 0) (pairBox .coreCorner .coreCorner)=true := by decide
theorem second_5_outer_outer_00_0 :
    certify 96 (wrongProblem .second 5 .outer .outer false false 0) (pairBox .outer .outer)=true := by decide
theorem second_5_outer_outer_00_1 :
    certify 96 (wrongProblem .second 5 .outer .outer false false 1) (pairBox .outer .outer)=true := by decide
theorem second_5_outer_outer_00_2 :
    certify 96 (wrongProblem .second 5 .outer .outer false false 2) (pairBox .outer .outer)=true := by decide
theorem second_5_outer_outer_00_3 :
    certify 96 (wrongProblem .second 5 .outer .outer false false 3) (pairBox .outer .outer)=true := by decide
theorem second_5_outer_coreSide_00_1 :
    certify 96 (wrongProblem .second 5 .outer .coreSide false false 1) (pairBox .outer .coreSide)=true := by decide
theorem second_5_outer_coreSide_00_2 :
    certify 96 (wrongProblem .second 5 .outer .coreSide false false 2) (pairBox .outer .coreSide)=true := by decide
theorem second_5_outer_coreSide_00_3 :
    certify 96 (wrongProblem .second 5 .outer .coreSide false false 3) (pairBox .outer .coreSide)=true := by decide
theorem second_5_outer_coreCorner_00_1 :
    certify 96 (wrongProblem .second 5 .outer .coreCorner false false 1) (pairBox .outer .coreCorner)=true := by decide
theorem second_5_outer_coreCorner_00_2 :
    certify 96 (wrongProblem .second 5 .outer .coreCorner false false 2) (pairBox .outer .coreCorner)=true := by decide
theorem second_5_outer_coreCorner_00_3 :
    certify 96 (wrongProblem .second 5 .outer .coreCorner false false 3) (pairBox .outer .coreCorner)=true := by decide
theorem second_5_coreSide_outer_00_0 :
    certify 96 (wrongProblem .second 5 .coreSide .outer false false 0) (pairBox .coreSide .outer)=true := by decide
theorem second_5_coreSide_outer_00_1 :
    certify 96 (wrongProblem .second 5 .coreSide .outer false false 1) (pairBox .coreSide .outer)=true := by decide
theorem second_5_coreSide_outer_00_2 :
    certify 96 (wrongProblem .second 5 .coreSide .outer false false 2) (pairBox .coreSide .outer)=true := by decide
theorem second_5_coreSide_outer_00_3 :
    certify 96 (wrongProblem .second 5 .coreSide .outer false false 3) (pairBox .coreSide .outer)=true := by decide
theorem second_5_coreSide_coreSide_00_1 :
    certify 96 (wrongProblem .second 5 .coreSide .coreSide false false 1) (pairBox .coreSide .coreSide)=true := by decide
theorem second_5_coreSide_coreSide_00_2 :
    certify 96 (wrongProblem .second 5 .coreSide .coreSide false false 2) (pairBox .coreSide .coreSide)=true := by decide
theorem second_5_coreSide_coreSide_00_3 :
    certify 96 (wrongProblem .second 5 .coreSide .coreSide false false 3) (pairBox .coreSide .coreSide)=true := by decide
theorem second_5_coreSide_coreCorner_00_1 :
    certify 96 (wrongProblem .second 5 .coreSide .coreCorner false false 1) (pairBox .coreSide .coreCorner)=true := by decide
theorem second_5_coreSide_coreCorner_00_2 :
    certify 96 (wrongProblem .second 5 .coreSide .coreCorner false false 2) (pairBox .coreSide .coreCorner)=true := by decide
theorem second_5_coreSide_coreCorner_00_3 :
    certify 96 (wrongProblem .second 5 .coreSide .coreCorner false false 3) (pairBox .coreSide .coreCorner)=true := by decide
theorem second_5_coreCorner_outer_00_0 :
    certify 96 (wrongProblem .second 5 .coreCorner .outer false false 0) (pairBox .coreCorner .outer)=true := by decide
theorem second_5_coreCorner_outer_00_1 :
    certify 96 (wrongProblem .second 5 .coreCorner .outer false false 1) (pairBox .coreCorner .outer)=true := by decide
theorem second_5_coreCorner_outer_00_2 :
    certify 96 (wrongProblem .second 5 .coreCorner .outer false false 2) (pairBox .coreCorner .outer)=true := by decide
theorem second_5_coreCorner_outer_00_3 :
    certify 96 (wrongProblem .second 5 .coreCorner .outer false false 3) (pairBox .coreCorner .outer)=true := by decide
theorem second_5_coreCorner_coreSide_00_1 :
    certify 96 (wrongProblem .second 5 .coreCorner .coreSide false false 1) (pairBox .coreCorner .coreSide)=true := by decide
theorem second_5_coreCorner_coreSide_00_2 :
    certify 96 (wrongProblem .second 5 .coreCorner .coreSide false false 2) (pairBox .coreCorner .coreSide)=true := by decide
theorem second_5_coreCorner_coreSide_00_3 :
    certify 96 (wrongProblem .second 5 .coreCorner .coreSide false false 3) (pairBox .coreCorner .coreSide)=true := by decide
theorem second_5_coreCorner_coreCorner_00_1 :
    certify 96 (wrongProblem .second 5 .coreCorner .coreCorner false false 1) (pairBox .coreCorner .coreCorner)=true := by decide
theorem second_5_coreCorner_coreCorner_00_2 :
    certify 96 (wrongProblem .second 5 .coreCorner .coreCorner false false 2) (pairBox .coreCorner .coreCorner)=true := by decide
theorem second_5_coreCorner_coreCorner_00_3 :
    certify 96 (wrongProblem .second 5 .coreCorner .coreCorner false false 3) (pairBox .coreCorner .coreCorner)=true := by decide
theorem second_5_outer_outer_01_0 :
    certify 96 (wrongProblem .second 5 .outer .outer false true 0) (pairBox .outer .outer)=true := by decide
theorem second_5_outer_outer_01_1 :
    certify 96 (wrongProblem .second 5 .outer .outer false true 1) (pairBox .outer .outer)=true := by decide
theorem second_5_outer_outer_01_2 :
    certify 96 (wrongProblem .second 5 .outer .outer false true 2) (pairBox .outer .outer)=true := by decide
theorem second_5_outer_outer_01_3 :
    certify 96 (wrongProblem .second 5 .outer .outer false true 3) (pairBox .outer .outer)=true := by decide
theorem second_5_outer_coreSide_01_1 :
    certify 96 (wrongProblem .second 5 .outer .coreSide false true 1) (pairBox .outer .coreSide)=true := by decide
theorem second_5_outer_coreSide_01_2 :
    certify 96 (wrongProblem .second 5 .outer .coreSide false true 2) (pairBox .outer .coreSide)=true := by decide
theorem second_5_outer_coreSide_01_3 :
    certify 96 (wrongProblem .second 5 .outer .coreSide false true 3) (pairBox .outer .coreSide)=true := by decide
theorem second_5_outer_coreCorner_01_1 :
    certify 96 (wrongProblem .second 5 .outer .coreCorner false true 1) (pairBox .outer .coreCorner)=true := by decide
theorem second_5_outer_coreCorner_01_2 :
    certify 96 (wrongProblem .second 5 .outer .coreCorner false true 2) (pairBox .outer .coreCorner)=true := by decide
theorem second_5_outer_coreCorner_01_3 :
    certify 96 (wrongProblem .second 5 .outer .coreCorner false true 3) (pairBox .outer .coreCorner)=true := by decide
theorem second_5_coreSide_outer_01_0 :
    certify 96 (wrongProblem .second 5 .coreSide .outer false true 0) (pairBox .coreSide .outer)=true := by decide
theorem second_5_coreSide_outer_01_1 :
    certify 96 (wrongProblem .second 5 .coreSide .outer false true 1) (pairBox .coreSide .outer)=true := by decide
theorem second_5_coreSide_outer_01_3 :
    certify 96 (wrongProblem .second 5 .coreSide .outer false true 3) (pairBox .coreSide .outer)=true := by decide
theorem second_5_coreSide_coreSide_01_1 :
    certify 96 (wrongProblem .second 5 .coreSide .coreSide false true 1) (pairBox .coreSide .coreSide)=true := by decide
theorem second_5_coreSide_coreSide_01_3 :
    certify 96 (wrongProblem .second 5 .coreSide .coreSide false true 3) (pairBox .coreSide .coreSide)=true := by decide
theorem second_5_coreSide_coreCorner_01_1 :
    certify 96 (wrongProblem .second 5 .coreSide .coreCorner false true 1) (pairBox .coreSide .coreCorner)=true := by decide
theorem second_5_coreSide_coreCorner_01_3 :
    certify 96 (wrongProblem .second 5 .coreSide .coreCorner false true 3) (pairBox .coreSide .coreCorner)=true := by decide
theorem second_5_coreCorner_outer_01_0 :
    certify 96 (wrongProblem .second 5 .coreCorner .outer false true 0) (pairBox .coreCorner .outer)=true := by decide
theorem second_5_coreCorner_outer_01_1 :
    certify 96 (wrongProblem .second 5 .coreCorner .outer false true 1) (pairBox .coreCorner .outer)=true := by decide
theorem second_5_coreCorner_outer_01_3 :
    certify 96 (wrongProblem .second 5 .coreCorner .outer false true 3) (pairBox .coreCorner .outer)=true := by decide
theorem second_5_coreCorner_coreSide_01_1 :
    certify 96 (wrongProblem .second 5 .coreCorner .coreSide false true 1) (pairBox .coreCorner .coreSide)=true := by decide
theorem second_5_coreCorner_coreSide_01_3 :
    certify 96 (wrongProblem .second 5 .coreCorner .coreSide false true 3) (pairBox .coreCorner .coreSide)=true := by decide
theorem second_5_coreCorner_coreCorner_01_1 :
    certify 96 (wrongProblem .second 5 .coreCorner .coreCorner false true 1) (pairBox .coreCorner .coreCorner)=true := by decide
theorem second_5_coreCorner_coreCorner_01_3 :
    certify 96 (wrongProblem .second 5 .coreCorner .coreCorner false true 3) (pairBox .coreCorner .coreCorner)=true := by decide
theorem second_5_outer_outer_10_0 :
    certify 96 (wrongProblem .second 5 .outer .outer true false 0) (pairBox .outer .outer)=true := by decide
theorem second_5_outer_outer_10_1 :
    certify 96 (wrongProblem .second 5 .outer .outer true false 1) (pairBox .outer .outer)=true := by decide
theorem second_5_outer_outer_10_2 :
    certify 96 (wrongProblem .second 5 .outer .outer true false 2) (pairBox .outer .outer)=true := by decide
theorem second_5_outer_outer_10_3 :
    certify 96 (wrongProblem .second 5 .outer .outer true false 3) (pairBox .outer .outer)=true := by decide
theorem second_5_outer_coreSide_10_0 :
    certify 96 (wrongProblem .second 5 .outer .coreSide true false 0) (pairBox .outer .coreSide)=true := by decide
theorem second_5_outer_coreSide_10_1 :
    certify 96 (wrongProblem .second 5 .outer .coreSide true false 1) (pairBox .outer .coreSide)=true := by decide
theorem second_5_outer_coreSide_10_2 :
    certify 96 (wrongProblem .second 5 .outer .coreSide true false 2) (pairBox .outer .coreSide)=true := by decide
theorem second_5_outer_coreSide_10_3 :
    certify 96 (wrongProblem .second 5 .outer .coreSide true false 3) (pairBox .outer .coreSide)=true := by decide
theorem second_5_outer_coreCorner_10_0 :
    certify 96 (wrongProblem .second 5 .outer .coreCorner true false 0) (pairBox .outer .coreCorner)=true := by decide
theorem second_5_outer_coreCorner_10_1 :
    certify 96 (wrongProblem .second 5 .outer .coreCorner true false 1) (pairBox .outer .coreCorner)=true := by decide
theorem second_5_outer_coreCorner_10_2 :
    certify 96 (wrongProblem .second 5 .outer .coreCorner true false 2) (pairBox .outer .coreCorner)=true := by decide
theorem second_5_outer_coreCorner_10_3 :
    certify 96 (wrongProblem .second 5 .outer .coreCorner true false 3) (pairBox .outer .coreCorner)=true := by decide
theorem second_5_coreSide_outer_10_0 :
    certify 96 (wrongProblem .second 5 .coreSide .outer true false 0) (pairBox .coreSide .outer)=true := by decide
theorem second_5_coreSide_outer_10_1 :
    certify 96 (wrongProblem .second 5 .coreSide .outer true false 1) (pairBox .coreSide .outer)=true := by decide
theorem second_5_coreSide_outer_10_2 :
    certify 96 (wrongProblem .second 5 .coreSide .outer true false 2) (pairBox .coreSide .outer)=true := by decide
theorem second_5_coreSide_outer_10_3 :
    certify 96 (wrongProblem .second 5 .coreSide .outer true false 3) (pairBox .coreSide .outer)=true := by decide
theorem second_5_coreCorner_outer_10_0 :
    certify 96 (wrongProblem .second 5 .coreCorner .outer true false 0) (pairBox .coreCorner .outer)=true := by decide
theorem second_5_coreCorner_outer_10_1 :
    certify 96 (wrongProblem .second 5 .coreCorner .outer true false 1) (pairBox .coreCorner .outer)=true := by decide
theorem second_5_coreCorner_outer_10_2 :
    certify 96 (wrongProblem .second 5 .coreCorner .outer true false 2) (pairBox .coreCorner .outer)=true := by decide
theorem second_5_coreCorner_outer_10_3 :
    certify 96 (wrongProblem .second 5 .coreCorner .outer true false 3) (pairBox .coreCorner .outer)=true := by decide
theorem second_5_outer_outer_11_0 :
    certify 96 (wrongProblem .second 5 .outer .outer true true 0) (pairBox .outer .outer)=true := by decide
theorem second_5_outer_outer_11_1 :
    certify 96 (wrongProblem .second 5 .outer .outer true true 1) (pairBox .outer .outer)=true := by decide
theorem second_5_outer_outer_11_2 :
    certify 96 (wrongProblem .second 5 .outer .outer true true 2) (pairBox .outer .outer)=true := by decide
theorem second_5_outer_outer_11_3 :
    certify 96 (wrongProblem .second 5 .outer .outer true true 3) (pairBox .outer .outer)=true := by decide
theorem second_5_outer_coreSide_11_0 :
    certify 96 (wrongProblem .second 5 .outer .coreSide true true 0) (pairBox .outer .coreSide)=true := by decide
theorem second_5_outer_coreSide_11_1 :
    certify 96 (wrongProblem .second 5 .outer .coreSide true true 1) (pairBox .outer .coreSide)=true := by decide
theorem second_5_outer_coreSide_11_2 :
    certify 96 (wrongProblem .second 5 .outer .coreSide true true 2) (pairBox .outer .coreSide)=true := by decide
theorem second_5_outer_coreSide_11_3 :
    certify 96 (wrongProblem .second 5 .outer .coreSide true true 3) (pairBox .outer .coreSide)=true := by decide
theorem second_5_outer_coreCorner_11_0 :
    certify 96 (wrongProblem .second 5 .outer .coreCorner true true 0) (pairBox .outer .coreCorner)=true := by decide
theorem second_5_outer_coreCorner_11_1 :
    certify 96 (wrongProblem .second 5 .outer .coreCorner true true 1) (pairBox .outer .coreCorner)=true := by decide
theorem second_5_outer_coreCorner_11_2 :
    certify 96 (wrongProblem .second 5 .outer .coreCorner true true 2) (pairBox .outer .coreCorner)=true := by decide
theorem second_5_outer_coreCorner_11_3 :
    certify 96 (wrongProblem .second 5 .outer .coreCorner true true 3) (pairBox .outer .coreCorner)=true := by decide
theorem second_5_coreSide_outer_11_0 :
    certify 96 (wrongProblem .second 5 .coreSide .outer true true 0) (pairBox .coreSide .outer)=true := by decide
theorem second_5_coreSide_outer_11_1 :
    certify 96 (wrongProblem .second 5 .coreSide .outer true true 1) (pairBox .coreSide .outer)=true := by decide
theorem second_5_coreSide_outer_11_3 :
    certify 96 (wrongProblem .second 5 .coreSide .outer true true 3) (pairBox .coreSide .outer)=true := by decide
theorem second_5_coreSide_coreSide_11_0 :
    certify 96 (wrongProblem .second 5 .coreSide .coreSide true true 0) (pairBox .coreSide .coreSide)=true := by decide
theorem second_5_coreSide_coreSide_11_1 :
    certify 96 (wrongProblem .second 5 .coreSide .coreSide true true 1) (pairBox .coreSide .coreSide)=true := by decide
theorem second_5_coreSide_coreSide_11_3 :
    certify 96 (wrongProblem .second 5 .coreSide .coreSide true true 3) (pairBox .coreSide .coreSide)=true := by decide
theorem second_5_coreSide_coreCorner_11_0 :
    certify 96 (wrongProblem .second 5 .coreSide .coreCorner true true 0) (pairBox .coreSide .coreCorner)=true := by decide
theorem second_5_coreSide_coreCorner_11_1 :
    certify 96 (wrongProblem .second 5 .coreSide .coreCorner true true 1) (pairBox .coreSide .coreCorner)=true := by decide
theorem second_5_coreSide_coreCorner_11_3 :
    certify 96 (wrongProblem .second 5 .coreSide .coreCorner true true 3) (pairBox .coreSide .coreCorner)=true := by decide
theorem second_5_coreCorner_outer_11_0 :
    certify 96 (wrongProblem .second 5 .coreCorner .outer true true 0) (pairBox .coreCorner .outer)=true := by decide
theorem second_5_coreCorner_outer_11_1 :
    certify 96 (wrongProblem .second 5 .coreCorner .outer true true 1) (pairBox .coreCorner .outer)=true := by decide
theorem second_5_coreCorner_outer_11_3 :
    certify 96 (wrongProblem .second 5 .coreCorner .outer true true 3) (pairBox .coreCorner .outer)=true := by decide
theorem second_5_coreCorner_coreSide_11_0 :
    certify 96 (wrongProblem .second 5 .coreCorner .coreSide true true 0) (pairBox .coreCorner .coreSide)=true := by decide
theorem second_5_coreCorner_coreSide_11_1 :
    certify 96 (wrongProblem .second 5 .coreCorner .coreSide true true 1) (pairBox .coreCorner .coreSide)=true := by decide
theorem second_5_coreCorner_coreSide_11_3 :
    certify 96 (wrongProblem .second 5 .coreCorner .coreSide true true 3) (pairBox .coreCorner .coreSide)=true := by decide
theorem second_5_coreCorner_coreCorner_11_0 :
    certify 96 (wrongProblem .second 5 .coreCorner .coreCorner true true 0) (pairBox .coreCorner .coreCorner)=true := by decide
theorem second_5_coreCorner_coreCorner_11_1 :
    certify 96 (wrongProblem .second 5 .coreCorner .coreCorner true true 1) (pairBox .coreCorner .coreCorner)=true := by decide
theorem second_5_coreCorner_coreCorner_11_3 :
    certify 96 (wrongProblem .second 5 .coreCorner .coreCorner true true 3) (pairBox .coreCorner .coreCorner)=true := by decide
theorem second_6_outer_outer_01_0 :
    certify 96 (wrongProblem .second 6 .outer .outer false true 0) (pairBox .outer .outer)=true := by decide
theorem second_6_outer_outer_01_1 :
    certify 96 (wrongProblem .second 6 .outer .outer false true 1) (pairBox .outer .outer)=true := by decide
theorem second_6_outer_outer_01_2 :
    certify 96 (wrongProblem .second 6 .outer .outer false true 2) (pairBox .outer .outer)=true := by decide
theorem second_6_outer_outer_01_3 :
    certify 96 (wrongProblem .second 6 .outer .outer false true 3) (pairBox .outer .outer)=true := by decide
theorem second_6_outer_coreSide_01_1 :
    certify 96 (wrongProblem .second 6 .outer .coreSide false true 1) (pairBox .outer .coreSide)=true := by decide
theorem second_6_outer_coreSide_01_2 :
    certify 96 (wrongProblem .second 6 .outer .coreSide false true 2) (pairBox .outer .coreSide)=true := by decide
theorem second_6_outer_coreSide_01_3 :
    certify 96 (wrongProblem .second 6 .outer .coreSide false true 3) (pairBox .outer .coreSide)=true := by decide
theorem second_6_outer_coreCorner_01_1 :
    certify 96 (wrongProblem .second 6 .outer .coreCorner false true 1) (pairBox .outer .coreCorner)=true := by decide
theorem second_6_outer_coreCorner_01_2 :
    certify 96 (wrongProblem .second 6 .outer .coreCorner false true 2) (pairBox .outer .coreCorner)=true := by decide
theorem second_6_outer_coreCorner_01_3 :
    certify 96 (wrongProblem .second 6 .outer .coreCorner false true 3) (pairBox .outer .coreCorner)=true := by decide
theorem second_6_coreSide_outer_01_0 :
    certify 96 (wrongProblem .second 6 .coreSide .outer false true 0) (pairBox .coreSide .outer)=true := by decide
theorem second_6_coreSide_outer_01_1 :
    certify 96 (wrongProblem .second 6 .coreSide .outer false true 1) (pairBox .coreSide .outer)=true := by decide
theorem second_6_coreSide_outer_01_3 :
    certify 96 (wrongProblem .second 6 .coreSide .outer false true 3) (pairBox .coreSide .outer)=true := by decide
theorem second_6_coreSide_coreSide_01_1 :
    certify 96 (wrongProblem .second 6 .coreSide .coreSide false true 1) (pairBox .coreSide .coreSide)=true := by decide
theorem second_6_coreSide_coreSide_01_3 :
    certify 96 (wrongProblem .second 6 .coreSide .coreSide false true 3) (pairBox .coreSide .coreSide)=true := by decide
theorem second_6_coreSide_coreCorner_01_1 :
    certify 96 (wrongProblem .second 6 .coreSide .coreCorner false true 1) (pairBox .coreSide .coreCorner)=true := by decide
theorem second_6_coreSide_coreCorner_01_3 :
    certify 96 (wrongProblem .second 6 .coreSide .coreCorner false true 3) (pairBox .coreSide .coreCorner)=true := by decide
theorem second_6_coreCorner_outer_01_0 :
    certify 96 (wrongProblem .second 6 .coreCorner .outer false true 0) (pairBox .coreCorner .outer)=true := by decide
theorem second_6_coreCorner_outer_01_1 :
    certify 96 (wrongProblem .second 6 .coreCorner .outer false true 1) (pairBox .coreCorner .outer)=true := by decide
theorem second_6_coreCorner_outer_01_3 :
    certify 96 (wrongProblem .second 6 .coreCorner .outer false true 3) (pairBox .coreCorner .outer)=true := by decide
theorem second_6_coreCorner_coreSide_01_1 :
    certify 96 (wrongProblem .second 6 .coreCorner .coreSide false true 1) (pairBox .coreCorner .coreSide)=true := by decide
theorem second_6_coreCorner_coreSide_01_3 :
    certify 96 (wrongProblem .second 6 .coreCorner .coreSide false true 3) (pairBox .coreCorner .coreSide)=true := by decide
theorem second_6_coreCorner_coreCorner_01_1 :
    certify 96 (wrongProblem .second 6 .coreCorner .coreCorner false true 1) (pairBox .coreCorner .coreCorner)=true := by decide
theorem second_6_coreCorner_coreCorner_01_3 :
    certify 96 (wrongProblem .second 6 .coreCorner .coreCorner false true 3) (pairBox .coreCorner .coreCorner)=true := by decide
theorem second_6_outer_outer_11_0 :
    certify 96 (wrongProblem .second 6 .outer .outer true true 0) (pairBox .outer .outer)=true := by decide
theorem second_6_outer_outer_11_1 :
    certify 96 (wrongProblem .second 6 .outer .outer true true 1) (pairBox .outer .outer)=true := by decide
theorem second_6_outer_outer_11_2 :
    certify 96 (wrongProblem .second 6 .outer .outer true true 2) (pairBox .outer .outer)=true := by decide
theorem second_6_outer_outer_11_3 :
    certify 96 (wrongProblem .second 6 .outer .outer true true 3) (pairBox .outer .outer)=true := by decide
theorem second_6_outer_coreSide_11_0 :
    certify 96 (wrongProblem .second 6 .outer .coreSide true true 0) (pairBox .outer .coreSide)=true := by decide
theorem second_6_outer_coreSide_11_1 :
    certify 96 (wrongProblem .second 6 .outer .coreSide true true 1) (pairBox .outer .coreSide)=true := by decide
theorem second_6_outer_coreSide_11_2 :
    certify 96 (wrongProblem .second 6 .outer .coreSide true true 2) (pairBox .outer .coreSide)=true := by decide
theorem second_6_outer_coreSide_11_3 :
    certify 96 (wrongProblem .second 6 .outer .coreSide true true 3) (pairBox .outer .coreSide)=true := by decide
theorem second_6_outer_coreCorner_11_0 :
    certify 96 (wrongProblem .second 6 .outer .coreCorner true true 0) (pairBox .outer .coreCorner)=true := by decide
theorem second_6_outer_coreCorner_11_1 :
    certify 96 (wrongProblem .second 6 .outer .coreCorner true true 1) (pairBox .outer .coreCorner)=true := by decide
theorem second_6_outer_coreCorner_11_2 :
    certify 96 (wrongProblem .second 6 .outer .coreCorner true true 2) (pairBox .outer .coreCorner)=true := by decide
theorem second_6_outer_coreCorner_11_3 :
    certify 96 (wrongProblem .second 6 .outer .coreCorner true true 3) (pairBox .outer .coreCorner)=true := by decide
theorem second_6_coreSide_outer_11_0 :
    certify 96 (wrongProblem .second 6 .coreSide .outer true true 0) (pairBox .coreSide .outer)=true := by decide
theorem second_6_coreSide_outer_11_1 :
    certify 96 (wrongProblem .second 6 .coreSide .outer true true 1) (pairBox .coreSide .outer)=true := by decide
theorem second_6_coreSide_outer_11_3 :
    certify 96 (wrongProblem .second 6 .coreSide .outer true true 3) (pairBox .coreSide .outer)=true := by decide
theorem second_6_coreSide_coreSide_11_0 :
    certify 96 (wrongProblem .second 6 .coreSide .coreSide true true 0) (pairBox .coreSide .coreSide)=true := by decide
theorem second_6_coreSide_coreSide_11_1 :
    certify 96 (wrongProblem .second 6 .coreSide .coreSide true true 1) (pairBox .coreSide .coreSide)=true := by decide
theorem second_6_coreSide_coreSide_11_3 :
    certify 96 (wrongProblem .second 6 .coreSide .coreSide true true 3) (pairBox .coreSide .coreSide)=true := by decide
theorem second_6_coreSide_coreCorner_11_0 :
    certify 96 (wrongProblem .second 6 .coreSide .coreCorner true true 0) (pairBox .coreSide .coreCorner)=true := by decide
theorem second_6_coreSide_coreCorner_11_1 :
    certify 96 (wrongProblem .second 6 .coreSide .coreCorner true true 1) (pairBox .coreSide .coreCorner)=true := by decide
theorem second_6_coreSide_coreCorner_11_3 :
    certify 96 (wrongProblem .second 6 .coreSide .coreCorner true true 3) (pairBox .coreSide .coreCorner)=true := by decide
theorem second_6_coreCorner_outer_11_0 :
    certify 96 (wrongProblem .second 6 .coreCorner .outer true true 0) (pairBox .coreCorner .outer)=true := by decide
theorem second_6_coreCorner_outer_11_1 :
    certify 96 (wrongProblem .second 6 .coreCorner .outer true true 1) (pairBox .coreCorner .outer)=true := by decide
theorem second_6_coreCorner_outer_11_3 :
    certify 96 (wrongProblem .second 6 .coreCorner .outer true true 3) (pairBox .coreCorner .outer)=true := by decide
theorem second_6_coreCorner_coreSide_11_0 :
    certify 96 (wrongProblem .second 6 .coreCorner .coreSide true true 0) (pairBox .coreCorner .coreSide)=true := by decide
theorem second_6_coreCorner_coreSide_11_1 :
    certify 96 (wrongProblem .second 6 .coreCorner .coreSide true true 1) (pairBox .coreCorner .coreSide)=true := by decide
theorem second_6_coreCorner_coreSide_11_3 :
    certify 96 (wrongProblem .second 6 .coreCorner .coreSide true true 3) (pairBox .coreCorner .coreSide)=true := by decide
theorem second_6_coreCorner_coreCorner_11_0 :
    certify 96 (wrongProblem .second 6 .coreCorner .coreCorner true true 0) (pairBox .coreCorner .coreCorner)=true := by decide
theorem second_6_coreCorner_coreCorner_11_1 :
    certify 96 (wrongProblem .second 6 .coreCorner .coreCorner true true 1) (pairBox .coreCorner .coreCorner)=true := by decide
theorem second_6_coreCorner_coreCorner_11_3 :
    certify 96 (wrongProblem .second 6 .coreCorner .coreCorner true true 3) (pairBox .coreCorner .coreCorner)=true := by decide

theorem wrong_certificates (w : WrongWord) (i : Vertex) (source target : RadialKind)
    (σ τ : Bool) (axis : Fin 4) (hallowed : allowed w i σ τ)
    (hkeep : ¬ CoreSeparatorExcluded (wrongWord w i) source target σ τ axis) :
    certify 96 (wrongProblem w i source target σ τ axis) (pairBox source target)=true := by
  cases w <;> fin_cases i <;> cases source <;> cases target <;> cases σ <;> cases τ <;> fin_cases axis
  all_goals first
  | contradiction
  | solve | simp [allowed,wrongWord,next] at hallowed
  | solve | simp [CoreSeparatorExcluded,wrongWord] at hkeep
  | exact short_0_outer_outer_10_0
  | exact short_0_outer_outer_10_1
  | exact short_0_outer_outer_10_2
  | exact short_0_outer_outer_10_3
  | exact short_0_outer_coreSide_10_0
  | exact short_0_outer_coreSide_10_2
  | exact short_0_outer_coreSide_10_3
  | exact short_0_outer_coreCorner_10_0
  | exact short_0_outer_coreCorner_10_2
  | exact short_0_outer_coreCorner_10_3
  | exact short_0_coreSide_outer_10_0
  | exact short_0_coreSide_outer_10_1
  | exact short_0_coreSide_outer_10_2
  | exact short_0_coreSide_coreSide_10_0
  | exact short_0_coreSide_coreSide_10_2
  | exact short_0_coreSide_coreCorner_10_0
  | exact short_0_coreSide_coreCorner_10_2
  | exact short_0_coreCorner_outer_10_0
  | exact short_0_coreCorner_outer_10_1
  | exact short_0_coreCorner_outer_10_2
  | exact short_0_coreCorner_coreSide_10_0
  | exact short_0_coreCorner_coreSide_10_2
  | exact short_0_coreCorner_coreCorner_10_0
  | exact short_0_coreCorner_coreCorner_10_2
  | exact short_0_outer_outer_11_0
  | exact short_0_outer_outer_11_1
  | exact short_0_outer_outer_11_2
  | exact short_0_outer_outer_11_3
  | exact short_0_outer_coreSide_11_0
  | exact short_0_outer_coreSide_11_2
  | exact short_0_outer_coreSide_11_3
  | exact short_0_outer_coreCorner_11_0
  | exact short_0_outer_coreCorner_11_2
  | exact short_0_outer_coreCorner_11_3
  | exact short_0_coreSide_outer_11_0
  | exact short_0_coreSide_outer_11_1
  | exact short_0_coreSide_coreSide_11_0
  | exact short_0_coreSide_coreCorner_11_0
  | exact short_0_coreCorner_outer_11_0
  | exact short_0_coreCorner_outer_11_1
  | exact short_0_coreCorner_coreSide_11_0
  | exact short_0_coreCorner_coreCorner_11_0
  | exact short_1_outer_outer_00_0
  | exact short_1_outer_outer_00_1
  | exact short_1_outer_outer_00_2
  | exact short_1_outer_outer_00_3
  | exact short_1_outer_coreSide_00_2
  | exact short_1_outer_coreSide_00_3
  | exact short_1_outer_coreCorner_00_2
  | exact short_1_outer_coreCorner_00_3
  | exact short_1_coreSide_outer_00_0
  | exact short_1_coreSide_outer_00_1
  | exact short_1_coreSide_outer_00_2
  | exact short_1_coreSide_coreSide_00_2
  | exact short_1_coreSide_coreCorner_00_2
  | exact short_1_coreCorner_outer_00_0
  | exact short_1_coreCorner_outer_00_1
  | exact short_1_coreCorner_outer_00_2
  | exact short_1_coreCorner_coreSide_00_2
  | exact short_1_coreCorner_coreCorner_00_2
  | exact short_1_outer_outer_10_0
  | exact short_1_outer_outer_10_1
  | exact short_1_outer_outer_10_2
  | exact short_1_outer_outer_10_3
  | exact short_1_outer_coreSide_10_0
  | exact short_1_outer_coreSide_10_2
  | exact short_1_outer_coreSide_10_3
  | exact short_1_outer_coreCorner_10_0
  | exact short_1_outer_coreCorner_10_2
  | exact short_1_outer_coreCorner_10_3
  | exact short_1_coreSide_outer_10_0
  | exact short_1_coreSide_outer_10_1
  | exact short_1_coreSide_outer_10_2
  | exact short_1_coreSide_coreSide_10_0
  | exact short_1_coreSide_coreSide_10_2
  | exact short_1_coreSide_coreCorner_10_0
  | exact short_1_coreSide_coreCorner_10_2
  | exact short_1_coreCorner_outer_10_0
  | exact short_1_coreCorner_outer_10_1
  | exact short_1_coreCorner_outer_10_2
  | exact short_1_coreCorner_coreSide_10_0
  | exact short_1_coreCorner_coreSide_10_2
  | exact short_1_coreCorner_coreCorner_10_0
  | exact short_1_coreCorner_coreCorner_10_2
  | exact short_2_outer_outer_00_0
  | exact short_2_outer_outer_00_1
  | exact short_2_outer_outer_00_2
  | exact short_2_outer_outer_00_3
  | exact short_2_outer_coreSide_00_1
  | exact short_2_outer_coreSide_00_2
  | exact short_2_outer_coreSide_00_3
  | exact short_2_outer_coreCorner_00_1
  | exact short_2_outer_coreCorner_00_2
  | exact short_2_outer_coreCorner_00_3
  | exact short_2_coreSide_outer_00_0
  | exact short_2_coreSide_outer_00_1
  | exact short_2_coreSide_outer_00_2
  | exact short_2_coreSide_outer_00_3
  | exact short_2_coreSide_coreSide_00_1
  | exact short_2_coreSide_coreSide_00_2
  | exact short_2_coreSide_coreSide_00_3
  | exact short_2_coreSide_coreCorner_00_1
  | exact short_2_coreSide_coreCorner_00_2
  | exact short_2_coreSide_coreCorner_00_3
  | exact short_2_coreCorner_outer_00_0
  | exact short_2_coreCorner_outer_00_1
  | exact short_2_coreCorner_outer_00_2
  | exact short_2_coreCorner_outer_00_3
  | exact short_2_coreCorner_coreSide_00_1
  | exact short_2_coreCorner_coreSide_00_2
  | exact short_2_coreCorner_coreSide_00_3
  | exact short_2_coreCorner_coreCorner_00_1
  | exact short_2_coreCorner_coreCorner_00_2
  | exact short_2_coreCorner_coreCorner_00_3
  | exact short_2_outer_outer_01_0
  | exact short_2_outer_outer_01_1
  | exact short_2_outer_outer_01_2
  | exact short_2_outer_outer_01_3
  | exact short_2_outer_coreSide_01_1
  | exact short_2_outer_coreSide_01_2
  | exact short_2_outer_coreSide_01_3
  | exact short_2_outer_coreCorner_01_1
  | exact short_2_outer_coreCorner_01_2
  | exact short_2_outer_coreCorner_01_3
  | exact short_2_coreSide_outer_01_0
  | exact short_2_coreSide_outer_01_1
  | exact short_2_coreSide_outer_01_3
  | exact short_2_coreSide_coreSide_01_1
  | exact short_2_coreSide_coreSide_01_3
  | exact short_2_coreSide_coreCorner_01_1
  | exact short_2_coreSide_coreCorner_01_3
  | exact short_2_coreCorner_outer_01_0
  | exact short_2_coreCorner_outer_01_1
  | exact short_2_coreCorner_outer_01_3
  | exact short_2_coreCorner_coreSide_01_1
  | exact short_2_coreCorner_coreSide_01_3
  | exact short_2_coreCorner_coreCorner_01_1
  | exact short_2_coreCorner_coreCorner_01_3
  | exact short_3_outer_outer_00_0
  | exact short_3_outer_outer_00_1
  | exact short_3_outer_outer_00_2
  | exact short_3_outer_outer_00_3
  | exact short_3_outer_coreSide_00_2
  | exact short_3_outer_coreSide_00_3
  | exact short_3_outer_coreCorner_00_2
  | exact short_3_outer_coreCorner_00_3
  | exact short_3_coreSide_outer_00_0
  | exact short_3_coreSide_outer_00_1
  | exact short_3_coreSide_outer_00_2
  | exact short_3_coreSide_coreSide_00_2
  | exact short_3_coreSide_coreCorner_00_2
  | exact short_3_coreCorner_outer_00_0
  | exact short_3_coreCorner_outer_00_1
  | exact short_3_coreCorner_outer_00_2
  | exact short_3_coreCorner_coreSide_00_2
  | exact short_3_coreCorner_coreCorner_00_2
  | exact short_3_outer_outer_10_0
  | exact short_3_outer_outer_10_1
  | exact short_3_outer_outer_10_2
  | exact short_3_outer_outer_10_3
  | exact short_3_outer_coreSide_10_0
  | exact short_3_outer_coreSide_10_2
  | exact short_3_outer_coreSide_10_3
  | exact short_3_outer_coreCorner_10_0
  | exact short_3_outer_coreCorner_10_2
  | exact short_3_outer_coreCorner_10_3
  | exact short_3_coreSide_outer_10_0
  | exact short_3_coreSide_outer_10_1
  | exact short_3_coreSide_outer_10_2
  | exact short_3_coreSide_coreSide_10_0
  | exact short_3_coreSide_coreSide_10_2
  | exact short_3_coreSide_coreCorner_10_0
  | exact short_3_coreSide_coreCorner_10_2
  | exact short_3_coreCorner_outer_10_0
  | exact short_3_coreCorner_outer_10_1
  | exact short_3_coreCorner_outer_10_2
  | exact short_3_coreCorner_coreSide_10_0
  | exact short_3_coreCorner_coreSide_10_2
  | exact short_3_coreCorner_coreCorner_10_0
  | exact short_3_coreCorner_coreCorner_10_2
  | exact short_3_outer_outer_11_0
  | exact short_3_outer_outer_11_1
  | exact short_3_outer_outer_11_2
  | exact short_3_outer_outer_11_3
  | exact short_3_outer_coreSide_11_0
  | exact short_3_outer_coreSide_11_2
  | exact short_3_outer_coreSide_11_3
  | exact short_3_outer_coreCorner_11_0
  | exact short_3_outer_coreCorner_11_2
  | exact short_3_outer_coreCorner_11_3
  | exact short_3_coreSide_outer_11_0
  | exact short_3_coreSide_outer_11_1
  | exact short_3_coreSide_coreSide_11_0
  | exact short_3_coreSide_coreCorner_11_0
  | exact short_3_coreCorner_outer_11_0
  | exact short_3_coreCorner_outer_11_1
  | exact short_3_coreCorner_coreSide_11_0
  | exact short_3_coreCorner_coreCorner_11_0
  | exact short_4_outer_outer_00_0
  | exact short_4_outer_outer_00_1
  | exact short_4_outer_outer_00_2
  | exact short_4_outer_outer_00_3
  | exact short_4_outer_coreSide_00_1
  | exact short_4_outer_coreSide_00_2
  | exact short_4_outer_coreSide_00_3
  | exact short_4_outer_coreCorner_00_1
  | exact short_4_outer_coreCorner_00_2
  | exact short_4_outer_coreCorner_00_3
  | exact short_4_coreSide_outer_00_0
  | exact short_4_coreSide_outer_00_1
  | exact short_4_coreSide_outer_00_2
  | exact short_4_coreSide_outer_00_3
  | exact short_4_coreSide_coreSide_00_1
  | exact short_4_coreSide_coreSide_00_2
  | exact short_4_coreSide_coreSide_00_3
  | exact short_4_coreSide_coreCorner_00_1
  | exact short_4_coreSide_coreCorner_00_2
  | exact short_4_coreSide_coreCorner_00_3
  | exact short_4_coreCorner_outer_00_0
  | exact short_4_coreCorner_outer_00_1
  | exact short_4_coreCorner_outer_00_2
  | exact short_4_coreCorner_outer_00_3
  | exact short_4_coreCorner_coreSide_00_1
  | exact short_4_coreCorner_coreSide_00_2
  | exact short_4_coreCorner_coreSide_00_3
  | exact short_4_coreCorner_coreCorner_00_1
  | exact short_4_coreCorner_coreCorner_00_2
  | exact short_4_coreCorner_coreCorner_00_3
  | exact short_4_outer_outer_01_0
  | exact short_4_outer_outer_01_1
  | exact short_4_outer_outer_01_2
  | exact short_4_outer_outer_01_3
  | exact short_4_outer_coreSide_01_1
  | exact short_4_outer_coreSide_01_2
  | exact short_4_outer_coreSide_01_3
  | exact short_4_outer_coreCorner_01_1
  | exact short_4_outer_coreCorner_01_2
  | exact short_4_outer_coreCorner_01_3
  | exact short_4_coreSide_outer_01_0
  | exact short_4_coreSide_outer_01_1
  | exact short_4_coreSide_outer_01_3
  | exact short_4_coreSide_coreSide_01_1
  | exact short_4_coreSide_coreSide_01_3
  | exact short_4_coreSide_coreCorner_01_1
  | exact short_4_coreSide_coreCorner_01_3
  | exact short_4_coreCorner_outer_01_0
  | exact short_4_coreCorner_outer_01_1
  | exact short_4_coreCorner_outer_01_3
  | exact short_4_coreCorner_coreSide_01_1
  | exact short_4_coreCorner_coreSide_01_3
  | exact short_4_coreCorner_coreCorner_01_1
  | exact short_4_coreCorner_coreCorner_01_3
  | exact short_4_outer_outer_10_0
  | exact short_4_outer_outer_10_1
  | exact short_4_outer_outer_10_2
  | exact short_4_outer_outer_10_3
  | exact short_4_outer_coreSide_10_0
  | exact short_4_outer_coreSide_10_1
  | exact short_4_outer_coreSide_10_2
  | exact short_4_outer_coreSide_10_3
  | exact short_4_outer_coreCorner_10_0
  | exact short_4_outer_coreCorner_10_1
  | exact short_4_outer_coreCorner_10_2
  | exact short_4_outer_coreCorner_10_3
  | exact short_4_coreSide_outer_10_0
  | exact short_4_coreSide_outer_10_1
  | exact short_4_coreSide_outer_10_2
  | exact short_4_coreSide_outer_10_3
  | exact short_4_coreCorner_outer_10_0
  | exact short_4_coreCorner_outer_10_1
  | exact short_4_coreCorner_outer_10_2
  | exact short_4_coreCorner_outer_10_3
  | exact short_4_outer_outer_11_0
  | exact short_4_outer_outer_11_1
  | exact short_4_outer_outer_11_2
  | exact short_4_outer_outer_11_3
  | exact short_4_outer_coreSide_11_0
  | exact short_4_outer_coreSide_11_1
  | exact short_4_outer_coreSide_11_2
  | exact short_4_outer_coreSide_11_3
  | exact short_4_outer_coreCorner_11_0
  | exact short_4_outer_coreCorner_11_1
  | exact short_4_outer_coreCorner_11_2
  | exact short_4_outer_coreCorner_11_3
  | exact short_4_coreSide_outer_11_0
  | exact short_4_coreSide_outer_11_1
  | exact short_4_coreSide_outer_11_3
  | exact short_4_coreSide_coreSide_11_0
  | exact short_4_coreSide_coreSide_11_1
  | exact short_4_coreSide_coreSide_11_3
  | exact short_4_coreSide_coreCorner_11_0
  | exact short_4_coreSide_coreCorner_11_1
  | exact short_4_coreSide_coreCorner_11_3
  | exact short_4_coreCorner_outer_11_0
  | exact short_4_coreCorner_outer_11_1
  | exact short_4_coreCorner_outer_11_3
  | exact short_4_coreCorner_coreSide_11_0
  | exact short_4_coreCorner_coreSide_11_1
  | exact short_4_coreCorner_coreSide_11_3
  | exact short_4_coreCorner_coreCorner_11_0
  | exact short_4_coreCorner_coreCorner_11_1
  | exact short_4_coreCorner_coreCorner_11_3
  | exact short_5_outer_outer_00_0
  | exact short_5_outer_outer_00_1
  | exact short_5_outer_outer_00_2
  | exact short_5_outer_outer_00_3
  | exact short_5_outer_coreSide_00_1
  | exact short_5_outer_coreSide_00_2
  | exact short_5_outer_coreSide_00_3
  | exact short_5_outer_coreCorner_00_1
  | exact short_5_outer_coreCorner_00_2
  | exact short_5_outer_coreCorner_00_3
  | exact short_5_coreSide_outer_00_0
  | exact short_5_coreSide_outer_00_1
  | exact short_5_coreSide_outer_00_2
  | exact short_5_coreSide_outer_00_3
  | exact short_5_coreSide_coreSide_00_1
  | exact short_5_coreSide_coreSide_00_2
  | exact short_5_coreSide_coreSide_00_3
  | exact short_5_coreSide_coreCorner_00_1
  | exact short_5_coreSide_coreCorner_00_2
  | exact short_5_coreSide_coreCorner_00_3
  | exact short_5_coreCorner_outer_00_0
  | exact short_5_coreCorner_outer_00_1
  | exact short_5_coreCorner_outer_00_2
  | exact short_5_coreCorner_outer_00_3
  | exact short_5_coreCorner_coreSide_00_1
  | exact short_5_coreCorner_coreSide_00_2
  | exact short_5_coreCorner_coreSide_00_3
  | exact short_5_coreCorner_coreCorner_00_1
  | exact short_5_coreCorner_coreCorner_00_2
  | exact short_5_coreCorner_coreCorner_00_3
  | exact short_5_outer_outer_01_0
  | exact short_5_outer_outer_01_1
  | exact short_5_outer_outer_01_2
  | exact short_5_outer_outer_01_3
  | exact short_5_outer_coreSide_01_1
  | exact short_5_outer_coreSide_01_2
  | exact short_5_outer_coreSide_01_3
  | exact short_5_outer_coreCorner_01_1
  | exact short_5_outer_coreCorner_01_2
  | exact short_5_outer_coreCorner_01_3
  | exact short_5_coreSide_outer_01_0
  | exact short_5_coreSide_outer_01_1
  | exact short_5_coreSide_outer_01_3
  | exact short_5_coreSide_coreSide_01_1
  | exact short_5_coreSide_coreSide_01_3
  | exact short_5_coreSide_coreCorner_01_1
  | exact short_5_coreSide_coreCorner_01_3
  | exact short_5_coreCorner_outer_01_0
  | exact short_5_coreCorner_outer_01_1
  | exact short_5_coreCorner_outer_01_3
  | exact short_5_coreCorner_coreSide_01_1
  | exact short_5_coreCorner_coreSide_01_3
  | exact short_5_coreCorner_coreCorner_01_1
  | exact short_5_coreCorner_coreCorner_01_3
  | exact short_5_outer_outer_10_0
  | exact short_5_outer_outer_10_1
  | exact short_5_outer_outer_10_2
  | exact short_5_outer_outer_10_3
  | exact short_5_outer_coreSide_10_0
  | exact short_5_outer_coreSide_10_1
  | exact short_5_outer_coreSide_10_2
  | exact short_5_outer_coreSide_10_3
  | exact short_5_outer_coreCorner_10_0
  | exact short_5_outer_coreCorner_10_1
  | exact short_5_outer_coreCorner_10_2
  | exact short_5_outer_coreCorner_10_3
  | exact short_5_coreSide_outer_10_0
  | exact short_5_coreSide_outer_10_1
  | exact short_5_coreSide_outer_10_2
  | exact short_5_coreSide_outer_10_3
  | exact short_5_coreCorner_outer_10_0
  | exact short_5_coreCorner_outer_10_1
  | exact short_5_coreCorner_outer_10_2
  | exact short_5_coreCorner_outer_10_3
  | exact short_5_outer_outer_11_0
  | exact short_5_outer_outer_11_1
  | exact short_5_outer_outer_11_2
  | exact short_5_outer_outer_11_3
  | exact short_5_outer_coreSide_11_0
  | exact short_5_outer_coreSide_11_1
  | exact short_5_outer_coreSide_11_2
  | exact short_5_outer_coreSide_11_3
  | exact short_5_outer_coreCorner_11_0
  | exact short_5_outer_coreCorner_11_1
  | exact short_5_outer_coreCorner_11_2
  | exact short_5_outer_coreCorner_11_3
  | exact short_5_coreSide_outer_11_0
  | exact short_5_coreSide_outer_11_1
  | exact short_5_coreSide_outer_11_3
  | exact short_5_coreSide_coreSide_11_0
  | exact short_5_coreSide_coreSide_11_1
  | exact short_5_coreSide_coreSide_11_3
  | exact short_5_coreSide_coreCorner_11_0
  | exact short_5_coreSide_coreCorner_11_1
  | exact short_5_coreSide_coreCorner_11_3
  | exact short_5_coreCorner_outer_11_0
  | exact short_5_coreCorner_outer_11_1
  | exact short_5_coreCorner_outer_11_3
  | exact short_5_coreCorner_coreSide_11_0
  | exact short_5_coreCorner_coreSide_11_1
  | exact short_5_coreCorner_coreSide_11_3
  | exact short_5_coreCorner_coreCorner_11_0
  | exact short_5_coreCorner_coreCorner_11_1
  | exact short_5_coreCorner_coreCorner_11_3
  | exact short_6_outer_outer_01_0
  | exact short_6_outer_outer_01_1
  | exact short_6_outer_outer_01_2
  | exact short_6_outer_outer_01_3
  | exact short_6_outer_coreSide_01_1
  | exact short_6_outer_coreSide_01_2
  | exact short_6_outer_coreSide_01_3
  | exact short_6_outer_coreCorner_01_1
  | exact short_6_outer_coreCorner_01_2
  | exact short_6_outer_coreCorner_01_3
  | exact short_6_coreSide_outer_01_0
  | exact short_6_coreSide_outer_01_1
  | exact short_6_coreSide_outer_01_3
  | exact short_6_coreSide_coreSide_01_1
  | exact short_6_coreSide_coreSide_01_3
  | exact short_6_coreSide_coreCorner_01_1
  | exact short_6_coreSide_coreCorner_01_3
  | exact short_6_coreCorner_outer_01_0
  | exact short_6_coreCorner_outer_01_1
  | exact short_6_coreCorner_outer_01_3
  | exact short_6_coreCorner_coreSide_01_1
  | exact short_6_coreCorner_coreSide_01_3
  | exact short_6_coreCorner_coreCorner_01_1
  | exact short_6_coreCorner_coreCorner_01_3
  | exact short_6_outer_outer_11_0
  | exact short_6_outer_outer_11_1
  | exact short_6_outer_outer_11_2
  | exact short_6_outer_outer_11_3
  | exact short_6_outer_coreSide_11_0
  | exact short_6_outer_coreSide_11_1
  | exact short_6_outer_coreSide_11_2
  | exact short_6_outer_coreSide_11_3
  | exact short_6_outer_coreCorner_11_0
  | exact short_6_outer_coreCorner_11_1
  | exact short_6_outer_coreCorner_11_2
  | exact short_6_outer_coreCorner_11_3
  | exact short_6_coreSide_outer_11_0
  | exact short_6_coreSide_outer_11_1
  | exact short_6_coreSide_outer_11_3
  | exact short_6_coreSide_coreSide_11_0
  | exact short_6_coreSide_coreSide_11_1
  | exact short_6_coreSide_coreSide_11_3
  | exact short_6_coreSide_coreCorner_11_0
  | exact short_6_coreSide_coreCorner_11_1
  | exact short_6_coreSide_coreCorner_11_3
  | exact short_6_coreCorner_outer_11_0
  | exact short_6_coreCorner_outer_11_1
  | exact short_6_coreCorner_outer_11_3
  | exact short_6_coreCorner_coreSide_11_0
  | exact short_6_coreCorner_coreSide_11_1
  | exact short_6_coreCorner_coreSide_11_3
  | exact short_6_coreCorner_coreCorner_11_0
  | exact short_6_coreCorner_coreCorner_11_1
  | exact short_6_coreCorner_coreCorner_11_3
  | exact second_0_outer_outer_10_0
  | exact second_0_outer_outer_10_1
  | exact second_0_outer_outer_10_2
  | exact second_0_outer_outer_10_3
  | exact second_0_outer_coreSide_10_0
  | exact second_0_outer_coreSide_10_2
  | exact second_0_outer_coreSide_10_3
  | exact second_0_outer_coreCorner_10_0
  | exact second_0_outer_coreCorner_10_2
  | exact second_0_outer_coreCorner_10_3
  | exact second_0_coreSide_outer_10_0
  | exact second_0_coreSide_outer_10_1
  | exact second_0_coreSide_outer_10_2
  | exact second_0_coreSide_coreSide_10_0
  | exact second_0_coreSide_coreSide_10_2
  | exact second_0_coreSide_coreCorner_10_0
  | exact second_0_coreSide_coreCorner_10_2
  | exact second_0_coreCorner_outer_10_0
  | exact second_0_coreCorner_outer_10_1
  | exact second_0_coreCorner_outer_10_2
  | exact second_0_coreCorner_coreSide_10_0
  | exact second_0_coreCorner_coreSide_10_2
  | exact second_0_coreCorner_coreCorner_10_0
  | exact second_0_coreCorner_coreCorner_10_2
  | exact second_0_outer_outer_11_0
  | exact second_0_outer_outer_11_1
  | exact second_0_outer_outer_11_2
  | exact second_0_outer_outer_11_3
  | exact second_0_outer_coreSide_11_0
  | exact second_0_outer_coreSide_11_2
  | exact second_0_outer_coreSide_11_3
  | exact second_0_outer_coreCorner_11_0
  | exact second_0_outer_coreCorner_11_2
  | exact second_0_outer_coreCorner_11_3
  | exact second_0_coreSide_outer_11_0
  | exact second_0_coreSide_outer_11_1
  | exact second_0_coreSide_coreSide_11_0
  | exact second_0_coreSide_coreCorner_11_0
  | exact second_0_coreCorner_outer_11_0
  | exact second_0_coreCorner_outer_11_1
  | exact second_0_coreCorner_coreSide_11_0
  | exact second_0_coreCorner_coreCorner_11_0
  | exact second_1_outer_outer_00_0
  | exact second_1_outer_outer_00_1
  | exact second_1_outer_outer_00_2
  | exact second_1_outer_outer_00_3
  | exact second_1_outer_coreSide_00_2
  | exact second_1_outer_coreSide_00_3
  | exact second_1_outer_coreCorner_00_2
  | exact second_1_outer_coreCorner_00_3
  | exact second_1_coreSide_outer_00_0
  | exact second_1_coreSide_outer_00_1
  | exact second_1_coreSide_outer_00_2
  | exact second_1_coreSide_coreSide_00_2
  | exact second_1_coreSide_coreCorner_00_2
  | exact second_1_coreCorner_outer_00_0
  | exact second_1_coreCorner_outer_00_1
  | exact second_1_coreCorner_outer_00_2
  | exact second_1_coreCorner_coreSide_00_2
  | exact second_1_coreCorner_coreCorner_00_2
  | exact second_1_outer_outer_10_0
  | exact second_1_outer_outer_10_1
  | exact second_1_outer_outer_10_2
  | exact second_1_outer_outer_10_3
  | exact second_1_outer_coreSide_10_0
  | exact second_1_outer_coreSide_10_2
  | exact second_1_outer_coreSide_10_3
  | exact second_1_outer_coreCorner_10_0
  | exact second_1_outer_coreCorner_10_2
  | exact second_1_outer_coreCorner_10_3
  | exact second_1_coreSide_outer_10_0
  | exact second_1_coreSide_outer_10_1
  | exact second_1_coreSide_outer_10_2
  | exact second_1_coreSide_coreSide_10_0
  | exact second_1_coreSide_coreSide_10_2
  | exact second_1_coreSide_coreCorner_10_0
  | exact second_1_coreSide_coreCorner_10_2
  | exact second_1_coreCorner_outer_10_0
  | exact second_1_coreCorner_outer_10_1
  | exact second_1_coreCorner_outer_10_2
  | exact second_1_coreCorner_coreSide_10_0
  | exact second_1_coreCorner_coreSide_10_2
  | exact second_1_coreCorner_coreCorner_10_0
  | exact second_1_coreCorner_coreCorner_10_2
  | exact second_2_outer_outer_00_0
  | exact second_2_outer_outer_00_1
  | exact second_2_outer_outer_00_2
  | exact second_2_outer_outer_00_3
  | exact second_2_outer_coreSide_00_1
  | exact second_2_outer_coreSide_00_2
  | exact second_2_outer_coreSide_00_3
  | exact second_2_outer_coreCorner_00_1
  | exact second_2_outer_coreCorner_00_2
  | exact second_2_outer_coreCorner_00_3
  | exact second_2_coreSide_outer_00_0
  | exact second_2_coreSide_outer_00_1
  | exact second_2_coreSide_outer_00_2
  | exact second_2_coreSide_outer_00_3
  | exact second_2_coreSide_coreSide_00_1
  | exact second_2_coreSide_coreSide_00_2
  | exact second_2_coreSide_coreSide_00_3
  | exact second_2_coreSide_coreCorner_00_1
  | exact second_2_coreSide_coreCorner_00_2
  | exact second_2_coreSide_coreCorner_00_3
  | exact second_2_coreCorner_outer_00_0
  | exact second_2_coreCorner_outer_00_1
  | exact second_2_coreCorner_outer_00_2
  | exact second_2_coreCorner_outer_00_3
  | exact second_2_coreCorner_coreSide_00_1
  | exact second_2_coreCorner_coreSide_00_2
  | exact second_2_coreCorner_coreSide_00_3
  | exact second_2_coreCorner_coreCorner_00_1
  | exact second_2_coreCorner_coreCorner_00_2
  | exact second_2_coreCorner_coreCorner_00_3
  | exact second_2_outer_outer_01_0
  | exact second_2_outer_outer_01_1
  | exact second_2_outer_outer_01_2
  | exact second_2_outer_outer_01_3
  | exact second_2_outer_coreSide_01_1
  | exact second_2_outer_coreSide_01_2
  | exact second_2_outer_coreSide_01_3
  | exact second_2_outer_coreCorner_01_1
  | exact second_2_outer_coreCorner_01_2
  | exact second_2_outer_coreCorner_01_3
  | exact second_2_coreSide_outer_01_0
  | exact second_2_coreSide_outer_01_1
  | exact second_2_coreSide_outer_01_3
  | exact second_2_coreSide_coreSide_01_1
  | exact second_2_coreSide_coreSide_01_3
  | exact second_2_coreSide_coreCorner_01_1
  | exact second_2_coreSide_coreCorner_01_3
  | exact second_2_coreCorner_outer_01_0
  | exact second_2_coreCorner_outer_01_1
  | exact second_2_coreCorner_outer_01_3
  | exact second_2_coreCorner_coreSide_01_1
  | exact second_2_coreCorner_coreSide_01_3
  | exact second_2_coreCorner_coreCorner_01_1
  | exact second_2_coreCorner_coreCorner_01_3
  | exact second_3_outer_outer_00_0
  | exact second_3_outer_outer_00_1
  | exact second_3_outer_outer_00_2
  | exact second_3_outer_outer_00_3
  | exact second_3_outer_coreSide_00_1
  | exact second_3_outer_coreSide_00_2
  | exact second_3_outer_coreSide_00_3
  | exact second_3_outer_coreCorner_00_1
  | exact second_3_outer_coreCorner_00_2
  | exact second_3_outer_coreCorner_00_3
  | exact second_3_coreSide_outer_00_0
  | exact second_3_coreSide_outer_00_1
  | exact second_3_coreSide_outer_00_2
  | exact second_3_coreSide_outer_00_3
  | exact second_3_coreSide_coreSide_00_1
  | exact second_3_coreSide_coreSide_00_2
  | exact second_3_coreSide_coreSide_00_3
  | exact second_3_coreSide_coreCorner_00_1
  | exact second_3_coreSide_coreCorner_00_2
  | exact second_3_coreSide_coreCorner_00_3
  | exact second_3_coreCorner_outer_00_0
  | exact second_3_coreCorner_outer_00_1
  | exact second_3_coreCorner_outer_00_2
  | exact second_3_coreCorner_outer_00_3
  | exact second_3_coreCorner_coreSide_00_1
  | exact second_3_coreCorner_coreSide_00_2
  | exact second_3_coreCorner_coreSide_00_3
  | exact second_3_coreCorner_coreCorner_00_1
  | exact second_3_coreCorner_coreCorner_00_2
  | exact second_3_coreCorner_coreCorner_00_3
  | exact second_3_outer_outer_01_0
  | exact second_3_outer_outer_01_1
  | exact second_3_outer_outer_01_2
  | exact second_3_outer_outer_01_3
  | exact second_3_outer_coreSide_01_1
  | exact second_3_outer_coreSide_01_2
  | exact second_3_outer_coreSide_01_3
  | exact second_3_outer_coreCorner_01_1
  | exact second_3_outer_coreCorner_01_2
  | exact second_3_outer_coreCorner_01_3
  | exact second_3_coreSide_outer_01_0
  | exact second_3_coreSide_outer_01_1
  | exact second_3_coreSide_outer_01_3
  | exact second_3_coreSide_coreSide_01_1
  | exact second_3_coreSide_coreSide_01_3
  | exact second_3_coreSide_coreCorner_01_1
  | exact second_3_coreSide_coreCorner_01_3
  | exact second_3_coreCorner_outer_01_0
  | exact second_3_coreCorner_outer_01_1
  | exact second_3_coreCorner_outer_01_3
  | exact second_3_coreCorner_coreSide_01_1
  | exact second_3_coreCorner_coreSide_01_3
  | exact second_3_coreCorner_coreCorner_01_1
  | exact second_3_coreCorner_coreCorner_01_3
  | exact second_3_outer_outer_10_0
  | exact second_3_outer_outer_10_1
  | exact second_3_outer_outer_10_2
  | exact second_3_outer_outer_10_3
  | exact second_3_outer_coreSide_10_0
  | exact second_3_outer_coreSide_10_1
  | exact second_3_outer_coreSide_10_2
  | exact second_3_outer_coreSide_10_3
  | exact second_3_outer_coreCorner_10_0
  | exact second_3_outer_coreCorner_10_1
  | exact second_3_outer_coreCorner_10_2
  | exact second_3_outer_coreCorner_10_3
  | exact second_3_coreSide_outer_10_0
  | exact second_3_coreSide_outer_10_1
  | exact second_3_coreSide_outer_10_2
  | exact second_3_coreSide_outer_10_3
  | exact second_3_coreCorner_outer_10_0
  | exact second_3_coreCorner_outer_10_1
  | exact second_3_coreCorner_outer_10_2
  | exact second_3_coreCorner_outer_10_3
  | exact second_3_outer_outer_11_0
  | exact second_3_outer_outer_11_1
  | exact second_3_outer_outer_11_2
  | exact second_3_outer_outer_11_3
  | exact second_3_outer_coreSide_11_0
  | exact second_3_outer_coreSide_11_1
  | exact second_3_outer_coreSide_11_2
  | exact second_3_outer_coreSide_11_3
  | exact second_3_outer_coreCorner_11_0
  | exact second_3_outer_coreCorner_11_1
  | exact second_3_outer_coreCorner_11_2
  | exact second_3_outer_coreCorner_11_3
  | exact second_3_coreSide_outer_11_0
  | exact second_3_coreSide_outer_11_1
  | exact second_3_coreSide_outer_11_3
  | exact second_3_coreSide_coreSide_11_0
  | exact second_3_coreSide_coreSide_11_1
  | exact second_3_coreSide_coreSide_11_3
  | exact second_3_coreSide_coreCorner_11_0
  | exact second_3_coreSide_coreCorner_11_1
  | exact second_3_coreSide_coreCorner_11_3
  | exact second_3_coreCorner_outer_11_0
  | exact second_3_coreCorner_outer_11_1
  | exact second_3_coreCorner_outer_11_3
  | exact second_3_coreCorner_coreSide_11_0
  | exact second_3_coreCorner_coreSide_11_1
  | exact second_3_coreCorner_coreSide_11_3
  | exact second_3_coreCorner_coreCorner_11_0
  | exact second_3_coreCorner_coreCorner_11_1
  | exact second_3_coreCorner_coreCorner_11_3
  | exact second_4_outer_outer_00_0
  | exact second_4_outer_outer_00_1
  | exact second_4_outer_outer_00_2
  | exact second_4_outer_outer_00_3
  | exact second_4_outer_coreSide_00_2
  | exact second_4_outer_coreSide_00_3
  | exact second_4_outer_coreCorner_00_2
  | exact second_4_outer_coreCorner_00_3
  | exact second_4_coreSide_outer_00_0
  | exact second_4_coreSide_outer_00_1
  | exact second_4_coreSide_outer_00_2
  | exact second_4_coreSide_coreSide_00_2
  | exact second_4_coreSide_coreCorner_00_2
  | exact second_4_coreCorner_outer_00_0
  | exact second_4_coreCorner_outer_00_1
  | exact second_4_coreCorner_outer_00_2
  | exact second_4_coreCorner_coreSide_00_2
  | exact second_4_coreCorner_coreCorner_00_2
  | exact second_4_outer_outer_10_0
  | exact second_4_outer_outer_10_1
  | exact second_4_outer_outer_10_2
  | exact second_4_outer_outer_10_3
  | exact second_4_outer_coreSide_10_0
  | exact second_4_outer_coreSide_10_2
  | exact second_4_outer_coreSide_10_3
  | exact second_4_outer_coreCorner_10_0
  | exact second_4_outer_coreCorner_10_2
  | exact second_4_outer_coreCorner_10_3
  | exact second_4_coreSide_outer_10_0
  | exact second_4_coreSide_outer_10_1
  | exact second_4_coreSide_outer_10_2
  | exact second_4_coreSide_coreSide_10_0
  | exact second_4_coreSide_coreSide_10_2
  | exact second_4_coreSide_coreCorner_10_0
  | exact second_4_coreSide_coreCorner_10_2
  | exact second_4_coreCorner_outer_10_0
  | exact second_4_coreCorner_outer_10_1
  | exact second_4_coreCorner_outer_10_2
  | exact second_4_coreCorner_coreSide_10_0
  | exact second_4_coreCorner_coreSide_10_2
  | exact second_4_coreCorner_coreCorner_10_0
  | exact second_4_coreCorner_coreCorner_10_2
  | exact second_4_outer_outer_11_0
  | exact second_4_outer_outer_11_1
  | exact second_4_outer_outer_11_2
  | exact second_4_outer_outer_11_3
  | exact second_4_outer_coreSide_11_0
  | exact second_4_outer_coreSide_11_2
  | exact second_4_outer_coreSide_11_3
  | exact second_4_outer_coreCorner_11_0
  | exact second_4_outer_coreCorner_11_2
  | exact second_4_outer_coreCorner_11_3
  | exact second_4_coreSide_outer_11_0
  | exact second_4_coreSide_outer_11_1
  | exact second_4_coreSide_coreSide_11_0
  | exact second_4_coreSide_coreCorner_11_0
  | exact second_4_coreCorner_outer_11_0
  | exact second_4_coreCorner_outer_11_1
  | exact second_4_coreCorner_coreSide_11_0
  | exact second_4_coreCorner_coreCorner_11_0
  | exact second_5_outer_outer_00_0
  | exact second_5_outer_outer_00_1
  | exact second_5_outer_outer_00_2
  | exact second_5_outer_outer_00_3
  | exact second_5_outer_coreSide_00_1
  | exact second_5_outer_coreSide_00_2
  | exact second_5_outer_coreSide_00_3
  | exact second_5_outer_coreCorner_00_1
  | exact second_5_outer_coreCorner_00_2
  | exact second_5_outer_coreCorner_00_3
  | exact second_5_coreSide_outer_00_0
  | exact second_5_coreSide_outer_00_1
  | exact second_5_coreSide_outer_00_2
  | exact second_5_coreSide_outer_00_3
  | exact second_5_coreSide_coreSide_00_1
  | exact second_5_coreSide_coreSide_00_2
  | exact second_5_coreSide_coreSide_00_3
  | exact second_5_coreSide_coreCorner_00_1
  | exact second_5_coreSide_coreCorner_00_2
  | exact second_5_coreSide_coreCorner_00_3
  | exact second_5_coreCorner_outer_00_0
  | exact second_5_coreCorner_outer_00_1
  | exact second_5_coreCorner_outer_00_2
  | exact second_5_coreCorner_outer_00_3
  | exact second_5_coreCorner_coreSide_00_1
  | exact second_5_coreCorner_coreSide_00_2
  | exact second_5_coreCorner_coreSide_00_3
  | exact second_5_coreCorner_coreCorner_00_1
  | exact second_5_coreCorner_coreCorner_00_2
  | exact second_5_coreCorner_coreCorner_00_3
  | exact second_5_outer_outer_01_0
  | exact second_5_outer_outer_01_1
  | exact second_5_outer_outer_01_2
  | exact second_5_outer_outer_01_3
  | exact second_5_outer_coreSide_01_1
  | exact second_5_outer_coreSide_01_2
  | exact second_5_outer_coreSide_01_3
  | exact second_5_outer_coreCorner_01_1
  | exact second_5_outer_coreCorner_01_2
  | exact second_5_outer_coreCorner_01_3
  | exact second_5_coreSide_outer_01_0
  | exact second_5_coreSide_outer_01_1
  | exact second_5_coreSide_outer_01_3
  | exact second_5_coreSide_coreSide_01_1
  | exact second_5_coreSide_coreSide_01_3
  | exact second_5_coreSide_coreCorner_01_1
  | exact second_5_coreSide_coreCorner_01_3
  | exact second_5_coreCorner_outer_01_0
  | exact second_5_coreCorner_outer_01_1
  | exact second_5_coreCorner_outer_01_3
  | exact second_5_coreCorner_coreSide_01_1
  | exact second_5_coreCorner_coreSide_01_3
  | exact second_5_coreCorner_coreCorner_01_1
  | exact second_5_coreCorner_coreCorner_01_3
  | exact second_5_outer_outer_10_0
  | exact second_5_outer_outer_10_1
  | exact second_5_outer_outer_10_2
  | exact second_5_outer_outer_10_3
  | exact second_5_outer_coreSide_10_0
  | exact second_5_outer_coreSide_10_1
  | exact second_5_outer_coreSide_10_2
  | exact second_5_outer_coreSide_10_3
  | exact second_5_outer_coreCorner_10_0
  | exact second_5_outer_coreCorner_10_1
  | exact second_5_outer_coreCorner_10_2
  | exact second_5_outer_coreCorner_10_3
  | exact second_5_coreSide_outer_10_0
  | exact second_5_coreSide_outer_10_1
  | exact second_5_coreSide_outer_10_2
  | exact second_5_coreSide_outer_10_3
  | exact second_5_coreCorner_outer_10_0
  | exact second_5_coreCorner_outer_10_1
  | exact second_5_coreCorner_outer_10_2
  | exact second_5_coreCorner_outer_10_3
  | exact second_5_outer_outer_11_0
  | exact second_5_outer_outer_11_1
  | exact second_5_outer_outer_11_2
  | exact second_5_outer_outer_11_3
  | exact second_5_outer_coreSide_11_0
  | exact second_5_outer_coreSide_11_1
  | exact second_5_outer_coreSide_11_2
  | exact second_5_outer_coreSide_11_3
  | exact second_5_outer_coreCorner_11_0
  | exact second_5_outer_coreCorner_11_1
  | exact second_5_outer_coreCorner_11_2
  | exact second_5_outer_coreCorner_11_3
  | exact second_5_coreSide_outer_11_0
  | exact second_5_coreSide_outer_11_1
  | exact second_5_coreSide_outer_11_3
  | exact second_5_coreSide_coreSide_11_0
  | exact second_5_coreSide_coreSide_11_1
  | exact second_5_coreSide_coreSide_11_3
  | exact second_5_coreSide_coreCorner_11_0
  | exact second_5_coreSide_coreCorner_11_1
  | exact second_5_coreSide_coreCorner_11_3
  | exact second_5_coreCorner_outer_11_0
  | exact second_5_coreCorner_outer_11_1
  | exact second_5_coreCorner_outer_11_3
  | exact second_5_coreCorner_coreSide_11_0
  | exact second_5_coreCorner_coreSide_11_1
  | exact second_5_coreCorner_coreSide_11_3
  | exact second_5_coreCorner_coreCorner_11_0
  | exact second_5_coreCorner_coreCorner_11_1
  | exact second_5_coreCorner_coreCorner_11_3
  | exact second_6_outer_outer_01_0
  | exact second_6_outer_outer_01_1
  | exact second_6_outer_outer_01_2
  | exact second_6_outer_outer_01_3
  | exact second_6_outer_coreSide_01_1
  | exact second_6_outer_coreSide_01_2
  | exact second_6_outer_coreSide_01_3
  | exact second_6_outer_coreCorner_01_1
  | exact second_6_outer_coreCorner_01_2
  | exact second_6_outer_coreCorner_01_3
  | exact second_6_coreSide_outer_01_0
  | exact second_6_coreSide_outer_01_1
  | exact second_6_coreSide_outer_01_3
  | exact second_6_coreSide_coreSide_01_1
  | exact second_6_coreSide_coreSide_01_3
  | exact second_6_coreSide_coreCorner_01_1
  | exact second_6_coreSide_coreCorner_01_3
  | exact second_6_coreCorner_outer_01_0
  | exact second_6_coreCorner_outer_01_1
  | exact second_6_coreCorner_outer_01_3
  | exact second_6_coreCorner_coreSide_01_1
  | exact second_6_coreCorner_coreSide_01_3
  | exact second_6_coreCorner_coreCorner_01_1
  | exact second_6_coreCorner_coreCorner_01_3
  | exact second_6_outer_outer_11_0
  | exact second_6_outer_outer_11_1
  | exact second_6_outer_outer_11_2
  | exact second_6_outer_outer_11_3
  | exact second_6_outer_coreSide_11_0
  | exact second_6_outer_coreSide_11_1
  | exact second_6_outer_coreSide_11_2
  | exact second_6_outer_coreSide_11_3
  | exact second_6_outer_coreCorner_11_0
  | exact second_6_outer_coreCorner_11_1
  | exact second_6_outer_coreCorner_11_2
  | exact second_6_outer_coreCorner_11_3
  | exact second_6_coreSide_outer_11_0
  | exact second_6_coreSide_outer_11_1
  | exact second_6_coreSide_outer_11_3
  | exact second_6_coreSide_coreSide_11_0
  | exact second_6_coreSide_coreSide_11_1
  | exact second_6_coreSide_coreSide_11_3
  | exact second_6_coreSide_coreCorner_11_0
  | exact second_6_coreSide_coreCorner_11_1
  | exact second_6_coreSide_coreCorner_11_3
  | exact second_6_coreCorner_outer_11_0
  | exact second_6_coreCorner_outer_11_1
  | exact second_6_coreCorner_outer_11_3
  | exact second_6_coreCorner_coreSide_11_0
  | exact second_6_coreCorner_coreSide_11_1
  | exact second_6_coreCorner_coreSide_11_3
  | exact second_6_coreCorner_coreCorner_11_0
  | exact second_6_coreCorner_coreCorner_11_1
  | exact second_6_coreCorner_coreCorner_11_3

end SquaresInCircles.Eight.WordProblems

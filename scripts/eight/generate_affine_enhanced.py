#!/usr/bin/env python3
"""Share the coarse rows with their retained strict rational reserves."""
from pathlib import Path
import json
root=Path(__file__).resolve().parents[2]
d=json.loads((root/'research/eight/CANDIDATE_COARSE_MISMATCH_HAND_DATA.json').read_text())
count=(len(d['rows'])+4095)//4096
ns='SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch'
lines=['module','',f'public import {ns}.Cover',
       'public import SquaresInCircles.Eight.Candidate.Mismatch','',
       '/-! The coarse table with its retained per-edge reserves. Uncompiled.',
       'All expressions, state data, row intervals, and closed covers are shared. -/','',
       '@[expose] public section',f'namespace {ns}.Enhanced','open Arithmetic','',
       'def reserve : Vertex→ℚ := ![15/1000000,13/1000000,18/1000000,12/1000000,',
       '  15/1000000,23/1000000,6/1000000]',
       f'def meta : AffineTableMeta := {{{ns}.meta with',
       f'  target:=fun i => {ns}.meta.target i+reserve i}}',
       'def upgrade (r : AffineTableRow) : AffineTableRow :=',
       '  {r with lowerTarget:=r.lowerTarget+reserve r.edge}',
       'def upgradeProof (p : PreparedRow) : PreparedRow := {p with row:=upgrade p.row}',
       f'def rows : List AffineTableRow := {ns}.rows.map upgrade','']
for k in range(count):
    tag=f'{k:03d}'
    lines += ['set_option maxRecDepth 1000000 in','set_option maxHeartbeats 0 in',
        f'theorem proofRows{tag}_numeric : ∀ i : Fin {ns}.rows{tag}.length,',
        f'    (upgradeProof ({ns}.proofRow{tag} i)).NumericValid ∧',
        f'    (upgradeProof ({ns}.proofRow{tag} i)).Matches meta := by',
        '  decide','',
        f'theorem rowClaims{tag} : ∀ r∈{ns}.rows{tag}, (upgrade r).Claim meta := by',
        '  intro r hr','  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hr',
        f'  exact PreparedRow.claim (proofRows{tag}_numeric i).1 (proofRows{tag}_numeric i).2','']
lines += ['theorem all_row_claims : ∀ r∈rows, r.Claim meta := by',
    '  intro r hr','  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hr',
    f'  simp only [{ns}.rows,List.mem_append] at hr',
    '  rcases hr with '+' | '.join(f'h{k}' for k in range(count))]
lines += [f'  · exact rowClaims{k:03d} r h{k}' for k in range(count)]
lines += ['',f'def cover : AffineCover := {ns}.cover','',
    'set_option maxRecDepth 1000000 in','set_option maxHeartbeats 0 in',
    'theorem cover_numeric : cover.NumericValid meta rows := by','  decide','',
    'noncomputable def charged_bound (C : BoundaryCycle (meta.radius:ℝ))',
    '    (F : Candidate.Frame C)',
    '    (hcuts : ∀ i, (meta.cuts i).Mem (C.tangent i))',
    '    (hdiff : ∀ i, (meta.differenceRange i).Mem (Candidate.delta F.theta i))',
    '    (haxes : ∀ i j, (forwardAxis j).Feasible (C.square i) (C.square (next i)) →',
    '      ForwardAxis.ofIndex j∈meta.allowedAxes i) :',
    '    Candidate.ChargedBound C F Candidate.coarseBeta Candidate.enhancedGamma := by',
    '  have hw : ∀ i, (meta.word i:ℝ)=(Candidate.word i:ℝ) := by',
    f'    intro i; fin_cases i <;> norm_num [meta,{ns}.meta,Candidate.word]',
    '  have hb : ∀ i, (meta.charge i:ℝ)=Candidate.charge Candidate.coarseBeta i := by',
    f'    intro i; fin_cases i <;> norm_num [meta,{ns}.meta,Candidate.charge,Candidate.charged,Candidate.coarseBeta]',
    '  have P := cover.chargedBound cover_numeric all_row_claims C F Candidate.coarseBeta hw hb hcuts hdiff haxes',
    f'  simpa [meta,{ns}.meta,reserve,Candidate.enhancedGamma,Candidate.coarseGamma,Candidate.retainedReserve] using P','',
    f'end {ns}.Enhanced','']
(root/'SquaresInCircles/Eight/Generated/Affine/CandidateCoarseMismatch/Enhanced.lean').write_text('\n'.join(lines))

#!/usr/bin/env python3
"""Independently audit report accounting against immutable literal rounds.

This does not reprove any bound. It checks cumulative continuation accounting,
SHA reuse, and separates retained ancestry from newly appended local rounds.
"""
from collections import defaultdict
from hashlib import sha256
from pathlib import Path
import argparse,json
sha=lambda p:sha256(Path(p).read_bytes()).hexdigest()
canon=lambda v:sha256(json.dumps(v,sort_keys=True,separators=(',',':')).encode()).hexdigest()
FIELDS=('bound_rounds','bound_deductions','printed_rows_checked','terminal_rows')
def audit(packet,report_path,output):
 packet=Path(packet).resolve();report_path=Path(report_path).resolve();output=Path(output).resolve();assert not output.exists()
 raw_report=report_path.read_bytes();report=json.loads(raw_report)
 manifest_path=packet/'ASSEMBLY_MANIFEST.json';manifest_bytes=manifest_path.read_bytes();files=json.loads(manifest_bytes)['files'];byhash=defaultdict(list)
 for name,h in files.items():byhash[h].append(name)
 records={};entries=[];rounds={};repeated_rounds=[];continued_prefix_in_counted_records=[]
 def record(h):
  if h not in records:
   names=sorted(byhash[h],key=lambda n:(not n.startswith('data'),len(n),n));p=packet/names[0]
   assert sha(p)==h;records[h]=(p,json.loads(p.read_text()))
  return records[h]
 groups=defaultdict(lambda:{k:0 for k in FIELDS})
 for h,proof in report['exact_bound_reports'].items():
  assert proof['certificate_sha256']==h
  path,raw=record(h);assert raw['id']==report['original_id']and raw['path']==report['original_path']
  rr=raw['rounds'];induction_rows=sum(len(r['printed_rows'])for r in rr);deductions=sum(len(r['proposals'])for r in rr)
  terminal=raw.get('terminal',{})
  assert not('printed_rows'in terminal and 'rows'in terminal)
  terminal_rows=len(terminal.get('printed_rows',terminal.get('rows',[])))
  expected=dict(bound_rounds=len(rr),bound_deductions=deductions,printed_rows_checked=induction_rows+terminal_rows,terminal_rows=terminal_rows)
  for key in FIELDS:assert proof[key]==expected[key],('literal_count_mismatch',h,key,proof[key],expected[key])
  domain={k:raw[k]for k in('id','path','prior','derived_H_cover','slope_restriction')if k in raw}
  inherited=0;continuation=raw.get('derived_H_continuation')or raw.get('continuation')
  if continuation:
   inherited=continuation.get('inherited_local_rounds',continuation.get('inherited_rounds'))
   assert type(inherited)is int and 0<=inherited<=len(rr)
   prefix_sha=continuation['sha256'];prefix_path,prefix=record(prefix_sha)
   assert rr[:inherited]==prefix['rounds']and len(prefix['rounds'])==inherited
   assert {k:prefix[k]for k in domain if k in prefix}==domain
   if prefix_sha in report['exact_bound_reports']:
    continued_prefix_in_counted_records.append(dict(continuation=h,prefix=prefix_sha,retained_rounds=inherited))
  for k,r in enumerate(rr):
   key=canon(dict(domain=domain,round=r))
   if key in rounds:repeated_rounds.append(dict(first=rounds[key],duplicate=[h,k]))
   else:rounds[key]=[h,k]
  group='restricted_slope_local'if'slope_restriction'in raw else'normal_H_local'if'derived_H_cover'in raw else'fixed_I_local'
  for key in FIELDS:groups[group][key]+=expected[key]
  old=rr[:inherited];fresh=rr[inherited:]
  entries.append(dict(certificate_sha256=h,certificate=str(path.relative_to(packet)),group=group,
   cumulative_record_totals=expected,retained_continuation_rounds=inherited,
   retained_continuation_deductions=sum(len(r['proposals'])for r in old),
   retained_continuation_premise_rows=sum(len(r['printed_rows'])for r in old),
   newly_appended_local_rounds=len(fresh),newly_appended_local_deductions=sum(len(r['proposals'])for r in fresh),
   newly_appended_local_premise_rows=sum(len(r['printed_rows'])for r in fresh)))
 totals={k:sum(e['cumulative_record_totals'][k]for e in entries)for k in FIELDS}
 assert totals==report['bound_record_totals']
 assert not repeated_rounds,'The component-report sum repeats one literal round on the same exact domain.'
 assert not continued_prefix_in_counted_records,'A cumulative continuation and its literal prefix were both counted.'
 split={key:sum(e[key]for e in entries)for key in('retained_continuation_rounds','retained_continuation_deductions','retained_continuation_premise_rows','newly_appended_local_rounds','newly_appended_local_deductions','newly_appended_local_premise_rows')}
 assert split['retained_continuation_rounds']+split['newly_appended_local_rounds']==totals['bound_rounds']
 assert split['retained_continuation_deductions']+split['newly_appended_local_deductions']==totals['bound_deductions']
 assert split['retained_continuation_premise_rows']+split['newly_appended_local_premise_rows']+totals['terminal_rows']==totals['printed_rows_checked']
 for name,h in files.items():assert sha(packet/name)==h
 assert manifest_path.read_bytes()==manifest_bytes and report_path.read_bytes()==raw_report
 result=dict(schema='Dc71_literal_round_continuation_accounting_audit_v1',status='PASS_NO_CONTINUATION_PREFIX_DOUBLE_COUNTING',
  exact_report_sha256=sha256(raw_report).hexdigest(),assembly_manifest_sha256=sha256(manifest_bytes).hexdigest(),
  outer_checker_sha256=report['checker_sha256'],reviewer_sha256=sha(__file__),
  distinct_counted_records=len(entries),literal_rounds_counted_once=len(rounds),totals=totals,
  grouped_current_record_totals=dict(groups),retained_versus_newly_appended_rounds=split,
  repeated_literal_rounds=repeated_rounds,counted_continuation_prefix_overlaps=continued_prefix_in_counted_records,
  entries=entries,all_frozen_inputs_and_report_unchanged=True,
  scope='Accounting audit only. Retained original-prefix induction remains in the separately replayed ancestry and is not mislabeled as new fixed-tile work. These totals count selected exact component records once; each continuation includes its retained rounds once, without a second count of its old prefix.',
  new_original_cells=0,new_masks=0,lean_lake_ci_run=False)
 output.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({k:result[k]for k in('status','distinct_counted_records','literal_rounds_counted_once','totals','retained_versus_newly_appended_rounds')}))
if __name__=='__main__':
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('packet',type=Path);p.add_argument('report',type=Path);p.add_argument('output',type=Path);a=p.parse_args();audit(a.packet,a.report,a.output)

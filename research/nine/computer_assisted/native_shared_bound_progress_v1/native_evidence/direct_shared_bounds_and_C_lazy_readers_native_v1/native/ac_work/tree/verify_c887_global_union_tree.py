#!/usr/bin/env python3
"""Exact complete C cover plus fresh whole-original SAT-union bound replay."""
from pathlib import Path
from fractions import Fraction as F
from copy import deepcopy
import argparse,json,sys
import verify_c887_all_guards_v3 as BASE
import verify_ac_whole_original_sat_shave as SOURCE
import independent_certified_union_original_rows as ROWS

OLD=BASE.OLD
_configuration=None
_checker=None

class Checker(BASE.Checker):
    def __init__(self):
        global _checker
        super().__init__();assert _configuration is not None
        folder,reference,report_path,report,state=_configuration
        assert OLD.sha(folder/'manifest.json')==reference['manifest_sha256']
        assert state is not None
        assert state['id']==reference['original_id']and state['path']==reference['original_path']
        assert state['id']==OLD.TARGET and state['path']==OLD.TARGET_PATH
        self.union_state=deepcopy(state);self.union_source_report=report
        self.union_sha=reference['manifest_sha256'];self.union_row_occurrences=0;_checker=self

class Adapter(BASE.Adapter):
    def rebuild(self,state,printed):
        parent=self.checker.union_state
        assert state['id']==parent['id']and state['path'][:len(parent['path'])]==parent['path']
        ordinary=[r for r in printed if not r['name'].startswith(ROWS.PREFIX)]
        answer,bounds,propagated=super().rebuild(state,ordinary)
        for r in printed:
            if not r['name'].startswith(ROWS.PREFIX):continue
            literal=(tuple((k,F(v))for k,v in r['coefficients']),F(r['rhs']),r['name'])
            ROWS.verify_literal(literal,parent,self.checker.union_sha)
            assert r['index']not in answer;answer[r['index']]=literal;self.checker.union_row_occurrences+=1
        return answer,bounds,propagated

def replay(parent,tree,output):
    global _configuration
    tree=Path(tree).resolve();m=json.loads((tree/'manifest.json').read_text());ref=m['global_original_union']
    folder=Path(ref['folder']);report_path=Path(output).with_name(Path(output).stem+'_SOURCE_UNION_REPLAY.json')
    assert OLD.sha(folder/'manifest.json')==ref['manifest_sha256']
    source_report,source_state=SOURCE.replay(folder,report_path);assert source_state is not None
    _configuration=(folder,ref,report_path,source_report,source_state)
    OLD.Checker=Checker;OLD.Adapter=Adapter
    report=BASE.replay(parent,tree,output);assert _checker is not None
    report.update(certified_global_union_row_occurrences_checked=_checker.union_row_occurrences,
        whole_original_source_union_replay=_checker.union_source_report,
        whole_original_source_union_manifest_sha256=_checker.union_sha,
        source_union_replay_report_sha256=OLD.sha(report_path))
    for p in(__file__,SOURCE.__file__,ROWS.__file__):report['checker_dependency_sha256'][str(Path(p).resolve())]=OLD.sha(p)
    assert not any(n in sys.modules for n in('ac_physical_global_union_runtime','certified_union_original_rows'))
    Path(output).write_text(json.dumps(report,indent=2)+'\n');return report

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('parent',type=Path);p.add_argument('tree',type=Path);p.add_argument('output',type=Path)
    a=p.parse_args();replay(a.parent,a.tree,a.output)

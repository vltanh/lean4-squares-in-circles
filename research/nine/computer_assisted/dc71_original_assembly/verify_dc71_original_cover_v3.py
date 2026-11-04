#!/usr/bin/env python3
"""Strict complete/explicit-partial Dc71 original assembly, with recursive slope covers.

This module supplies coverage and immutable caller attachment only.  Every
physical induction and terminal is delegated to the pinned unchanged exact
checkers.  An OPEN state can be retained in a checkpoint but never promoted.
"""
from collections import Counter
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from pathlib import Path
import argparse
import importlib
import json
import subprocess
import sys
import time

ID='positive-c71dc2feef1abb0b'
PATH=[['angle',3,1],['angle_cut',[0,'0'],1],['alternate_four_escape',[1,7],[2]]]
PREFIX='3d5c6def24cd920103c2a26b81d4f898e135cda0b125a2eea87a8880fee840fa'
SLOPE_SCHEMA='CD_inherited_slope_affine_bound_discovery_v1'
H_SCHEMAS=('CD_proved_I_state_H_subcover_bound_discovery_v1',
           'CD_proved_I_state_H_subcover_bound_continuation_discovery_v1')
PARENTS={(1,0):'ffec90e294ac1175f987e03d99f870987d63f0ee5798fa8b20baa185bddf220c',
 (1,1):'5f99a70bf711b844c7958934d662688b2dd0a96aaad38f8f9896930ebca529b2',
 (1,2):'5f47f999555be6ac45b0becce96c06ef4c31e3e8f032b33bdbed0cfaf3a01719',
 (1,3):'db36b83c09c7a719a77720ca34f282e808fcd966bd29349fa897a84f1fe319ec',
 (2,1):'b2cc82f8e68f41d6cc0819ee5eebf394ecfb294887d8d12f08f410bfe157a705',
 (2,2):'aa42c473eeb96b880d5b757e1308e04beae1fcfdce3fdceaccdc514ef3bf18a8',
 (2,3):'1f5b8a5d8b4302c71e741d3ba3446da76f35db021da1943b41780008f06cba04'}
PINS={
 'verify_cd_triple_energy_recursive_bounds.py':'e73773f57e99797edcf5ee9726000c57ce212936b853c75247ff63ce9f16e0f4',
 'verify_dc71_energy_derived_h_continued_bounds.py':'f0572c7a8ee407a5b8fa426445be709c19b5f87b922cd4fb160117e02c5bb038',
 'verify_dc71_derived_H_slope_bounds.py':'2f8735901cdd74be4e68eaba14de8a21e62f3fa365bf5c2659d85ecc90a9f6a3',
 'verify_dc71_fast6_energy_derived_h_bounds.py':'f5624b46b0f359c251ebf96379fb5c59171a80c0f1de61fee3bbfbbb30149ade',
 'verify_dc71_initial_difference_terminals.py':'791febc12e94354163d9c2f995ba81506d552cafc18c663312259be9d3f1a493',
 'verify_dc71_derived_H_difference_terminals.py':'c7c788ee9809c5048efb9c643282da9e5c47c45ed58c21d7f4ca0e60472399f5',
 'verify_dc71_finished_H_prefix_difference_terminal.py':'02a6057cb678d3a21a5c64889b484d965b03168820cd637f0214c861b3df4b95',
 'independent_three_square_energy_rows.py':'d7f0e356bf268e6c9396287c1d1cadbebc32505b6dd71771e999f918baba5edc',
 'energy_proof/verify_all.py':'3ba968b5697568df8b5f06519f234608036cf0eb85f6b3d67be6cbca3c5f0488'}
SHARP_PINS={
 'shared_strict_row_terminal.py':'43a74c66c7c0b91da76e6577ce511e6ae8de7bda9ab6e0adbf81a1cc2b013d43',
 'hand_inputs/SHARED_ABID_STRICT_BOUNDARY_TERMINAL.md':'a4b923589a52be57fb84e484c92f4438c275dbc13e5b01a8e9add9d4dd40edcb',
 'hand_inputs/ALL_SIGN_CORRELATED_CORNER_ROW_HAND_STRENGTHENING.md':'0d233bddea414938482cb312519da061a546d26c4ee5a5bb83a14b48c178ed02'}
PINS.update(SHARP_PINS)
FINISHED_PREFIX='bbf5ac672a800b1a791935960c0c731a6ecbebb0772fbb7f16afc99fe4551a0b'
DIRECT_H={(1,0,0,2),(1,1,0,2),(1,1,1,0),(1,2,0,2),(1,3,0,2)}
OPEN_STATUSES={'PASS_CERTIFIED_TILE_STATE_OPEN','PASS_CERTIFIED_RESTRICTED_TILE_STATE_OPEN'}
CLOSED_STATUSES={'PASS_COMPLETE_PHYSICAL_TILE','PASS_COMPLETE_RESTRICTED_PHYSICAL_TILE'}
digest=lambda p:sha256(Path(p).read_bytes()).hexdigest()

def value_digest(value):
    return sha256(json.dumps(value,sort_keys=True,separators=(',',':')).encode()).hexdigest()

def view(box):return [list(map(str,ab))for ab in box]

def interval(lo,hi,index,parts):
    assert type(index)is int and type(parts)is int and 0<=index<parts and 2<=parts<=16
    lo,hi=F(lo),F(hi);assert lo<=hi
    return [str(lo+(hi-lo)*F(index,parts)),str(lo+(hi-lo)*F(index+1,parts))]

def rectangle(box,tile,parts):
    assert len(box)==len(tile)==len(parts)==2
    return [interval(*ab,index,count)for ab,index,count in zip(box,tile,parts)]

def validate_slope_child(parent_literal,parent_hash,parent_state,original,parts,index,child):
    """Pure complete-child attachment check, also exercised by focused tests."""
    assert type(original)is int and 0<=original<9
    assert type(parts)is int and 2<=parts<=16
    assert type(index)is int and 0<=index<parts
    assert child['schema']==SLOPE_SCHEMA
    assert child['id']==parent_literal['id']==ID and child['path']==parent_literal['path']==PATH
    assert child['prior']==parent_literal['prior']
    r=child['slope_restriction']
    assert r['kind']=='original_slope_closed_equal_partition'
    assert r['all_other_inherited_bounds_retained']is True
    assert r['parent']['sha256']==parent_hash and r['parent']['schema']==parent_literal['schema']
    assert r['original']==original and r['parts']==parts and r['index']==index
    lo,hi=parent_state['angles'][original];assert lo<hi
    assert r['parent_interval']==list(map(str,(lo,hi)))
    expected=interval(lo,hi,index,parts);assert r['interval']==expected
    return expected

class Assembly:
    def __init__(self,packet,index_name='DC71_ORIGINAL_COVER_INDEX.json',output_name='assembly_replay'):
        self.packet=Path(packet).resolve();assert Path(__file__).resolve().is_relative_to(self.packet)
        self.manifest_path=self.packet/'ASSEMBLY_MANIFEST.json'
        self.manifest_bytes=self.manifest_path.read_bytes()
        self.files=json.loads(self.manifest_bytes)['files'];self.touched={}
        self.index_path=self.path(index_name);self.index_bytes=self.index_path.read_bytes()
        self.index=json.loads(self.index_bytes)
        assert self.files[index_name]==sha256(self.index_bytes).hexdigest()
        assert self.files[Path(__file__).name]==digest(__file__)
        self.core_bytes=(self.packet/'SHA256_MANIFEST.json').read_bytes()
        assert self.index['core_manifest_sha256']==sha256(self.core_bytes).hexdigest()
        for name,h in json.loads(self.core_bytes)['files'].items():assert self.files[name]==h
        for name,h in PINS.items():assert self.files[name]==h and digest(self.path(name))==h
        self.unchanged()
        self.output=self.path(output_name,require_input=False);assert not self.output.exists()
        self.output.mkdir()
        sys.path.insert(0,str(self.packet))
        R=importlib.import_module('verify_cd_triple_energy_recursive_bounds')
        S=importlib.import_module('verify_dc71_derived_H_slope_bounds')
        for module,name in ((R,'verify_cd_triple_energy_recursive_bounds.py'),(S,'verify_dc71_derived_H_slope_bounds.py')):
            assert Path(module.__file__).resolve()==self.packet/name
        self.ordinary=R.Checker(self.packet,self.packet/'ancestry',self.packet)
        self.slope=S.Checker(self.packet,self.packet/'ancestry',self.packet)
        self.cache={};self.active=set();self.bound_reports={};self.tables=[];self.open_leaves=[]

    def path(self,name,require_input=True):
        assert isinstance(name,str)and not Path(name).is_absolute()and '..'not in Path(name).parts
        p=(self.packet/name).resolve();assert p.is_relative_to(self.packet)
        if require_input:
            assert name in self.files and digest(p)==self.files[name]
            self.register(p,self.files[name])
        return p

    def register(self,path,expected):
        path=Path(path).resolve();assert path.is_relative_to(self.packet)
        name=str(path.relative_to(self.packet));assert self.files[name]==expected and digest(path)==expected
        assert name not in self.touched or self.touched[name]==expected
        self.touched[name]=expected

    def binding(self,binding):
        assert set(binding)=={'file','sha256'}
        path=self.path(binding['file']);assert digest(path)==binding['sha256']
        self.register(path,binding['sha256']);return path,json.loads(path.read_text())

    def unchanged(self):
        assert self.manifest_path.read_bytes()==self.manifest_bytes
        assert self.index_path.read_bytes()==self.index_bytes
        assert (self.packet/'SHA256_MANIFEST.json').read_bytes()==self.core_bytes
        for name,h in self.files.items():
            p=(self.packet/name).resolve();assert p.is_relative_to(self.packet)
            assert not Path(name).is_absolute()and '..'not in Path(name).parts
            assert digest(p)==h,('changed_frozen_assembly_input',name)
        for name,h in self.touched.items():assert digest(self.packet/name)==h

    def dependency_path(self,name):
        # Reports may already contain absolute relocated packet paths.  These
        # need no historical rebinding; register() still enforces the inventory,
        # expected hash and final unchanged-byte checks.  Every other spelling
        # must pass the unchanged component's explicit historical bindings.
        path=Path(name)
        if path.is_absolute()and path.resolve().is_relative_to(self.packet):
            return path.resolve()
        return self.slope.locate(name)

    def dependencies(self,value):
        if isinstance(value,dict):
            for key in('source_sha256','checker_dependency_sha256'):
                mapping=value.get(key)
                if isinstance(mapping,dict):
                    for name,h in mapping.items():
                        resolved=self.dependency_path(name)
                        self.register(resolved,h)
            if all(k in value for k in('certificate_sha256','bound_rounds','bound_deductions','printed_rows_checked','terminal_rows')):
                h=value['certificate_sha256']
                if h in self.bound_reports:
                    for k in('bound_rounds','bound_deductions','printed_rows_checked','terminal_rows'):
                        assert self.bound_reports[h][k]==value[k],('inconsistent_duplicate_bound_report',h,k)
                self.bound_reports[h]=value
            for child in value.values():
                if isinstance(child,(dict,list)):self.dependencies(child)
        elif isinstance(value,list):
            for child in value:self.dependencies(child)

    def component(self,binding,ordinary=False):
        path,literal=self.binding(binding);h=binding['sha256'];key=(h,ordinary)
        assert literal['id']==ID and literal['path']==PATH
        assert key not in self.active,'cyclic component ancestry'
        if key not in self.cache:
            self.active.add(key)
            try:
                checker=self.ordinary if ordinary else self.slope
                report,state,diagonal=checker.replay(path,allow_open=True,return_state=True)
                assert report['certificate_sha256']==h and report['id']==ID and report['original_parent_path']==PATH
                assert report['status']in OPEN_STATUSES|CLOSED_STATUSES
                if report['status']in OPEN_STATUSES:
                    assert literal['status']=='OPEN'and 'terminal'not in literal
                    assert literal['final']==checker.view(state,diagonal)
                    assert literal['final_test']['round']==len(literal['rounds'])
                    assert literal['final_test']['proposals']==[]
                    assert literal['final_test']['before']==literal['final']
                    checker.reconstruct(literal['final_test'],state,diagonal)
                self.dependencies(report);self.cache[key]=(report,state,diagonal)
                # Cache only states already fully replayed above. The unchanged
                # component checks their parent hashes again at every reuse.
                if not ordinary and report['status']in OPEN_STATUSES and literal['schema']in(H_SCHEMAS[1],SLOPE_SCHEMA):
                    self.slope.inherited_records[h]=(report,state,diagonal)
            finally:self.active.remove(key)
        assert digest(path)==h
        for name,expected in self.touched.items():assert digest(self.packet/name)==expected
        return literal,*self.cache[key]

    def run_script(self,name,args,tag):
        script=self.path(name);log=self.output/(tag+'.log')
        with log.open('w')as stream:
            subprocess.run([sys.executable,'-B','-S',str(script),*map(str,args)],cwd=self.packet,
                           stdout=stream,stderr=subprocess.STDOUT,check=True)
        self.unchanged()

    def primitive_replays(self):
        self.run_script('energy_proof/verify_all.py',[],'energy')
        energy=json.loads((self.packet/'energy_proof/COMPLETE_REPLAY.json').read_text())
        assert energy['status']=='PASS_SHARED_THREE_SQUARE_ENERGY_ROWS'and energy['energy_lower_bound']=='7/2'
        assert energy['exact_geometric_evaluators']==2 and energy['row_identities_checked']==1877
        reports={}
        for name,tag in (('verify_dc71_initial_difference_terminals.py','initial_I'),
                         ('verify_dc71_derived_H_difference_terminals.py','initial_H')):
            out=self.output/(tag+'.json');self.run_script(name,['--context',self.packet,'--report',out],tag)
            report=json.loads(out.read_text());assert report['id']==ID and report['original_parent_path']==PATH
            assert report['original_prefix_sha256']==PREFIX
            self.dependencies(report);reports[tag]=report
        source,_=self.binding(self.index['finished_H_prefix'])
        assert digest(source)==FINISHED_PREFIX
        out=self.output/'finished_H_prefix.json'
        self.run_script('verify_dc71_finished_H_prefix_difference_terminal.py',
                        [source,'--context',self.packet,'--report',out],'finished_H_prefix')
        finished=json.loads(out.read_text())
        assert finished['status']=='PASS_COMPLETE_PHYSICAL_H_RECTANGLE'and finished['id']==ID
        assert finished['original_parent_path']==PATH and finished['tile']==[1,2,0,0]
        assert finished['certificate_sha256']==FINISHED_PREFIX
        assert finished['unfinished_round_admitted']is False and finished['raw_interrupted_record_modified']is False
        assert finished['witnesses']and all(F(w['strict_gap'])>0 for w in finished['witnesses'])
        self.dependencies(finished)
        assert reports['initial_I']['status']=='PASS_ALL_LISTED_PHYSICAL_TILES'
        self.direct_I={tuple(r['tile']):r for r in reports['initial_I']['tile_reports']}
        assert set(self.direct_I)=={(0,1),(0,2)}
        self.direct_H={tuple(r['tile']):r for r in reports['initial_H']['H_reports']if r['status']=='PASS_COMPLETE_PHYSICAL_H_RECTANGLE'}
        assert set(self.direct_H)==DIRECT_H
        self.finished=finished
        return dict(energy=energy,initial_I=reports['initial_I'],initial_H=reports['initial_H'],finished_H_prefix=finished)

    def h_scope(self,report,tile,Ibox,Hbox,common):
        assert report['id']==ID and report['original_parent_path']==PATH
        assert report['tile']==list(tile) and report['rectangle']==Ibox and report['h_rectangle']==Hbox
        ancestor=report
        while 'inherited_bound_parent_replay'in ancestor:
            facts=ancestor['inherited_parent_facts']
            assert facts['original_prefix_sha256']==PREFIX and facts['original_tile']==list(tile)
            assert facts['all_other_inherited_bounds_retained']is True
            ancestor=ancestor['inherited_bound_parent_replay']
        assert ancestor['derived_parent_facts']==common
        assert ancestor['original_prefix_replay']['certificate_sha256']==PREFIX

    def accepted_sharp_guard(self,literal,report,state,diagonal):
        # This is a fresh terminal on the same already-replayed OPEN physical
        # state.  The immutable OPEN certificate itself is never relabeled.
        assert report['status']in OPEN_STATUSES and literal['status']=='OPEN'
        assert literal['id']==state['id']==ID and literal['path']==state['path']==PATH
        assert report['original_prefix_replay']['certificate_sha256']==PREFIX
        for name,expected in SHARP_PINS.items():self.register(self.path(name),expected)
        sharp=importlib.import_module('shared_strict_row_terminal')
        assert Path(sharp.__file__).resolve()==self.packet/'shared_strict_row_terminal.py'
        assert digest(sharp.__file__)==SHARP_PINS['shared_strict_row_terminal.py']
        rr=literal['final_test'];assert rr['round']==len(literal['rounds'])and rr['proposals']==[]
        base,bounds,pos,scalar,differences,guards=self.slope.reconstruct(rr,state,diagonal)
        physical=dict(state,positions=pos,scalar=scalar,differences=differences)
        guard=sharp.evaluate_any_guard(physical)
        assert guard['status']=='PASS_SHARP_PHYSICAL_ROW_GUARD'
        assert guard['strict_radius_excluded']is True and guard['closed_Q_strict_weak_bit_excluded']is True
        for name,expected in SHARP_PINS.items():self.register(self.path(name),expected)
        return dict(kind='accepted_shared_sharp_boundary_terminal',guard=guard,
            independently_replayed_OPEN_state_sha256=report['certificate_sha256'],
            strict_original_Dc71_caller_replayed=True,all_nine_originals_retained=True,
            immutable_OPEN_record_status_retained=True,physical_theorem_sha256=dict(SHARP_PINS))

    def tree(self,node,tile,Ibox,Hbox,common,address,ancestors=()):
        assert node['kind']in('terminal','open','slope_cover','accepted_sharp_guard')
        literal,report,state,diagonal=self.component(node['bound'])
        h=node['bound']['sha256'];assert h not in ancestors,'cyclic cover attachment'
        self.h_scope(report,tile,Ibox,Hbox,common)
        summary=dict(address=address,full_HI_tile=list(tile),bound=node['bound'],kind=node['kind'],
                     bound_rounds=report['bound_rounds'],deductions=report['bound_deductions'],
                     total_printed_rows=report['printed_rows_checked'],terminal_rows=report['terminal_rows'],
                     terminal_kind=report['terminal_kind'],reserve=report['reserve'])
        if node['kind']=='terminal':
            assert set(node)=={'kind','bound'} and report['status']in CLOSED_STATUSES
            summary['closed']=True;self.tables.append(summary);return summary
        assert report['status']in OPEN_STATUSES
        if node['kind']=='accepted_sharp_guard':
            assert set(node)=={'kind','bound'}
            evidence=self.accepted_sharp_guard(literal,report,state,diagonal)
            summary.update(closed=True,terminal_kind=evidence['kind'],terminal_evidence=evidence)
            self.tables.append(summary);return summary
        if node['kind']=='open':
            assert set(node)=={'kind','bound'}
            summary['closed']=False;self.tables.append(summary);self.open_leaves.append(summary);return summary
        assert set(node)=={'kind','bound','original','parts','children'}
        assert literal['schema']in(H_SCHEMAS[1],SLOPE_SCHEMA)
        original,parts=node['original'],node['parts']
        assert type(original)is int and 0<=original<9 and type(parts)is int and 2<=parts<=16
        children=node['children'];assert len(children)==parts
        assert [child['index']for child in children]==list(range(parts))
        results=[];intervals=[]
        for entry in children:
            assert set(entry)=={'index','node'}
            _,child=self.binding(entry['node']['bound'])
            intervals.append(validate_slope_child(literal,h,state,original,parts,entry['index'],child))
            parent_path=self.slope.locate(child['slope_restriction']['parent']['path'])
            assert digest(parent_path)==h and json.loads(parent_path.read_text())==literal
            self.register(parent_path,h)
            result=self.tree(entry['node'],tile,Ibox,Hbox,common,address+[dict(original=original,parts=parts,index=entry['index'])],ancestors+(h,))
            results.append(result)
        lo,hi=state['angles'][original]
        assert intervals[0][0]==str(lo)and intervals[-1][1]==str(hi)
        assert all(left[1]==right[0]for left,right in zip(intervals,intervals[1:]))
        summary.update(closed=all(r['closed']for r in results),split_original=original,parts=parts,
                       closed_intervals=intervals,children=results,conditional_parent_only=True)
        return summary

    def verify(self):
        started=time.monotonic();index=self.index
        assert index['schema']=='Dc71_full_original_fixed_I_H_recursive_slope_cover_v1'
        assert index['original_id']==ID and index['original_path']==PATH
        assert index['original_I_parts']==[4,4]and index['derived_H_parts']==[2,4]
        assert index['original_cell_denominator']==231 and index['mask_denominator']==32
        assert index['original_count']==9 and index['original_corner_count']==36 and index['original_pair_count']==36
        assert index['original_strict_weak_CD_retained']is True
        prefix_path,literal=self.binding(index['original_prefix'])
        assert index['original_prefix']['sha256']==PREFIX and literal['id']==ID and literal['path']==PATH
        original_report,original,original_diagonal=self.ordinary.D.replay(prefix_path)
        assert original_report['status']=='PASS_CERTIFIED_PARENT_STATE_OPEN'and original_report['certificate_sha256']==PREFIX
        assert original['id']==ID and original['path']==PATH
        primitives=self.primitive_replays()
        members=index['I_members'];assert len(members)==16
        assert [m['tile']for m in members]==[list(t)for t in product(range(4),repeat=2)]
        results=[];H_count=0;split_parents=set()
        for m in members:
            tile=tuple(m['tile']);Ibox=rectangle(original['positions'][16:18],tile,(4,4))
            if m['kind']=='initial_I_difference':
                assert set(m)=={'tile','kind'}and tile in self.direct_I
                r=self.direct_I[tile];assert r['rectangle']==Ibox and r['closed_faces_retained']is True
                assert r['status']=='PASS_COMPLETE_PHYSICAL_TILE'
                assert r['witnesses']and all(F(w['strict_gap'])>0 for w in r['witnesses'])
                result=dict(tile=list(tile),kind=m['kind'],rectangle=Ibox,closed=True,terminal_evidence=r)
            elif m['kind']=='I_terminal':
                assert set(m)=={'tile','kind','bound'}
                raw,r,state,diag=self.component(m['bound'],ordinary=True)
                assert r['status']=='PASS_COMPLETE_PHYSICAL_TILE'and r['tile']==list(tile)
                assert r['closed_cover_parts']==[4,4]and r['rectangle']==Ibox and r['h_rectangle']is None
                assert r['original_prefix_replay']['certificate_sha256']==PREFIX
                result=dict(tile=list(tile),kind=m['kind'],rectangle=Ibox,closed=True,bound=m['bound'])
            else:
                assert m['kind']=='derived_H_cover'and set(m)=={'tile','kind','parent','children'}
                assert tile in PARENTS and m['parent']['sha256']==PARENTS[tile];split_parents.add(tile)
                raw,parent,state,diag=self.component(m['parent'],ordinary=True)
                assert parent['status']=='PASS_CERTIFIED_TILE_STATE_OPEN'and parent['bound_rounds']==6
                assert parent['tile']==list(tile)and parent['rectangle']==Ibox and parent['h_rectangle']is None
                assert raw['prior']['sha256']==PREFIX and raw['prior']['closed_cover_parts']==[4,4]
                assert raw['prior']['tile']==list(tile)and raw['prior']['rectangle']==Ibox
                assert parent['original_prefix_replay']['certificate_sha256']==PREFIX
                common=dict(parent_bound_record_sha256=m['parent']['sha256'],
                    parent_physical_state_sha256=value_digest(self.ordinary.view(state,diag)),
                    original_prefix_sha256=PREFIX,original_I_tile=list(tile),original_I_rectangle=Ibox,
                    certified_parent_I_rectangle=view(state['positions'][16:18]),
                    certified_parent_H_rectangle=view(state['positions'][14:16]),H_parts=[2,4],
                    H_grid_derived_from_certified_six_round_state=True,inherited_state_counted_as_one_common_antecedent=True)
                self.slope.derived_parents[m['parent']['sha256']]=(parent,state,diag)
                children=m['children'];assert len(children)==8
                assert [c['tile']for c in children]==[list(t)for t in product(range(2),range(4))]
                H_results=[]
                for child in children:
                    ht=tuple(child['tile']);full=tile+ht;Hbox=rectangle(state['positions'][14:16],ht,(2,4));H_count+=1
                    if child['kind']=='initial_H_difference':
                        assert set(child)=={'tile','kind'}and full in self.direct_H
                        r=self.direct_H[full]
                        assert r['parent_bound_record_sha256']==m['parent']['sha256']and r['original_prefix_sha256']==PREFIX
                        assert r['certified_parent_H_rectangle']==common['certified_parent_H_rectangle']and r['H_rectangle']==Hbox
                        assert r['closed_faces_retained']and r['every_other_parent_bound_retained']
                        assert r['witnesses']and all(F(w['strict_gap'])>0 for w in r['witnesses'])
                        hr=dict(full_HI_tile=list(full),kind=child['kind'],H_rectangle=Hbox,closed=True,terminal_evidence=r)
                    elif child['kind']=='finished_H_prefix_difference':
                        assert set(child)=={'tile','kind'}and full==(1,2,0,0)
                        r=self.finished['exact_prefix_replay'];self.h_scope(r,full,Ibox,Hbox,common)
                        assert r['certificate_sha256']==FINISHED_PREFIX
                        hr=dict(full_HI_tile=list(full),kind=child['kind'],H_rectangle=Hbox,closed=True,terminal_evidence=self.finished['witnesses'])
                    else:
                        assert child['kind']=='proof_tree'and set(child)=={'tile','kind','node'}
                        _,root=self.binding(child['node']['bound']);assert root['schema']in H_SCHEMAS
                        hr=self.tree(child['node'],full,Ibox,Hbox,common,[dict(I=list(tile),H=list(ht))])
                    H_results.append(hr)
                result=dict(tile=list(tile),kind=m['kind'],rectangle=Ibox,common_derived_parent=common,
                            closed=all(r['closed']for r in H_results),H_children=H_results)
            results.append(result)
        assert split_parents==set(PARENTS)and H_count==56
        closed=[r['tile']for r in results if r['closed']];opened=[r['tile']for r in results if not r['closed']]
        assert bool(opened)==bool(self.open_leaves)
        complete=not opened
        totals={k:sum(r[k]for r in self.bound_reports.values())for k in('bound_rounds','bound_deductions','printed_rows_checked','terminal_rows')}
        modules={}
        for name,module in sys.modules.items():
            filename=getattr(module,'__file__',None)
            if filename and Path(filename).resolve().is_relative_to('/workspace'):
                p=Path(filename).resolve();assert p.is_relative_to(self.packet),('external_workspace_module',name,str(p))
                modules[name]=str(p.relative_to(self.packet))
        assert not any(n in sys.modules for n in('numpy','scipy','highspy','v3_whole_parent_pass','three_square_energy_rows','quadratic_moment_pilot'))
        self.unchanged()
        report=dict(schema='strict_Dc71_complete_or_explicit_partial_original_assembly_v2',
            status='PASS_COMPLETE_ORIGINAL_PARENT'if complete else'PASS_COMPLETE_DECLARED_COVER_WITH_EXPLICIT_OPEN_LEAVES',
            original_id=ID,original_path=PATH,original_prefix_sha256=PREFIX,
            original_I_parts=[4,4],declared_I_rectangles=16,derived_H_parts=[2,4],declared_H_rectangles=56,
            complete_closed_domain_union_checked=True,all_boundary_faces_retained=True,
            closed_I_rectangles=closed,open_I_rectangles=opened,complete_fixed_I_rectangles=len(closed),
            explicit_open_leaf_count=len(self.open_leaves),explicit_open_leaves=self.open_leaves,
            I_results=results,terminal_or_open_leaf_table=self.tables,
            distinct_bound_records=len(self.bound_reports),bound_record_totals=totals,
            accounting='SHA-deduplicated exact component bound reports; inherited continuations are not recounted as new geometric branches.',
            exact_bound_reports=self.bound_reports,primitive_replays=primitives,
            accepted_sharp_guard_terminals=sum(r['kind']=='accepted_sharp_guard'for r in self.tables),
            original_count=9,original_corner_count=36,original_pair_count=36,
            original_cell_denominator=231,mask_denominator=32,
            source_manifest_sha256=sha256(self.manifest_bytes).hexdigest(),core_manifest_sha256=sha256(self.core_bytes).hexdigest(),
            cover_index_sha256=sha256(self.index_bytes).hexdigest(),checker_sha256=digest(__file__),
            frozen_inputs=len(self.files),all_frozen_inputs_unchanged=True,all_declared_dependencies_rehashed=True,
            local_module_import_audit=modules,unfinished_records_admitted=False,
            whole_original_closed=complete,whole_original_cover_checked=complete,
            new_original_cells=int(complete),new_masks=0,lean_lake_ci_run=False,seconds=time.monotonic()-started)
        (self.output/'COMPLETE_OR_EXPLICIT_PARTIAL_REPLAY.json').write_text(json.dumps(report,indent=2)+'\n')
        (self.output/'TERMINAL_OR_OPEN_LEAF_TABLE.json').write_text(json.dumps(self.tables,indent=2)+'\n')
        print(json.dumps({k:report[k]for k in('status','complete_fixed_I_rectangles','open_I_rectangles','explicit_open_leaf_count','bound_record_totals','new_original_cells','new_masks','seconds')}))
        return report

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--packet',type=Path,default=Path(__file__).resolve().parent)
    parser.add_argument('--index',default='DC71_ORIGINAL_COVER_INDEX.json')
    parser.add_argument('--output',default='assembly_replay')
    a=parser.parse_args();assert __debug__
    Assembly(a.packet,a.index,a.output).verify()

if __name__=='__main__':main()

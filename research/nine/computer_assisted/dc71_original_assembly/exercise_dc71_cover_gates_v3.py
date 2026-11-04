#!/usr/bin/env python3
"""Focused actual-gate rejection tests; fixture reports are assembly-only stubs."""
from copy import deepcopy
from fractions import Fraction as F
from hashlib import sha256
from pathlib import Path
from types import SimpleNamespace
import importlib.util
import json
import tempfile

HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('tested_dc71_gate',HERE/'verify_dc71_original_cover_v3.py')
G=importlib.util.module_from_spec(spec);spec.loader.exec_module(G)
digest=lambda p:sha256(Path(p).read_bytes()).hexdigest()

def main():
    checks=[]
    def reject(label,call):
        try:call()
        except AssertionError:checks.append(dict(case=label,outcome='REJECTED'))
        else:raise AssertionError(('invalid fixture accepted',label))
    parent=dict(schema=G.H_SCHEMAS[1],id=G.ID,path=G.PATH,prior=dict(tile=[1,0],sha256=G.PREFIX))
    state=dict(angles=tuple((F(-1),F(1))for _ in range(9)))
    child=dict(schema=G.SLOPE_SCHEMA,id=G.ID,path=deepcopy(G.PATH),prior=deepcopy(parent['prior']),
        slope_restriction=dict(kind='original_slope_closed_equal_partition',
          parent=dict(path='parent.json',sha256='a'*64,schema=parent['schema']),
          original=8,parts=2,index=0,parent_interval=['-1','1'],interval=['-1','0'],
          all_other_inherited_bounds_retained=True))
    assert G.validate_slope_child(parent,'a'*64,state,8,2,0,child)==['-1','0']
    other=deepcopy(child);other['slope_restriction'].update(index=1,interval=['0','1'])
    assert G.validate_slope_child(parent,'a'*64,state,8,2,1,other)==['0','1']
    checks.append(dict(case='both_closed_halves_share_zero_face',outcome='PASS'))
    mutations=[('wrong_original_identity',lambda c:c.update(id='positive-other')),
      ('changed_canonical_caller',lambda c:c.update(path=[])),
      ('changed_fixed_parent_prior',lambda c:c['prior'].update(tile=[2,0])),
      ('wrong_restriction_kind',lambda c:c['slope_restriction'].update(kind='sharp_row_closed_complement')),
      ('dropped_other_inherited_bounds',lambda c:c['slope_restriction'].update(all_other_inherited_bounds_retained=False)),
      ('wrong_parent_hash',lambda c:c['slope_restriction']['parent'].update(sha256='b'*64)),
      ('wrong_parent_schema',lambda c:c['slope_restriction']['parent'].update(schema=G.SLOPE_SCHEMA)),
      ('wrong_original_frame',lambda c:c['slope_restriction'].update(original=7)),
      ('wrong_partition_size',lambda c:c['slope_restriction'].update(parts=4)),
      ('wrong_child_index',lambda c:c['slope_restriction'].update(index=1)),
      ('wrong_source_interval',lambda c:c['slope_restriction'].update(parent_interval=['-1','1/2'])),
      ('discarded_closed_threshold_face',lambda c:c['slope_restriction'].update(interval=['-1','-1/1000'])),
      ('extended_child_interval',lambda c:c['slope_restriction'].update(interval=['-1','1/1000'])),
      ('different_child_schema',lambda c:c.update(schema=G.H_SCHEMAS[0]))]
    for label,change in mutations:
        c=deepcopy(child);change(c);reject(label,lambda c=c:G.validate_slope_child(parent,'a'*64,state,8,2,0,c))
    reject('boolean_original_selector',lambda:G.validate_slope_child(parent,'a'*64,state,True,2,0,child))
    reject('boolean_partition_size',lambda:G.validate_slope_child(parent,'a'*64,state,8,True,0,child))
    reject('boolean_child_index',lambda:G.validate_slope_child(parent,'a'*64,state,8,2,False,child))

    class Fixture(G.Assembly):
        """No physical proof is simulated: reports exercise only gate routing."""
        def __init__(self,folder):
            self.packet=folder;self.tables=[];self.open_leaves=[];self.records={};self.reports={}
            self.files={};self.touched={};self.slope=SimpleNamespace(locate=lambda name:Path(name))
            self.tile=(1,0,0,0);self.Ibox=[['-1','0'],['0','1']];self.Hbox=[['-1','0'],['0','1']]
            self.common=dict(test_only='identical_certified_H_parent')
            p=deepcopy(parent)
            self.parent_binding=self.save('parent.json',p)
            self.parent_report=self.base_report(self.parent_binding,False)
            self.parent_report['derived_parent_facts']=self.common
            self.parent_report['original_prefix_replay']=dict(certificate_sha256=G.PREFIX)
            self.reports[self.parent_binding['sha256']]=self.parent_report
            nodes=[]
            for k in range(2):
                c=deepcopy(child);r=c['slope_restriction'];r.update(index=k,interval=G.interval(-1,1,k,2))
                r['parent']=dict(path=str(folder/'parent.json'),sha256=self.parent_binding['sha256'],schema=p['schema'])
                b=self.save('child%d.json'%k,c);report=self.base_report(b,True)
                report['inherited_parent_facts']=dict(original_prefix_sha256=G.PREFIX,original_tile=list(self.tile),all_other_inherited_bounds_retained=True)
                report['inherited_bound_parent_replay']=self.parent_report
                self.reports[b['sha256']]=report;nodes.append(dict(index=k,node=dict(kind='terminal',bound=b)))
            self.node=dict(kind='slope_cover',bound=self.parent_binding,original=8,parts=2,children=nodes)
        def save(self,name,record):
            p=self.packet/name;p.write_text(json.dumps(record,sort_keys=True)+'\n');h=digest(p)
            self.files[name]=h;self.records[h]=record;return dict(file=name,sha256=h)
        def base_report(self,binding,closed):
            return dict(id=G.ID,original_parent_path=G.PATH,tile=list(self.tile),rectangle=self.Ibox,h_rectangle=self.Hbox,
                status='PASS_COMPLETE_RESTRICTED_PHYSICAL_TILE'if closed else'PASS_CERTIFIED_TILE_STATE_OPEN',
                certificate_sha256=binding['sha256'],bound_rounds=0,bound_deductions=0,printed_rows_checked=0,
                terminal_rows=0,terminal_kind='assembly_fixture_only'if closed else None,reserve='1'if closed else None)
        def component(self,binding,ordinary=False):
            path,literal=self.binding(binding)
            return literal,self.reports[binding['sha256']],state,{}
        def call(self,node=None):return self.tree(node or self.node,self.tile,self.Ibox,self.Hbox,self.common,[])
    with tempfile.TemporaryDirectory(prefix='dc71_gate_tests_',dir=HERE)as temp:
        folder=Path(temp)
        def fixture(name):p=folder/name;p.mkdir();return Fixture(p)
        f=fixture('closed');assert f.call()['closed']and not f.open_leaves
        checks.append(dict(case='complete_two_sibling_cover',outcome='PASS'))
        f=fixture('open');n=f.node['children'][1]['node'];n['kind']='open'
        f.reports[n['bound']['sha256']]['status']='PASS_CERTIFIED_RESTRICTED_TILE_STATE_OPEN'
        assert not f.call()['closed']and len(f.open_leaves)==1
        checks.append(dict(case='explicit_OPEN_blocks_parent_closure',outcome='PASS'))
        f=fixture('open_as_terminal');n=f.node['children'][1]['node']
        f.reports[n['bound']['sha256']]['status']='PASS_CERTIFIED_RESTRICTED_TILE_STATE_OPEN'
        reject('OPEN_child_cannot_be_terminal',f.call)
        f=fixture('missing_sibling');f.node['children'].pop();reject('missing_sibling',f.call)
        f=fixture('duplicate_sibling');f.node['children'][1]['index']=0;reject('duplicate_sibling_index',f.call)
        f=fixture('wrong_full_tile');h=f.node['children'][1]['node']['bound']['sha256']
        f.reports[h]['tile']=[1,0,0,1];reject('changed_full_HI_tile',f.call)
        f=fixture('wrong_fixed_rectangle');h=f.node['children'][1]['node']['bound']['sha256']
        f.reports[h]['h_rectangle']=[['-1','1'],['0','1']];reject('changed_H_rectangle',f.call)
        f=fixture('stale_parent');(f.packet/'parent.json').write_text('{}\n');reject('parent_bytes_changed_before_cache_use',f.call)
        f=fixture('earlier_sibling_mutation');f.call();(f.packet/'child0.json').write_text('{}\n')
        reject('earlier_sibling_bytes_changed_on_reuse',f.call)
        # Exercise the real final inventory guard independently of arithmetic.
        p=folder/'inventory';p.mkdir()
        payloads={'index.json':'{}\n','SHA256_MANIFEST.json':'{}\n','first_source.py':'pass\n','later_source.py':'pass # later\n'}
        for name,text in payloads.items():(p/name).write_text(text)
        obj=G.Assembly.__new__(G.Assembly);obj.packet=p;obj.index_path=p/'index.json'
        obj.index_bytes=obj.index_path.read_bytes();obj.core_bytes=(p/'SHA256_MANIFEST.json').read_bytes()
        obj.files={name:digest(p/name)for name in payloads};obj.touched=dict(obj.files)
        obj.manifest_path=p/'ASSEMBLY_MANIFEST.json';obj.manifest_path.write_text(json.dumps(dict(files=obj.files)))
        obj.manifest_bytes=obj.manifest_path.read_bytes();obj.unchanged()
        for name in payloads:
            saved=(p/name).read_bytes();(p/name).write_text('changed\n')
            reject('final_inventory_rejects_'+name,obj.unchanged);(p/name).write_bytes(saved)
        saved=obj.manifest_bytes;obj.manifest_path.write_text('{}\n')
        reject('outer_manifest_mutation',obj.unchanged);obj.manifest_path.write_bytes(saved)
        reject('outside_packet_relative_path',lambda:obj.path('../outside'))
        reject('conflicting_source_hash',lambda:obj.register(p/'first_source.py','f'*64))
        obj.unchanged()
        # Report dependencies are either already relocated local paths or
        # historical names resolved only through the component's bound map.
        obj.bound_reports={};calls=[]
        def locate(name):
            calls.append(name)
            assert name=='/historical/frozen/first_source.py'
            return p/'first_source.py'
        obj.slope=SimpleNamespace(locate=locate)
        obj.dependencies(dict(source_sha256={str(p/'first_source.py'):digest(p/'first_source.py')}))
        assert calls==[]
        checks.append(dict(case='resolved_packet_dependency_keeps_manifest_hash_gate',outcome='PASS'))
        obj.dependencies(dict(checker_dependency_sha256={'/historical/frozen/first_source.py':digest(p/'first_source.py')}))
        assert calls==['/historical/frozen/first_source.py']
        checks.append(dict(case='historical_dependency_uses_only_explicit_binding',outcome='PASS'))
        reject('unbound_external_absolute_dependency',lambda:obj.dependencies(dict(source_sha256={'/external/unbound.py':'a'*64})))
        reject('resolved_local_dependency_wrong_hash',lambda:obj.dependencies(dict(source_sha256={str(p/'first_source.py'):'b'*64})))
        unknown=p/'unlisted_source.py';unknown.write_text('pass\n')
        try:obj.dependencies(dict(source_sha256={str(unknown):digest(unknown)}))
        except KeyError:checks.append(dict(case='resolved_local_dependency_unlisted_in_manifest',outcome='REJECTED'))
        else:raise AssertionError('unlisted local dependency accepted')
        obj.unchanged()
    report=dict(schema='Dc71_outer_assembly_focused_gate_tests_v1',status='PASS_ALL_FOCUSED_ROUTING_AND_IMMUTABILITY_TESTS',
        outer_source_sha256=digest(HERE/'verify_dc71_original_cover_v3.py'),test_source_sha256=digest(__file__),
        test_cases=len(checks),checks=checks,fixture_scope='Assembly-only stubs; no physical terminal or arithmetic replay is claimed.',
        actual_gate_functions_exercised=['validate_slope_child','interval','Assembly.tree','Assembly.h_scope','Assembly.binding','Assembly.path','Assembly.register','Assembly.unchanged','Assembly.dependency_path','Assembly.dependencies'],
        new_original_cells=0,new_masks=0,lean_lake_ci_run=False)
    out=HERE/'FOCUSED_GATE_TEST_RESULTS_V3.json';assert not out.exists();out.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(dict(status=report['status'],test_cases=len(checks),report_sha256=digest(out))))

if __name__=='__main__':main()

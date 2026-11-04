#!/usr/bin/env python3
"""The unchanged Cb882 exact height cover with bounded-memory node reads."""
from pathlib import Path
from fractions import Fraction as F
from copy import deepcopy
from itertools import product
from collections import Counter
import argparse,hashlib,json,subprocess,sys,tempfile,time
import verify_c887_unit_four_corner_tree as FOUR
import verify_ac_original_bound_pass as PARSE
import independent_physical_sat_diagonal_replay as SAT
import independent_physical_proxy_cover as PROXY

HERE = Path(__file__).resolve().parent
LOADER = HERE.parent.parent/'d_work/cb882_tools/replay_height_seeds.py'
LOADER_SHA = '93c7b82265c1103e42436074e80dc158a4d73a13fb63f11a40910dc0f702cc1e'
TARGET = 'negative-b882d8ade0cf9ea0'
ORIGINAL_PATH = [['angle',3,0],['angle_cut',[0,'0'],1],['alternate_four_escape',[1,7],[3]]]
SCOPE = 'ONE_CLOSED_MEMBER_OF_COMPLETE_OPPOSITE_TILT_EIGHT_COVER'
PREFIX = 'opposite_tilt_AHID_variation_'


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def literal_height_row(component):
    assert type(component) is int and component in (0,1,2,3,5,6)
    # Expand minus the selected signed AH, HI, ID vertical differences.
    signs = tuple(product((-1,1),repeat=3))[component]
    terms = {}
    for sign,left,right in zip(signs,(0,7,8),(7,8,3)):
        terms[2*left+1] = terms.get(2*left+1,F(0)) + sign
        terms[2*right+1] = terms.get(2*right+1,F(0)) - sign
    return tuple((k,F(v)) for k,v in sorted(terms.items()) if v), -F(23,100), PREFIX+str(component)


class Checker(FOUR.Checker):
    def __init__(self):
        super().__init__()
        self.height_row_occurrences = 0


class Adapter(FOUR.Adapter):
    def __init__(self,checker,component):
        super().__init__(checker)
        self.component = component
        self.height_row = literal_height_row(component)

    def rebuild(self,state,printed):
        assert state['id'] == TARGET and state['path'][:len(ORIGINAL_PATH)] == ORIGINAL_PATH
        ordinary = [row for row in printed if not row['name'].startswith(PREFIX)]
        rows,bounds,physical = super().rebuild(state,ordinary)
        for row in printed:
            if not row['name'].startswith(PREFIX):
                continue
            literal = (tuple((k,F(v)) for k,v in row['coefficients']),F(row['rhs']),row['name'])
            assert literal == self.height_row and row['index'] not in rows
            rows[row['index']] = literal
            self.checker.height_row_occurrences += 1
        return rows,bounds,physical


def fresh_seed(reference):
    seed_path = Path(reference['path'])
    assert sha(seed_path) == reference['sha256']
    saved = json.loads(seed_path.read_text())
    assert saved['schema'] == reference['schema'] == 'CB882_exact_named_height_seed_v1'
    component = saved['component']
    assert type(component) is int and component in (0,1,2,3,5,6)
    assert sha(LOADER) == saved['loader_sha256'] == LOADER_SHA
    with tempfile.TemporaryDirectory(prefix='cb882_fresh_height_seed_') as temporary:
        output = Path(temporary)/'fresh'
        completed = subprocess.run([sys.executable,'-B','-S',str(LOADER),'--branch',str(component),
                                    '--output',str(output)],capture_output=True,text=True)
        assert completed.returncode == 0, completed.stdout+'\n'+completed.stderr
        fresh = json.loads((output/f'component_{component}.json').read_text())
    assert sha(LOADER) == LOADER_SHA
    for field in ('schema','status','original_id','original_path','component','scope','conditional_row',
                  'state','parent','archive_manifest','cover_table','loader_sha256',
                  'all_nine_originals_retained','mask','closed_shared_faces_retained','new_original_cells','new_masks'):
        assert fresh[field] == saved[field], ('fresh seed mismatch',field)
    assert fresh['original_id'] == TARGET and fresh['original_path'] == ORIGINAL_PATH
    assert fresh['status'] == 'PASS_CERTIFIED_CONDITIONAL_ORIGINAL_STATE_OPEN'
    assert fresh['scope'] == SCOPE
    assert fresh['exact_ancestry']['certificate_sha256'] == fresh['parent']['sha256']
    assert fresh['exact_ancestry']['conditional_sharp_rows'] == [fresh['conditional_row']]
    return fresh


def angle_child(parent,owner,cut,side,adapter):
    assert type(owner) is int and 0<=owner<9 and type(side) is int and side in (0,1)
    lo,hi = parent['angles'][owner]
    cut = F(cut)
    assert lo<cut<hi
    child = deepcopy(parent)
    angles = list(child['angles'])
    angles[owner] = (lo,cut) if side==0 else (cut,hi)
    child.update(angles=tuple(angles),path=deepcopy(parent['path'])+[['angle_cut',[owner,str(cut)],side]])
    child['choices'] = adapter.choices(child['path'])
    return child


def replay(folder,output):
    started = time.monotonic()
    folder = Path(folder).resolve()
    mp = folder/'manifest.json'
    manifest = json.loads(mp.read_text())
    assert manifest['schema'] == 'same_original_physical_SAT_proxy_angle_tree_discovery_v1'
    assert manifest['id'] == TARGET and manifest['original_path'] == ORIGINAL_PATH
    assert manifest['scope'] == SCOPE and manifest['new_original_cells'] == manifest['new_masks'] == 0
    seed = fresh_seed(manifest['parent'])
    assert manifest['component'] == seed['component']
    assert manifest['conditional_parent'] == seed['parent']
    assert manifest['closed_domain'] == seed['conditional_row']
    assert manifest['archive_manifest'] == seed['archive_manifest'] and manifest['cover_table'] == seed['cover_table']
    assert manifest['preexisting_excluded_height_components'] == [4,7]
    assert manifest['all_eight_closed_domains_required_for_original'] is True
    checker = Checker()
    adapter = Adapter(checker,seed['component'])
    co,rhs,name = adapter.height_row
    assert seed['conditional_row'] == dict(coefficients=[[k,str(v)] for k,v in co],rhs=str(rhs),name=name)
    assert checker.K.V.Q == F(1105,256)
    assert checker.K.V.EDGES == ((0,1,0),(1,2,0),(2,3,1),(4,5,0),(5,6,0))
    state = PARSE.parse_state(seed['state'],adapter)
    assert [n['index'] for n in manifest['nodes']] == list(range(len(manifest['nodes'])))
    nodes = {n['index']:n for n in manifest['nodes']}
    bindings = {str(mp):sha(mp),manifest['parent']['path']:manifest['parent']['sha256'],str(LOADER):LOADER_SHA}
    for path,h in manifest['source_sha256'].items():
        assert sha(path) == h
        bindings[path] = h
    for index,node in nodes.items():
        assert node['file'] == f'node_{index:05d}.json'
        path = folder/node['file']
        assert sha(path) == node['sha256']
        bindings[str(path)] = node['sha256']
    visited = set()
    audits,covers,leaves = [],[],[]

    def visit(index,initial,parent=None,depth=0,restriction=None):
        assert index not in visited
        visited.add(index)
        node = nodes[index]
        node_path = folder/node['file']
        assert sha(node_path) == node['sha256']
        record = json.loads(node_path.read_text())
        assert (node['parent'],node['depth'],node['restriction']) == (parent,depth,restriction)
        assert record['id'] == TARGET and record['original_path'] == ORIGINAL_PATH
        audit,after = SAT.check_record(record,initial,adapter)
        audits.append(dict(index=index,**audit))
        children = node['children']
        assert isinstance(children,list) and len(children)==len(set(children))
        if after is None:
            assert children==[] and 'split' not in node and node['status']=='CANDIDATE_CLOSED'
            leaves.append(dict(index=index,excluded=True,terminal_kind=record['terminal']['kind']))
            return True
        if not children:
            assert node['status'] in ('OPEN','OPEN_NO_SPLIT_SELECTED') and 'split' not in node
            leaves.append(dict(index=index,excluded=False))
            return False
        # The arithmetic has consumed this node; release its large payload
        # before visiting children, retaining only the certified state.
        del record
        assert node['complete_children'] is True
        split = node['split']
        outcomes = []
        restrictions = [nodes[k]['restriction'] for k in children]
        if split['kind'] in ('complete_physical_sat','complete_physical_proxy'):
            pair = tuple(split['pair'])
            assert len(pair)==2 and all(type(k) is int for k in pair) and 0<=pair[0]<pair[1]<9
            is_sat = split['kind']=='complete_physical_sat'
            kind = 'physical_sat' if is_sat else 'physical_proxy'
            expected = set(product(pair,(0,1),(-1,1))) if is_sat else set(product((0,1),(-1,1)))
            assert all(set(r)=={'kind','pair','choice'} and r['kind']==kind and r['pair']==list(pair) for r in restrictions)
            actual = [tuple(r['choice']) for r in restrictions]
            assert len(actual)==len(set(actual))==len(expected) and set(actual)==expected
            if not is_sat:
                PROXY.check_choices([r['choice'] for r in restrictions])
            for k,r in zip(children,restrictions):
                child = SAT.sat_child(after,pair,r['choice'],adapter) if is_sat else PROXY.proxy_child(after,pair,r['choice'],adapter)
                outcomes.append(visit(k,child,index,depth+1,r))
        else:
            assert split['kind']=='closed_angle_bisection'
            owner,cut = split['owner'],F(split['cut'])
            assert len(children)==2 and sorted(r['side'] for r in restrictions)==[0,1]
            assert all(set(r)=={'kind','owner','cut','side'} and r['kind']=='closed_angle' and r['owner']==owner and F(r['cut'])==cut for r in restrictions)
            for k,r in zip(children,restrictions):
                outcomes.append(visit(k,angle_child(after,owner,cut,r['side'],adapter),index,depth+1,r))
        closed = all(outcomes)
        assert node['status']==('CANDIDATE_COVER_CLOSED' if closed else 'OPEN')
        covers.append(dict(index=index,kind=split['kind'],children=children,
                           all_closed_alternatives_present=True,all_children_excluded=closed))
        return closed

    complete = visit(0,state)
    assert visited==set(nodes)
    assert manifest['status']==('CANDIDATE_COVER_CLOSED' if complete else 'OPEN')
    for path,h in bindings.items():
        assert sha(path)==h
    FOUR.verify_all_bindings()
    forbidden = ('numpy','scipy','highspy','cb882_height_four_runtime','ac_objective_unit_four_corner_runtime')
    assert not any(name in sys.modules for name in forbidden)
    dependencies = {}
    for name,module in tuple(sys.modules.items()):
        path = getattr(module,'__file__',None)
        if path and Path(path).suffix=='.py' and Path(path).resolve().is_relative_to(HERE.parent):
            dependencies[str(Path(path).resolve())] = sha(path)
    dependencies[str(LOADER)] = LOADER_SHA
    result = dict(status='PASS_COMPLETE_CB882_HEIGHT_COMPONENT_TREE' if complete else 'PASS_PARTIAL_CB882_HEIGHT_COMPONENT_TREE',
        original_id=TARGET,original_path=ORIGINAL_PATH,component=seed['component'],scope=SCOPE,
        conditional_parent=seed['parent'],closed_domain=seed['conditional_row'],
        archived_height_ancestry=seed['exact_ancestry'],fresh_seed_loader_sha256=LOADER_SHA,
        complete=complete,nodes=len(nodes),leaf_domains=len(leaves),excluded_leaves=sum(x['excluded'] for x in leaves),
        open_leaves=sum(not x['excluded'] for x in leaves),closed_unions=dict(Counter(x['kind'] for x in covers)),
        rounds=sum(x['rounds'] for x in audits),deductions=sum(x['deductions'] for x in audits),
        printed_rows_checked=sum(x['printed_rows_checked'] for x in audits),
        conditional_height_row_occurrences=checker.height_row_occurrences,
        unit_four_corner_row_occurrences=checker.unit_four_corner_row_occurrences,
        node_audits=audits,leaf_table=leaves,complete_closed_covers=covers,
        input_sha256=bindings,checker_dependency_sha256=dependencies,
        node_payloads_replayed_lazily=True,
        all_nine_originals_retained=True,mask='001/00',closed_shared_faces_retained=True,
        whole_original_coverage_not_claimed=True,all_eight_height_components_required_for_original=True,
        new_original_cells=0,new_masks=0,numerical_producer_imported=False,lean_lake_ci_run=False,
        seconds=time.monotonic()-started)
    Path(output).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ('status','component','nodes','excluded_leaves','open_leaves','deductions','printed_rows_checked','seconds')}),flush=True)
    return result


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('folder',type=Path)
    parser.add_argument('output',type=Path)
    args=parser.parse_args()
    replay(args.folder,args.output)

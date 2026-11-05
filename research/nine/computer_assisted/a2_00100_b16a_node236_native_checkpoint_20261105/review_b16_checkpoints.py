"""Independent structural, byte, arithmetic and conditional physical review."""
from pathlib import Path
from fractions import Fraction as F
from itertools import product
from collections import Counter
from copy import deepcopy
import hashlib
import json
import sys
import tarfile
import time

HERE = Path(__file__).resolve().parent
WORK = Path('/workspace/scratch/f9f48fcfb253/b_work')
sys.path.insert(0, str(WORK))
import verify_b_accepted_center_disk_tree_v1 as EXACT

def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def read(p):
    return json.loads(Path(p).read_text())

def check_transport(folder):
    manifest = read(folder / 'MANIFEST.json')
    for name, digest in manifest['files'].items():
        assert Path(name).name == name and sha(folder / name) == digest
    index = read(folder / 'INPUTS.json')['files']
    expected = {e['sha256']: e['bytes'] for e in index}
    assert len(index) == manifest['source_input_paths']
    assert len(expected) == manifest['unique_input_blobs']
    seen = set()
    with tarfile.open(folder / 'inputs.tar.xz', 'r|xz') as archive:
        for member in archive:
            assert member.isfile() and member.name.startswith('sources/')
            digest = member.name.removeprefix('sources/')
            assert digest in expected and digest not in seen
            raw = archive.extractfile(member).read()
            assert len(raw) == member.size == expected[digest]
            assert hashlib.sha256(raw).hexdigest() == digest
            seen.add(digest)
    assert seen == set(expected)
    for entry in index:
        p = Path(entry['path'])
        assert p.is_file() and p.stat().st_size == entry['bytes']
        assert sha(p) == entry['sha256'], str(p)
    return dict(paths=len(index), blobs=len(expected), archive_sha256=sha(folder / 'inputs.tar.xz'))

def tree(folder):
    m = read(folder / 'manifest.json')
    assert m['completed'] is True and m['original_cells_closed'] == m['masks_closed'] == 0
    nodes = []
    for e in m['nodes']:
        assert e['index'] == len(nodes) and sha(folder / e['file']) == e['sha256']
        n = read(folder / e['file'])
        assert (n['index'],n['depth'],n['status']) == (e['index'],e['depth'],e['status'])
        assert n['record']['initial'] == n['initial']
        nodes.append(n)
    seen, unions = set(), Counter()
    def visit(k, parent=None, depth=0, choice=None):
        assert k not in seen
        seen.add(k); n = nodes[k]
        assert (n['parent'],n['depth'],n['choice']) == (parent,depth,choice)
        if not n['children']:
            assert n['status'] in ('OPEN','CANDIDATE_CLOSED')
            return n['status'] == 'CANDIDATE_CLOSED'
        assert n['complete_closed_children'] is True
        state = n['record']['final']; split = n['split']; kind = split['kind']
        if kind == 'proxy': expected = list(map(list, product((0,1),(-1,1))))
        elif kind == 'sat': expected = list(map(list, product(split['pair'],(0,1),(-1,1))))
        else:
            assert kind == 'angle'; expected = [0,1]
        assert len(n['children']) == len(expected) == len(set(n['children']))
        unions[kind] += 1
        results = []
        for child, ch in zip(n['children'], expected):
            actual = deepcopy(state)
            if kind == 'angle':
                owner, cut = split['owner'], F(split['cut'])
                lo, hi = map(F, actual['angles'][owner]); assert lo < cut < hi
                actual['angles'][owner] = [str(lo), str(cut)] if ch == 0 else [str(cut), str(hi)]
                actual['path'].append(['angle_cut',[owner,str(cut)],ch])
            else: actual['path'].append([kind,split['pair'],ch])
            assert nodes[child]['initial'] == actual, (k,child)
            results.append(visit(child,k,depth+1,ch))
        closed = all(results)
        assert n['status'] == ('CANDIDATE_COVER_CLOSED' if closed else 'OPEN')
        return closed
    assert visit(0) is False and seen == set(range(len(nodes)))
    leaves = [n for n in nodes if not n['children']]
    return m,nodes,dict(nodes=len(nodes),unions=dict(unions),
        excluded=sum(n['status']=='CANDIDATE_CLOSED' for n in leaves),
        open=sum(n['status']=='OPEN' for n in leaves))

def parse_state(raw, adapter):
    s = dict(id=raw['id'],path=deepcopy(raw['path']))
    for key in ('angles','positions','scalar'):
        s[key] = tuple(tuple(map(F,x)) for x in raw[key])
    s['differences'] = {tuple(e['pair']):tuple(tuple(map(F,x)) for x in e['intervals']) for e in raw['differences']}
    s['choices'] = adapter.choices(s['path'])
    assert EXACT.CORE.state_view(s) == raw
    return s

def literal_sum(terminal):
    rows = {r['index']:r for r in terminal['rows']}
    assert len(rows) == len(terminal['rows'])
    bounds = list(map(F,terminal['absolute_variable_bounds']))
    assert all(x >= 0 for x in bounds)
    co = [F(0)] * len(bounds); rhs = F(0); used=set()
    for i,w in terminal['weights']:
        assert type(w) is int and w > 0 and i not in used
        used.add(i); row=rows[i]; q=F(w,2**40); rhs += q*F(row['rhs'])
        for k,c in row['coefficients']: co[k] += q*F(c)
    assert used == set(rows)
    residual = sum(a*abs(b) for a,b in zip(bounds,co))
    reserve = -rhs-residual
    assert reserve > 0 and reserve == F(terminal['reserve'])
    assert rhs == F(terminal['weighted_rhs'])
    assert co == list(map(F,terminal['weighted_coefficients']))
    return str(reserve)

def main():
    started=time.monotonic()
    pub=HERE/'published'
    transport={name:check_transport(pub/name) for name in (
        'a2_00100_b16a_75_native_checkpoint_20261105',
        'a2_00100_b16a_hi_cover_native_checkpoint_20261105')}
    m45,n45,s45=tree(WORK/'b16_fresh_interval45_20261105')
    m75,n75,s75=tree(WORK/'b16_broad_phase_20261105')
    m203,n203,s203=tree(WORK/'b16_hi_cover_v2_20261105')
    assert m45['parent']==m75['parent']==m203['parent']
    assert n45[0]['initial']==n75[0]['initial']==n203[0]['initial']
    for old,new in zip(n45,n75):
        assert old['initial']==new['initial']
        assert new['record']['rounds'][:len(old['record']['rounds'])] == old['record']['rounds']
        if old['status']=='CANDIDATE_CLOSED': assert old==new
    for old,new in zip(n75,n203):
        assert old['initial']==new['initial'] and old['record']==new['record']
        if old['children'] or old['status']=='CANDIDATE_CLOSED': assert old==new
    new75=[n for n in n75 if n['status']=='CANDIDATE_CLOSED' and
           (n['index']>=45 or n45[n['index']]['status']!='CANDIDATE_CLOSED')]
    new203=[n for n in n203[75:] if n['status']=='CANDIDATE_CLOSED']
    assert len(new75)==18 and len(new203)==81
    changed=[n for n in n75 if n['index']>=45 or n['record']!=n45[n['index']]['record']]
    cap=WORK/'recovery_20261105/extracted_b340/unpacked/b340_complete_original_package/accepted_repo/research/nine/computer_assisted/full_angle_common_side_row_v1'
    adapter=EXACT.Adapter(WORK/'b16a_I32_complete_H_checkpoint',cap)
    audits=[]
    for label,collection in [('new75records',changed),('new203records',n203[75:])]:
        for n in collection:
            record=n['record']; t=record.get('terminal')
            reserve=literal_sum(t) if t and t['kind']=='positive_exact_reserve' else None
            audit, after=EXACT.CORE.check_record(record,parse_state(n['initial'],adapter),adapter)
            assert (after is None)==(record['status']=='CANDIDATE_CLOSED')
            audits.append(dict(group=label,node=n['index'],literal_reserve=reserve,audit=audit))
    adapter.recheck()
    assert not any(name in sys.modules for name in ('numpy','scipy','highspy'))
    result=dict(status='PASS_SCOPED_NONAUTHOR_REVIEW',transport=transport,
        structure={'prior45':s45,'checkpoint75':s75,'checkpoint203':s203},
        unchanged_original_caller=True,unchanged_old_closed_payloads=True,
        exact_old_round_prefixes_retained=True,all_new_closed_faces_and_owner_sign_cases=True,
        new75_terminal_arguments=18,new203_terminal_arguments=81,
        conditional_records_replayed=audits,
        fresh_full_ancestry_replay_repeated=False,
        accepted_full_reports_reused_for_original_parent_ancestry=True,
        independent_literal_weight_sums_recomputed=True,
        no_original_cell_or_mask_closure=True,whole_proof_audit_claimed=False,
        source_pins_rechecked=len(adapter.files),seconds=time.monotonic()-started,
        reviewer_source_sha256=sha(__file__))
    (HERE/'B16_CHECKPOINTS_NONAUTHOR_REVIEW.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ('status','structure','new75_terminal_arguments','new203_terminal_arguments','seconds')}))

if __name__=='__main__':
    assert __debug__
    main()

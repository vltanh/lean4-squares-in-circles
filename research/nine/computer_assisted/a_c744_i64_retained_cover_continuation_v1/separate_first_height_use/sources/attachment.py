"""Fixed native source attachment for a first I64 height-row use."""
if not __debug__:raise RuntimeError('Exact attachment requires assertions.')
from contextlib import contextmanager
from copy import deepcopy
from fractions import Fraction as F
from pathlib import Path
import hashlib,json,sys
HERE=Path(__file__).resolve().parent
WORK=HERE.parent
sys.path.insert(0,str(WORK/'a165_i64_exact_continuation_v1'))
import i64_retained_cover_adapter as ACCEPTED
import independent_physical_sat_diagonal_replay as CORE
ROWS=ACCEPTED.ROWS
TREE=WORK/'a165_i64_exact_continued_tree_v1'
REPORT=WORK/'A165_I64_EXACT_CONTINUATION_REPLAY_V1.json'
REPORT_SHA='98bc7f287f1eb62e0a132437d808c48121a017317adde4ea9083f83364d2ad8f'
MANIFEST_SHA='4469ce8ceda7692f49faa58ece25872c0448fbd8fc86447acb6facf0cd4e2283'
LEAF=154
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
def parse(value,choices):
    s=dict(id=value['id'],path=deepcopy(value['path']),choices=choices(value['path']))
    for k in('angles','positions','scalar'):s[k]=tuple(tuple(map(F,x))for x in value[k])
    for k in('differences','diagonal'):s[k]={tuple(x['pair']):tuple(tuple(map(F,v))for v in x['intervals'])for x in value[k]}
    CORE.valid_state(s);return s
def sources():
    assert sha(REPORT)==REPORT_SHA and sha(TREE/'manifest.json')==MANIFEST_SHA
    r,m=read(REPORT),read(TREE/'manifest.json')
    assert r['status']=='PASS_A165_I64_COMPLETE_RETAINED_COVER_OPEN'and r['all165_nodes_freshly_replayed']is True
    assert(r['nodes'],r['excluded_leaves'],r['open_leaves'])==(165,118,14)
    assert m['component']==r['component']==3 and m['closed_domain']==r['closed_domain']
    assert m['closed_domain']['rhs']=='-3/5'and r['continued_manifest_sha256']==MANIFEST_SHA
    assert sha(r['inherited_complete_arithmetic_report']['path'])==r['inherited_complete_arithmetic_report']['sha256']
    for node in m['nodes']:assert sha(TREE/node['file'])==node['sha256']
    n=m['nodes'][LEAF];assert n['index']==LEAF and n['status']=='OPEN'and n['children']==[]
    prior=read(TREE/n['file']);assert prior['status']=='OPEN'
    freeze=read(HERE/'SOURCE_BINDINGS.json')
    for name,h in freeze['files'].items():assert sha(HERE/name)==h
    for path,h in freeze['external_input_sha256'].items():assert sha(path)==h
    return m,n,prior

@contextmanager
def environment():
    m,n,prior=sources();binding=ROWS.verify_binding();historical,cache=ROWS.HISTORY.validate()
    before=ACCEPTED.CONSEQUENCE._source_report;ACCEPTED.CONSEQUENCE._source_report=deepcopy(cache['complements'])
    instances=[];Checker,Adapter=ACCEPTED.classes(binding,instances)
    try:
        checker=Checker();whole=parse(read(binding['whole_original_parent']['path'])['record']['final'],
            lambda path:checker.K.V.reconstruct(path)[2]);adapter=Adapter(checker,whole,3)
        initial=parse(prior['final'],adapter.choices)
        yield dict(manifest=m,node=n,prior=prior,binding=binding,checker=checker,adapter=adapter,initial=initial,
            source_reuse=dict(full165_report_sha256=REPORT_SHA,manifest_sha256=MANIFEST_SHA,
                all165_payload_hashes_verified=True,full165_arithmetic_repeated=False,
                historical_source_identity_reuse=historical,fresh813_source_arithmetic_repeated=False))
        sources();ROWS.verify_binding()
    finally:ACCEPTED.CONSEQUENCE._source_report=before

def write(path,value):
    path=Path(path);assert not path.exists()
    with path.open('x')as stream:json.dump(value,stream,indent=2);stream.write('\n')

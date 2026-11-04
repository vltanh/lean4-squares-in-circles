"""Original-variable affine bounds from the unsplit Cb882 source record."""
from pathlib import Path
import hashlib,json,sys

HERE=Path(__file__).resolve().parent
AC=HERE.parents[1]/'ac_work/tree'
sys.path.insert(0,str(AC))
import certified_union_original_rows as LITERAL

BINDING=HERE/'CB882_WHOLE_HEIGHT_BOUND_STATE_BINDING.json'
BINDING_SHA='f0e49cf500739a4c878ef34c5f420e5430ca22dd9e147986615a4c546554ee38'
PREFIX='certified_cb882_root_bound_'

def declaration():
    assert hashlib.sha256(BINDING.read_bytes()).hexdigest()==BINDING_SHA
    return json.loads(BINDING.read_text())

def rows(state):
    binding=declaration();path=binding['original_path']
    assert state['id']==binding['original_id']and state['path'][:len(path)]==path
    answer=[]
    for co,rhs,name in LITERAL.rows(binding['state'],BINDING_SHA):
        assert name.startswith(LITERAL.PREFIX)
        answer.append((co,rhs,PREFIX+name[len(LITERAL.PREFIX):]))
    assert len(answer)==414
    return answer

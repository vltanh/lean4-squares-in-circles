"""Original-variable bounds from one unsplit complete-original C887 record."""
from pathlib import Path
import hashlib,json
import certified_union_original_rows as LITERAL

HERE=Path(__file__).resolve().parent
BINDING=HERE/'C887_WHOLE_HEIGHT_BOUND_STATE_BINDING.json'
BINDING_SHA='b24a9fa7675eb4d2330518da7481e5bca75700928035d202eeb9bf964a4adf2d'
PREFIX='certified_original_root_bound_'

def declaration():
    assert hashlib.sha256(BINDING.read_bytes()).hexdigest()==BINDING_SHA
    return json.loads(BINDING.read_text())

def rows(state):
    binding=declaration();path=binding['original_path']
    assert state['id']==binding['original_id']and state['path'][:len(path)]==path
    result=[]
    for co,rhs,name in LITERAL.rows(binding['state'],BINDING_SHA):
        assert name.startswith(LITERAL.PREFIX)
        result.append((co,rhs,PREFIX+name[len(LITERAL.PREFIX):]))
    return result

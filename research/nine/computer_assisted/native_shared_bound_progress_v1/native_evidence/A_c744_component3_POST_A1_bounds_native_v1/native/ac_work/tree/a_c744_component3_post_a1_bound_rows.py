"""Original-variable bounds valid only in the fixed A c744 component 3."""
from pathlib import Path
import hashlib,json
import certified_union_original_rows as LITERAL

HERE=Path(__file__).resolve().parent
BINDING=HERE/'A_C744_COMPONENT3_POST_A1_BOUND_STATE_BINDING.json'
BINDING_SHA='338e53440f35ab321c126d6050f9de36c89a0424141ea6e1f6ba2fa6b756c23d'
PREFIX='certified_a_c744_component3_post_a1_root_bound_'

def declaration():
    assert hashlib.sha256(BINDING.read_bytes()).hexdigest()==BINDING_SHA
    return json.loads(BINDING.read_text())

def rows(state,component,closed_domain):
    binding=declaration();path=binding['original_path']
    assert type(component)is int and component==3
    assert closed_domain==binding['closed_domain']
    assert state['id']==binding['original_id']and state['path'][:len(path)]==path
    result=[]
    for co,rhs,name in LITERAL.rows(binding['state'],BINDING_SHA):
        assert name.startswith(LITERAL.PREFIX)
        result.append((co,rhs,PREFIX+name[len(LITERAL.PREFIX):]))
    return result

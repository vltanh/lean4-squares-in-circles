"""Discovery-only affine endpoints; independent attachment is separate."""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json,sys
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
sys.path.insert(0,str(ROOT/'ac_work/tree'))
import certified_union_original_rows as EXPAND
BINDING=HERE/'PREMISE_BINDING.json'
BINDING_SHA='63458318a3681d677745baf4a00d8a738a5705c6276659174e59f440fa9a06e3'
TARGET='positive-c744bc031d40ee64'
ORIGINAL_PATH=[['angle',3,1],['angle_cut',[0,'0'],0],['inward_row_escape',[7,8],[4]]]
PREFIX='certified_a_c744_original_i64_bound_'
HEIGHT_NAME='certified_a_c744_original_i64_height_'+BINDING_SHA

def binding():
    assert hashlib.sha256(BINDING.read_bytes()).hexdigest()==BINDING_SHA
    value=json.loads(BINDING.read_text())
    assert value['scope']=='WHOLE_UNCHANGED_ORIGINAL_PARENT'and value['valid_on_whole_original']is True
    return value

def assert_caller(state):
    assert state['id']==TARGET and state['path'][:len(ORIGINAL_PATH)]==ORIGINAL_PATH
    assert len(state['angles'])==9 and len(state['positions'])==18 and len(state['scalar'])==36

def necessary_rows(state,source=None):
    assert_caller(state);source=binding()if source is None else source
    assert source['original_id']==TARGET and source['original_path']==ORIGINAL_PATH
    answer=[(co,rhs,PREFIX+name[len(EXPAND.PREFIX):])for co,rhs,name in EXPAND.rows(source['source_final_state'],BINDING_SHA)]
    assert len(answer)==414
    return answer

def necessary_height_row(state):
    assert_caller(state)
    return ((3,F(1)),(7,F(1)),(17,F(-2))),F(-16,25),HEIGHT_NAME

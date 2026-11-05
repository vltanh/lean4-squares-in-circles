"""Pinned source loading only; no geometric formulas or discovery imports."""
if not __debug__:
    raise RuntimeError('Exact corner attachment requires assertions.')
from hashlib import sha256
import importlib.util
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
FAMILY='c70be479889dc3bf9f3f250a7d0711724ae8542d13b8ac41278e315af47c7a22'
FOUNDATION='ac389f6184af6503294a13fb30c1da82e38d052a5d579bf43ccd4a0017b0485b'
MODELS={
    'full-strict-01100-root-v2':('strict_011_full_root_v2','strict_011_root.py'),
    'full-strict-01100-representative-root-v1':('strict_011_representative_root_v1','representative_strict_011_root.py')}
def digest(path):return sha256(Path(path).read_bytes()).hexdigest()
def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    result=importlib.util.module_from_spec(spec);spec.loader.exec_module(result)
    return result
def verify_family():
    assert digest(HERE/'ACCEPTED_FAMILY.json')==FAMILY
    value=json.loads((HERE/'ACCEPTED_FAMILY.json').read_text())
    assert len(value['files'])==15 and value['exact_accepted_bytes'] is True
    for name,entry in value['files'].items():
        path=(HERE/name).resolve()
        assert path.is_relative_to(HERE) and not (HERE/name).is_symlink()
        assert path.stat().st_size==entry['bytes'] and digest(path)==entry['sha256']
    assert digest(HERE/'accepted/PREMISE_BINDINGS.json')=='de2a53541969a1083aa002b4d663a6010deacbdbca53fd4e80b01b8094a892f1'
    return value
def verify_foundation(folder):
    folder=Path(folder).resolve()
    assert digest(folder/'CHECKPOINT_MANIFEST.json')==FOUNDATION
    value=json.loads((folder/'CHECKPOINT_MANIFEST.json').read_text())
    assert len(value['files'])==184 and value['conditional_terminals_installed'] is False
    for name,entry in value['files'].items():
        path=(folder/name).resolve()
        assert path.is_relative_to(folder) and not (folder/name).is_symlink()
        assert path.stat().st_size==entry['bytes'] and digest(path)==entry['sha256']
    return value
def load_model(foundation,document,producer):
    foundation=Path(foundation).resolve()
    verify_family();verify_foundation(foundation)
    folder,producer_name=MODELS[document['original_id']]
    root=foundation/folder
    assert document==json.loads((root/'snapshots/ROOT_DOCUMENT.json').read_text())
    assert document['mask']=='011/00' and document['radius_mode']=='strict'
    path=root/(producer_name if producer else 'independent_strict_011_adapter.py')
    model=load(('corner_producer_' if producer else 'corner_independent_')+folder,path)
    if producer:assert model.root_document()==document
    else:model.verify_root(document)
    return model

def verify_layer_binding(expected):
    assert digest(HERE/'PREMISE_BINDINGS.json')==expected
    binding=json.loads((HERE/'PREMISE_BINDINGS.json').read_text())
    assert binding['schema']=='new_strict011_four_product_same_state_layer_v2'
    assert binding['installed_in_tree_replay'] is False and binding['actual_weighted_use_gate_passed'] is False
    assert binding['original_cell_credit']==binding['whole_mask_credit']==0
    for name,entry in binding['files'].items():
        path=(HERE/name).resolve();assert path.is_relative_to(HERE) and not (HERE/name).is_symlink()
        assert path.stat().st_size==entry['bytes'] and digest(path)==entry['sha256']
    verify_family()
    return binding

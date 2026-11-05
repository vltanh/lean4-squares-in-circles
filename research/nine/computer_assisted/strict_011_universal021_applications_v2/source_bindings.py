"""Hash checking and explicit fresh scalar replay for a future actual use."""
if not __debug__:
    raise RuntimeError('Exact source binding requires assertions.')
from pathlib import Path
from hashlib import sha256
import json
import subprocess
import sys

HERE=Path(__file__).resolve().parent
DEPENDENCY_SHA='a561561ac870a02a0b55ac9aa64bde307977771a91efdc079bb8bff2aae4e626'
def digest(path):return sha256(Path(path).read_bytes()).hexdigest()
def verify_dependencies():
    assert digest(HERE/'DEPENDENCIES.json')==DEPENDENCY_SHA
    value=json.loads((HERE/'DEPENDENCIES.json').read_text())
    assert value['missing_old_guard_or_C_receipt_used'] is False
    for relative,entry in value['files'].items():
        path=(HERE/relative).resolve()
        assert path.is_relative_to(HERE) and path.stat().st_size==entry['bytes']
        assert digest(path)==entry['sha256']
    return value
def verify_binding(expected):
    assert digest(HERE/'PREMISE_BINDINGS.json')==expected
    value=json.loads((HERE/'PREMISE_BINDINGS.json').read_text())
    assert value['schema']=='new_strict011_universal021_HI_and_C_applications_v2'
    assert value['mask']=='011/00' and value['radius_mode']=='strict'
    assert value['middle_originals']==[2,7,8]
    assert value['installed_in_tree_replay'] is False
    assert value['original_cell_credit']==value['whole_mask_credit']==0
    verify_dependencies()
    for relative,entry in value['files'].items():
        path=(HERE/relative).resolve()
        assert path.is_relative_to(HERE) and path.stat().st_size==entry['bytes']
        assert digest(path)==entry['sha256']
    return value
def fresh_scalar_replay(expected_binding,new_output_folder):
    verify_binding(expected_binding)
    folder=Path(new_output_folder).resolve()
    assert not folder.is_relative_to(HERE)
    folder.mkdir(parents=True,exist_ok=False)
    report_path=folder/'SCALAR_REPLAY.json'
    with (folder/'SCALAR_REPLAY.log').open('x') as log:
        subprocess.run([sys.executable,'-B','-S',str(HERE/'theorem/check_universal_two_link.py'),
            str(HERE/'theorem/cover'),str(report_path)],check=True,stdout=log,stderr=subprocess.STDOUT)
    report=json.loads(report_path.read_text())
    assert report['status']=='PASS_COMPLETE_EXACT_TWO_LINK_SCALAR_COVER'
    assert (report['domains'],report['leaves'],report['bernstein_coefficients'])==(28,351,43875)
    assert report['frontier']==0 and report['strict_except_all_zero'] is True
    assert report['coefficient']=='211/1000' and report['target_variation']=='21/100'
    verify_binding(expected_binding)
    return dict(status='PASS_FRESH_ACCEPTED_UNIVERSAL021_SCALAR_FOR_NEW_STRICT011_APPLICATION',
        binding_sha256=expected_binding,report_sha256=digest(report_path),report=report)

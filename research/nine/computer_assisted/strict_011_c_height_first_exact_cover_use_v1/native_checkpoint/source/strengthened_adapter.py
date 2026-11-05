"""Prepared complete-tree attachment for reviewed strict011 row/guard sources.

The enclosing frozen 4/8/2 walk supplies the certified state ancestry. This
module loads no producer or numerical package. Accepted scalar replay is lazy
but mandatory before any conditional theorem terminal can be accepted.
"""
if not __debug__:
    raise RuntimeError('Exact strengthened replay rejects optimized Python.')

from copy import deepcopy
from hashlib import sha256
import importlib.util
import json
from pathlib import Path

CORNER_BINDING='efcf09c0494c1f36875533aeb3e4562173f84c49e8856de2d25b81eba781f778'
GUARD_BINDING='4c1fb0040f43281fd6e21bbece48d7293d0310a7341f490930c40ef51b689023'
FOUNDATION_BINDING='ac389f6184af6503294a13fb30c1da82e38d052a5d579bf43ccd4a0017b0485b'
TERMINAL_KIND='strict011_conditional_universal021_terminal_v1'

def digest(path):return sha256(Path(path).read_bytes()).hexdigest()
def load(name,path,expected):
    assert digest(path)==expected
    spec=importlib.util.spec_from_file_location(name,path)
    value=importlib.util.module_from_spec(spec);spec.loader.exec_module(value)
    return value
def packet(folder,binding_name,expected):
    folder=Path(folder).resolve()
    binding=folder/binding_name
    assert digest(binding)==expected
    value=json.loads(binding.read_text())
    hashes={str(binding):expected}
    for name,entry in value['files'].items():
        path=(folder/name).resolve()
        assert path.is_relative_to(folder)and not(folder/name).is_symlink()
        assert path.stat().st_size==entry['bytes']and digest(path)==entry['sha256']
        hashes[str(path)]=entry['sha256']
    return value,hashes

class Adapter:
    def __init__(self,foundation,corner_folder,guard_folder,document,scalar_output_folder):
        foundation=Path(foundation).resolve()
        self.corner_folder=Path(corner_folder).resolve()
        self.guard_folder=Path(guard_folder).resolve()
        self.scalar_output_folder=Path(scalar_output_folder).resolve()
        assert not self.scalar_output_folder.exists()
        assert all(not self.scalar_output_folder.is_relative_to(folder)
                   for folder in (foundation,self.corner_folder,self.guard_folder))
        self.document=deepcopy(document)
        base,base_hashes=packet(foundation,'CHECKPOINT_MANIFEST.json',FOUNDATION_BINDING)
        corners,corner_hashes=packet(self.corner_folder,'PREMISE_BINDINGS.json',CORNER_BINDING)
        guards,guard_hashes=packet(self.guard_folder,'PREMISE_BINDINGS.json',GUARD_BINDING)
        assert corners['accepted_literal_decoder_unchanged']is True
        assert guards['mask']=='011/00'and guards['radius_mode']=='strict'
        self.source_hashes={**base_hashes,**corner_hashes,**guard_hashes}
        self.source_hashes[str(Path(__file__).resolve())]=digest(__file__)
        CI=load('strengthened011_independent_corner_layer',
            self.corner_folder/'independent_strict011_four_product.py',
            corners['files']['independent_strict011_four_product.py']['sha256'])
        self.corner=CI.Adapter(foundation,self.document)
        self.guard=load('strengthened011_independent_guard',self.guard_folder/'independent_strict021_guards.py',
            guards['files']['independent_strict021_guards.py']['sha256'])
        self.guard_source=load('strengthened011_guard_scalar_source',self.guard_folder/'source_bindings.py',
            guards['files']['source_bindings.py']['sha256'])
        self.guard_source.verify_binding(GUARD_BINDING)
        self.guard.assert_caller(self.document)
        self.choices=self.corner.choices
        self.analytic=self.corner.analytic
        self.infer_angles=self.corner.infer_angles
        self.guard_audits=[]
        self.scalar_audit=None

    def binding_hashes(self):
        for path,expected in self.source_hashes.items():assert digest(path)==expected
        return dict(self.source_hashes)

    def rebuild(self,state,printed_rows):
        return self.corner.rebuild(state,printed_rows)

    def verify_early_terminal(self,state,terminal):
        if terminal.get('kind')!=TERMINAL_KIND:
            return self.corner.verify_early_terminal(state,terminal)
        assert set(terminal)=={'kind','attachment_binding_sha256','guard'}
        assert terminal['attachment_binding_sha256']==GUARD_BINDING
        # This reconstruction uses the same certified state, including exact
        # angle/frame and pair-box propagation, before checking the guard.
        _,bounds,current=self.corner.rebuild(state,[])
        verified=self.guard.verify_literal(terminal['guard'],current,self.document)
        if self.scalar_audit is None:
            self.scalar_audit=self.guard_source.fresh_scalar_replay(GUARD_BINDING,self.scalar_output_folder)
            assert self.scalar_audit['status']=='PASS_FRESH_ACCEPTED_UNIVERSAL021_SCALAR_FOR_NEW_STRICT011_APPLICATION'
        self.binding_hashes()
        view=self.corner.model.state_view(current)
        canonical=json.dumps(view,sort_keys=True,separators=(',',':')).encode()
        self.guard_audits.append(dict(kind=verified['kind'],middle_original=verified['middle_original'],
            caller_path=deepcopy(current['path']),certified_propagated_state_sha256=sha256(canonical).hexdigest(),
            guard=deepcopy(verified),fresh_scalar_report_sha256=self.scalar_audit['report_sha256'],
            certified_state_columns=len(bounds),whole_mask_credit=0))
        return True

    def final_audit(self):
        self.binding_hashes()
        assert bool(self.guard_audits)==(self.scalar_audit is not None)
        if self.scalar_audit is not None:
            report=self.scalar_output_folder/'SCALAR_REPLAY.json'
            assert digest(report)==self.scalar_audit['report_sha256']
        return dict(corner_layer_binding_sha256=CORNER_BINDING,
            universal021_application_binding_sha256=GUARD_BINDING,
            conditional_theorem_used=bool(self.guard_audits),conditional_terminals=len(self.guard_audits),
            terminal_audits=deepcopy(self.guard_audits),fresh_scalar_replay=deepcopy(self.scalar_audit),
            accepted_scalar_report_trusted_without_fresh_run=False,
            original_caller_scope='all nine physical originals,36 corners,36 pairs,five exact strict011 links',
            actual_LP_weighted_use_gate_claimed=False)

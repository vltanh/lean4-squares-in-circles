"""Exact accepted caller/scalar sources for a prepared C-height cover."""
if not __debug__:
    raise RuntimeError('C-height source checks require assertions.')
from hashlib import sha256
import importlib.util
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
GUARD_BINDING='4c1fb0040f43281fd6e21bbece48d7293d0310a7341f490930c40ef51b689023'
def digest(path):return sha256(Path(path).read_bytes()).hexdigest()
def load(name,path,expected):
    assert digest(path)==expected
    spec=importlib.util.spec_from_file_location(name,path)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    return module

class Sources:
    def __init__(self,guard_folder):
        self.folder=Path(guard_folder).resolve()
        binding=self.folder/'PREMISE_BINDINGS.json';assert digest(binding)==GUARD_BINDING
        self.binding=json.loads(binding.read_text())
        assert self.binding['mask']=='011/00'and self.binding['radius_mode']=='strict'
        assert self.binding['middle_originals']==[2,7,8]
        self.hashes={str(binding):GUARD_BINDING}
        for name,entry in self.binding['files'].items():
            path=(self.folder/name).resolve()
            assert path.is_relative_to(self.folder)and not(self.folder/name).is_symlink()
            assert path.stat().st_size==entry['bytes']and digest(path)==entry['sha256']
            self.hashes[str(path)]=entry['sha256']
        self.guard=load('C_height_accepted_independent_caller',self.folder/'independent_strict021_guards.py',
            self.binding['files']['independent_strict021_guards.py']['sha256'])
        self.scalar=load('C_height_accepted_fresh_scalar_gate',self.folder/'source_bindings.py',
            self.binding['files']['source_bindings.py']['sha256'])
        self.scalar.verify_binding(GUARD_BINDING)

    def check_unchanged(self):
        for path,expected in self.hashes.items():assert digest(path)==expected
        return dict(self.hashes)

    def assert_caller(self,document):
        return self.guard.assert_caller(document)

    def cone_order(self):
        return self.guard.original_cone_order()

    def fresh_scalar_gate_at_actual_use(self,new_output_folder):
        # This function intentionally has no argument accepting an old receipt.
        # A future complete ancestry adapter must invoke it before cover use.
        output=Path(new_output_folder).resolve()
        assert not output.exists()and not output.is_relative_to(HERE)
        assert not output.is_relative_to(self.folder)
        self.check_unchanged()
        audit=self.scalar.fresh_scalar_replay(GUARD_BINDING,output)
        self.check_unchanged()
        return dict(status='PASS_FRESH_SCALAR_PREREQUISITE_FOR_C_HEIGHT_COVER_ONLY',
            accepted_guard_binding_sha256=GUARD_BINDING,fresh_scalar=audit,
            complete_cover_ancestry_checked=False,cover_installed=False,
            original_cell_credit=0,whole_mask_credit=0)

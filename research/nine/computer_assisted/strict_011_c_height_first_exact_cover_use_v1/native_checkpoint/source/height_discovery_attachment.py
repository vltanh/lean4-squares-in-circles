"""Proposal-only height rows and atomic fresh-tree attachment; no LP entry.

This module never declares a full caller covered. The separately versioned
complete checker must freshly replay the scalar before accepting a height
union. Conditional arithmetic below remains useful before that global gate.
"""
if not __debug__:
    raise RuntimeError('C-height discovery attachment rejects optimized Python.')
from copy import deepcopy
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
import os
from pathlib import Path
from types import SimpleNamespace

HERE=Path(__file__).resolve().parent
BASE_SHA='58a85d7976aff42bbda10137f0c951985c674e220568f93d9244dfdf1b92275e'
STRENGTHENED_SHA='eda928822b3a9af0ca002a3f9a5c1c7b124b04ad7ab3cb0f3e2407961f3df0dd'
CORNER_BINDING='efcf09c0494c1f36875533aeb3e4562173f84c49e8856de2d25b81eba781f778'
SCHEMA='fresh_full_strict011_C_height_context_tree_v1'
def digest(path):return sha256(Path(path).read_bytes()).hexdigest()
def load(name,path,expected=None):
    if expected is not None:assert digest(path)==expected
    spec=importlib.util.spec_from_file_location(name,path)
    value=importlib.util.module_from_spec(spec);spec.loader.exec_module(value);return value
B=load('height_discovery_unchanged_atomic_and_rational_core',HERE/'accepted_base_discovery.py',BASE_SHA)
H=load('height_discovery_exact_context_definitions',HERE/'height_context_adapter.py')

class Context:
    def __init__(self,foundation,corner_folder,guard_folder,height_folder,guard_scalar_output,height_scalar_output):
        self.bundle=B.bootstrap(foundation)
        self.document=json.loads((self.bundle['checkpoint']/B.MODEL_NAME/'snapshots/ROOT_DOCUMENT.json').read_text())
        E=load('height_discovery_strengthened_exact_adapter',HERE/'strengthened_adapter.py',STRENGTHENED_SHA)
        self.base_exact=E.Adapter(self.bundle['checkpoint'],corner_folder,guard_folder,self.document,guard_scalar_output)
        self.manager=H.Manager(self.base_exact,self.bundle['I'],height_folder,guard_folder,self.document,height_scalar_output)
        folder=Path(corner_folder).resolve();assert digest(folder/'PREMISE_BINDINGS.json')==CORNER_BINDING
        value=json.loads((folder/'PREMISE_BINDINGS.json').read_text())
        C=load('height_discovery_accepted_corner_factory',folder/'strict011_four_product_rows.py',
            value['files']['strict011_four_product_rows.py']['sha256'])
        self.corner=C.Context(self.bundle['checkpoint'],self.document)
        hb=json.loads((Path(height_folder)/'PREMISE_BINDINGS.json').read_text())
        P=load('height_discovery_accepted_cover_producer',Path(height_folder)/'c_height_cover.py',
            hb['files']['c_height_cover.py']['sha256'])
        self.cover=P.literal(self.document,self.manager.sources)
        assert self.cover==self.manager.cover

    def conditional_bundle(self,expected_context):
        self.manager.validate_context(expected_context)
        adapter=self.manager.adapter(expected_context)
        original=self.bundle['I']
        class LocalAdapter:
            def __new__(cls):return adapter
            @staticmethod
            def verify_early_terminal(state,terminal):return adapter.verify_early_terminal(state,terminal)
        facade=SimpleNamespace(**{key:getattr(original,key)for key in dir(original)if not key.startswith('__')})
        facade.Adapter=LocalAdapter
        return dict(self.bundle,I=facade)

    def collect(self,state,expected_context,parameters=(),seed_midpoints=False):
        self.manager.validate_context(expected_context)
        rows,bounds,current,terminal=self.corner.collect(state,parameters,seed_midpoints)
        if terminal is None and expected_context is not None:
            # The producer and independent cover were already compared in full.
            literal=self.cover['branches'][expected_context['branch']]['affine_row']
            row=(tuple((column,F(value))for column,value in literal['coefficients']),F(literal['rhs']),literal['name'])
            assert row[2]not in {item[2]for item in rows}
            printed=dict(index=len(rows),**deepcopy(literal))
            assert self.manager.verify_height_literal(printed,expected_context)==row
            rows.append(row)
        return rows,bounds,current,terminal

    def proposed_height_partition(self,node,parent,parent_context,child_nodes):
        assert parent_context is None and len(child_nodes)==4
        assert all(type(child)is int and child>=0 for child in child_nodes)and len(set(child_nodes))==4
        split=dict(kind=H.HEIGHT_KIND,parent_node=node,
            parent_state_sha256=H.canonical_digest(self.bundle['P'].state_view(parent)),
            cover_binding_sha256=H.HEIGHT_BINDING,cover_literal=deepcopy(self.cover),
            children=[dict(branch=branch,node=child)for branch,child in enumerate(child_nodes)])
        # This checks literals and exact child definitions only. It does not
        # run the scalar or claim this candidate partition is an accepted tree.
        expected=self.manager.validate_union(node,parent,parent_context,split)
        generated=[]
        for branch,child in enumerate(child_nodes):
            context=dict(kind=H.CONTEXT_KIND,cover_binding_sha256=H.HEIGHT_BINDING,
                caller_root_document_sha256=self.cover['caller_root_document_sha256'],origin_node=node,
                parent_state_sha256=split['parent_state_sha256'],branch=branch)
            generated.append((child,deepcopy(parent),context))
        assert generated==expected
        return split,generated

class FreshHeightStore:
    """Fresh candidates only; context expectations originate here, not in files.

    There is deliberately no arbitrary-tree resume API. A future resume
    attachment must reconstruct expected contexts with the new full checker.
    """
    def __init__(self,context,folder):
        self.context=context;self.folder=Path(folder).resolve();assert not self.folder.exists()
        self.folder.mkdir(parents=True);(self.folder/'nodes').mkdir()
        raw=(context.bundle['checkpoint']/B.MODEL_NAME/'snapshots/ROOT_DOCUMENT.json').read_bytes()
        with(self.folder/'root_document.json').open('xb')as stream:
            stream.write(raw);stream.flush();os.fsync(stream.fileno())
        manifest=dict(schema=SCHEMA,root_document=dict(file='root_document.json',sha256=sha256(raw).hexdigest()),root=0,nodes=[])
        self.base=B.Store(context.bundle,self.folder,manifest)
        self._expected_contexts={0:None}
        state=context.bundle['P'].fresh_state()
        self._expected_initials={0:context.bundle['P'].state_view(state)}
        assert context.bundle['I'].verify_root(json.loads(raw))==state
        record=dict(status='OPEN',initial=context.bundle['P'].state_view(state),rounds=[],
            final=context.bundle['P'].state_view(state),height_context=None)
        context.manager.check_record_envelope(record,None)
        context.bundle['G'].check_record(record,state,context.manager.adapter(None))
        manifest['nodes']=[self.base.put_immutable(0,record)];self.base.install(manifest)

    @property
    def manifest(self):return self.base.manifest

    def expected_context(self,node):
        assert node in self._expected_contexts
        return deepcopy(self._expected_contexts[node])

    def record(self,node):
        value=self.base.record(node)
        self.context.manager.check_record_envelope(value,self.expected_context(node))
        assert value['initial']==self._expected_initials[node]
        return value

    def checked_final(self,node):
        record=self.record(node);I=self.context.bundle['P'];G=self.context.bundle['G']
        return G.check_record(record,I.parse_state(record['initial']),self.context.manager.adapter(self.expected_context(node)))

    def local_store(self,node):
        expected_context=self.expected_context(node)
        bundle=self.context.conditional_bundle(expected_context)
        class InheritedContextStore(B.Store):
            def put_immutable(inner,child,record):
                if 'height_context'in record:
                    self.context.manager.check_record_envelope(record,expected_context)
                    value=record
                else:value=dict(deepcopy(record),height_context=deepcopy(expected_context))
                return super().put_immutable(child,value)
        return InheritedContextStore(bundle,self.folder,self.manifest)

    def update_record(self,node,record):
        old=self.record(node)
        self.context.manager.check_record_envelope(record,self.expected_context(node))
        assert old['height_context']==record['height_context']
        local=self.local_store(node);result=local.update_record(node,record)
        self.base.manifest=deepcopy(local.manifest)
        return result

    def split(self,node,kind,argument=None,cut=None):
        parent_context=self.expected_context(node)
        if kind!=H.HEIGHT_KIND:
            assert kind in('proxy','sat','angle')
            audit,parent=self.checked_final(node);assert parent is not None
            local=self.local_store(node);children=local.split(node,kind,argument,cut)
            self.base.manifest=deepcopy(local.manifest)
            split=next(entry for entry in self.manifest['nodes']if entry['id']==node)['split']
            G,X,I=(self.context.bundle[name]for name in('G','X','I'))
            adapter=self.context.manager.adapter(parent_context)
            for child_entry in split['children']:
                child=child_entry['node']
                if kind=='angle':expected=I.angle_child(parent,argument,cut,child_entry['side'])
                elif kind=='sat':expected=G.sat_child(parent,argument,child_entry['choice'],adapter)
                else:expected=X.proxy_child(parent,argument,child_entry['choice'],adapter)
                self._expected_contexts[child]=deepcopy(parent_context)
                self._expected_initials[child]=self.context.bundle['P'].state_view(expected)
                self.record(child)
            return children
        assert argument is None and cut is None
        audit,parent=self.checked_final(node);assert parent is not None
        current=next(entry for entry in self.manifest['nodes']if entry['id']==node)
        assert 'split'not in current
        first=max(entry['id']for entry in self.manifest['nodes'])+1
        split,successors=self.context.proposed_height_partition(node,parent,parent_context,list(range(first,first+4)))
        entries=[]
        for child,state,child_context in successors:
            view=self.context.bundle['P'].state_view(state)
            record=dict(status='OPEN',initial=view,rounds=[],final=deepcopy(view),height_context=deepcopy(child_context))
            self.context.manager.check_record_envelope(record,child_context)
            self.context.bundle['G'].check_record(record,state,self.context.manager.adapter(child_context))
            entries.append(self.base.put_immutable(child,record))
        manifest=deepcopy(self.manifest)
        next(entry for entry in manifest['nodes']if entry['id']==node)['split']=split
        manifest['nodes'].extend(entries)
        self.base.install(manifest)  # Every immutable alternative is durable first.
        for child,state,child_context in successors:
            self._expected_contexts[child]=deepcopy(child_context)
            self._expected_initials[child]=self.context.bundle['P'].state_view(state)
        return [child for child,state,child_context in successors]

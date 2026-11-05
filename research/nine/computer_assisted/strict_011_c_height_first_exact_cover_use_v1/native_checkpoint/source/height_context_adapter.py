"""Checker-owned C-height domains, fixed literals, and fresh-cover source gate.

The base state dictionaries and their 4/8/2 path language are unchanged.
Local row arithmetic is conditional on a constructor-supplied height context.
Only the complete walk proves that context from an accepted four-way cover.
"""
if not __debug__:
    raise RuntimeError('Exact C-height context checks reject optimized Python.')
from copy import deepcopy
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path

HEIGHT_BINDING='06aba6fc518e44d1b859bccb9cc81b6ab57ef5b2df91970f654ba9fe8ab3fd79'
HEIGHT_KIND='strict011_C_height_four_way_v1'
CONTEXT_KIND='strict011_C_height_domain_v1'
ROW_PREFIX='strict011_C_height_complement_v1:'
CONTEXT_FIELDS={'kind','cover_binding_sha256','caller_root_document_sha256','origin_node','parent_state_sha256','branch'}

def digest(path):return sha256(Path(path).read_bytes()).hexdigest()
def canonical_digest(value):
    return sha256(json.dumps(value,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def load(name,path,expected):
    assert digest(path)==expected
    spec=importlib.util.spec_from_file_location(name,path)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);return module
def packet(folder):
    folder=Path(folder).resolve();binding=folder/'PREMISE_BINDINGS.json'
    assert digest(binding)==HEIGHT_BINDING
    value=json.loads(binding.read_text())
    assert value['schema']=='prepared_strict011_C_height_closed_complement_v1'
    assert value['mask']=='011/00'and value['radius_mode']=='strict'
    assert value['closed_alternatives']==4 and value['shared_boundary_faces_retained']is True
    hashes={str(binding):HEIGHT_BINDING}
    for name,entry in value['files'].items():
        path=(folder/name).resolve();assert path.is_relative_to(folder)and not(folder/name).is_symlink()
        assert path.stat().st_size==entry['bytes']and digest(path)==entry['sha256']
        hashes[str(path)]=entry['sha256']
    return folder,value,hashes

class Manager:
    def __init__(self,base_adapter,base_model,height_folder,guard_folder,document,scalar_output_folder):
        self.base=base_adapter;self.model=base_model;self.document=deepcopy(document)
        self.folder,binding,self.hashes=packet(height_folder)
        self.scalar_folder=Path(scalar_output_folder).resolve()
        assert not self.scalar_folder.exists()
        frozen_folders=(self.folder,Path(__file__).resolve().parent,
            Path(base_model.__file__).resolve().parent.parent,
            Path(base_adapter.corner_folder).resolve(),Path(base_adapter.guard_folder).resolve())
        assert all(not self.scalar_folder.is_relative_to(folder)for folder in frozen_folders)
        other_scalar=Path(base_adapter.scalar_output_folder).resolve()
        assert not self.scalar_folder.is_relative_to(other_scalar)and not other_scalar.is_relative_to(self.scalar_folder)
        S=load('C_height_tree_accepted_sources',self.folder/'accepted_sources.py',binding['files']['accepted_sources.py']['sha256'])
        self.sources=S.Sources(guard_folder)
        self.decoder=load('C_height_tree_independent_cover',self.folder/'independent_c_height_cover.py',
            binding['files']['independent_c_height_cover.py']['sha256'])
        self.cover=self.decoder.reconstruct(document,self.sources)
        self.decoder.verify_literal(self.cover,document,self.sources)
        self.hashes.update(self.sources.check_unchanged())
        self.hashes[str(Path(__file__).resolve())]=digest(__file__)
        self.scalar_audit=None;self.unions=[]

    def binding_hashes(self):
        for path,expected in self.hashes.items():assert digest(path)==expected
        return dict(self.hashes)

    def validate_context(self,context):
        if context is None:return
        assert type(context)is dict and set(context)==CONTEXT_FIELDS
        assert context['kind']==CONTEXT_KIND and context['cover_binding_sha256']==HEIGHT_BINDING
        assert context['caller_root_document_sha256']==self.cover['caller_root_document_sha256']
        assert type(context['origin_node'])is int and context['origin_node']>=0
        assert type(context['branch'])is int and 0<=context['branch']<4
        text=context['parent_state_sha256'];assert type(text)is str and len(text)==64
        assert all(letter in '0123456789abcdef'for letter in text)

    def parent_hash(self,state):
        self.model.validate_state(state)
        return canonical_digest(self.model.state_view(state))

    def child_context(self,node,state,parent_context,branch):
        assert parent_context is None,'A second C-height union on one path is not supported.'
        assert type(node)is int and node>=0 and type(branch)is int and 0<=branch<4
        return dict(kind=CONTEXT_KIND,cover_binding_sha256=HEIGHT_BINDING,
            caller_root_document_sha256=self.cover['caller_root_document_sha256'],
            origin_node=node,parent_state_sha256=self.parent_hash(state),branch=branch)

    def validate_union(self,node,state,parent_context,split):
        assert parent_context is None,'A second C-height union on one path is not supported.'
        assert set(split)=={'kind','parent_node','parent_state_sha256','cover_binding_sha256','cover_literal','children'}
        assert split['kind']==HEIGHT_KIND and type(split['parent_node'])is int and split['parent_node']==node
        assert split['parent_state_sha256']==self.parent_hash(state)
        assert split['cover_binding_sha256']==HEIGHT_BINDING
        self.decoder.verify_literal(split['cover_literal'],self.document,self.sources)
        children=split['children'];assert isinstance(children,list)and len(children)==4
        choices=[];nodes=[]
        for child in children:
            assert set(child)=={'branch','node'}
            assert type(child['branch'])is int and type(child['node'])is int and child['node']>=0
            choices.append(child['branch']);nodes.append(child['node'])
        assert set(choices)==set(range(4))and len(set(choices))==4
        assert len(set(nodes))==4 and node not in nodes
        return [(child['node'],deepcopy(state),self.child_context(node,state,parent_context,child['branch']))for child in children]

    def ensure_scalar(self):
        if self.scalar_audit is None:
            self.scalar_audit=self.sources.fresh_scalar_gate_at_actual_use(self.scalar_folder)
            assert self.scalar_audit['status']=='PASS_FRESH_SCALAR_PREREQUISITE_FOR_C_HEIGHT_COVER_ONLY'
        self.binding_hashes()
        return self.scalar_audit

    def accept_union(self,node,state,parent_context,split):
        successors=self.validate_union(node,state,parent_context,split)
        # Coverage is not accepted and no child is replayed before this gate.
        fresh=self.ensure_scalar()
        self.unions.append(dict(node=node,parent_state_sha256=self.parent_hash(state),
            cover_binding_sha256=HEIGHT_BINDING,branches=[child['branch']for child in split['children']],
            child_nodes=[child['node']for child in split['children']],
            fresh_scalar_report_sha256=fresh['fresh_scalar']['report_sha256']))
        return successors

    def assert_active_context(self,context):
        self.validate_context(context)
        if context is not None:
            assert self.scalar_audit is not None,'Complete ancestry requires a fresh scalar gate before height children.'
            assert any(item['node']==context['origin_node']and item['parent_state_sha256']==context['parent_state_sha256']
                       for item in self.unions),'Context does not originate in an accepted ancestor union.'

    def check_record_envelope(self,record,expected_context):
        self.validate_context(expected_context)
        assert 'height_context'in record
        self.validate_context(record['height_context'])
        assert record['height_context']==expected_context

    def height_row(self,context):
        self.validate_context(context);assert context is not None
        row=deepcopy(self.cover['branches'][context['branch']]['affine_row'])
        assert row['name']==ROW_PREFIX+str(context['branch'])
        return row

    def verify_height_literal(self,printed,context):
        assert context is not None,'Height literals are forbidden outside a selected height domain.'
        self.validate_context(context)
        assert set(printed)=={'index','name','coefficients','rhs'}
        assert type(printed['index'])is int and printed['index']>=0
        row={key:printed[key]for key in('name','coefficients','rhs')}
        assert row==self.height_row(context)
        return (tuple((column,F(value))for column,value in row['coefficients']),F(row['rhs']),row['name'])

    def adapter(self,context):
        self.validate_context(context)
        return ContextAdapter(self,deepcopy(context))

    def final_audit(self):
        self.binding_hashes()
        assert bool(self.unions)==(self.scalar_audit is not None)
        if self.scalar_audit is not None:
            assert digest(self.scalar_folder/'SCALAR_REPLAY.json')==self.scalar_audit['fresh_scalar']['report_sha256']
        return dict(cover_binding_sha256=HEIGHT_BINDING,complete_height_unions=len(self.unions),
            union_audits=deepcopy(self.unions),fresh_scalar_replay=deepcopy(self.scalar_audit),
            root_height_context=None,base_state_dictionaries_unchanged=True,
            contexts_reconstructed_from_complete_parent_unions=True,second_height_union_on_path_allowed=False,
            physical_originals=9,original_corners=36,original_pairs=36,marked_cones=5,
            mask='011/00',radius_mode='strict',original_cell_credit=0,automatic_mask_credit=0)

class ContextAdapter:
    def __init__(self,manager,context):
        self.manager=manager;self.context=context;self.base=manager.base
        self.choices=self.base.choices;self.analytic=self.base.analytic;self.infer_angles=self.base.infer_angles

    def rebuild(self,state,printed_rows):
        ordinary=[];height=[];indices=set()
        for item in printed_rows:
            index=item['index'];assert type(index)is int and index>=0 and index not in indices
            indices.add(index);assert type(item['name'])is str
            (height if item['name'].startswith(ROW_PREFIX)else ordinary).append(item)
        rows,bounds,current=self.base.rebuild(state,ordinary)
        for item in height:
            assert item['index']not in rows
            rows[item['index']]=self.manager.verify_height_literal(item,self.context)
        assert set(rows)==indices
        return rows,bounds,current

    def verify_early_terminal(self,state,terminal):
        return self.base.verify_early_terminal(state,terminal)

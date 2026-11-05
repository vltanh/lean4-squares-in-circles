"""Independent current-box attachment; accepted corner decoder is unchanged."""
if not __debug__:
    raise RuntimeError('Exact corner replay requires assertions.')
from fractions import Fraction as F
import importlib.util
from pathlib import Path

HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('strict011_four_product_independent_dependencies',HERE/'layer_dependencies.py')
D=importlib.util.module_from_spec(spec);spec.loader.exec_module(D)

class Adapter:
    def __init__(self,foundation,document):
        self.model=D.load_model(foundation,document,False)
        self.document=document
        self.decoder=D.load('strict011_accepted_four_product_independent',HERE/'accepted/independent_physical_unit_four_corner_rows.py')
        self.choices=self.model.Adapter.choices
        self.analytic=self.model.Adapter.analytic
        self.infer_angles=self.model.Adapter.infer_angles

    def verify_root(self,document):
        assert document==self.document
        return self.model.verify_root(document)

    def rebuild(self,state,printed_rows):
        self.model.validate_state(state)
        ordinary=[];additional=[];indices=set()
        for item in printed_rows:
            index=item['index']
            assert type(index)is int and index>=0 and index not in indices
            indices.add(index)
            assert type(item['name'])is str
            (additional if item['name'].startswith(self.decoder.PREFIX) else ordinary).append(item)
        answer,bounds,current=self.model.Adapter.rebuild(state,ordinary)
        for item in additional:
            literal=(tuple((column,F(value))for column,value in item['coefficients']),F(item['rhs']),item['name'])
            assert all(type(column)is int and 0<=column<54 for column,value in literal[0])
            assert self.decoder.verify_literal(literal,current['positions'],current['scalar'])==literal
            assert item['index']not in answer
            answer[item['index']]=literal
        assert set(answer)==indices
        return answer,bounds,current

    def verify_early_terminal(self,state,terminal):
        return self.model.Adapter.verify_early_terminal(state,terminal)

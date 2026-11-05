"""New same-state producer layer around unchanged accepted corner formulas."""
if not __debug__:
    raise RuntimeError('Exact corner rows require assertions.')
from fractions import Fraction as F
import importlib.util
from itertools import product
from pathlib import Path

HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('strict011_four_product_producer_dependencies',HERE/'layer_dependencies.py')
D=importlib.util.module_from_spec(spec);spec.loader.exec_module(D)

class Context:
    def __init__(self,foundation,document):
        self.model=D.load_model(foundation,document,True)
        self.document=document
        self.exact=D.load('strict011_accepted_four_product_producer',HERE/'accepted/physical_unit_four_corner_rows.py')

    def collect(self,state,parameters=(),seed_midpoints=False):
        rows,bounds,current,terminal=self.model.collect(state)
        if terminal is not None:return rows,bounds,current,terminal
        selected=list(parameters)
        if seed_midpoints:selected.extend(self.midpoint_parameters(current))
        names={row[2] for row in rows}
        for parameters in selected:
            row=self.exact.row(current['positions'],current['scalar'],*parameters)
            if row[2] not in names:rows.append(row);names.add(row[2])
        assert len(rows)==len(names)
        return rows,bounds,current,None

    @staticmethod
    def midpoint_parameters(current):
        parameters=[]
        for i,e,t in product(range(9),(-1,1),(-1,1)):
            px=sum(map(F,current['positions'][2*i]))/2
            py=sum(map(F,current['positions'][2*i+1]))/2
            for bits in product((0,1),repeat=4):parameters.append((i,e,t,px,py,bits))
        assert len(parameters)==576
        return parameters

    def row_on_current(self,current,parameters):
        self.model.validate_state(current)
        return self.exact.row(current['positions'],current['scalar'],*parameters)

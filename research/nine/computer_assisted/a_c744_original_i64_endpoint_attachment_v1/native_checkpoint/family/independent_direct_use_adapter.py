"""New endpoint literals on the unchanged independent physical propagation."""
from fractions import Fraction as F
import independent_original_i64_bounds as ROWS
import verify_c887_ownerfree_physical_tree as BASE

class Adapter(BASE.Adapter):
    def __init__(self,checker,binding):
        super().__init__(checker);self.binding=binding;self.endpoint_uses=0;self.height_uses=0
    def rebuild(self,state,printed):
        ROWS.assert_caller(state)
        def extra(item):return item['name'].startswith(ROWS.PREFIX)or item['name']==ROWS.HEIGHT_NAME
        answer,bounds,current=super().rebuild(state,[item for item in printed if not extra(item)])
        for item in printed:
            if not extra(item):continue
            literal=(tuple((i,F(value))for i,value in item['coefficients']),F(item['rhs']),item['name'])
            ROWS.verify_literal(literal,state,self.binding)
            assert item['index']not in answer;answer[item['index']]=literal
            if item['name']==ROWS.HEIGHT_NAME:self.height_uses+=1
            else:self.endpoint_uses+=1
        return answer,bounds,current

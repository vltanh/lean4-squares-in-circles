"""General cone rows checked against independently reconstructed angles."""
from fractions import Fraction as F
import sys
import independent_c_new_rows_adapter as OLD
import independent_general_center_cone_rows as GENERAL
COUNTS={'general_cone':0}
def extend_adapter(parent,allow_rotating=False):
 inherited=OLD.extend_adapter(parent,allow_rotating=allow_rotating)
 class Adapter(inherited):
  def rebuild(self,state,printed):
   ordinary=[row for row in printed if not row['name'].startswith(GENERAL.PREFIX)]
   answer,bounds,physical=super().rebuild(state,ordinary)
   for row in printed:
    if not row['name'].startswith(GENERAL.PREFIX):continue
    literal=(tuple((j,F(c))for j,c in row['coefficients']),F(row['rhs']),row['name'])
    GENERAL.verify_literal(literal,physical['angles']);assert row['index']not in answer
    answer[row['index']]=literal;COUNTS['general_cone']+=1
   return answer,bounds,physical
 return Adapter

def no_producers():
 OLD.no_producers();assert not any(name in sys.modules for name in('physical_general_center_cone_rows','c_general_center_runtime'))
 COUNTS.update(OLD.COUNTS)

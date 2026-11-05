"""Exact four-case closed original-inset cover; no numerical imports."""
from copy import deepcopy
from itertools import product


def proxy_child(parent,pair,choice,adapter):
 pair=tuple(pair);choice=tuple(choice)
 assert len(pair)==2 and all(type(i)is int for i in pair)and 0<=pair[0]<pair[1]<9
 assert len(choice)==2 and all(type(i)is int for i in choice)
 assert choice[0]in(0,1)and choice[1]in(-1,1)
 path=deepcopy(parent['path'])+[['proxy',list(pair),list(choice)]]
 child=deepcopy(parent);child['path']=path;child['choices']=adapter.choices(path)
 return child


def check_choices(choices):
 actual=[tuple(choice)for choice in choices]
 assert len(actual)==4 and len(set(actual))==4
 assert set(actual)==set(product((0,1),(-1,1)))
 return True


def check_complete_proxy_cover(parent,pair,children,adapter,check_record):
 """Pass the desired frozen scalar/difference or diagonal check_record API."""
 check_choices([choice for choice,record in children])
 reports=[];remaining=[]
 for choice,record in children:
  report,state=check_record(record,proxy_child(parent,pair,choice,adapter),adapter)
  reports.append(dict(choice=list(choice),audit=report))
  if state is not None:remaining.append((tuple(choice),state))
 return dict(status='PASS_COMPLETE_PHYSICAL_PROXY_COVER'if not remaining else'PASS_PARTIAL_PHYSICAL_PROXY_COVER',
  pair=list(pair),all_four_closed_original_inset_alternatives=True,closed_shared_faces_retained=True,
  excluded_alternatives=4-len(remaining),children=reports,whole_original_credit=0,whole_mask_credit=0),remaining

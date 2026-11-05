"""Exact filename transport for the accepted C height archives.

Only complete JSON string values in one SHA-pinned declaration are changed.
All proof/certificate bytes, coefficients, guards, and archived checkers remain
unchanged. The original archived loader is executed in a fresh stdlib child.
"""
from pathlib import Path
import hashlib,json,subprocess,sys,runpy
from types import SimpleNamespace
HERE=Path(__file__).resolve().parent
BINDING=HERE/'source/ac_work/tree/C_HEIGHT_EXCLUSION_CONSEQUENCES_BINDING.json'
BINDING_SHA='0ba7dd5ecd014197634b57df6c51b1d1fa1f8a258ff44f48464d4b8b0b55eebb'
LOADER=HERE/'source/ac_work/tree/replay_c_archived_height_exclusions.py'
LOADER_SHA='937912734bd47b820577eaa4933dbfd4daa049ce2f8721a5002dcdcede69c308'
REAL_LOADS=json.loads
REAL_RUN=subprocess.run

def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def inventory():
 assert sha(BINDING)==BINDING_SHA and sha(LOADER)==LOADER_SHA
 original=REAL_LOADS(BINDING.read_text());aliases={};inputs={str(BINDING):BINDING_SHA,str(LOADER):LOADER_SHA}
 assert original['schema']=='C_original_archived_height_exclusion_consequences_v1'
 assert [e['key']for e in original['originals']]==['c887','cb882']
 for entry in original['originals']:
  key=entry['key'];logical=Path(entry['archive']['folder']);local=HERE/(key+'_whole_eight_checkpoint_package')
  assert str(logical)=='/workspace/scratch/f9f48fcfb253/ac_work/'+key+'/'+local.name
  manifest=local/'SHA256_MANIFEST.json';assert sha(manifest)==entry['archive']['manifest_sha256'];inputs[str(manifest)]=sha(manifest)
  aliases[str(logical)]=str(local)
  refs=[entry['independent_source_checker'],entry['whole_original_parent'],entry['closed_domain_table']]+[c['certificate']for c in entry['consequences']]
  for ref in refs:
   old=Path(ref['path']);assert old.is_relative_to(logical)
   target=local/old.relative_to(logical);assert target.is_relative_to(local)and sha(target)==ref['sha256']
   aliases[str(old)]=str(target);inputs[str(target)]=ref['sha256']
 assert len(aliases)==11 and len(set(aliases.values()))==11
 return aliases,inputs

def map_values(value,aliases):
 if type(value)is str:return aliases.get(value,value)
 if type(value)is list:return [map_values(v,aliases)for v in value]
 if type(value)is dict:return {k:map_values(v,aliases)for k,v in value.items()}
 return value

def install(height=None):
 aliases,inputs=inventory()
 def exact_loads(s,*args,**kw):
  result=REAL_LOADS(s,*args,**kw)
  if not args and not kw and isinstance(s,(str,bytes,bytearray)):
   raw=s.encode()if isinstance(s,str)else bytes(s)
   if hashlib.sha256(raw).hexdigest()==BINDING_SHA:return map_values(result,aliases)
  return result
 json.loads=exact_loads
 if height is not None:
  assert height.BINDING==BINDING and height.BINDING_SHA==BINDING_SHA and height.LOADER==LOADER and height.LOADER_SHA==LOADER_SHA
  def run_child(args,**kwargs):
   assert type(args)is list and len(args)==6
   assert args[:4]==[sys.executable,'-B','-S',str(LOADER)]and args[4]in('c887','cb882')
   assert kwargs.get('check')is True
   return REAL_RUN([sys.executable,'-B','-S',str(Path(__file__).resolve()),'--archived',args[4],args[5]],**kwargs)
  height.subprocess=SimpleNamespace(run=run_child,STDOUT=subprocess.STDOUT)
 return {'schema':'exact_c_height_filename_transport_v1','raw_binding_sha256':BINDING_SHA,'unchanged_archived_loader_sha256':LOADER_SHA,'exact_string_aliases':aliases,'input_sha256':inputs,'transport_source_sha256':sha(__file__),'certificate_bytes_rewritten':False,'checker_code_rewritten':False,'numerical_producer_imported':False}

if __name__=='__main__':
 assert __debug__ and len(sys.argv)==4 and sys.argv[1]=='--archived'and sys.argv[2]in('c887','cb882')
 key,output=sys.argv[2:];install();sys.argv=[str(LOADER),key,output];runpy.run_path(str(LOADER),run_name='__main__')

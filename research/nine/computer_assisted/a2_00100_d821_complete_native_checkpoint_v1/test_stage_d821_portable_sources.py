"""Synthetic negative controls for the D821 source-freeze staging gate."""
import hashlib, json, tempfile, unittest
from pathlib import Path
from stage_d821_portable_sources import ID, PATH, digest, stage

class StageTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.src = self.root / 'source'; self.src.mkdir()
        self.paths = []
        for k in range(50):
            p = self.src / f'record{k:03d}.json'
            p.write_text(json.dumps({'item':k})+'\n')
            self.paths.append(p)
        self.report = self.root / 'report.json'
        self.plan = self.root / 'plan.json'
        self.audit = self.root / 'audit.json'
        self.ledger = self.root / 'register.json'
        self.output = self.root / 'frozen'
        self.report_body = {
          'status':'PASS_COMPLETE_ORIGINAL_CELL','original_id':ID,
          'original_path':PATH,'mask':'001/00','whole_original_proved':True,
          'complete_closed_complement_domains':5,'grafted_cover_nodes':[{} for _ in range(46)],
          'input_sha256':{str(p):digest(p) for p in self.paths},
          'checker_sha256':{str(self.paths[0]):digest(self.paths[0])}}
        self.plan_body = {
            'schema':'D821_grafted_five_complement_complete_original_plan_v1',
            'original_id':ID, 'component_trees':{s: {'path':str(self.paths[j]), 'sha256':digest(self.paths[j])} for j,s in enumerate(['0','1','3','4'])}}
        self.ledger_body={'cells':[{'id':ID,'path':PATH,'status':'OPEN'}]+[{'id':str(i)} for i in range(230)]}
        self.write()

    def write(self):
        self.report.write_text(json.dumps(self.report_body))
        self.plan.write_text(json.dumps(self.plan_body))
        self.audit.write_text(json.dumps({'report_sha256':digest(self.report),'trees':46,
                                          'nodes':650,'independent_affine_terminal_sums':[{} for _ in range(242)]}))
        self.ledger.write_text(json.dumps(self.ledger_body))

    def run_stage(self):
        return stage(self.root,self.report,self.plan,self.audit,self.ledger,self.output,
                     expected_report=digest(self.report),expected_plan=digest(self.plan),expected_audit=digest(self.audit))

    def test_complete_snapshot(self):
        result=self.run_stage()
        self.assertEqual(result['inputs'],50)
        self.assertEqual(result['original_cells_closed'],0)
        data=json.loads((self.output/'STAGING_MANIFEST.json').read_text())
        self.assertFalse(data['fresh_portable_replay_completed'])
        self.assertEqual(len(data['inputs']),50)

    def test_changed_source_is_rejected(self):
        self.paths[8].write_text('tampered')
        with self.assertRaises(ValueError):self.run_stage()
        self.assertFalse(self.output.exists())

    def test_missing_source_is_rejected(self):
        self.paths[8].unlink()
        with self.assertRaises((ValueError,FileNotFoundError)):self.run_stage()
        self.assertFalse(self.output.exists())

    def test_mismatched_duplicate_ref_is_rejected(self):
        self.plan_body['component_trees']['0']['sha256']='0'*64
        self.write()
        with self.assertRaises(ValueError):self.run_stage()
        self.assertFalse(self.output.exists())

    def test_out_of_root_path_is_rejected(self):
        external=Path(tempfile.mkdtemp())/'external.json'
        self.addCleanup(lambda: external.parent.rmdir())
        external.write_text('x')
        self.addCleanup(external.unlink)
        self.plan_body['component_trees']['0']={'path':str(external),'sha256':digest(external)}
        self.write()
        with self.assertRaises(ValueError):self.run_stage()

    def test_closed_cell_cannot_be_staged(self):
        self.ledger_body['cells'][0]['status']='CLOSED_STRICT'
        self.write()
        with self.assertRaises(ValueError):self.run_stage()

if __name__=='__main__':unittest.main()

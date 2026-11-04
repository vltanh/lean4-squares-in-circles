"""Discovery for the unchanged Cd402 original; no C887/Cb882 consequences."""
from pathlib import Path
from copy import deepcopy
import hashlib
import json
import sys

HERE = Path(__file__).resolve().parent
WORK = HERE.parent.parent
sys.path.insert(0, str(WORK / 'ac_work/tree'))
import ac_objective_unit_four_corner_runtime as BASE
from ac_objective_unit_four_corner_runtime import E, stateview, state_from_view

TARGET = 'negative-d4021ade840b985c'
ORIGINAL_PATH = [['angle', 3, 0], ['angle_cut', [0, '0'], 1],
                 ['alternate_four_escape', [1, 7], [2]]]
DECLARATION = HERE / 'CD402_FRESH_ORIGINAL.json'
DECLARATION_SHA = '9b1a3ee9d3d327b7bbdb368e0b48a486ac30df43c143dcbf1733a5d5647d5311'


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


class Context(BASE.Context):
    def original(self):
        assert sha(DECLARATION) == DECLARATION_SHA
        declaration = json.loads(DECLARATION.read_text())
        assert declaration['id'] == TARGET and declaration['original_path'] == ORIGINAL_PATH
        register = declaration['original_register']
        assert sha(register['path']) == register['sha256']
        cells = json.loads(Path(register['path']).read_text())['cells']
        matches = [cell for cell in cells if cell['id'] == TARGET]
        assert len(matches) == 1 and matches[0]['path'] == ORIGINAL_PATH
        angles, positions, choices = self.V.reconstruct(ORIGINAL_PATH)
        angles = tuple(map(tuple, angles))
        positions = tuple(map(tuple, positions))
        state = dict(id=TARGET, path=deepcopy(ORIGINAL_PATH), angles=angles,
            positions=positions, choices=choices, scalar=self.K.analytic(angles),
            differences={}, diagonal={})
        assert E.stateview(state) == declaration['initial']
        return state, declaration

    def collect(self, state):
        assert state['id'] == TARGET and state['path'][:len(ORIGINAL_PATH)] == ORIGINAL_PATH
        return super().collect(state)


def source_bindings():
    answer = dict(BASE.sources())
    answer[str(DECLARATION)] = DECLARATION_SHA
    answer[str(Path(__file__).resolve())] = sha(__file__)
    for module in tuple(sys.modules.values()):
        name = getattr(module, '__file__', None)
        if name is None:
            continue
        path = Path(name).resolve()
        if path.is_relative_to(WORK) and path.is_file():
            answer[str(path)] = sha(path)
    return answer

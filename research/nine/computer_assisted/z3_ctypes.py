#!/usr/bin/env python3
"""Run SMT-LIB through an installed Z3 shared library, without z3py.

Solver answers are discovery output, not independently replayed certificates.
Set solver resource limits in the supplied SMT-LIB. This module runs no Lean.
"""
from __future__ import annotations
import ctypes as C
import ctypes.util
import sys
from pathlib import Path

def run(text: str) -> str:
    if not isinstance(text, str):
        raise TypeError('SMT-LIB input must be text')
    name = ctypes.util.find_library('z3')
    if not name:
        raise RuntimeError('No Z3 shared library found')
    lib = C.CDLL(name)
    lib.Z3_mk_config.restype = C.c_void_p
    lib.Z3_mk_context.argtypes = [C.c_void_p]
    lib.Z3_mk_context.restype = C.c_void_p
    lib.Z3_del_config.argtypes = [C.c_void_p]
    lib.Z3_del_context.argtypes = [C.c_void_p]
    lib.Z3_eval_smtlib2_string.argtypes = [C.c_void_p, C.c_char_p]
    lib.Z3_eval_smtlib2_string.restype = C.c_char_p
    handler_type = C.CFUNCTYPE(None, C.c_void_p, C.c_uint)
    lib.Z3_set_error_handler.argtypes = [C.c_void_p, handler_type]
    lib.Z3_get_error_msg.argtypes = [C.c_void_p, C.c_uint]
    lib.Z3_get_error_msg.restype = C.c_char_p
    errors = []
    @handler_type
    def on_error(context, code):
        message = lib.Z3_get_error_msg(context, code)
        errors.append(message.decode() if message else str(code))
    config = lib.Z3_mk_config()
    if not config:
        raise RuntimeError('Z3 configuration allocation failed')
    try:
        context = lib.Z3_mk_context(config)
    finally:
        lib.Z3_del_config(config)
    if not context:
        raise RuntimeError('Z3 context allocation failed')
    try:
        lib.Z3_set_error_handler(context, on_error)
        answer = lib.Z3_eval_smtlib2_string(context, text.encode('utf-8'))
        if errors:
            raise RuntimeError('; '.join(errors))
        if answer is None:
            raise RuntimeError('Z3 returned no response')
        return answer.decode('utf-8')
    finally:
        lib.Z3_del_context(context)

if __name__ == '__main__':
    source = Path(sys.argv[1]).read_text() if len(sys.argv) > 1 else sys.stdin.read()
    print(run(source), end='')

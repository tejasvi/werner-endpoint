"""Max of the abs-bound passes (cut-(3,) blocks and Stiefel rows)."""
import sys, glob, pickle, math
import numpy as np
for tag in sys.argv[1:]:
    files = sorted(glob.glob('<ROOT>/independent_check/alld/work/e_%s_c*.pkl' % tag))
    m3 = ms = 0.0
    nv = 0
    for fn in files:
        R = pickle.load(open(fn, 'rb'))
        nv += len(R['vars'])
        for bi, dct in R['F3'].items():
            for i, A in dct.items():
                m3 = max(m3, float(A.max()))
        for i, A in R['ST'].items():
            ms = max(ms, float(A.max()))
    print('%s: %d files, %d variables; max F3 bound %.3e (%d bits), max St bound %.3e (%d bits)' % (
        tag, len(files), nv, m3, math.ceil(math.log2(m3 + 1)), ms, math.ceil(math.log2(ms + 1)) if ms > 0 else 0))

"""Restricted unpickler: only numpy array reconstruction and fractions.Fraction may be imported."""
import pickle

ALLOWED = {
    ('numpy._core.multiarray', '_reconstruct'),
    ('numpy.core.multiarray', '_reconstruct'),
    ('numpy._core.multiarray', 'scalar'),
    ('numpy.core.multiarray', 'scalar'),
    ('numpy', 'ndarray'),
    ('numpy', 'dtype'),
    ('fractions', 'Fraction'),
}


class SafeUnpickler(pickle.Unpickler):
    def find_class(self, module, name):
        if (module, name) in ALLOWED:
            return super().find_class(module, name)
        raise pickle.UnpicklingError('blocked global %s.%s' % (module, name))


def load(path):
    with open(path, 'rb') as fh:
        return SafeUnpickler(fh).load()


def describe(obj, depth=0, maxdepth=3, name='', maxitems=40):
    """Short structural description (types, shapes, small values)."""
    import numpy as np
    pad = '  ' * depth
    if isinstance(obj, dict):
        print('%s%s dict[%d]' % (pad, name, len(obj)))
        if depth < maxdepth:
            for i, (k, v) in enumerate(obj.items()):
                if i >= maxitems:
                    print('%s  ... (%d more keys)' % (pad, len(obj) - maxitems))
                    break
                describe(v, depth + 1, maxdepth, repr(k)[:80], maxitems)
    elif isinstance(obj, (list, tuple)):
        print('%s%s %s[%d]' % (pad, name, type(obj).__name__, len(obj)))
        if depth < maxdepth and len(obj):
            describe(obj[0], depth + 1, maxdepth, '[0]', maxitems)
            if len(obj) > 1:
                describe(obj[-1], depth + 1, maxdepth, '[-1]', maxitems)
    elif isinstance(obj, np.ndarray):
        extra = ''
        if obj.size and obj.size <= 8:
            extra = ' = %r' % (obj.tolist(),)
        elif obj.size and obj.dtype == object:
            extra = ' first=%r' % (obj.ravel()[0],)
        print('%s%s ndarray %s %s%s' % (pad, name, obj.dtype, obj.shape, extra[:200]))
    elif isinstance(obj, int) and abs(obj).bit_length() > 512:
        print('%s%s int (%d bits)' % (pad, name, abs(obj).bit_length()))
    else:
        s = repr(obj)
        print('%s%s %s %s' % (pad, name, type(obj).__name__, s[:160]))

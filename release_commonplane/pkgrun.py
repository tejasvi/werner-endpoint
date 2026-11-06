#!/usr/bin/env python3
"""Run one of the scripts in verifiers/ or independent_check/ with its paths mapped onto this package.

The scripts were run in one directory tree.  In the shipped copies every absolute path of that tree is written
<ROOT>/REL, where REL is the path inside this package (for example '<ROOT>/certificates/alld/xpoly4.pkl' or
'<ROOT>/independent_check/alld/work/bB.pkl').  This wrapper maps every path that contains '<ROOT>/' + REL, or ends in
'<ROOT>':
    read:   $PKG_ROOT/REL if PKG_ROOT is set and that file exists, else the package's REL, else OUT/REL
            (files written by an earlier step, e.g. the auditor's local tables or bound files)
    write:  OUT/REL (the package itself is never written)
Four auditor paths name copies of the certificate files and are read from certificates/ (ALIAS below).
OUT is $PKG_OUT, by default the directory <package>_out next to the package directory; it must lie outside the
package.  PKG_ROOT is an optional directory with the package's layout, searched first and never written.

The mapping covers open() and io.open (hence pickle and numpy file access), sys.path entries,
importlib.util.spec_from_file_location, os.path.exists/isfile/isdir and glob.glob/glob.iglob.  Other paths (for
example the command-line arguments of the scripts) are used as given.  An audit hook stops the run if anything opens
or lists a <ROOT> path that was not mapped.

Usage:  python3 -I -B pkgrun.py SCRIPT [ARGS ...]
        SCRIPT is relative to the package (e.g. independent_check/alld/bounds_C.py) or a path to a file inside
        verifiers/ or independent_check/.
"""
import builtins
import glob
import importlib.util
import io
import os
import runpy
import sys

PKG = os.path.dirname(os.path.abspath(__file__))
CODE = PKG
MARK = '<ROOT>'
OUT = os.path.abspath(os.environ.get('PKG_OUT') or PKG + '_out')
USER = os.path.abspath(os.environ['PKG_ROOT']) if os.environ.get('PKG_ROOT') else None
ROOTS = ((USER,) if USER else ()) + (PKG, OUT)
# the auditor read its copies of the certificate files from these places; they are the files in certificates/
ALIAS = {'independent_check/alld/bundle/': 'certificates/alld/',
         'independent_check/p1x/slice/xk4_min.pkl': 'certificates/d3/data_k4d3_min.pkl',
         'independent_check/p1x/slice/xrat4min_q.pkl': 'certificates/d3/cert_k4d3_min.pkl',
         'independent_check/pkt/struct_k4d3_min.pkl': 'certificates/d3/struct_k4d3_min.pkl'}


def _alias(rel):
    for a, b in ALIAS.items():
        if rel == a or (a.endswith('/') and rel.startswith(a)):
            return b + rel[len(a):]
    return rel
# never mapped: the package, the output directory and the interpreter's own installation
KEEP = tuple(sorted({os.path.join(p, '') for p in (PKG, OUT, sys.prefix, sys.base_prefix, sys.exec_prefix) if p}))

_open = builtins.open
_exists, _isfile, _isdir = os.path.exists, os.path.isfile, os.path.isdir
_iglob = glob.iglob
_spec_from_file_location = importlib.util.spec_from_file_location


def _inside(path, root):
    path, root = os.path.realpath(path), os.path.realpath(root)
    return path == root or path.startswith(root + os.sep)


def _split(path):
    """(prefix, rel) if path names something under <ROOT>, else None; prefix is the path up to '<ROOT>/'."""
    if isinstance(path, os.PathLike):
        path = os.fspath(path)
    if not isinstance(path, str) or path.startswith(KEEP):
        return None
    i = path.find(MARK)
    if i < 0:
        return None
    rest = path[i + len(MARK):]
    if rest and not rest.startswith('/'):
        return None
    return path[:i + len(MARK)] + '/', rest[1:]


def _read_path(path):
    m = _split(path)
    if m is None:
        return path
    rel = _alias(m[1])
    for root in ROOTS:
        p = os.path.join(root, rel)
        if _exists(p):
            return p
    return os.path.join(PKG, rel)


def _write_path(path):
    m = _split(path)
    if m is None:
        return path
    p = os.path.join(OUT, m[1])
    os.makedirs(os.path.dirname(p), exist_ok=True)
    return p


def _dir_paths(path):
    """the existing directories that a <ROOT> directory maps to, in search order (sys.path gets all of them)"""
    m = _split(path)
    if m is None:
        return [path]
    found = [os.path.join(root, m[1]) for root in ROOTS if _isdir(os.path.join(root, m[1]))]
    return found or [os.path.join(CODE, m[1])]


def _mapped_open(file, mode='r', *args, **kwargs):
    if isinstance(file, int):
        return _open(file, mode, *args, **kwargs)
    write = any(c in mode for c in 'wax+')
    return _open(_write_path(file) if write else _read_path(file), mode, *args, **kwargs)


def _mapped_spec_from_file_location(name, location=None, *args, **kwargs):
    if location is not None:
        location = _read_path(location)
    return _spec_from_file_location(name, location, *args, **kwargs)


def _mapped_iglob(pattern, *args, **kwargs):
    m = _split(pattern)
    if m is None:
        yield from _iglob(pattern, *args, **kwargs)
        return
    prefix, rel = m
    seen = set()
    for root in ROOTS:
        for p in _iglob(os.path.join(root, rel), *args, **kwargs):
            r = os.path.relpath(p, root)
            if r not in seen:
                seen.add(r)
                yield prefix + r


def _mapped_glob(pattern, *args, **kwargs):
    return list(_mapped_iglob(pattern, *args, **kwargs))


class _SysPath(list):
    """sys.path whose new <ROOT> entries become the matching directories of all roots, in search order."""

    def insert(self, i, x):
        for d in reversed(_dir_paths(x)):
            super().insert(i, d)

    def append(self, x):
        super().extend(_dir_paths(x))

    def extend(self, xs):
        for x in xs:
            super().extend(_dir_paths(x))


def _audit(event, args):
    if event in ('open', 'os.listdir', 'os.scandir', 'glob.glob') and args and _split(args[0]) is not None:
        raise RuntimeError('pkgrun: unmapped access to a <ROOT> path: %r (%s)' % (args[0], event))


def install():
    builtins.open = io.open = _mapped_open
    importlib.util.spec_from_file_location = _mapped_spec_from_file_location
    os.path.exists = lambda p: _exists(_read_path(p))
    os.path.isfile = lambda p: _isfile(_read_path(p))
    os.path.isdir = lambda p: _isdir(_dir_paths(p)[0])
    glob.glob = _mapped_glob
    glob.iglob = _mapped_iglob
    sys.path = _SysPath(sys.path)
    sys.addaudithook(_audit)


def main():
    if len(sys.argv) < 2:
        sys.exit(__doc__)
    if _inside(OUT, PKG):
        sys.exit('pkgrun: the output directory %s lies inside the package; set PKG_OUT to a directory outside it' % OUT)
    if USER and _inside(OUT, USER):
        sys.exit('pkgrun: the output directory %s lies inside PKG_ROOT; choose another PKG_OUT' % OUT)
    script = sys.argv[1]
    path = os.path.abspath(script if _isfile(script) else os.path.join(CODE, script))
    if not (_isfile(path) and any(_inside(path, os.path.join(PKG, d)) for d in ('verifiers', 'independent_check'))):
        sys.exit('pkgrun: %s is not a script in verifiers/ or independent_check/' % script)
    sys.argv = [path] + sys.argv[2:]
    install()
    runpy.run_path(path, run_name='__main__')


if __name__ == '__main__':
    main()

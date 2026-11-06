"""Product of the primes with all-zero W residues (from the wcheck logs) against the printed bound."""
import glob, re, math
ps = []
for fn in sorted(glob.glob('<ROOT>/independent_check/alld/logs/wcheck_modp_*.log')):
    t = open(fn).read()
    m = re.search(r'prime (\d+): \(a\) nonzero residues (\d+), \(b\) nonzero residues (\d+)', t)
    if m and m.group(2) == '0' and m.group(3) == '0':
        ps.append(int(m.group(1)))
b = int(re.search(r'need prod p > 2\^(\d+)', open(sorted(glob.glob('<ROOT>/independent_check/alld/logs/wcheck_modp_*.log'))[0]).read()).group(1))
P = math.prod(ps)
print('primes with zero residues: %d, product 2^%.2f, need > 2^%d -> %s' % (len(ps), math.log2(P), b, 'EXACT' if P > 2 ** b else 'NOT EXACT'))

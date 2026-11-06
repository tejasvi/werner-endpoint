"""Largest primes below 2^30 (trial division)."""
import math
out = []
x = (1 << 30) - 1
while len(out) < 8:
    if x % 2 and all(x % q for q in range(3, math.isqrt(x) + 1, 2)):
        out.append(x)
    x -= 2 if x % 2 else 1
print(out)

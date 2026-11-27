# Fixed points of the decimal prime-factor encoding with at most two distinct primes

**ptlom · November 27, 2026 · Research note prepared with OpenAI Codex**

Franklin T. Adams-Watters asked whether an integer can equal its own decimal prime-factor encoding. For example, 18 factors as 2¹ × 3², so its encoding is 2132. The question concerns integers at least 2. [OEIS A067599](https://oeis.org/A067599)

## Result

Every fixed point with at most two distinct prime factors belongs to one of the following two families. Each prime value of the displayed quotient gives a fixed point. Here d is the number of decimal digits of q, and t is any nonnegative integer.

| Fixed point | Candidate for the larger prime q | Decimal length d |
|---|---|---|
| 3⁷q | (37 × 10^(d+1) + 1) / 2177 | 666 + 930t |
| 7⁴q | (74 × 10^(d+1) + 1) / 2391 | 136 + 199t |

There are no prime-power fixed points. A fixed point with two distinct prime factors must have a larger prime of at least 136 digits. Existence of a prime quotient in either family remains open here. Integers with three or more distinct prime factors are outside this classification.

ArtemCherbaev previously gave the 7⁴ construction. The calculation below identifies the 3⁷ construction and establishes that these exhaust the one- and two-prime cases. [Earlier reduction, PR #1029](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/1029)

## Proof

Write L(x) for decimal length. For x ≥ 1, 10^L(x) ≤ 10x.

**One prime.** If p^e has encoding equal to itself, p^e < (p+1)10^L(e) ≤ 10e(p+1), so p^(e−1) < 15e. Exponent 1 is impossible because appending 1 increases p. For e ≥ 8, even p = 2 exceeds the bound, and 2^(e−1)/e increases thereafter. The finite check below handles e = 2 through 7.

**Two primes, repeated larger prime.** Write n = p^e q^f, p < q, with f ≥ 2. Because the encoding starts with p, it is less than (p+1)10^(L(e)+L(q)+L(f)). Thus p^(e−1) q^(f−1) < 1500ef. In particular (2^(e−1)/e)(3^(f−1)/f) < 1500. The first factor is at least 1, the second is at least 3/2, and both are nondecreasing. Substituting e = 15 or f = 10 rules out e ≥ 15 and f ≥ 10. Also p^(e−1) ≥ e, so q^(f−1) < 1500f. For f = 2 this gives q < 3000. For f ≥ 3 it gives q² < 13500. Direct integer comparison finds no fixed point anywhere in these ranges.

**Two primes, larger prime appearing once.** The encoding ends in 1, so p is an odd prime other than 5. Write C for the concatenation of p and e, D = p^e − 10, and d = L(q). Collecting the terms in q gives

    D q = C × 10^(d+1) + 1.

The bounds 10^(d−1) ≤ q < 10^d give 10C < D ≤ 100C + 1. Exponent 1 immediately fails. Since C ≤ 10ep + e, we get p^(e−1)/e ≤ 1000 + 100/p + 11/(pe). For e ≥ 10 the left side is at least 3⁹/10 and increases thereafter, which is impossible. Now e ≤ 9 and C = 10p+e, so p² ≤ 1000p+911 and p ≤ 1000.

For each remaining pair (p,e), scan the residues C × 10^(d+1) modulo D through one full period. Since 10 is coprime to D, returning to the starting residue proves the scan is exhaustive. The only hits are the two rows in the table. In both rows 10C < D < 100C, so the integer quotient really has d digits (the upper inequality for q also follows from D ≥ 10C+1). It exceeds p. If it is prime, reversing the displayed algebra shows the resulting integer equals its encoding.

## Reproduce the finite checks

Run with Python 3. The script tests exact integer equalities and modular periods. It uses only the standard library.

~~~python
from math import gcd, isqrt

primes = [p for p in range(2, 3001)
          if all(p % k for k in range(2, isqrt(p) + 1))]

for p in primes:
    for e in range(2, 8):
        if p**(e-1) < 15*e:
            assert p**e != int(f'{p}{e}')

for q in primes:
    for f in range(2, 10):
        if q**(f-1) >= 1500*f:
            continue
        for p in primes:
            if p >= q:
                break
            for e in range(1, 15):
                if p**(e-1)*q**(f-1) < 1500*e*f:
                    assert p**e*q**f != int(f'{p}{e}{q}{f}')

families = []
for p in primes:
    if p > 1000 or p in (2, 5):
        continue
    for e in range(2, 10):
        C, D = 10*p + e, p**e - 10
        if not 10*C < D <= 100*C + 1 or gcd(C, D) != 1:
            continue
        start = (100*C) % D
        d, residue, hits = 1, start, []
        while True:
            if residue == D-1:
                hits.append(d)
            residue = residue * 10 % D
            if residue == start:
                break
            d += 1
        families.extend((p, e, D, first, d) for first in hits)

assert families == [(3, 7, 2177, 666, 930), (7, 4, 2391, 136, 199)]
print(families)
~~~

"""Propagate polarized character trials over the archived tension intervals."""
import json
from fractions import Fraction as Q
from pathlib import Path


TRIALS = [
    (1,), (1000, 42, 1), (1000, 83, 4), (1000, 171, 17, 1),
    (1000, 293, 53, 5), (1000, 393, 103, 13, 1),
    (1000, 468, 157, 25, 3), (1000, 527, 213, 40, 6, 1),
    (1000, 576, 269, 57, 10, 1),
]


def upper_field(v, x, log_bound, beta1):
    norm = sum(k*k for k in v)
    parity = sum((-1)**n * k*k for n, k in enumerate(v))
    assert parity > 0
    electric = Q(4, 3) * sum(n*(n+2)*k*k for n, k in enumerate(v))
    hopping = sum(a*b for a, b in zip(v, v[1:]))
    return (norm*(1 + log_bound/(2*beta1)) + electric - x*hopping)/parity


def field_on(row, left, right):
    a, b = row['la'], row['lb']
    assert a <= left <= right <= b
    def at(x, v):
        log_upper = ((b-x)*row['l_a'] + (x-a)*row['l_b'])/(b-a)
        return upper_field(v, x, log_upper, row['beta1'])
    # Each trial gives an affine upper bound on the critical field on this row.
    return min(max(at(left, v), at(right, v)) for v in TRIALS)


def main():
    root = Path(__file__).resolve().parents[2]
    data = json.loads((root/'handoff/tension/tension_certificate.json').read_text())
    rows = [{k: Q(value) for k, value in row.items()} for row in data]
    assert len(rows) == 180 and rows[0]['la'] == 0 and rows[-1]['lb'] == 12
    assert all(r['la'] < r['lb'] and r['sigma'] > 0 for r in rows)
    assert all(r['lb'] == s['la'] for r, s in zip(rows, rows[1:]))
    for left, right in [(0, 1), (1, 2), (Q(107,50), Q(107,50)), (2, 4),
                        (4, 6), (6, 8), (8, 10), (10, 12)]:
        values = []
        for row in rows:
            a, b = max(left, row['la']), min(right, row['lb'])
            if a < b or (a == b and left == right):
                upper = field_on(row, a, b)
                assert upper >= row['sigma']
                values.append((upper, row['sigma']/upper))
        upper = max(h for h, _ in values)
        jump = min(m for _, m in values)
        # Round away from the interior of the enclosure before display.
        print(f'{left}..{right}: h_c <= {-((-10000*upper)//1)/10000:.4f}, '
              f'jump >= {(10000*jump//1)/10000:.4f}')


if __name__ == '__main__':
    main()

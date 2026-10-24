"""半棋盘轮廓计数；不导入 A001 的基本块或生成函数。"""

from functools import cache


@cache
def transitions(height):
    full = (1 << height) - 1
    table = []
    for incoming in range(full + 1):
        outputs = []

        def fill(occupied, outgoing):
            if occupied == full:
                outputs.append(outgoing)
                return
            bit = ((full ^ occupied) & -(full ^ occupied))
            row = bit.bit_length() - 1
            fill(occupied | bit, outgoing | bit)
            if row + 1 < height and not occupied & (bit << 1):
                fill(occupied | bit | (bit << 1), outgoing)

        fill(incoming, 0)
        assert len(outputs) == len(set(outputs))
        table.append(tuple(sorted(outputs)))
    # 用剩余连续段的偶长判据，独立核对逐列构造。
    for p in range(full + 1):
        expected = []
        for q in range(full + 1):
            if p & q:
                continue
            remaining = full ^ (p | q)
            run = 0
            good = True
            for row in range(height + 1):
                if row < height and remaining & (1 << row):
                    run += 1
                else:
                    good &= run % 2 == 0
                    run = 0
            if good:
                expected.append(q)
        assert tuple(expected) == table[p]
    return tuple(table)


def reverse_mask(mask, height):
    return sum(((mask >> row) & 1) << (height-1-row) for row in range(height))


@cache
def profiles(height, width):
    table = transitions(height)
    counts = [0] * len(table)
    counts[0] = 1
    for _ in range(width):
        following = [0] * len(table)
        for p, value in enumerate(counts):
            for q in table[p]:
                following[q] += value
        counts = following
    return tuple(counts)


def fixed_counts(height, n):
    assert height >= 1 and height % 2 == 1 and n >= 0
    half = profiles(height, n)
    return [profiles(height, 2*n)[0], profiles(height//2, 2*n)[0],
            sum(half), sum(value for mask, value in enumerate(half)
                           if reverse_mask(mask, height) == mask)]


def three_row_closed_counts(n):
    d = [1, 3]
    for j in range(2, n + 2):
        d.append(4*d[-1]-d[-2])
    k = n // 2
    v = d[k+1] if n % 2 else d[k+1]-2*d[k]
    r = d[k]
    return [d[n], 1, v, r]


def three_row_orbit_types(n):
    d, _, v, r = three_row_closed_counts(n)
    values = {"full_group":1,"rowflip_only":0,"colflip_only":(v-1)//2,
              "halfturn_only":(r-1)//2,"trivial":(d-v-r+1)//4}
    assert (v-1) % 2 == 0 and (r-1) % 2 == 0 and (d-v-r+1) % 4 == 0
    assert all(value >= 0 for value in values.values())
    return values

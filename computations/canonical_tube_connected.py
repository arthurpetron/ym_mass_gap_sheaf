"""Bounded exact separator regression; Lean proves every margin independently."""

from itertools import product
import json
import signal

from leading_tube_support import edges


def pilot():
    checked = 0
    for margin in (0, 1, 3):
        origin = (1 + margin,) * 3
        lower = edges((origin + (margin,), (0, 1)))
        upper = edges((origin + (margin + 3,), (0, 1)))
        tube = sorted({(vertex[:3] + (time,), (direction, 3))
                       for vertex, direction in lower
                       for time in range(margin, margin + 3)})
        assert len(tube) == 12
        boundaries = [edges(face) for face in tube]
        strip = [(origin + (margin + i,), (0, 3)) for i in range(3)]
        assert all(face in tube for face in strip)
        assert edges(strip[0]) & lower
        assert edges(strip[0]) & edges(strip[1])
        assert edges(strip[1]) & edges(strip[2])
        assert edges(strip[2]) & upper
        for assignment in product((False, True), repeat=12):
            left, right = set(lower), set(upper)
            for boundary, side in zip(boundaries, assignment):
                (left if side else right).update(boundary)
            assert left & right
            checked += 1
    return {"margins": [0, 1, 3], "original_positional_cuts": checked,
            "separators_found": 0, "connecting_strip_faces": 3,
            "full_interacting_response_positivity": "NOT TESTED"}


if __name__ == "__main__":
    signal.alarm(30)
    print(json.dumps(pilot(), separators=(",", ":")))

# Usage: python3 -I gen_data.py pyth3col_N25000000.raw Proofs/Data.lean
# Turns the raw colouring (1 byte per vertex, 0/1/2) into the Lean string literal Pyth.dataStr.
import sys
d = open(sys.argv[1], 'rb').read()
assert len(d) == 25000000
s = d.translate(bytes.maketrans(bytes([0, 1, 2]), b'012'))
assert set(s) <= set(b'012')
open(sys.argv[2], 'wb').write(b'namespace Pyth\ndef dataStr : String := "' + s + b'"\nend Pyth\n')

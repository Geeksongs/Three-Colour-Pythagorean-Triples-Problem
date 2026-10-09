/-- Independent Lean 4 checker: 3-colouring of {1..N} (byte i = colour of i+1)
    has no monochromatic Pythagorean triple a^2+b^2=c^2, c ≤ N.
    Triples enumerated via Euclid: (t(m²-n²), t·2mn, t(m²+n²)), gcd(m,n)=1, m-n odd. -/
def colour (d : ByteArray) (v : Nat) : UInt8 := d.get! (v - 1)

def check (d : ByteArray) (N : Nat) : Nat × Nat × Nat := Id.run do
  let mut triples := 0
  let mut mono := 0
  let mut bad := 0   -- colour byte outside {0,1,2}
  for v in [0:N] do
    if d.get! v > 2 then bad := bad + 1
  let mut m := 2
  while m * m + 1 ≤ N do
    let mut n := 1
    while n < m do
      if (m - n) % 2 == 1 && Nat.gcd m n == 1 then
        let a := m*m - n*n
        let b := 2*m*n
        let c := m*m + n*n
        if c ≤ N then
          let mut t := 1
          while t * c ≤ N do
            triples := triples + 1
            let ca := colour d (t*a)
            if ca == colour d (t*b) && ca == colour d (t*c) then mono := mono + 1
            t := t + 1
      n := n + 1
    m := m + 1
  return (triples, mono, bad)

def main (args : List String) : IO UInt32 := do
  let path := args[0]!
  let N := args[1]!.toNat!
  let d ← IO.FS.readBinFile path
  if d.size != N then
    IO.println s!"size mismatch: {d.size} vs {N}"; return 2
  let (t, mo, bad) := check d N
  IO.println s!"N={N} triples={t} monochromatic={mo} invalid_colour_bytes={bad}"
  return (if mo == 0 && bad == 0 then 0 else 1)

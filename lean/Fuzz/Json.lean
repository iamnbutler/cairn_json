import CairnJson

/-! `jsonfuzz`: the Lean side of the trusted fuzz check (docs/trusted.md, `make fuzz`).

Reads one document per line on stdin, as hex bytes, and prints one line per document:

* `ERR` when `decodeBytes` refuses it;
* otherwise `OK`, a tab, the value in a canonical form the Swift driver compares with
  `JSONSerialization`'s, a tab, the hex of `encode v`, a tab, the hex of `pretty v`, a tab, and
  `checks`: `1` when `decode (encode v)` and `decode (pretty v)` give `v` back (compared by
  their encodings) and the parse is the same with four times the fuel, a tab, and the canonical
  form again with a leading U+FEFF dropped from every string (Foundation drops them).

The canonical form: `n`, `t`, `f`, `#<mantissa>e<exponent>`, `s` and the string's scalars in
hex separated by `.`, `[a,b]`, and `{k:v,…}` with keys in canonical form, the first of duplicate
keys kept (as `JSONSerialization` does), sorted by their canonical form. -/

open CairnJson

def hexNibble (c : Char) : Option Nat := hexVal c

def unhex (s : String) : Option ByteArray := Id.run do
  let cs := s.toList.toArray
  if cs.size % 2 != 0 then return none
  let mut out := ByteArray.empty
  for i in [0:cs.size / 2] do
    match hexNibble cs[2 * i]!, hexNibble cs[2 * i + 1]! with
    | some a, some b => out := out.push (a * 16 + b).toUInt8
    | _, _ => return none
  return some out

def hexOf (bs : ByteArray) : String :=
  String.ofList (bs.toList.flatMap fun b => [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)])

def scalarsHex (s : String) : String :=
  ".".intercalate (s.toList.map fun c => String.ofList (Nat.toDigits 16 c.toNat))

/-- A leading U+FEFF dropped, as Foundation drops it from the strings it reads. -/
def dropBom (stripBom : Bool) (s : String) : String :=
  match stripBom, s.toList with
  | true, '\uFEFF' :: rest => String.ofList rest
  | _, _ => s

mutual
def canon (stripBom : Bool) : Json → String
  | .null => "n"
  | .bool true => "t"
  | .bool false => "f"
  | .num x => s!"#{x.mantissa}e{x.exponent}"
  | .str s => "s" ++ scalarsHex (dropBom stripBom s)
  | .arr xs => "[" ++ ",".intercalate (canonList stripBom xs) ++ "]"
  | .obj kvs =>
    let entries := canonMembers stripBom kvs
    -- the first of duplicate keys wins, as in `JSONSerialization`
    let dedup := entries.foldl (fun acc (k, v) => if acc.any (·.1 == k) then acc else acc.push (k, v)) #[]
    let sorted := dedup.toList.mergeSort fun a b => decide (a.1 ≤ b.1)
    "{" ++ ",".intercalate (sorted.map fun (k, v) => k ++ ":" ++ v) ++ "}"
def canonList (stripBom : Bool) : List Json → List String
  | [] => []
  | x :: xs => canon stripBom x :: canonList stripBom xs
def canonMembers (stripBom : Bool) : List (String × Json) → List (String × String)
  | [] => []
  | (k, x) :: kvs => ("s" ++ scalarsHex (dropBom stripBom k), canon stripBom x) :: canonMembers stripBom kvs
end

def fuelSame (bs : ByteArray) : Bool :=
  match text bs with
  | none => true
  | some s =>
    let cs := s.toList
    let a := value maxDepth (cs.length + 1) 0 cs
    let b := value maxDepth (4 * cs.length + 4) 0 cs
    (a.map fun (v, r) => (encode v, r)) == (b.map fun (v, r) => (encode v, r))

def main : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let line := line.trimAscii.toString
    match unhex line with
    | none => stdout.putStrLn "BADHEX"
    | some bs =>
      match decodeBytes bs with
      | none => stdout.putStrLn (if fuelSame bs then "ERR" else "ERR\tfuel")
      | some v =>
        let e := encode v
        let p := pretty v
        let ok := (decode e).map encode == some e && (decode p).map encode == some e && fuelSame bs
        stdout.putStrLn s!"OK\t{canon false v}\t{hexOf e.toUTF8}\t{hexOf p.toUTF8}\t{if ok then 1 else 0}\t{canon true v}"
  stdout.flush
  return 0

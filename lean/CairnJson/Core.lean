module

/-! # JSON

A total JSON parser and encoder (RFC 8259), ported from yap-cairn's `Yap.Json`.

* `Json.decode` reads a document; `Json.encode` writes one compactly, `Json.pretty` as
  `JSONEncoder`'s `.prettyPrinted` does. `CairnJsonProofs.RoundTrip` proves
  `decode (encode v) = some v` for every value nested at most `maxDepth` deep.
* The parser is total: plain structural recursion on a fuel argument (the input's length is
  enough, and the proofs show it), no `partial def`.
* It accepts what Foundation's `JSONSerialization` accepts, with the differences listed in
  docs/trusted.md: one trailing comma in an array or object, nesting at most 512 deep.
* Numbers are exact decimals, `mantissa * 10 ^ exponent`, as written (`1.50` is `150e-2`), never
  floats. `Json.getInt` reads one as `JSONDecoder` reads an `Int`.
* Objects keep their members in order, duplicates included. `Json.field` takes the first. -/

@[expose] public section

namespace CairnJson

/-- A decimal number, `mantissa * 10 ^ exponent`. The parser keeps the digits as written:
`1.50` is `⟨150, -2⟩` and `1.5e3` is `⟨15, 2⟩`. `-0` is `⟨0, 0⟩`. -/
structure Number where
  mantissa : Int
  exponent : Int
deriving Repr, Inhabited, DecidableEq

inductive Json where
  | null
  | bool (b : Bool)
  | num (n : Number)
  | str (s : String)
  | arr (xs : List Json)
  | obj (kvs : List (String × Json))
deriving Repr, Inhabited

/-- How deeply arrays and objects nest: a scalar is 0, `[]` is 1. -/
def Json.depth : Json → Nat
  | .arr xs => depthList xs + 1
  | .obj kvs => depthMembers kvs + 1
  | _ => 0
where
  depthList : List Json → Nat
    | [] => 0
    | x :: xs => max x.depth (depthList xs)
  depthMembers : List (String × Json) → Nat
    | [] => 0
    | (_, x) :: xs => max x.depth (depthMembers xs)

/-- An integer as a number. -/
def Json.int (n : Int) : Json := .num ⟨n, 0⟩

/-! ## Reading -/

def isWs (c : Char) : Bool := c = ' ' ∨ c = '\n' ∨ c = '\r' ∨ c = '\t'

def skipWs : List Char → List Char
  | c :: cs => if isWs c then skipWs cs else c :: cs
  | [] => []

def isDigit (c : Char) : Bool := '0' ≤ c ∧ c ≤ '9'

def digitVal (c : Char) : Nat := c.toNat - '0'.toNat

/-- The value of a run of decimal digits. -/
def digitsVal (cs : List Char) : Nat := cs.foldl (fun n c => n * 10 + digitVal c) 0

def hexVal (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

def hex4 : List Char → Option (Nat × List Char)
  | a :: b :: c :: d :: rest =>
    match hexVal a, hexVal b, hexVal c, hexVal d with
    | some a, some b, some c, some d => some (((a * 16 + b) * 16 + c) * 16 + d, rest)
    | _, _, _, _ => none
  | _ => none

/-- The character a one-letter escape stands for. -/
def unescape : Char → Option Char
  | '"' => some '"'
  | '\\' => some '\\'
  | '/' => some '/'
  | 'b' => some '\x08'
  | 'f' => some '\x0c'
  | 'n' => some '\n'
  | 'r' => some '\r'
  | 't' => some '\t'
  | _ => none

/-- After `\u` and four hex digits `hi`: the character, joining a surrogate pair, and what
follows. A lone surrogate is an error, as in `JSONSerialization`. -/
def unicode (hi : Nat) (rest : List Char) : Option (Char × List Char) :=
  if 0xD800 ≤ hi ∧ hi < 0xDC00 then
    match rest with
    | '\\' :: 'u' :: more =>
      match hex4 more with
      | some (lo, rest') =>
        if 0xDC00 ≤ lo ∧ lo < 0xE000 then
          some (Char.ofNat (0x10000 + (hi - 0xD800) * 0x400 + (lo - 0xDC00)), rest')
        else none
      | none => none
    | _ => none
  else if 0xDC00 ≤ hi ∧ hi < 0xE000 then none
  else some (Char.ofNat hi, rest)

/-- The rest of a string literal after its opening quote: its characters (escapes decoded,
newest first in `acc`) and what follows the closing quote. Control characters must be
escaped. -/
def strBody : Nat → List Char → List Char → Option (String × List Char)
  | 0, _, _ => none
  | _ + 1, _, [] => none
  | fuel + 1, acc, c :: rest =>
    if c = '"' then some (String.ofList acc.reverse, rest)
    else if c = '\\' then
      match rest with
      | [] => none
      | e :: rest =>
        if e = 'u' then
          match hex4 rest with
          | some (hi, rest) =>
            match unicode hi rest with
            | some (d, rest) => strBody fuel (d :: acc) rest
            | none => none
          | none => none
        else
          match unescape e with
          | some d => strBody fuel (d :: acc) rest
          | none => none
    else if c.toNat < 0x20 then none
    else strBody fuel (c :: acc) rest

/-- A string literal's body, with enough fuel. -/
def string (cs : List Char) : Option (String × List Char) := strBody (cs.length + 1) [] cs

/-! ### Linear-time string literals

`string` gives `strBody` the remaining input's length as fuel, which costs a pass over the rest
of the document for every string literal: decoding was quadratic in the number of strings.
`strBodyGo` is the same loop without fuel, by well-founded recursion on what is left, and
`string_eq_fast` (`@[csimp]`) proves `string` equal to it, so compiled code runs the linear one
while every definition and proof about `string` stays as it was. -/

theorem hex4_length {cs rest : List Char} {n : Nat} (h : hex4 cs = some (n, rest)) :
    rest.length < cs.length := by
  match cs, h with
  | a :: b :: c :: d :: r, h =>
    simp only [hex4] at h
    split at h
    · cases h; simp only [List.length_cons]; omega
    · cases h

theorem ite_some_snd {α β : Type} {p : Prop} [Decidable p] {x : α × β} {y : α × β}
    (h : (if p then some x else none) = some y) : y.2 = x.2 := by
  by_cases hp : p
  · rw [ite_eq_left hp] at h; cases h; rfl
  · rw [ite_eq_right hp] at h; cases h

theorem pair_len (hi : Nat) (more rest' : List Char) (d : Char)
    (h : (match hex4 more with
          | some (lo, rest') =>
            if 0xDC00 ≤ lo ∧ lo < 0xE000 then
              some (Char.ofNat (0x10000 + (hi - 0xD800) * 0x400 + (lo - 0xDC00)), rest')
            else none
          | none => none) = some (d, rest')) : rest'.length < more.length := by
  cases hr : hex4 more with
  | none => rw [hr] at h; cases h
  | some p =>
    obtain ⟨lo, r⟩ := p
    rw [hr] at h
    have := ite_some_snd h
    simp only at this; subst this
    exact hex4_length hr

theorem unicode_length {hi : Nat} {rest rest' : List Char} {d : Char}
    (h : unicode hi rest = some (d, rest')) : rest'.length ≤ rest.length := by
  unfold unicode at h
  by_cases h1 : 0xD800 ≤ hi ∧ hi < 0xDC00
  · rw [ite_eq_left h1] at h
    rcases rest with _ | ⟨c1, _ | ⟨c2, more⟩⟩
    · cases h
    · split at h
      · next _ heq => simp at heq
      · cases h
    · by_cases e : c1 = '\\' ∧ c2 = 'u'
      · obtain ⟨rfl, rfl⟩ := e
        have := pair_len hi more rest' d h
        simp only [List.length_cons]; omega
      · split at h
        · next more' heq =>
          simp only [List.cons.injEq] at heq
          exact absurd ⟨heq.1, heq.2.1⟩ e
        · cases h
  · rw [ite_eq_right h1] at h
    by_cases h2 : 0xDC00 ≤ hi ∧ hi < 0xE000
    · rw [ite_eq_left h2] at h; cases h
    · rw [ite_eq_right h2] at h; cases h; exact Nat.le_refl _

/-- After a backslash in a string literal: the character the escape stands for, and what
follows it. -/
def escStep : List Char → Option (Char × List Char)
  | [] => none
  | e :: rest =>
    if e = 'u' then
      match hex4 rest with
      | some (hi, r) => unicode hi r
      | none => none
    else (unescape e).map (·, rest)

theorem escStep_length {cs rest : List Char} {d : Char} (h : escStep cs = some (d, rest)) :
    rest.length < cs.length := by
  match cs, h with
  | e :: r, h =>
    simp only [escStep] at h
    split at h
    · split at h
      · next hi r' h4 =>
        have := unicode_length h; have := hex4_length h4; simp only [List.length_cons]; omega
      · cases h
    · cases hu : unescape e with
      | none => simp [hu] at h
      | some x => simp only [hu, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨-, rfl⟩ := h; simp

/-- `strBody` without fuel: the same steps, recursing on a shorter rest each time. -/
def strBodyGo (acc : List Char) : List Char → Option (String × List Char)
  | [] => none
  | c :: rest =>
    if c = '"' then some (String.ofList acc.reverse, rest)
    else if c = '\\' then
      match h : escStep rest with
      | some (d, r) =>
        have : r.length < rest.length := escStep_length h
        strBodyGo (d :: acc) r
      | none => none
    else if c.toNat < 0x20 then none
    else strBodyGo (c :: acc) rest
termination_by cs => cs.length
decreasing_by all_goals simp_wf <;> omega

/-- With fuel beyond the input's length, `strBody` is `strBodyGo`. -/
theorem strBody_eq_go : ∀ (n : Nat) (acc cs : List Char), cs.length < n →
    strBody n acc cs = strBodyGo acc cs
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | _ + 1, _, [], _ => by simp [strBody, strBodyGo]
  | n + 1, acc, c :: rest, h => by
    simp only [List.length_cons] at h
    rw [strBodyGo.eq_def]
    simp only [strBody]
    split
    · rfl
    · split
      · match rest, h with
        | [], _ => simp [escStep]
        | e :: rest, h =>
          simp only [List.length_cons] at h
          have go : ∀ d r, escStep (e :: rest) = some (d, r) →
              strBody n (d :: acc) r = strBodyGo (d :: acc) r := fun d r hx =>
            strBody_eq_go n (d :: acc) r (by have := escStep_length hx; simp only [List.length_cons] at this; omega)
          by_cases he : e = 'u'
          · subst he
            cases h4 : hex4 rest with
            | none =>
              have hx : escStep ('u' :: rest) = none := by simp [escStep, h4]
              simp only [↓reduceIte, h4]
              split
              · next heq => rw [hx] at heq; cases heq
              · rfl
            | some p =>
              obtain ⟨hi, r⟩ := p
              cases hu : unicode hi r with
              | none =>
                have hx : escStep ('u' :: rest) = none := by simp [escStep, h4, hu]
                simp only [↓reduceIte, h4, hu]
                split
                · next heq => rw [hx] at heq; cases heq
                · rfl
              | some q =>
                obtain ⟨d, r'⟩ := q
                have hx : escStep ('u' :: rest) = some (d, r') := by simp [escStep, h4, hu]
                simp only [↓reduceIte, h4, hu]
                split
                · next d' r'' heq => rw [hx] at heq; cases heq; exact go d r' hx
                · next heq => rw [hx] at heq; cases heq
          · cases hu : unescape e with
            | none =>
              have hx : escStep (e :: rest) = none := by simp [escStep, he, hu]
              simp only [he, ↓reduceIte, hu]
              split
              · next heq => rw [hx] at heq; cases heq
              · rfl
            | some d =>
              have hx : escStep (e :: rest) = some (d, rest) := by simp [escStep, he, hu]
              simp only [he, ↓reduceIte, hu]
              split
              · next d' r'' heq => rw [hx] at heq; cases heq; exact go d rest hx
              · next heq => rw [hx] at heq; cases heq
      · split
        · rfl
        · exact strBody_eq_go n (c :: acc) rest (by omega)

/-- `string`, in linear time. -/
def stringFast (cs : List Char) : Option (String × List Char) := strBodyGo [] cs

@[csimp] theorem string_eq_fast : @string = @stringFast := by
  funext cs
  exact strBody_eq_go _ [] cs (Nat.lt_succ_self _)

/-- `.` and at least one digit, or nothing. -/
def fraction : List Char → Option (List Char × List Char)
  | '.' :: r =>
    let f := r.takeWhile isDigit
    if f.isEmpty then none else some (f, r.dropWhile isDigit)
  | r => some ([], r)

/-- An exponent (`e` or `E`, a sign, at least one digit), or nothing. -/
def exponent : List Char → Option (Int × List Char)
  | e :: r =>
    if e = 'e' ∨ e = 'E' then
      let (neg, r) := match r with
        | '+' :: r' => (false, r')
        | '-' :: r' => (true, r')
        | r' => (false, r')
      let d := r.takeWhile isDigit
      if d.isEmpty then none
      else some (if neg then -(digitsVal d : Int) else digitsVal d, r.dropWhile isDigit)
    else some (0, e :: r)
  | [] => some (0, [])

/-- A number: `-`? digits (no leading zero), then optionally a fraction and an exponent. -/
def number (cs : List Char) : Option (Json × List Char) :=
  let (neg, cs) := match cs with
    | '-' :: r => (true, r)
    | r => (false, r)
  let ds := cs.takeWhile isDigit
  if ds.isEmpty then none
  else if ds.head? = some '0' ∧ 1 < ds.length then none
  else
    match fraction (cs.dropWhile isDigit) with
    | none => none
    | some (fs, rest) =>
      match exponent rest with
      | none => none
      | some (ex, rest) =>
        let m := digitsVal (ds ++ fs)
        some (.num ⟨if neg then -(m : Int) else m, ex - fs.length⟩, rest)

/-- How deep arrays and objects may nest by default: `JSONSerialization` gives up past 512. -/
def maxDepth : Nat := 512

mutual
/-- A value, then what follows it. `fuel` bounds the work (the input's length is enough);
`depth` is how many arrays and objects enclose it, at most `limit`. -/
def value (limit : Nat) : Nat → Nat → List Char → Option (Json × List Char)
  | 0, _, _ => none
  | fuel + 1, depth, cs =>
    match skipWs cs with
    | '{' :: rest => if depth < limit then members limit fuel (depth + 1) [] (skipWs rest) true else none
    | '[' :: rest => if depth < limit then elements limit fuel (depth + 1) [] (skipWs rest) true else none
    | '"' :: rest => (string rest).map fun (s, r) => (.str s, r)
    | 't' :: 'r' :: 'u' :: 'e' :: rest => some (.bool true, rest)
    | 'f' :: 'a' :: 'l' :: 's' :: 'e' :: rest => some (.bool false, rest)
    | 'n' :: 'u' :: 'l' :: 'l' :: rest => some (.null, rest)
    | cs' => number cs'

/-- An object's members after `{` (and white space), newest first in `acc`. As in
`JSONSerialization`, one comma may follow the last member. -/
def members (limit : Nat) : Nat → Nat → List (String × Json) → List Char → Bool → Option (Json × List Char)
  | 0, _, _, _, _ => none
  | fuel + 1, depth, acc, cs, first =>
    match cs with
    | '}' :: rest => if first then some (.obj [], rest) else some (.obj acc.reverse, rest)
    | '"' :: rest =>
      match string rest with
      | none => none
      | some (k, rest) =>
        match skipWs rest with
        | ':' :: rest =>
          match value limit fuel depth rest with
          | none => none
          | some (v, rest) =>
            match skipWs rest with
            | ',' :: rest => members limit fuel depth ((k, v) :: acc) (skipWs rest) false
            | '}' :: rest => some (.obj ((k, v) :: acc).reverse, rest)
            | _ => none
        | _ => none
    | _ => none

/-- An array's elements after `[` (and white space); one comma may follow the last. -/
def elements (limit : Nat) : Nat → Nat → List Json → List Char → Bool → Option (Json × List Char)
  | 0, _, _, _, _ => none
  | fuel + 1, depth, acc, cs, first =>
    match cs with
    | ']' :: rest => if first then some (.arr [], rest) else some (.arr acc.reverse, rest)
    | cs =>
      match value limit fuel depth cs with
      | none => none
      | some (v, rest) =>
        match skipWs rest with
        | ',' :: rest => elements limit fuel depth (v :: acc) (skipWs rest) false
        | ']' :: rest => some (.arr (v :: acc).reverse, rest)
        | _ => none
end

/-- A whole document as characters: one value and nothing after it but white space. -/
def decodeChars (limit : Nat) (cs : List Char) : Option Json :=
  match value limit (cs.length + 1) 0 cs with
  | some (v, rest) => if skipWs rest = [] then some v else none
  | none => none

/-- A document, with arrays and objects nested at most `limit` deep. -/
def decodeWith (limit : Nat) (s : String) : Option Json := decodeChars limit s.toList

/-- A document, nested at most 512 deep as `JSONSerialization` allows. -/
def decode (s : String) : Option Json := decodeWith maxDepth s

/-! ### Bytes

`JSONSerialization` reads UTF-8 (a byte order mark is skipped), and UTF-16 or UTF-32 when a
byte order mark says so, or when the zero bytes among the first four do. -/

/-- Big-endian (or little-endian) 16-bit units, an odd last byte dropped. -/
def units16 (be : Bool) : List UInt8 → List Nat
  | a :: b :: rest => (if be then a.toNat * 256 + b.toNat else b.toNat * 256 + a.toNat) :: units16 be rest
  | _ => []

def units32 (be : Bool) : List UInt8 → List Nat
  | a :: b :: c :: d :: rest =>
    (if be then ((a.toNat * 256 + b.toNat) * 256 + c.toNat) * 256 + d.toNat
     else ((d.toNat * 256 + c.toNat) * 256 + b.toNat) * 256 + a.toNat) :: units32 be rest
  | _ => []

/-- UTF-16 units as characters: none for a surrogate out of its pair. -/
def fromUtf16 : List Nat → Option (List Char)
  | [] => some []
  | u :: rest =>
    if 0xD800 ≤ u ∧ u < 0xDC00 then
      match rest with
      | l :: rest' =>
        if 0xDC00 ≤ l ∧ l < 0xE000 then
          (fromUtf16 rest').map (Char.ofNat (0x10000 + (u - 0xD800) * 0x400 + (l - 0xDC00)) :: ·)
        else none
      | [] => none
    else if 0xDC00 ≤ u ∧ u < 0xE000 then none
    else (fromUtf16 rest).map (Char.ofNat u :: ·)

def fromUtf32 (us : List Nat) : Option (List Char) :=
  us.mapM fun u => if u < 0x110000 ∧ !(0xD800 ≤ u ∧ u < 0xE000) then some (Char.ofNat u) else none

/-- The text of a JSON document's bytes, as `JSONSerialization` finds its encoding: a byte order
mark, else the zero bytes among the first four (`00 00 00 xx` is UTF-32BE, `xx 00 00 00`
UTF-32LE, `00 xx 00 xx` UTF-16BE, `xx 00 xx 00` UTF-16LE), else UTF-8. -/
def text (d : ByteArray) : Option String :=
  let bs := d.toList
  let u16 (be : Bool) (skip : Nat) := (fromUtf16 (units16 be (bs.drop skip))).map String.ofList
  let u32 (be : Bool) (skip : Nat) := (fromUtf32 (units32 be (bs.drop skip))).map String.ofList
  let utf8 (skip : Nat) := String.fromUTF8? (ByteArray.mk (bs.drop skip).toArray)
  match bs with
  | 0 :: 0 :: 0xFE :: 0xFF :: _ => u32 true 4
  | 0xFE :: 0xFF :: _ => u16 true 2
  | 0xFF :: 0xFE :: _ => u16 false 2
  | 0xEF :: 0xBB :: 0xBF :: _ => utf8 3
  | 0 :: 0 :: 0 :: _ :: _ => u32 true 0
  | _ :: 0 :: 0 :: 0 :: _ => u32 false 0
  | 0 :: _ :: 0 :: _ :: _ => u16 true 0
  | _ :: 0 :: _ :: 0 :: _ => u16 false 0
  | _ => utf8 0

/-- A document from its bytes. -/
def decodeBytes (d : ByteArray) : Option Json := (text d).bind decode

/-! ## Reading values -/

/-- The first member named `k`. -/
def Json.field (j : Json) (k : String) : Option Json :=
  match j with
  | .obj kvs => (kvs.find? (·.1 == k)).map (·.2)
  | _ => none

def Json.getStr : Json → Option String
  | .str s => some s
  | _ => none

def Json.getBool : Json → Option Bool
  | .bool b => some b
  | _ => none

def Json.getArr : Json → Option (List Json)
  | .arr xs => some xs
  | _ => none

def Json.getObj : Json → Option (List (String × Json))
  | .obj kvs => some kvs
  | _ => none

def Json.getNum : Json → Option Number
  | .num n => some n
  | _ => none

def int64Min : Int := -9223372036854775808
def int64Max : Int := 9223372036854775807

/-- `n / d` rounded to the nearest integer, ties to even. -/
def roundHalfEven (n d : Nat) : Nat :=
  let q := n / d
  let r := n % d
  if 2 * r < d then q else if d < 2 * r then q + 1 else if q % 2 = 0 then q else q + 1

/-- The double nearest `n / d` (positive, at least 1/10 and below 10^20) as `q * 2^k`, with
`2^52 ≤ q < 2^53`. -/
def nearestDouble (n d : Nat) : Nat × Int :=
  let scaled (k : Int) : Nat × Nat :=
    if 0 ≤ k then (n, d * 2 ^ k.toNat) else (n * 2 ^ (-k).toNat, d)
  let k := ((List.range 140).map fun (i : Nat) => (i : Int) - 70).find? fun k =>
    let (a, b) := scaled k
    2 ^ 52 * b ≤ a ∧ a < 2 ^ 53 * b
  let k := k.getD 0
  let (a, b) := scaled k
  let q := roundHalfEven a b
  if q = 2 ^ 53 then (2 ^ 52, k + 1) else (q, k)

/-- The number of decimal digits of `n` (1 for 0). -/
def decimalLength (n : Nat) : Nat := if n < 10 then 1 else decimalLength (n / 10) + 1

/-- What `JSONDecoder` makes of a number read as an `Int`: the number when it is a whole number
that fits in 64 bits and is written without a fraction or exponent; otherwise the nearest
double, when that is a whole number that fits in 64 bits. -/
def Number.toInt64? (x : Number) : Option Int := do
  if x.exponent = 0 then
    return ← if int64Min ≤ x.mantissa ∧ x.mantissa ≤ int64Max then some x.mantissa else none
  let m := x.mantissa.natAbs
  let e := x.exponent
  if m = 0 then return 0
  -- The magnitude is about 10^(mag): at least 10^20 is out of range, below 10^-400 is zero.
  let mag : Int := (decimalLength m : Int) - 1 + e
  if 20 ≤ mag then none
  else if mag < -400 then return 0
  else
    let (n, d) : Nat × Nat := if 0 ≤ e then (m * 10 ^ e.toNat, 1) else (m, 10 ^ (-e).toNat)
    if n * 2 ^ 1075 ≤ d then return 0  -- rounds to zero
    else if 10 * n < d then none  -- below 1/10: never a whole number
    else
      let (q, k) := nearestDouble n d
      let v : Int ← if 0 ≤ k then some ((q * 2 ^ k.toNat : Nat) : Int)
        else if q % 2 ^ (-k).toNat = 0 then some ((q / 2 ^ (-k).toNat : Nat) : Int) else none
      let v := if x.mantissa < 0 then -v else v
      if int64Min ≤ v ∧ v ≤ int64Max then some v else none

/-- An `Int` as `JSONDecoder` reads one (`Number.toInt64?`). -/
def Json.getInt : Json → Option Int
  | .num n => n.toInt64?
  | _ => none

/-! ## Writing -/

/-- The decimal digits of `n`. -/
def natDigits (n : Nat) : List Char :=
  if n < 10 then [Char.ofNat (48 + n)] else natDigits (n / 10) ++ [Char.ofNat (48 + n % 10)]

def intDigits (n : Int) : List Char :=
  if n < 0 then '-' :: natDigits n.natAbs else natDigits n.natAbs

/-- `mantissa`, then `e` and the exponent unless it is 0: `15e-1`, `-3`, `0e5`. -/
def Number.chars (x : Number) : List Char :=
  intDigits x.mantissa ++ (if x.exponent = 0 then [] else 'e' :: intDigits x.exponent)

def hexDigit (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- One character of a string literal as `JSONEncoder` writes it: `"` and `\` escaped, `/` too
when `slash` (`JSONEncoder`'s default, unlike `.withoutEscapingSlashes`), the control characters
as `\n`, `\t`, … or `\u00xx`, everything else as it is. -/
def escape (slash : Bool) (c : Char) : List Char :=
  if c = '"' then ['\\', '"']
  else if c = '\\' then ['\\', '\\']
  else if slash ∧ c = '/' then ['\\', '/']
  else if c = '\n' then ['\\', 'n']
  else if c = '\r' then ['\\', 'r']
  else if c = '\t' then ['\\', 't']
  else if c = '\x08' then ['\\', 'b']
  else if c = '\x0c' then ['\\', 'f']
  else if c.toNat < 0x20 then ['\\', 'u', '0', '0', hexDigit (c.toNat / 16), hexDigit (c.toNat % 16)]
  else [c]

def quoteChars (slash : Bool) (s : String) : List Char :=
  '"' :: (s.toList.flatMap (escape slash) ++ ['"'])

/-- A string literal. -/
def quote (s : String) (slash : Bool := false) : String := String.ofList (quoteChars slash s)

mutual
/-- A value, compactly: no white space, members in the order given. -/
def encChars (slash : Bool) : Json → List Char
  | .null => ['n', 'u', 'l', 'l']
  | .bool true => ['t', 'r', 'u', 'e']
  | .bool false => ['f', 'a', 'l', 's', 'e']
  | .num x => x.chars
  | .str s => quoteChars slash s
  | .arr [] => ['[', ']']
  | .arr (x :: xs) => '[' :: (encChars slash x ++ encList slash xs)
  | .obj [] => ['{', '}']
  | .obj ((k, x) :: kvs) => '{' :: (quoteChars slash k ++ ':' :: (encChars slash x ++ encMembers slash kvs))

/-- The elements after the first, then `]`. -/
def encList (slash : Bool) : List Json → List Char
  | [] => [']']
  | x :: xs => ',' :: (encChars slash x ++ encList slash xs)

/-- The members after the first, then `}`. -/
def encMembers (slash : Bool) : List (String × Json) → List Char
  | [] => ['}']
  | (k, x) :: kvs => ',' :: (quoteChars slash k ++ ':' :: (encChars slash x ++ encMembers slash kvs))
end

/-- A document, compactly, as `JSONEncoder` writes it with `.withoutEscapingSlashes` (or
without it, `slash := true`) and members in the order given. -/
def encode (v : Json) (slash : Bool := false) : String := String.ofList (encChars slash v)

def indent (n : Nat) : List Char := List.replicate (2 * n) ' '

mutual
/-- A value as `JSONEncoder`'s `.prettyPrinted` writes it, `level` deep: two spaces per level,
`" : "` after a key, and `[\n\n]`, `{\n\n}` for empty containers. -/
def prettyChars (slash : Bool) (level : Nat) : Json → List Char
  | .arr [] => ['[', '\n', '\n'] ++ indent level ++ [']']
  | .arr (x :: xs) =>
    '[' :: '\n' :: (indent (level + 1) ++ prettyChars slash (level + 1) x ++ prettyList slash level xs)
  | .obj [] => ['{', '\n', '\n'] ++ indent level ++ ['}']
  | .obj ((k, x) :: kvs) =>
    '{' :: '\n' :: (indent (level + 1) ++ quoteChars slash k ++ [' ', ':', ' '] ++
      prettyChars slash (level + 1) x ++ prettyMembers slash level kvs)
  | v => encChars slash v

def prettyList (slash : Bool) (level : Nat) : List Json → List Char
  | [] => '\n' :: (indent level ++ [']'])
  | x :: xs => ',' :: '\n' :: (indent (level + 1) ++ prettyChars slash (level + 1) x ++ prettyList slash level xs)

def prettyMembers (slash : Bool) (level : Nat) : List (String × Json) → List Char
  | [] => '\n' :: (indent level ++ ['}'])
  | (k, x) :: kvs =>
    ',' :: '\n' :: (indent (level + 1) ++ quoteChars slash k ++ [' ', ':', ' '] ++
      prettyChars slash (level + 1) x ++ prettyMembers slash level kvs)
end

/-- A document as `JSONEncoder` writes it with `.prettyPrinted` (`slash := true` unless
`.withoutEscapingSlashes`), members in the order given. -/
def pretty (v : Json) (slash : Bool := true) : String := String.ofList (prettyChars slash 0 v)

/-- Members sorted by key (code point order), at every level: `.sortedKeys` for ASCII keys. -/
def Json.sortKeys : Json → Json
  | .arr xs => .arr (sortList xs)
  | .obj kvs => .obj ((sortMembers kvs).mergeSort fun a b => decide (a.1 ≤ b.1))
  | v => v
where
  sortList : List Json → List Json
    | [] => []
    | x :: xs => x.sortKeys :: sortList xs
  sortMembers : List (String × Json) → List (String × Json)
    | [] => []
    | (k, x) :: kvs => (k, x.sortKeys) :: sortMembers kvs

end CairnJson

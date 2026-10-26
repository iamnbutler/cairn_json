# cairn_json

A total JSON parser and encoder in pure Lean for [Cairn](https://github.com/iamnbutler/cairn)
apps, with proofs. It started as yap-cairn's `Yap.Json`. Registry package `cairn_json`, Lean
library `CairnJson`, claim scope `cairn_json`. No Swift product and no `@[extern]`.

```lean
-- lean/lakefile.lean, after `cairn add cairn_json`
require "iamnbutler" / "cairn_json" @ "^0.1.0"

import CairnJson
open CairnJson

decode "{\"a\": [1, 2.5e3, \"é\"]}"
-- some (.obj [("a", .arr [.num ⟨1, 0⟩, .num ⟨25, 2⟩, .str "é"])])
encode (.obj [("ok", .bool true)])   -- "{\"ok\":true}"
pretty (.obj [("ok", .bool true)])   -- "{\n  \"ok\" : true\n}", as JSONEncoder's .prettyPrinted
```

## What's in it

| | |
|---|---|
| `Json` | `null`, `bool`, `num`, `str`, `arr`, `obj`. Objects keep members in order, duplicates included |
| `Number` | an exact decimal `mantissa * 10 ^ exponent`, as written: `1.50` is `⟨150, -2⟩`. Never a float |
| `decode`, `decodeWith limit` | a document from a `String`, nesting at most 512 (or `limit`) deep |
| `decodeBytes` | a document from bytes: UTF-8, UTF-16 or UTF-32, found as `JSONSerialization` finds them |
| `encode v (slash := false)` | compact; `slash` escapes `/` as `JSONEncoder` does by default |
| `pretty v (slash := true)` | `JSONEncoder`'s `.prettyPrinted`: two-space indent, `" : "` |
| `Json.sortKeys` | members sorted by key at every level (`.sortedKeys`, for ASCII keys) |
| `field`, `getStr`, `getBool`, `getNum`, `getArr`, `getObj` | readers |
| `getInt` | an `Int` as `JSONDecoder` reads one: exact in 64 bits, or a whole nearest double |

The parser accepts what `JSONSerialization` accepts (one trailing comma in an array or object
included) with the differences in [docs/trusted.md](docs/trusted.md).

## What is proved

In `lean/CairnJsonProofs/`, with no `sorry` and no axioms beyond `propext`,
`Classical.choice` and `Quot.sound` (`make audit`), each declaration replayed by the kernel
(`make kernel`):

```lean
-- Round trip, compact: every value nested at most `limit` deep, either slash style.
theorem decodeWith_encode (limit : Nat) (v : Json) (slash : Bool) (h : v.depth ≤ limit) :
    decodeWith limit (encode v slash) = some v
theorem decode_encode (v : Json) (slash : Bool) (h : v.depth ≤ maxDepth) :
    decode (encode v slash) = some v
theorem decodeWith_depth_encode (v : Json) (slash : Bool) :
    decodeWith v.depth (encode v slash) = some v

-- Round trip, pretty.
theorem decodeWith_pretty (limit : Nat) (v : Json) (slash : Bool) (h : v.depth ≤ limit) :
    decodeWith limit (pretty v slash) = some v
theorem decode_pretty (v : Json) (slash : Bool) (h : v.depth ≤ maxDepth) :
    decode (pretty v slash) = some v

-- Fuel only cuts a parse short; it never changes an answer.
theorem value_mono_le (limit : Nat) {f g : Nat} (d : Nat) (cs : List Char) (r : Json × List Char)
    (hfg : f ≤ g) (h : value limit f d cs = some r) : value limit g d cs = some r
```

`v.depth` counts nested arrays and objects (a scalar is 0, `[]` is 1); `maxDepth` is 512, as
in `JSONDecoder`. `decodeWith_depth_encode` is the "every value" form: no value is too deep for
a limit of its own depth.

**Totality.** `decode` is total by construction: `value`, `members` and `elements` are
structural recursion on a fuel argument (the input's length plus one), nothing is a
`partial def`, `unsafe` or `implemented_by` (`make lint`), and Lean accepts every definition
without `sorry`. The round-trip theorems show the fuel is enough for every encoded value;
`value_mono_le` shows more fuel would never change an answer it gives. For arbitrary input the
fuel bound is fuzzed rather than proved: every fuzz case is parsed again with four times the
fuel and must give the same answer.

**Speed.** `string` is specified with the rest of the input's length as fuel, which would cost a
pass over the rest of the document for every string literal. Compiled code runs `stringFast`
instead (`strBodyGo`, the same loop by well-founded recursion on what is left), through
`@[csimp] string_eq_fast : @string = @stringFast`, proved from `strBody_eq_go`; so decoding is
linear and every theorem above is about the same definitions. From 0.1.1: a 17 KB document of
540 strings decodes in 53 µs, down from 539 µs.

`Number` is exact, so there is no canonical form to choose: `decode` keeps a number's digits
as written and `encode` writes `mantissa` then `e` and the exponent (`15e-1`), which reads back
as the same `Number`. Equality is the structure's, so `1.5` (`⟨15, -1⟩`) and `1.50`
(`⟨150, -2⟩`) are different values, and `-0` reads as `⟨0, 0⟩`.

Not proved: `decodeBytes`' encoding detection, `getInt`'s rounding, and that the parser
accepts exactly RFC 8259 plus the trailing comma. Those are fuzzed against Foundation
(below), as Cairn's trusted base is.

## Building

```
make build        # lake build CairnJson CairnJsonProofs
make check        # lint, build, axiom audit, kernel replay, quick fuzz
make fuzz         # 220,164 cases against JSONSerialization; SEED=2 make fuzz for another run
```

Toolchain is Cairn's (`lean/lean-toolchain`, v4.35.0). `lake update` needs
`RESERVOIR_API_URL=https://cairn.registry.nexthub.sh/api/v1` to resolve `cairn` from the
registry (the `cairn` CLI sets it).

## The fuzz check

`fuzz/main.swift` generates documents (random valid ones with white space, escapes, surrogate
pairs and long or extreme numbers; mutations of them; UTF-16 and UTF-32 encodings; random bytes;
164 hand-written edge cases), and `lean/Fuzz/Json.lean` (`jsonfuzz`) parses each with
`decodeBytes`. The driver checks that CairnJson and `JSONSerialization` accept the same
documents and read the same values (numbers compared as their nearest `Double`), that
`JSONSerialization` reads CairnJson's `encode` and `pretty` output back as the same value, and
CairnJson's own round trips and fuel. See docs/trusted.md for the results.

MIT licensed.

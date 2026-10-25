# Trusted base

What cairn_json relies on without a proof, and how each piece is checked.

## Proved, not trusted

The round trips (`decode (encode v) = some v`, `decode (pretty v) = some v`) and fuel
monotonicity, in `lean/CairnJsonProofs/` (README.md, "What is proved"). They hold for every
value; nothing below weakens them.

## Fuzzed against Foundation

`make fuzz` (`fuzz/main.swift` driving `lean/Fuzz/Json.lean`) compares `decodeBytes` with
`JSONSerialization.jsonObject(with:options: .fragmentsAllowed)` on macOS 27, Swift 6. A run
is 100,000 random valid documents, 100,000 mutations of them, 10,000 UTF-16 or UTF-32
encodings, 10,000 short random byte strings and 164 hand-written edge cases (220,164 in all).
For each it checks:

1. CairnJson accepts it exactly when Foundation does;
2. both read the same value: same structure, strings by Unicode scalar, numbers as the `Double`
   nearest each (an `NSDecimalNumber` through its exact digits), objects with the first of
   duplicate keys kept, as Foundation keeps it;
3. Foundation reads CairnJson's `encode v` and `pretty v` as that same value;
4. `decode (encode v)` and `decode (pretty v)` give `v` back, and the parse is the same with
   four times the fuel.

Seeds 1 to 5 (1,100,820 cases) end with **0 unexplained differences**. Seed 1: CairnJson
accepted 122,553 documents and refused 97,611, in 4.9 s on the Lean side. Every difference
falls in one of these known classes (seed 1's counts):

| Class | Seed 1 | CairnJson | Foundation |
|---|---:|---|---|
| A number Foundation can't hold | 4,045 | accepts any number exactly | refuses a positive number beyond `Double`'s range (`1e309`, while `-1e309` is `-inf`), a number of 18 or more significant digits whose exponent is outside `Decimal`'s (−128 to 127, e.g. `123456789012345678e-200`), and an exponent of 1000 or more in magnitude (`1e-1000`, `0e999999999`) |
| A leading U+FEFF in a string | 614 | keeps it | drops one U+FEFF at the start of every string and key (`"﻿"` reads as `""`) |
| A short UTF-16 or UTF-32 document | 160 | reads `31 00` style documents of up to 4 bytes by the zero-byte rule | refuses them; `JSONDecoder` accepts them |
| Invalid UTF-8 | 17 | refuses the document | reads invalid bytes inside a string as U+FFFD |
| A number at the edge of `Double` | 7 | exact | gives ±infinity or a different `Double` near `1.8e308` |
| Nesting 513 deep | 2 | refuses past 512, as `JSONDecoder` does | accepts 513, refuses 514 |

Agreements worth stating, each among the edge cases: one trailing comma in an array or object
is accepted by both (`[1,]`, `{"a":1,}`), two are refused; leading zeros, `+1`, `.5`, `1.`,
`NaN`, `Infinity`, comments, single quotes and unquoted keys are refused by both; raw control
characters in strings are refused and escaped ones (`\u0000`) accepted; lone surrogate
escapes are refused; a byte order mark (UTF-8, UTF-16 either way, UTF-32BE) is skipped, and
without one the zero bytes among the first four bytes pick UTF-16 or UTF-32; a UTF-16
document without a byte order mark is read only when its first two characters are below
U+0100 (Foundation's rule, so CairnJson's too).

### Not covered

- `getInt` is checked against `JSONDecoder` by the examples in
  `lean/CairnJsonProofs/Tests.lean` (from yap-cairn's parity notes), not fuzzed.
- `pretty` matches `JSONEncoder`'s `.prettyPrinted` layout by example only, and `sortKeys`
  sorts by code point, which matches `.sortedKeys` for ASCII keys only.
- Documents over a few kilobytes and deeply nested ones are only among the edge cases
  (10,000-element array, 100,000-character string, 512 and 513 deep).

// The trusted fuzz check (docs/trusted.md): CairnJson's parser against Foundation's
// JSONSerialization on random and edge-case documents.
//
//   swiftc -O fuzz/main.swift -o build/jsonfuzz-driver
//   build/jsonfuzz-driver lean/.lake/build/bin/jsonfuzz [count] [seed]
//
// For every document it checks that both accept it or both refuse it, that they read the same
// value (numbers compared as the Double each is nearest to), that JSONSerialization reads
// CairnJson's `encode` and `pretty` output as the same value, and CairnJson's own checks
// (round trips and fuel). Known differences are classified and counted, not failed; anything
// else fails the run.

import Foundation

// MARK: Random numbers (SplitMix64, so a seed reproduces a run)

struct Rng {
    var state: UInt64
    mutating func next() -> UInt64 {
        state &+= 0x9E37_79B9_7F4A_7C15
        var z = state
        z = (z ^ (z >> 30)) &* 0xBF58_476D_1CE4_E5B9
        z = (z ^ (z >> 27)) &* 0x94D0_49BB_1331_11EB
        return z ^ (z >> 31)
    }
    mutating func int(_ n: Int) -> Int { Int(next() % UInt64(n)) }
    mutating func chance(_ p: Double) -> Bool { Double(next() % 1_000_000) / 1_000_000 < p }
    mutating func pick<T>(_ xs: [T]) -> T { xs[int(xs.count)] }
}

// MARK: Generating documents

let wsChars = [" ", "\n", "\r", "\t"]

func ws(_ r: inout Rng) -> String {
    if !r.chance(0.3) { return "" }
    return (0..<(1 + r.int(3))).map { _ in r.pick(wsChars) }.joined()
}

func hex4(_ v: Int, upper: Bool) -> String {
    let s = String(v, radix: 16, uppercase: upper)
    return String(repeating: "0", count: 4 - s.count) + s
}

func genStringBody(_ r: inout Rng) -> String {
    var out = ""
    for _ in 0..<r.int(12) {
        switch r.int(14) {
        case 0: out += r.pick(["\\\"", "\\\\", "\\/", "\\b", "\\f", "\\n", "\\r", "\\t"])
        case 1: out += "\\u" + hex4(r.int(0x20), upper: r.chance(0.5))
        case 2: // a BMP character, not a surrogate
            var v = r.int(0x10000)
            if (0xD800..<0xE000).contains(v) { v = 0x41 }
            out += "\\u" + hex4(v, upper: r.chance(0.5))
        case 3: // a surrogate pair
            let s = 0x10000 + r.int(0x100000)
            let hi = 0xD800 + ((s - 0x10000) >> 10), lo = 0xDC00 + ((s - 0x10000) & 0x3FF)
            out += "\\u" + hex4(hi, upper: false) + "\\u" + hex4(lo, upper: true)
        case 4: out += r.pick(["é", "😀", "中", "\u{2028}", "\u{FEFF}", "e\u{301}", "\u{7F}", "\u{10FFFF}"])
        case 5: out += r.pick(["/", "'", "a b", "\\u0000"])
        default: out += String(UnicodeScalar(UInt8(0x20 + r.int(0x5F))))
                .replacingOccurrences(of: "\\", with: "\\\\").replacingOccurrences(of: "\"", with: "\\\"")
        }
    }
    return out
}

func genNumber(_ r: inout Rng) -> String {
    var s = r.chance(0.3) ? "-" : ""
    if r.chance(0.2) { s += "0" } else {
        s += String(1 + r.int(9))
        for _ in 0..<r.pick([0, 1, 2, 5, 10, 15, 18, 19, 20, 25]) { s += String(r.int(10)) }
    }
    if r.chance(0.3) { s += "."; for _ in 0..<(1 + r.int(8)) { s += String(r.int(10)) } }
    if r.chance(0.25) {
        s += r.pick(["e", "E"]) + r.pick(["", "+", "-"])
        s += String(r.pick([0, 1, 2, 5, 10, 22, 23, 100, 300, 308, 309, 324, 400]) + r.int(3))
    }
    return s
}

func genValue(_ r: inout Rng, _ depth: Int) -> String {
    let k = depth > 4 ? r.int(5) : r.int(7)
    switch k {
    case 0: return "null"
    case 1: return r.chance(0.5) ? "true" : "false"
    case 2, 3: return genNumber(&r)
    case 4: return "\"" + genStringBody(&r) + "\""
    case 5:
        let n = r.int(5)
        var parts: [String] = []
        for _ in 0..<n { parts.append(ws(&r) + genValue(&r, depth + 1) + ws(&r)) }
        let trailing = n > 0 && r.chance(0.05) ? "," : ""
        return "[" + ws(&r) + parts.joined(separator: ",") + trailing + "]"
    default:
        let n = r.int(5)
        var parts: [String] = []
        for _ in 0..<n {
            let key = r.chance(0.3) ? r.pick(["a", "b", "a"]) : genStringBody(&r)
            parts.append(ws(&r) + "\"" + key + "\"" + ws(&r) + ":" + ws(&r) + genValue(&r, depth + 1) + ws(&r))
        }
        let trailing = n > 0 && r.chance(0.05) ? "," : ""
        return "{" + ws(&r) + parts.joined(separator: ",") + trailing + "}"
    }
}

func genDocument(_ r: inout Rng) -> String { ws(&r) + genValue(&r, 0) + ws(&r) }

let interesting: [UInt8] = Array("{}[]\",:\\/ \n\t-+.eE0123456789tfnulrsaUu".utf8) + [0, 0x7F, 0x80, 0xC3, 0xFF, 0x1F]

func mutate(_ d: [UInt8], _ r: inout Rng) -> [UInt8] {
    var d = d
    for _ in 0..<(1 + r.int(3)) {
        switch r.int(5) {
        case 0 where !d.isEmpty: d.remove(at: r.int(d.count))
        case 1: d.insert(r.pick(interesting), at: r.int(d.count + 1))
        case 2 where !d.isEmpty: d[r.int(d.count)] = r.pick(interesting)
        case 3 where !d.isEmpty: d = Array(d.prefix(r.int(d.count)))
        default: d.insert(UInt8(r.int(256)), at: r.int(d.count + 1))
        }
    }
    return d
}

func utf16(_ s: String, bigEndian: Bool, bom: Bool) -> [UInt8] {
    var out: [UInt8] = bom ? (bigEndian ? [0xFE, 0xFF] : [0xFF, 0xFE]) : []
    for u in s.utf16 { out += bigEndian ? [UInt8(u >> 8), UInt8(u & 0xFF)] : [UInt8(u & 0xFF), UInt8(u >> 8)] }
    return out
}

func utf32(_ s: String, bigEndian: Bool, bom: Bool) -> [UInt8] {
    var out: [UInt8] = bom ? (bigEndian ? [0, 0, 0xFE, 0xFF] : [0xFF, 0xFE, 0, 0]) : []
    for u in s.unicodeScalars {
        let v = u.value
        let be = [UInt8(v >> 24), UInt8((v >> 16) & 0xFF), UInt8((v >> 8) & 0xFF), UInt8(v & 0xFF)]
        out += bigEndian ? be : be.reversed()
    }
    return out
}

// MARK: Edge cases

let edgeStrings: [String] = [
    "", " ", "\n", "null", "true", "false", "nul", "tru", "fals", "nulll", "True", "NULL",
    "0", "-0", "1", "-1", "01", "-01", "00", "1.", ".5", "+1", "1.0", "-0.0", "1e5", "1E5", "1e+5",
    "1e-5", "1e", "1e+", "1e-", "1.e5", "1.5e", "-", "--1", "0x10", "Infinity", "-Infinity", "NaN",
    "1e308", "1e309", "-1e309", "1e-324", "1e-400", "2.2250738585072014e-308", "4.9e-324",
    "9223372036854775807", "9223372036854775808", "-9223372036854775808", "-9223372036854775809",
    "18446744073709551615", "18446744073709551616", "99999999999999999999999999999999999999",
    "123456789012345678901234567890e-10", "0.1", "0.30000000000000004", "1e0", "1E-0", "0e999999999",
    "1e999999999", "100000000000000000000000000000000000000000000000000e-30",
    "\"\"", "\"", "\"a", "a\"", "\"\\\"", "\"\\u\"", "\"\\u12\"", "\"\\u123\"", "\"\\u12345\"", "\"\\uGGGG\"",
    "\"\\U0041\"", "\"\\x41\"", "\"\\a\"", "\"\\'\"", "\"\\ud83d\\ude00\"", "\"\\ud83d\"", "\"\\ude00\"",
    "\"\\ud83d\\u0041\"", "\"\\ud83dx\"", "\"\\udbff\\udfff\"", "\"\\u0000\"", "\"\\uFFFF\"", "\"\\uFEFF\"",
    "\"\t\"", "\"\n\"", "\"\u{7F}\"", "\"\u{1F}\"", "\"é\"", "\"😀\"",
    "[]", "[", "]", "[1", "[1,]", "[1,,]", "[,1]", "[,]", "[1 2]", "[1,]]", "[[]]", "[[]", "[]]",
    "{}", "{", "}", "{\"a\"}", "{\"a\":}", "{\"a\":1,}", "{,}", "{\"a\":1,,}", "{\"a\" 1}", "{a:1}",
    "{'a':1}", "{\"a\":1}x", "{\"a\":1} ", "{\"a\":1,\"a\":2}", "{\"\":0}", "{1:1}", "{\"a\":1 , }",
    "[1]x", "[1] [2]", "1 2", "/* c */{}", "// c\n{}", "[1]\u{0}", "\u{FEFF}[1]", "[\u{A0}1]",
    "[\u{0B}1]", "[\u{0C}1]", "[\r\n1]", "  [  1  ,  2  ]  ",
]

func deep(_ n: Int, _ open: String, _ close: String, inner: String = "") -> String {
    String(repeating: open, count: n) + inner + String(repeating: close, count: n)
}

let edgeDocs: [[UInt8]] = edgeStrings.map { Array($0.utf8) } + [
    deep(511, "[", "]"), deep(512, "[", "]"), deep(513, "[", "]"), deep(2000, "[", "]"),
    "{\"a\":" + deep(511, "[", "]") + "}", "{\"a\":" + deep(512, "[", "]") + "}",
    deep(512, "{\"a\":", "}", inner: "1"), deep(513, "{\"a\":", "}", inner: "1"),
    "[" + String(repeating: "1,", count: 10000) + "1]", "\"" + String(repeating: "a", count: 100_000) + "\"",
].map { Array($0.utf8) } + [
    [0xEF, 0xBB, 0xBF] + Array("[1]".utf8), [0xEF, 0xBB, 0xBF], [0xEF, 0xBB], [0xFE, 0xFF], [0xFF, 0xFE],
    [0x22, 0xC3, 0x22], [0x22, 0xFF, 0x22], [0x22, 0xED, 0xA0, 0x80, 0x22], [0x22, 0xC0, 0xAF, 0x22],
    [0x22, 0xF4, 0x90, 0x80, 0x80, 0x22], [0x31, 0x00], [0x00, 0x31], [0x00], [0x00, 0x00, 0x00, 0x31],
    [0x31, 0x00, 0x00, 0x00], [0x00, 0x00, 0xFE, 0xFF, 0, 0, 0, 0x31], [0xFF, 0xFE, 0, 0, 0x31, 0, 0, 0],
    [0x5B, 0x00, 0x31, 0x00, 0x5D, 0x00], [0x00, 0x5B, 0x00, 0x31, 0x00, 0x5D], [0x00, 0x5B, 0x00],
    [0xFE, 0xFF, 0xD8, 0x3D], [0xFE, 0xFF, 0x00, 0x22, 0xD8, 0x3D, 0x00, 0x22],
]

// MARK: Comparing

func scalarsHex(_ s: String) -> String {
    s.unicodeScalars.map { String($0.value, radix: 16) }.joined(separator: ".")
}

func numberKey(_ d: Double) -> String { d == 0 ? "0" : String(d.bitPattern, radix: 16) }

func canon(_ o: Any) -> String {
    switch o {
    case is NSNull: return "n"
    case let n as NSNumber:
        if CFGetTypeID(n) == CFBooleanGetTypeID() { return n.boolValue ? "t" : "f" }
        // An NSDecimalNumber's doubleValue can be an ulp off; its decimal digits are exact.
        if let d = n as? NSDecimalNumber, let v = Double(d.stringValue) { return "#" + numberKey(v) }
        return "#" + numberKey(n.doubleValue)
    case let s as String: return "s" + scalarsHex(s)
    case let a as [Any]: return "[" + a.map(canon).joined(separator: ",") + "]"
    case let d as [String: Any]:
        let entries = d.map { ("s" + scalarsHex($0.key), canon($0.value)) }
            .sorted { Array($0.0.utf8).lexicographicallyPrecedes(Array($1.0.utf8)) }
        return "{" + entries.map { $0.0 + ":" + $0.1 }.joined(separator: ",") + "}"
    default: return "?\(type(of: o))"
    }
}

let numberToken = try! NSRegularExpression(pattern: "#(-?[0-9]+)e(-?[0-9]+)")

/// Lean's canonical form with each exact number replaced by the Double nearest it.
func leanCanon(_ s: String) -> String {
    let ns = s as NSString
    var out = ""
    var last = 0
    for m in numberToken.matches(in: s, range: NSRange(location: 0, length: ns.length)) {
        out += ns.substring(with: NSRange(location: last, length: m.range.location - last))
        let mant = ns.substring(with: m.range(at: 1)), ex = ns.substring(with: m.range(at: 2))
        out += "#" + numberKey(Double(mant + "e" + ex) ?? .nan)
        last = m.range.location + m.range.length
    }
    return out + ns.substring(from: last)
}

func foundation(_ d: [UInt8]) -> Any? {
    try? JSONSerialization.jsonObject(with: Data(d), options: [.fragmentsAllowed])
}

func hex(_ d: [UInt8]) -> String { d.map { String(format: "%02x", $0) }.joined() }

func unhex(_ s: Substring) -> [UInt8] {
    var out: [UInt8] = []
    var i = s.startIndex
    while i < s.endIndex {
        let j = s.index(i, offsetBy: 2)
        out.append(UInt8(s[i..<j], radix: 16)!)
        i = j
    }
    return out
}

let numberPattern = try! NSRegularExpression(pattern: "-?(0|[1-9][0-9]*)(\\.[0-9]+)?([eE][+-]?[0-9]+)?")

/// Numbers Foundation refuses: one it reads as a `Decimal` (18 or more significant digits) whose
/// exponent is outside `Decimal`'s, or a positive one beyond Double's range.
func foundationRefusesNumber(_ text: String) -> Bool {
    let ns = text as NSString
    for m in numberPattern.matches(in: text, range: NSRange(location: 0, length: ns.length)) {
        let token = ns.substring(with: m.range)
        if let d = Double(token), d.isInfinite, d > 0 { return true }
        let intPart = m.range(at: 1).location != NSNotFound ? ns.substring(with: m.range(at: 1)) : ""
        let frac = m.range(at: 2).location != NSNotFound ? String(ns.substring(with: m.range(at: 2)).dropFirst()) : ""
        let exText = m.range(at: 3).location != NSNotFound ? String(ns.substring(with: m.range(at: 3)).dropFirst()) : "0"
        let ex = Int(exText) ?? (exText.hasPrefix("-") ? -1_000_000 : 1_000_000)
        let digits = (intPart + frac).drop { $0 == "0" }
        let e10 = ex - frac.count
        if digits.count >= 18 && (e10 < -128 || e10 > 127) { return true }
        if abs(ex) >= 1000 { return true }
    }
    return false
}

/// A known difference (docs/trusted.md), or nil.
func classify(_ d: [UInt8], lean: String?, leanNoBom: String?, leanEncoded: String?, fnd: String?) -> String? {
    // Numbers are found in CairnJson's own encoding of the value when it has one (the input may
    // be UTF-16 or UTF-32).
    let text = leanEncoded ?? String(decoding: d, as: UTF8.self)
    if let raw = lean, let f = fnd, let rawNoBom = leanNoBom {
        let l = leanCanon(raw)
        if l.contains("#7ff0000000000000") || l.contains("#fff0000000000000") {
            return "a number beyond Double's range"
        }
        if leanCanon(rawNoBom) == f { return "Foundation drops U+FEFF at the start of a string" }
        return nil
    }
    if lean != nil && fnd == nil {
        if foundationRefusesNumber(text) { return "Foundation refuses a number beyond Double's range, outside Decimal's, or with an exponent of 1000 or more" }
        if d.count <= 4 && d.contains(0) { return "Foundation refuses a short UTF-16 or UTF-32 document without a byte order mark" }
    }
    if lean == nil && fnd != nil && String(validatingCString: d.map { CChar(bitPattern: $0) } + [0]) == nil && !d.contains(0) {
        return "Foundation reads invalid UTF-8 in a string as U+FFFD; CairnJson refuses the document"
    }
    if lean == nil && fnd != nil {
        var depth = 0, maxDepth = 0
        for b in d { if b == 0x5B || b == 0x7B { depth += 1; maxDepth = max(maxDepth, depth) } else if b == 0x5D || b == 0x7D { depth -= 1 } }
        if maxDepth == 513 { return "JSONSerialization nests 513 deep, CairnJson (and JSONDecoder) 512" }
    }
    return nil
}

// MARK: Running

let args = CommandLine.arguments
guard args.count >= 2 else {
    print("usage: jsonfuzz-driver <path to lean jsonfuzz> [random count] [seed]"); exit(2)
}
let count = args.count > 2 ? Int(args[2])! : 20000
let seed = args.count > 3 ? UInt64(args[3])! : 1
var rng = Rng(state: seed)

var cases: [(String, [UInt8])] = edgeDocs.map { ("edge", $0) }
for _ in 0..<count { cases.append(("valid", Array(genDocument(&rng).utf8))) }
for _ in 0..<count {
    cases.append(("mutated", mutate(Array(genDocument(&rng).utf8), &rng)))
}
for _ in 0..<(count / 10) {
    let doc = genDocument(&rng)
    let be = rng.chance(0.5), bom = rng.chance(0.5)
    cases.append(("encoded", rng.chance(0.7) ? utf16(doc, bigEndian: be, bom: bom) : utf32(doc, bigEndian: be, bom: bom)))
    cases.append(("bytes", (0..<rng.int(12)).map { _ in UInt8(rng.int(256)) }))
}

let tmp = FileManager.default.temporaryDirectory.appendingPathComponent("cairn_json-fuzz-\(getpid())")
try! FileManager.default.createDirectory(at: tmp, withIntermediateDirectories: true)
defer { try? FileManager.default.removeItem(at: tmp) }
let input = tmp.appendingPathComponent("in.txt"), output = tmp.appendingPathComponent("out.txt")
try! cases.map { hex($0.1) }.joined(separator: "\n").appending("\n").write(to: input, atomically: true, encoding: .utf8)
let p = Process()
p.executableURL = URL(fileURLWithPath: args[1])
p.standardInput = try! FileHandle(forReadingFrom: input)
FileManager.default.createFile(atPath: output.path, contents: nil)
p.standardOutput = try! FileHandle(forWritingTo: output)
let start = Date()
try! p.run()
p.waitUntilExit()
let leanSeconds = Date().timeIntervalSince(start)
let lines = try! String(contentsOf: output, encoding: .utf8).split(separator: "\n", omittingEmptySubsequences: false)
guard lines.count >= cases.count else { print("lean side printed \(lines.count) lines for \(cases.count) cases"); exit(1) }

var tally: [String: Int] = [:]
var known: [String: Int] = [:]
var failures: [String] = []
var accepted = 0, refused = 0
for (i, (kind, d)) in cases.enumerated() {
    tally[kind, default: 0] += 1
    let fields = lines[i].split(separator: "\t", omittingEmptySubsequences: false)
    let leanOK = fields[0] == "OK"
    let fObj = foundation(d)
    let fCanon = fObj.map(canon)
    let lRaw = leanOK ? String(fields[1]) : nil
    let lCanon = lRaw.map(leanCanon)
    var problems: [String] = []
    if fields[0] == "ERR" && fields.count > 1 { problems.append("fuel changed a refusal") }
    if leanOK {
        accepted += 1
        if fields[4] != "1" { problems.append("CairnJson's own round trip or fuel check failed") }
        // JSONSerialization reads CairnJson's output as the same value.
        let enc = foundation(unhex(fields[2])).map(canon), pre = foundation(unhex(fields[3])).map(canon)
        if enc != lCanon { problems.append("Foundation reads encode as \(enc ?? "nil")") }
        if pre != lCanon { problems.append("Foundation reads pretty as \(pre ?? "nil")") }
    } else { refused += 1 }
    if lCanon != fCanon {
        let encText = leanOK ? String(decoding: unhex(fields[2]), as: UTF8.self) : nil
        if let k = classify(d, lean: lRaw, leanNoBom: leanOK ? String(fields[5]) : nil, leanEncoded: encText, fnd: fCanon) { known[k, default: 0] += 1; problems = problems.filter { $0.hasPrefix("CairnJson") || $0.hasPrefix("fuel") } }
        else { problems.append("lean \(lCanon ?? "refuses") / foundation \(fCanon ?? "refuses")") }
    }
    if !problems.isEmpty {
        let shown = d.count > 120 ? hex(Array(d.prefix(60))) + "…(\(d.count) bytes)" : hex(d)
        failures.append("[\(kind)] \(shown) \(String(decoding: d.prefix(80), as: UTF8.self).debugDescription): " + problems.joined(separator: "; "))
    }
}

print("cases: \(cases.count) (" + tally.sorted { $0.key < $1.key }.map { "\($0.key) \($0.value)" }.joined(separator: ", ") + ")")
print("CairnJson accepted \(accepted), refused \(refused); lean side \(String(format: "%.2f", leanSeconds)) s")
for (k, v) in known.sorted(by: { $0.key < $1.key }) { print("known difference: \(k): \(v)") }
print("unexplained: \(failures.count)")
for f in failures.prefix(40) { print("  " + f) }
exit(failures.isEmpty ? 0 : 1)

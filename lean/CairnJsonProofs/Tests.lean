import CairnJson.Core

/-! Examples for `CairnJson`, checked at build time. The leniencies and limits are
`JSONSerialization`'s (docs/trusted.md). -/

namespace CairnJson

private def str? (s : String) (k : String) : Option String :=
  (decode s).bind (·.field k) |>.bind Json.getStr

#guard str? "{\"text\":\"Hello, world.\",\"usage\":{\"type\":\"tokens\",\"total_tokens\":12.5e1}}" "text" == some "Hello, world."
#guard str? "{ \"a\" : [1, -2, {\"b\": null}], \"c\": \"\\u00e9\\ud83d\\ude00\\n\" }" "c" == some "é😀\n"
#guard (decode "[1 2]").isNone && (decode "{\"a\":1} x").isNone
#guard (decode "{\"a\":1,}").isSome && (decode "[1,]").isSome && (decode "{\"a\":1 , }").isSome
#guard (decode "[1,,]").isNone && (decode "{,}").isNone && (decode "[,1]").isNone && (decode "[1,]]").isNone
#guard (decode "01").isNone && (decode "-01").isNone && (decode "1.").isNone && (decode "+1").isNone
#guard (decode ".5").isNone && (decode "/* c */{}").isNone && (decode "\"\\U0041\"").isNone
#guard (decode "0e5").isSome && (decode "-0").isSome && (decode "\"a\\u0000b\"").isSome
#guard (decode "\"\\ud800\"").isNone && (decode "\"\\udc00\"").isNone && (decode "\"a\x01\"").isNone
#guard (decode ("{\"a\":" ++ String.ofList (List.replicate 511 '[') ++ String.ofList (List.replicate 511 ']') ++ "}")).isSome
#guard (decode ("{\"a\":" ++ String.ofList (List.replicate 512 '[') ++ String.ofList (List.replicate 512 ']') ++ "}")).isNone
#guard (decode (String.ofList (List.replicate 512 '[') ++ String.ofList (List.replicate 512 ']'))).isSome
#guard (decode (String.ofList (List.replicate 513 '[') ++ String.ofList (List.replicate 513 ']'))).isNone

-- Numbers keep their digits.
#guard (decode "1.50").bind Json.getNum == some ⟨150, -2⟩
#guard (decode "-1.5E+3").bind Json.getNum == some ⟨-15, 2⟩
#guard (decode "0.05e-1").bind Json.getNum == some ⟨5, -3⟩
#guard (decode "-0").bind Json.getNum == some ⟨0, 0⟩
#guard encode (.num ⟨-15, -1⟩) == "-15e-1" && encode (.num ⟨0, 5⟩) == "0e5" && encode (.int 42) == "42"

-- Whole numbers as `Int`: exact up to 64 bits; otherwise through the nearest double.
#guard ["30.0", "1e1", "-0", "1E2", "2.0e0", "100e-2", "1.5e1", "0.0", "-0.0", "1.0000000000000000001",
    "9223372036854775807", "-9223372036854775808", "0e999999999", "1e-400"].map (fun t => (decode t).bind Json.getInt)
  == [some 30, some 10, some 0, some 100, some 2, some 1, some 15, some 0, some 0, some 1,
      some 9223372036854775807, some (-9223372036854775808), some 0, some 0]
#guard ["30.5", "99999999999999999999", "9223372036854775808", "9223372036854775807.0", "1e400",
    "-9223372036854775809", "5e-1", "1e-300"].all fun t => ((decode t).bind Json.getInt).isNone
#guard ((decode "-9223372036854775808.0").bind Json.getInt) == some (-9223372036854775808)
#guard ((decode "9007199254740993.0").bind Json.getInt) == some 9007199254740992

-- Writing.
#guard encode (.obj [("app", .str "Notes"), ("date", .str "2026-10-23T10:00:00Z"), ("text", .str "a \"b\"/c"), ("typed", .bool false)])
  == "{\"app\":\"Notes\",\"date\":\"2026-10-23T10:00:00Z\",\"text\":\"a \\\"b\\\"/c\",\"typed\":false}"
#guard pretty (.obj [("key", .str "a/b\"é\x01"), ("retentionDays", .int (-4))])
  == "{\n  \"key\" : \"a\\/b\\\"é\\u0001\",\n  \"retentionDays\" : -4\n}"
#guard pretty (.obj [("a", .arr [.int 1, .obj []]), ("b", .arr [])])
  == "{\n  \"a\" : [\n    1,\n    {\n\n    }\n  ],\n  \"b\" : [\n\n  ]\n}"
#guard (decode (quote "tab\there \x01 é")).bind Json.getStr == some "tab\there \x01 é"
#guard encode (Json.obj [("b", .int 1), ("a", .obj [("d", .null), ("c", .null)])]).sortKeys
  == "{\"a\":{\"c\":null,\"d\":null},\"b\":1}"

-- Bytes: UTF-8 with or without a byte order mark, UTF-16 and UTF-32 either way round.
#guard (decodeBytes "[\"é\"]".toUTF8).isSome
#guard (decodeBytes (ByteArray.mk #[0xEF, 0xBB, 0xBF, 0x31])).bind Json.getInt == some 1
#guard (decodeBytes (ByteArray.mk #[0, 0x31, 0, 0x32])).bind Json.getInt == some 12
#guard (decodeBytes (ByteArray.mk #[0x31, 0, 0x32, 0])).bind Json.getInt == some 12
#guard (decodeBytes (ByteArray.mk #[0xFF, 0xFE, 0x31, 0])).bind Json.getInt == some 1
#guard (decodeBytes (ByteArray.mk #[0, 0, 0, 0x37])).bind Json.getInt == some 7

-- README examples
#guard (decode "{\"a\": [1, 2.5e3, \"é\"]}").map encode ==
  some (encode (.obj [("a", .arr [.num ⟨1, 0⟩, .num ⟨25, 2⟩, .str "é"])]))
#guard encode (.obj [("ok", .bool true)]) == "{\"ok\":true}"
#guard pretty (.obj [("ok", .bool true)]) == "{\n  \"ok\" : true\n}"
#guard (decode "1.50").bind Json.getNum == some ⟨150, -2⟩
#guard encode (.num ⟨15, -1⟩) == "15e-1"
#guard (decode "-0").bind Json.getNum == some ⟨0, 0⟩


/- The linear-time string body (`strBodyGo`, which compiled code runs for `string`) agrees with
the fuelled `strBody` on escapes, surrogate pairs, lone surrogates, control characters and an
unterminated literal. -/
private def bodies : List String :=
  ["plain\" rest", "a\\u00e9\\ud83d\\ude00\\n\\t\\\"\\\\\\/\" tail", "\\ud800\"", "\\udc00\"",
   "\\ud83dx\"", "a\x01\"", "no end", "\\q\"", "\\u12\"", "\"", ""]
#guard bodies.all fun b => strBodyGo [] b.toList == strBody (b.length + 1) [] b.toList

end CairnJson

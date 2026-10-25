import CairnJson.Core

/-! # `decode (encode v) = some v`

For every value `v` nested at most `limit` deep, and either slash style:

* `decodeWith_encode`: `decodeWith limit (encode v slash) = some v`;
* `decode_encode`: `decode (encode v slash) = some v` when `v.depth ≤ maxDepth` (512);
* `decodeWith_pretty`, `decode_pretty`: the same for `pretty`.

The parser runs on fuel (the input's length plus one); the proofs show that is always enough
for an encoded value. -/

namespace CairnJson

/-! ## White space -/

theorem skipWs_cons_of_not_ws {c : Char} {cs : List Char} (h : isWs c = false) :
    skipWs (c :: cs) = c :: cs := by
  simp [skipWs, h]

/-! ## Digits -/

theorem digit_char (k : Nat) (h : k < 10) :
    isDigit (Char.ofNat (48 + k)) = true ∧ digitVal (Char.ofNat (48 + k)) = k ∧
    isWs (Char.ofNat (48 + k)) = false ∧ Char.ofNat (48 + k) ≠ '-' ∧
    Char.ofNat (48 + k) ≠ '+' ∧ Char.ofNat (48 + k) ≠ '.' ∧ Char.ofNat (48 + k) ≠ 'e' ∧
    Char.ofNat (48 + k) ≠ 'E' ∧ Char.ofNat (48 + k) ≠ ']' ∧ Char.ofNat (48 + k) ≠ '}' ∧
    (Char.ofNat (48 + k) = '0' ↔ k = 0) := by
  match k, h with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ => decide
  | _ + 10, h => exact absurd h (by omega)

theorem natDigits_all (n : Nat) : ∀ c ∈ natDigits n, isDigit c = true := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [natDigits]
    split
    · intro c hc; simp at hc; subst hc; exact (digit_char n (by omega)).1
    · intro c hc
      simp only [List.mem_append, List.mem_singleton] at hc
      rcases hc with hc | hc
      · exact ih (n / 10) (by omega) c hc
      · subst hc; exact (digit_char (n % 10) (by omega)).1

theorem digitsVal_append (a b : List Char) :
    digitsVal (a ++ b) = b.foldl (fun n c => n * 10 + digitVal c) (digitsVal a) := by
  simp [digitsVal, List.foldl_append]

theorem digitsVal_natDigits (n : Nat) : digitsVal (natDigits n) = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [natDigits]
    split
    · simp [digitsVal, (digit_char n (by omega)).2.1]
    · rw [digitsVal_append, ih (n / 10) (by omega)]
      simp [(digit_char (n % 10) (by omega)).2.1]
      omega

/-- The first digit, and that it is `0` only for `0`. -/
theorem natDigits_head (n : Nat) : ∃ d ds, natDigits n = d :: ds ∧
    isDigit d = true ∧ isWs d = false ∧ d ≠ '-' ∧ d ≠ '+' ∧ d ≠ ']' ∧ d ≠ '}' ∧
    (d = '0' → n = 0 ∧ ds = []) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [natDigits]
    split
    · have := digit_char n (by omega)
      refine ⟨_, [], rfl, this.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2.1, this.2.2.2.2.2.2.2.2.1,
        this.2.2.2.2.2.2.2.2.2.1, fun h => ⟨this.2.2.2.2.2.2.2.2.2.2.1 h, rfl⟩⟩
    · obtain ⟨d, ds, h, h1, h2, h3, h4, h5, h6, h7⟩ := ih (n / 10) (by omega)
      refine ⟨d, ds ++ [Char.ofNat (48 + n % 10)], by rw [h]; rfl, h1, h2, h3, h4, h5, h6, ?_⟩
      intro hd; have := (h7 hd).1; omega

theorem natDigits_ne_nil (n : Nat) : natDigits n ≠ [] := by
  obtain ⟨d, ds, h, -⟩ := natDigits_head n; simp [h]

/-! ## Strings -/

theorem hexVal_hexDigit (n : Nat) (h : n < 16) : hexVal (hexDigit n) = some n := by
  match n, h with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _
  | 10, _ | 11, _ | 12, _ | 13, _ | 14, _ | 15, _ => decide
  | _ + 16, h => exact absurd h (by omega)

/-- One escaped character is read back as itself. -/
theorem strBody_escape (slash : Bool) (f : Nat) (acc : List Char) (c : Char) (tail : List Char) :
    strBody (f + 1) acc (escape slash c ++ tail) = strBody f (c :: acc) tail := by
  unfold escape
  by_cases h1 : c = '"'
  · subst h1; simp [strBody, unescape]
  by_cases h2 : c = '\\'
  · subst h2; simp [strBody, unescape]
  by_cases h3 : slash = true ∧ c = '/'
  · obtain ⟨hs, rfl⟩ := h3; subst hs; simp [strBody, unescape]
  by_cases h4 : c = '\n'
  · subst h4; simp [strBody, unescape]
  by_cases h5 : c = '\r'
  · subst h5; simp [strBody, unescape]
  by_cases h6 : c = '\t'
  · subst h6; simp [strBody, unescape]
  by_cases h7 : c = '\x08'
  · subst h7; simp [strBody, unescape]
  by_cases h8 : c = '\x0c'
  · subst h8; simp [strBody, unescape]
  by_cases h9 : c.toNat < 0x20
  · simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, ite_false, ite_true]
    have ha := hexVal_hexDigit (c.toNat / 16) (by omega)
    have hb := hexVal_hexDigit (c.toNat % 16) (by omega)
    have hz : hexVal '0' = some 0 := by decide
    have : (c.toNat / 16 * 16 + c.toNat % 16) = c.toNat := by omega
    have hs1 : ¬(55296 ≤ c.toNat ∧ c.toNat < 56320) := by omega
    have hs2 : ¬(56320 ≤ c.toNat ∧ c.toNat < 57344) := by omega
    simp [strBody, hex4, ha, hb, hz, unicode, this, hs1, hs2]
  · simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, ite_false, List.singleton_append]
    simp [strBody, h1, h2, h9]

theorem length_le_flatMap_escape (slash : Bool) (cs : List Char) :
    cs.length ≤ (cs.flatMap (escape slash)).length := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    have : 1 ≤ (escape slash c).length := by
      unfold escape; repeat' split
      all_goals simp
    simp only [List.flatMap_cons, List.length_append, List.length_cons]; omega

theorem strBody_quoted (slash : Bool) (cs : List Char) :
    ∀ (f : Nat) (acc tail : List Char), cs.length < f →
      strBody f acc (cs.flatMap (escape slash) ++ '"' :: tail) =
        some (String.ofList (acc.reverse ++ cs), tail) := by
  induction cs with
  | nil =>
    intro f acc tail h
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp at h; omega⟩
    simp [strBody]
  | cons c cs ih =>
    intro f acc tail h
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp at h; omega⟩
    rw [List.flatMap_cons, List.append_assoc, strBody_escape, ih f (c :: acc) tail (by simp at h; omega)]
    simp

/-- A string literal is read back as its string. -/
theorem string_quoteChars (slash : Bool) (s : String) (tail : List Char) :
    (match quoteChars slash s ++ tail with
      | '"' :: rest => string rest
      | _ => none) = some (s, tail) := by
  simp only [quoteChars, List.cons_append, List.append_assoc, List.nil_append, string]
  rw [strBody_quoted slash s.toList _ [] tail]
  · simp
  · have := length_le_flatMap_escape slash s.toList
    simp only [List.length_append, List.length_cons]; omega

/-! ## Numbers -/

/-- What may follow a value in an encoding: nothing, a delimiter or white space. -/
def Follow : List Char → Prop
  | [] => True
  | c :: _ => c = ',' ∨ c = ']' ∨ c = '}' ∨ isWs c = true

/-- No digit next. -/
def NoDigit (t : List Char) : Prop := ∀ c t', t = c :: t' → isDigit c = false

theorem follow_char {c : Char} (h : c = ',' ∨ c = ']' ∨ c = '}' ∨ isWs c = true) :
    isDigit c = false ∧ c ≠ '.' ∧ c ≠ 'e' ∧ c ≠ 'E' := by
  have hw : isWs c = true → c = ' ' ∨ c = '\n' ∨ c = '\r' ∨ c = '\t' := by
    simp [isWs]
  rcases h with rfl | rfl | rfl | h
  · decide
  · decide
  · decide
  · rcases hw h with rfl | rfl | rfl | rfl <;> decide

theorem takeWhile_natDigits (n : Nat) (t : List Char) (h : NoDigit t) :
    (natDigits n ++ t).takeWhile isDigit = natDigits n := by
  rw [List.takeWhile_append_of_pos (natDigits_all n)]
  cases t with
  | nil => simp
  | cons c t' => simp [h c t' rfl]

theorem dropWhile_natDigits (n : Nat) (t : List Char) (h : NoDigit t) :
    (natDigits n ++ t).dropWhile isDigit = t := by
  rw [List.dropWhile_append_of_pos (natDigits_all n)]
  cases t with
  | nil => simp
  | cons c t' => simp [h c t' rfl]

theorem exponent_chars (e : Int) (rest : List Char) (h : Follow rest) :
    exponent ((if e = 0 then [] else 'e' :: intDigits e) ++ rest) = some (e, rest) := by
  have nd : NoDigit rest := by
    intro c t' hr; subst hr; exact (follow_char h).1
  by_cases he : e = 0
  · subst he
    cases rest with
    | nil => simp [exponent]
    | cons c t =>
      have := follow_char h
      simp [exponent, this.2.2.1, this.2.2.2]
  · simp only [he, ite_false, List.cons_append, exponent]
    simp only [true_or, ite_true]
    unfold intDigits
    by_cases hn : e < 0
    · simp only [hn, ite_true, List.cons_append]
      rw [takeWhile_natDigits _ _ nd, dropWhile_natDigits _ _ nd, digitsVal_natDigits]
      simp [natDigits_ne_nil]; omega
    · simp only [hn, ite_false]
      obtain ⟨d, ds, hd, -, -, h1, h2, -⟩ := natDigits_head e.natAbs
      have k1 := takeWhile_natDigits e.natAbs rest nd
      have k2 := dropWhile_natDigits e.natAbs rest nd
      rw [hd] at k1 k2 ⊢
      simp only [List.cons_append] at k1 k2 ⊢
      split
      · rename_i r' heq; simp at heq; exact absurd heq.1 h2
      · rename_i r' heq; simp at heq; exact absurd heq.1 h1
      · simp only [k1, k2]
        rw [← hd, digitsVal_natDigits]
        simp [natDigits_ne_nil]; omega

theorem number_chars (x : Number) (rest : List Char) (h : Follow rest) :
    number (x.chars ++ rest) = some (.num x, rest) := by
  have nd : NoDigit ((if x.exponent = 0 then [] else 'e' :: intDigits x.exponent) ++ rest) := by
    intro c t' hr
    by_cases he : x.exponent = 0
    · simp [he] at hr; subst hr; exact (follow_char h).1
    · simp [he] at hr; rw [← hr.1]; decide
  have hfrac : fraction ((if x.exponent = 0 then [] else 'e' :: intDigits x.exponent) ++ rest) =
      some ([], (if x.exponent = 0 then [] else 'e' :: intDigits x.exponent) ++ rest) := by
    by_cases he : x.exponent = 0
    · simp only [he, ite_true, List.nil_append]
      cases rest with
      | nil => simp [fraction]
      | cons c t => simp [fraction, (follow_char h).2.1]
    · simp [he, fraction]
  have hexp := exponent_chars x.exponent rest h
  obtain ⟨m, e⟩ := x
  simp only [Number.chars, List.append_assoc] at nd hfrac hexp ⊢
  generalize (if e = 0 then [] else 'e' :: intDigits e) ++ rest = T at nd hfrac hexp ⊢
  obtain ⟨d, ds, hd, -, -, h1, -, -, -, h0⟩ := natDigits_head m.natAbs
  have k1 := takeWhile_natDigits m.natAbs _ nd
  have k2 := dropWhile_natDigits m.natAbs _ nd
  unfold intDigits
  by_cases hn : m < 0
  · simp only [hn, ite_true, List.cons_append, number]
    rw [k1, k2, hfrac]
    simp only [hexp, natDigits_ne_nil, List.isEmpty_iff, ite_false, List.append_nil,
      digitsVal_natDigits]
    rw [hd]
    have : ¬(d = '0' ∧ 1 < (d :: ds).length) := by
      intro ⟨a, b⟩; have := h0 a; simp [this.2] at b
    simp only [List.head?_cons, Option.some.injEq, this, ite_false]
    simp; omega
  · simp only [hn, ite_false, number]
    rw [hd] at k1 k2 ⊢
    simp only [List.cons_append] at k1 k2 ⊢
    split
    · rename_i r heq; simp at heq; exact absurd heq.1 h1
    · simp only [k1, k2, hfrac, hexp]
      have : ¬(d = '0' ∧ 1 < (d :: ds).length) := by
        intro ⟨a, b⟩; have := h0 a; simp [this.2] at b
      simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false, List.head?_cons,
        Option.some.injEq, this, List.append_nil]
      rw [← hd, digitsVal_natDigits]
      simp; omega

/-- A string literal's body, read back. -/
theorem string_body (slash : Bool) (s : String) (tail : List Char) :
    string (s.toList.flatMap (escape slash) ++ '"' :: tail) = some (s, tail) := by
  unfold string
  rw [strBody_quoted slash s.toList _ [] tail]
  · simp
  · have := length_le_flatMap_escape slash s.toList
    simp only [List.length_append, List.length_cons]; omega

/-! ## Values -/

/-- An encoding starts with a character that is not white space or a closing bracket. -/
theorem encChars_head (slash : Bool) (v : Json) : ∃ c t, encChars slash v = c :: t ∧
    isWs c = false ∧ c ≠ ']' ∧ c ≠ '}' := by
  cases v with
  | null => exact ⟨_, _, rfl, by decide, by decide, by decide⟩
  | bool b => cases b <;> exact ⟨_, _, rfl, by decide, by decide, by decide⟩
  | str s => exact ⟨_, _, rfl, by decide, by decide, by decide⟩
  | arr xs => cases xs <;> exact ⟨_, _, rfl, by decide, by decide, by decide⟩
  | obj kvs => cases kvs with
    | nil => exact ⟨_, _, rfl, by decide, by decide, by decide⟩
    | cons kv kvs => exact ⟨_, _, rfl, by decide, by decide, by decide⟩
  | num x =>
    simp only [encChars, Number.chars, intDigits]
    split
    · exact ⟨_, _, rfl, by decide, by decide, by decide⟩
    · obtain ⟨d, ds, hd, -, h1, -, -, h2, h3, -⟩ := natDigits_head x.mantissa.natAbs
      rw [hd]; exact ⟨_, _, rfl, h1, h2, h3⟩

theorem skipWs_quoteChars (slash : Bool) (s : String) (rest : List Char) :
    skipWs (quoteChars slash s ++ rest) = quoteChars slash s ++ rest := by
  simp only [quoteChars, List.cons_append]; exact skipWs_cons_of_not_ws (by decide)

theorem skipWs_encChars (slash : Bool) (v : Json) (rest : List Char) :
    skipWs (encChars slash v ++ rest) = encChars slash v ++ rest := by
  obtain ⟨c, t, h, hw, -, -⟩ := encChars_head slash v
  rw [h]; exact skipWs_cons_of_not_ws hw

theorem length_encChars_pos (slash : Bool) (v : Json) : 0 < (encChars slash v).length := by
  obtain ⟨c, t, h, -⟩ := encChars_head slash v
  simp [h]

theorem value_number (limit f d : Nat) (c : Char) (t : List Char)
    (hc : c = '-' ∨ isDigit c = true) :
    value limit (f + 1) d (c :: t) = number (c :: t) := by
  have hw : isWs c = false := by
    rcases hc with rfl | hc
    · decide
    · revert hc; simp only [isDigit, isWs]; intro hc
      simp only [decide_eq_true_eq] at hc ⊢
      rcases hc with ⟨h1, h2⟩
      refine Bool.eq_false_iff.mpr ?_
      intro h; simp only [decide_eq_true_eq] at h
      rcases h with rfl | rfl | rfl | rfl <;> simp_all <;> contradiction
  unfold value
  rw [skipWs_cons_of_not_ws hw]
  split
  all_goals first
    | rfl
    | (rename_i heq; simp only [List.cons.injEq] at heq; obtain ⟨rfl, -⟩ := heq
       rcases hc with h | h <;> exfalso <;> revert h <;> decide)

mutual
theorem value_encChars (limit : Nat) (slash : Bool) (v : Json) (f d : Nat) (rest : List Char)
    (hf : (encChars slash v).length ≤ f) (hd : d + v.depth ≤ limit) (hr : Follow rest) :
    value limit f d (encChars slash v ++ rest) = some (v, rest) := by
  obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by have := length_encChars_pos slash v; omega⟩
  match hv : v with
  | .null => simp [encChars, value, skipWs, isWs]
  | .bool true => simp [encChars, value, skipWs, isWs]
  | .bool false => simp [encChars, value, skipWs, isWs]
  | .num x =>
    have hn := number_chars x rest hr
    simp only [encChars] at hf ⊢
    revert hn
    simp only [Number.chars, intDigits]
    split
    · simp only [List.cons_append]; intro hn
      rw [value_number limit f d '-' _ (Or.inl rfl), hn]
    · obtain ⟨c, t, hc, hdig, -⟩ := natDigits_head x.mantissa.natAbs
      rw [hc]; simp only [List.cons_append]; intro hn
      rw [value_number limit f d c _ (Or.inr hdig), hn]
  | .str s =>
    simp only [encChars, quoteChars, List.cons_append, List.append_assoc, value, skipWs, isWs]
    simp [string_body]
  | .arr [] =>
    simp only [Json.depth, Json.depth.depthList] at hd
    simp only [encChars, List.length_cons, List.length_nil] at hf
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    simp only [encChars, List.cons_append, List.nil_append, value]
    rw [skipWs_cons_of_not_ws (by decide)]
    simp only [show d < limit by omega, ite_true]
    rw [skipWs_cons_of_not_ws (by decide)]
    simp [elements]
  | .arr (x :: xs) =>
    simp only [Json.depth] at hd
    simp only [encChars, List.cons_append, List.length_cons] at hf ⊢
    simp only [value]
    rw [skipWs_cons_of_not_ws (by decide)]
    simp only [show d < limit by omega, ite_true]
    rw [List.append_assoc, skipWs_encChars, ← List.append_assoc]
    rw [elements_encChars limit slash x xs f (d + 1) [] true rest (by omega) (by omega) hr]
    simp
  | .obj [] =>
    simp only [Json.depth, Json.depth.depthMembers] at hd
    simp only [encChars, List.length_cons, List.length_nil] at hf
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    simp only [encChars, List.cons_append, List.nil_append, value]
    rw [skipWs_cons_of_not_ws (by decide)]
    simp only [show d < limit by omega, ite_true]
    rw [skipWs_cons_of_not_ws (by decide)]
    simp [members]
  | .obj ((k, x) :: kvs) =>
    simp only [Json.depth] at hd
    simp only [encChars, List.cons_append, List.length_cons] at hf ⊢
    simp only [value]
    rw [skipWs_cons_of_not_ws (by decide)]
    simp only [show d < limit by omega, ite_true]
    rw [List.append_assoc, skipWs_quoteChars, ← List.append_assoc]
    rw [members_encChars limit slash k x kvs f (d + 1) [] true rest (by omega) (by omega) hr]
    simp
termination_by sizeOf v
decreasing_by all_goals (subst hv; simp only [Json.arr.sizeOf_spec, Json.obj.sizeOf_spec, List.cons.sizeOf_spec, Prod.mk.sizeOf_spec]; omega)

theorem elements_encChars (limit : Nat) (slash : Bool) (x : Json) (xs : List Json)
    (f d : Nat) (acc : List Json) (first : Bool) (rest : List Char)
    (hf : (encChars slash x ++ encList slash xs).length ≤ f)
    (hd : d + Json.depth.depthList (x :: xs) ≤ limit) (hr : Follow rest) :
    elements limit f d acc (encChars slash x ++ encList slash xs ++ rest) first =
      some (.arr (acc.reverse ++ x :: xs), rest) := by
  have hpos := length_encChars_pos slash x
  have hlist : 0 < (encList slash xs).length := by cases xs <;> simp [encList]
  obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp only [List.length_append] at hf; omega⟩
  simp only [Json.depth.depthList] at hd
  unfold elements
  split
  · rename_i r heq
    obtain ⟨c, t, hc, -, hc2, -⟩ := encChars_head slash x
    rw [hc] at heq; simp only [List.cons_append, List.cons.injEq] at heq
    exact absurd heq.1 hc2
  · rw [List.append_assoc, value_encChars limit slash x f d (encList slash xs ++ rest)
      (by simp only [List.length_append] at hf; omega) (by omega)
      (by cases xs <;> simp [encList, Follow])]
    match hx : xs with
    | [] =>
      simp only [encList, List.cons_append, List.nil_append]
      rw [skipWs_cons_of_not_ws (by decide)]
      simp
    | y :: ys =>
      simp only [encList, List.cons_append]
      rw [skipWs_cons_of_not_ws (by decide)]
      simp only [Json.depth.depthList] at hd
      simp only [encList, List.length_append, List.length_cons] at hf
      simp only
      rw [List.append_assoc, skipWs_encChars, ← List.append_assoc]
      rw [elements_encChars limit slash y ys f d (x :: acc) false rest
        (by simp only [List.length_append]; omega) (by simp only [Json.depth.depthList]; omega) hr]
      simp
termination_by sizeOf x + sizeOf xs + 1
decreasing_by all_goals (try subst hx); all_goals (simp only [List.cons.sizeOf_spec] at *; omega)

theorem members_encChars (limit : Nat) (slash : Bool) (k : String) (x : Json)
    (kvs : List (String × Json)) (f d : Nat) (acc : List (String × Json)) (first : Bool)
    (rest : List Char)
    (hf : (quoteChars slash k ++ ':' :: (encChars slash x ++ encMembers slash kvs)).length ≤ f)
    (hd : d + Json.depth.depthMembers ((k, x) :: kvs) ≤ limit) (hr : Follow rest) :
    members limit f d acc (quoteChars slash k ++ ':' :: (encChars slash x ++ encMembers slash kvs) ++ rest) first =
      some (.obj (acc.reverse ++ (k, x) :: kvs), rest) := by
  have hpos := length_encChars_pos slash x
  have hlist : 0 < (encMembers slash kvs).length := by cases kvs <;> simp [encMembers]
  obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 :=
    ⟨f - 1, by simp only [List.length_append, List.length_cons] at hf; omega⟩
  simp only [Json.depth.depthMembers] at hd
  simp only [quoteChars, List.length_cons, List.length_append, List.length_nil] at hf
  simp only [members, quoteChars, List.cons_append, List.append_assoc]
  rw [string_body]
  simp only [List.nil_append]
  rw [skipWs_cons_of_not_ws (by decide)]
  simp only
  rw [value_encChars limit slash x f d (encMembers slash kvs ++ rest) (by omega) (by omega)
      (by cases kvs <;> simp [encMembers, Follow])]
  match hk : kvs with
  | [] =>
    simp only [encMembers, List.cons_append, List.nil_append]
    rw [skipWs_cons_of_not_ws (by decide)]
    simp
  | (k', y) :: kvs =>
    simp only [encMembers, List.cons_append]
    rw [skipWs_cons_of_not_ws (by decide)]
    simp only [Json.depth.depthMembers] at hd
    simp only [encMembers, List.length_append, List.length_cons] at hf
    simp only
    rw [List.append_assoc, skipWs_quoteChars]
    have := members_encChars limit slash k' y kvs f d ((k, x) :: acc) false rest
      (by simp only [List.length_append, List.length_cons]; omega)
      (by simp only [Json.depth.depthMembers]; omega) hr
    simp only [List.append_assoc, List.cons_append] at this ⊢
    rw [this]
    simp
termination_by sizeOf x + sizeOf kvs + 1
decreasing_by all_goals (try subst hk); all_goals (simp only [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec] at *; omega)
end

/-! ## Documents, compact -/

theorem decodeChars_encChars (limit : Nat) (slash : Bool) (v : Json) (h : v.depth ≤ limit) :
    decodeChars limit (encChars slash v) = some v := by
  unfold decodeChars
  have := value_encChars limit slash v ((encChars slash v).length + 1) 0 [] (by omega) (by omega)
    (by simp [Follow])
  rw [List.append_nil] at this
  rw [this]; simp [skipWs]

/-- **Round trip.** Every value nested at most `limit` deep is read back from its compact
encoding, with `/` escaped or not. -/
theorem decodeWith_encode (limit : Nat) (v : Json) (slash : Bool) (h : v.depth ≤ limit) :
    decodeWith limit (encode v slash) = some v := by
  simp [decodeWith, encode, decodeChars_encChars limit slash v h]

/-- **Round trip.** `decode (encode v) = some v` for every value nested at most 512 deep. -/
theorem decode_encode (v : Json) (slash : Bool) (h : v.depth ≤ maxDepth) :
    decode (encode v slash) = some v :=
  decodeWith_encode maxDepth v slash h

/-- With the limit set to the value's own depth, every value round-trips. -/
theorem decodeWith_depth_encode (v : Json) (slash : Bool) :
    decodeWith v.depth (encode v slash) = some v :=
  decodeWith_encode v.depth v slash (Nat.le_refl _)

/-! ## Documents, pretty -/

theorem skipWs_ws {c : Char} (cs : List Char) (h : isWs c = true) : skipWs (c :: cs) = skipWs cs := by
  simp [skipWs, h]

theorem skipWs_indent (n : Nat) (cs : List Char) : skipWs (indent n ++ cs) = skipWs cs := by
  unfold indent
  induction 2 * n with
  | zero => simp
  | succ k ih => simp only [List.replicate_succ, List.cons_append]; rw [skipWs_ws _ (by decide), ih]

theorem value_ws (limit f d : Nat) {c : Char} (cs : List Char) (h : isWs c = true) :
    value limit f d (c :: cs) = value limit f d cs := by
  cases f with
  | zero => simp [value]
  | succ f => simp only [value]; rw [skipWs_ws _ h]

theorem value_indent (limit f d n : Nat) (cs : List Char) :
    value limit f d (indent n ++ cs) = value limit f d cs := by
  unfold indent
  induction 2 * n with
  | zero => simp
  | succ k ih => simp only [List.replicate_succ, List.cons_append]; rw [value_ws _ _ _ _ (by decide), ih]

theorem prettyChars_scalar (slash : Bool) (l : Nat) (v : Json)
    (h : (∀ xs, v ≠ .arr xs) ∧ ∀ kvs, v ≠ .obj kvs) : prettyChars slash l v = encChars slash v := by
  cases v with
  | arr xs => exact absurd rfl (h.1 xs)
  | obj kvs => exact absurd rfl (h.2 kvs)
  | _ => simp [prettyChars]

theorem prettyChars_head (slash : Bool) (l : Nat) (v : Json) : ∃ c t, prettyChars slash l v = c :: t ∧
    isWs c = false ∧ c ≠ ']' ∧ c ≠ '}' := by
  cases v with
  | arr xs => cases xs <;> exact ⟨_, _, rfl, by decide, by decide, by decide⟩
  | obj kvs => cases kvs with
    | nil => exact ⟨_, _, rfl, by decide, by decide, by decide⟩
    | cons kv kvs => exact ⟨_, _, rfl, by decide, by decide, by decide⟩
  | null => rw [prettyChars_scalar _ _ _ ⟨by simp, by simp⟩]; exact encChars_head slash _
  | bool b => rw [prettyChars_scalar _ _ _ ⟨by simp, by simp⟩]; exact encChars_head slash _
  | num x => rw [prettyChars_scalar _ _ _ ⟨by simp, by simp⟩]; exact encChars_head slash _
  | str s => rw [prettyChars_scalar _ _ _ ⟨by simp, by simp⟩]; exact encChars_head slash _

theorem skipWs_prettyChars (slash : Bool) (l : Nat) (v : Json) (rest : List Char) :
    skipWs (prettyChars slash l v ++ rest) = prettyChars slash l v ++ rest := by
  obtain ⟨c, t, h, hw, -, -⟩ := prettyChars_head slash l v
  rw [h]; exact skipWs_cons_of_not_ws hw

theorem length_prettyChars_pos (slash : Bool) (l : Nat) (v : Json) : 0 < (prettyChars slash l v).length := by
  obtain ⟨c, t, h, -⟩ := prettyChars_head slash l v
  simp [h]

mutual
theorem value_prettyChars (limit : Nat) (slash : Bool) (l : Nat) (v : Json) (f d : Nat) (rest : List Char)
    (hf : (prettyChars slash l v).length ≤ f) (hd : d + v.depth ≤ limit) (hr : Follow rest) :
    value limit f d (prettyChars slash l v ++ rest) = some (v, rest) := by
  match hv : v with
  | .null | .bool _ | .num _ | .str _ =>
    rw [prettyChars_scalar _ _ _ ⟨by simp, by simp⟩] at hf ⊢
    exact value_encChars limit slash _ f d rest hf hd hr
  | .arr [] =>
    simp only [Json.depth, Json.depth.depthList] at hd
    simp only [prettyChars, List.length_append, List.length_cons, List.length_nil] at hf
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    simp only [prettyChars, List.cons_append, List.nil_append, List.append_assoc, value]
    rw [skipWs_cons_of_not_ws (by decide)]
    simp only [show d < limit by omega, ite_true]
    rw [skipWs_ws _ (by decide), skipWs_ws _ (by decide), skipWs_indent]
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    simp [skipWs, isWs, elements]
  | .arr (x :: xs) =>
    simp only [Json.depth] at hd
    simp only [prettyChars, List.length_cons, List.length_append] at hf
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    simp only [prettyChars, List.cons_append, List.append_assoc, value]
    rw [skipWs_cons_of_not_ws (by decide)]
    simp only [show d < limit by omega, ite_true]
    rw [skipWs_ws _ (by decide), skipWs_indent, skipWs_prettyChars, ← List.append_assoc]
    rw [elements_prettyChars limit slash l x xs f (d + 1) [] true rest
      (by simp only [List.length_append]; omega) (by omega) hr]
    simp
  | .obj [] =>
    simp only [Json.depth, Json.depth.depthMembers] at hd
    simp only [prettyChars, List.length_append, List.length_cons, List.length_nil] at hf
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    simp only [prettyChars, List.cons_append, List.nil_append, List.append_assoc, value]
    rw [skipWs_cons_of_not_ws (by decide)]
    simp only [show d < limit by omega, ite_true]
    rw [skipWs_ws _ (by decide), skipWs_ws _ (by decide), skipWs_indent]
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    simp [skipWs, isWs, members]
  | .obj ((k, x) :: kvs) =>
    simp only [Json.depth] at hd
    simp only [prettyChars, List.length_cons, List.length_append] at hf
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    simp only [prettyChars, List.cons_append, List.append_assoc, value]
    rw [skipWs_cons_of_not_ws (by decide)]
    simp only [show d < limit by omega, ite_true]
    rw [skipWs_ws _ (by decide), skipWs_indent, skipWs_quoteChars]
    have := members_prettyChars limit slash l k x kvs f (d + 1) [] true rest
      (by simp only [List.length_append, List.length_cons]; omega) (by omega) hr
    simp only [List.append_assoc, List.cons_append] at this
    rw [this]
    simp
termination_by sizeOf v
decreasing_by all_goals (subst hv; simp only [Json.arr.sizeOf_spec, Json.obj.sizeOf_spec, List.cons.sizeOf_spec, Prod.mk.sizeOf_spec]; omega)

theorem elements_prettyChars (limit : Nat) (slash : Bool) (l : Nat) (x : Json) (xs : List Json)
    (f d : Nat) (acc : List Json) (first : Bool) (rest : List Char)
    (hf : (prettyChars slash (l + 1) x ++ prettyList slash l xs).length ≤ f)
    (hd : d + Json.depth.depthList (x :: xs) ≤ limit) (hr : Follow rest) :
    elements limit f d acc (prettyChars slash (l + 1) x ++ prettyList slash l xs ++ rest) first =
      some (.arr (acc.reverse ++ x :: xs), rest) := by
  have hpos := length_prettyChars_pos slash (l + 1) x
  have hlist : 0 < (prettyList slash l xs).length := by cases xs <;> simp [prettyList]
  obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp only [List.length_append] at hf; omega⟩
  simp only [Json.depth.depthList] at hd
  unfold elements
  split
  · rename_i r heq
    obtain ⟨c, t, hc, -, hc2, -⟩ := prettyChars_head slash (l + 1) x
    rw [hc] at heq; simp only [List.cons_append, List.cons.injEq] at heq
    exact absurd heq.1 hc2
  · rw [List.append_assoc, value_prettyChars limit slash (l + 1) x f d (prettyList slash l xs ++ rest)
      (by simp only [List.length_append] at hf; omega) (by omega)
      (by cases xs <;> simp [prettyList, Follow, isWs])]
    match hx : xs with
    | [] =>
      simp only [prettyList, List.cons_append, List.append_assoc]
      rw [skipWs_ws _ (by decide), skipWs_indent, skipWs_cons_of_not_ws (by decide)]
      simp
    | y :: ys =>
      simp only [prettyList, List.cons_append, List.append_assoc]
      rw [skipWs_cons_of_not_ws (by decide)]
      simp only [Json.depth.depthList] at hd
      simp only [prettyList, List.length_append, List.length_cons] at hf
      simp only
      rw [skipWs_ws _ (by decide), skipWs_indent, skipWs_prettyChars, ← List.append_assoc]
      rw [elements_prettyChars limit slash l y ys f d (x :: acc) false rest
        (by simp only [List.length_append]; omega) (by simp only [Json.depth.depthList]; omega) hr]
      simp
termination_by sizeOf x + sizeOf xs + 1
decreasing_by all_goals (try subst hx); all_goals (simp only [List.cons.sizeOf_spec] at *; omega)

theorem members_prettyChars (limit : Nat) (slash : Bool) (l : Nat) (k : String) (x : Json)
    (kvs : List (String × Json)) (f d : Nat) (acc : List (String × Json)) (first : Bool)
    (rest : List Char)
    (hf : (quoteChars slash k ++ [' ', ':', ' '] ++ prettyChars slash (l + 1) x ++ prettyMembers slash l kvs).length ≤ f)
    (hd : d + Json.depth.depthMembers ((k, x) :: kvs) ≤ limit) (hr : Follow rest) :
    members limit f d acc (quoteChars slash k ++ [' ', ':', ' '] ++ prettyChars slash (l + 1) x ++ prettyMembers slash l kvs ++ rest) first =
      some (.obj (acc.reverse ++ (k, x) :: kvs), rest) := by
  have hpos := length_prettyChars_pos slash (l + 1) x
  have hlist : 0 < (prettyMembers slash l kvs).length := by cases kvs <;> simp [prettyMembers]
  obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 :=
    ⟨f - 1, by simp only [List.length_append, List.length_cons] at hf; omega⟩
  simp only [Json.depth.depthMembers] at hd
  simp only [quoteChars, List.length_cons, List.length_append, List.length_nil] at hf
  simp only [members, quoteChars, List.cons_append, List.append_assoc]
  rw [string_body]
  simp only [List.nil_append]
  rw [skipWs_ws _ (by decide), skipWs_cons_of_not_ws (by decide)]
  simp only
  rw [value_ws _ _ _ _ (by decide)]
  rw [value_prettyChars limit slash (l + 1) x f d (prettyMembers slash l kvs ++ rest) (by omega) (by omega)
      (by cases kvs <;> simp [prettyMembers, Follow, isWs])]
  match hk : kvs with
  | [] =>
    simp only [prettyMembers, List.cons_append, List.append_assoc]
    rw [skipWs_ws _ (by decide), skipWs_indent, skipWs_cons_of_not_ws (by decide)]
    simp
  | (k', y) :: kvs =>
    simp only [prettyMembers, List.cons_append, List.append_assoc]
    rw [skipWs_cons_of_not_ws (by decide)]
    simp only [Json.depth.depthMembers] at hd
    simp only [prettyMembers, List.length_append, List.length_cons] at hf
    simp only
    rw [skipWs_ws _ (by decide), skipWs_indent, skipWs_quoteChars]
    have := members_prettyChars limit slash l k' y kvs f d ((k, x) :: acc) false rest
      (by simp only [List.length_append, List.length_cons]; omega)
      (by simp only [Json.depth.depthMembers]; omega) hr
    simp only [List.append_assoc, List.cons_append] at this ⊢
    rw [this]
    simp
termination_by sizeOf x + sizeOf kvs + 1
decreasing_by all_goals (try subst hk); all_goals (simp only [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec] at *; omega)
end

theorem decodeChars_prettyChars (limit : Nat) (slash : Bool) (v : Json) (h : v.depth ≤ limit) :
    decodeChars limit (prettyChars slash 0 v) = some v := by
  unfold decodeChars
  have := value_prettyChars limit slash 0 v ((prettyChars slash 0 v).length + 1) 0 [] (by omega)
    (by omega) (by simp [Follow])
  rw [List.append_nil] at this
  rw [this]; simp [skipWs]

/-- **Round trip, pretty.** Every value nested at most `limit` deep is read back from its
`.prettyPrinted` encoding. -/
theorem decodeWith_pretty (limit : Nat) (v : Json) (slash : Bool) (h : v.depth ≤ limit) :
    decodeWith limit (pretty v slash) = some v := by
  simp [decodeWith, pretty, decodeChars_prettyChars limit slash v h]

theorem decode_pretty (v : Json) (slash : Bool) (h : v.depth ≤ maxDepth) :
    decode (pretty v slash) = some v :=
  decodeWith_pretty maxDepth v slash h

end CairnJson

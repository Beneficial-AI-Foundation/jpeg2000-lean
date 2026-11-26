import Spec.Resources.PacketLocalWork
import Spec.ColorResources.MappingPrefix

/-!
# Diagnostic construction (Plan.md §§3–5, 7, S3; T.800 A.4–A.6, B.10, I.4)

The three textual error constructors retain a UTF-8 string. A limit error retains its
location, kind and two naturals. In particular, the very first reduction check can
return a reference to an arbitrarily large caller-owned natural. Rendering such a
value with `Error.toString` is a separate operation.

The logical charge below counts digit-loop iterations at the widths of their operands,
UTF-8 bytes, and copies at the individual append nodes of a message. Charging cumulative
temporary payload covers simultaneously live payload, including intermediate prefixes,
even without in-place appends. These are structural units, independent of heap headers,
compiler sharing and the machine-word fast path for `Nat.repr`.

The public certificates cover admission, the signature read, SOC/SIZ, SOT framing,
PPM count preflight, SOP, colour resolution, final channel selection and interleaving.
The parser, packet and reconstruction stages between these prefixes still need their
own diagnostic traces before these bounds can be summed over an entire decode.
-/

namespace JPEG2000.Spec.Resources.DiagnosticCost

/-! ## Numeric conversion and message expressions -/

/-- Bit positions sufficient for a natural, including zero. -/
def bits (n : Nat) : Nat := n.log2 + 1

private theorem bits_mono {a b : Nat} (h : a ≤ b) : bits a ≤ bits b := by
  cases a with
  | zero => simp [bits, Nat.log2_zero]
  | succ a =>
    have hb : b ≠ 0 := by omega
    exact Nat.succ_le_succ ((Nat.le_log2 hb).2 (Nat.le_trans (Nat.log2_self_le (Nat.succ_ne_zero a)) h))

/-- Each iteration of the library's `Nat.toDigitsCore` performs a quotient and remainder
by a small fixed base, tests zero, decrements fuel, and prepends one digit. Charge bit
visits for the numeric operands and a constant allowance for digit selection, list
construction and writing the ASCII character. -/
def digitWork (base : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n =>
    let q := n / base
    let here := 32 + 8 * (bits (fuel + 1) + bits n)
    here + if q = 0 then 0 else digitWork base fuel q

/-- Cumulative logical payload allocated during digit extraction. A step holds a
digit and list link, the quotient, remainder, and decremented fuel. Count bit widths
as bytes to overestimate numeric payload, and count a list link as one logical slot. -/
def digitStorage (base : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n =>
    let q := n / base
    6 + bits q + bits (n % base) + bits fuel +
      if q = 0 then 0 else digitStorage base fuel q

private theorem digit_storage_le (base fuel n : Nat) : digitStorage base fuel n ≤ digitWork base fuel n := by
  induction fuel generalizing n with
  | zero => exact Nat.le_refl _
  | succ f ih =>
    simp only [digitStorage,digitWork]
    have q := bits_mono (Nat.div_le_self n base)
    have r := bits_mono (Nat.mod_le n base)
    have ff : bits f ≤ bits (f + 1) := bits_mono (by omega)
    split <;> have := ih (n/base) <;> omega

private theorem digit_size (n : Nat) : n.digitChar.utf8Size = 1 := by
  by_cases h : 16 ≤ n
  · rw [Nat.digitChar_eq_star.mpr h]; rfl
  · have : n < 16 := by omega
    exact (show ∀ i : Fin 16, i.val.digitChar.utf8Size = 1 by decide) ⟨n, this⟩

private theorem cons_bytes (c : Char) (xs : List Char) :
    (String.ofList (c :: xs)).utf8ByteSize = c.utf8Size + (String.ofList xs).utf8ByteSize := by
  rw [show c :: xs = [c] ++ xs from rfl, String.ofList_append, String.utf8ByteSize_append,
    ← String.singleton_eq_ofList, String.utf8ByteSize_singleton]

private theorem loop_cost (base cap : Nat) (fuel n : Nat) (acc : List Char)
    (hf : fuel ≤ cap + 1) (hn : n ≤ cap) :
    let out := Nat.toDigitsCore base fuel n acc
    (String.ofList out).utf8ByteSize + acc.length =
      (String.ofList acc).utf8ByteSize + out.length ∧
    digitWork base fuel n + acc.length * (32 + 16 * bits (cap + 1)) ≤
      out.length * (32 + 16 * bits (cap + 1)) := by
  induction fuel generalizing n acc with
  | zero => simp [digitWork, Nat.toDigitsCore, Nat.add_comm]
  | succ f ih =>
    simp only [Nat.toDigitsCore, digitWork]
    have a := bits_mono hf
    have b : bits n ≤ bits (cap + 1) := bits_mono (by omega)
    split
    · simp only [cons_bytes, digit_size, List.length_cons, Nat.add_one_mul, Nat.add_zero]
      omega
    · have ⟨s, w⟩ := ih (n / base) ((n % base).digitChar :: acc) (by omega)
          (Nat.le_trans (Nat.div_le_self ..) hn)
      simp only [cons_bytes, digit_size, List.length_cons] at s w
      rw [Nat.add_one_mul acc.length] at w
      constructor <;> omega

/-- UTF-8 bytes equal decimal/hex digit count. The digit loop is bounded by the binary
width of the largest field, including the initial fuel `n + 1`. -/
theorem radix_cost {base n cap : Nat} (baseOK : 2 ≤ base) (hn : n ≤ cap) :
    let ds := Nat.toDigits base n
    (String.ofList ds).utf8ByteSize = ds.length ∧ ds.length ≤ bits cap ∧
    digitWork base (n + 1) n ≤ bits cap * (32 + 16 * bits (cap + 1)) := by
  have ⟨bytes, work⟩ := loop_cost base cap (n + 1) n [] (by omega) hn
  have count : (Nat.toDigits base n).length ≤ bits cap :=
    (Nat.length_toDigits_le_iff baseOK (Nat.succ_pos _)).2
      (Nat.lt_of_le_of_lt hn (Nat.lt_of_lt_of_le Nat.lt_log2_self
        (Nat.pow_le_pow_left baseOK (bits cap))))
  refine ⟨by simpa [Nat.toDigits] using bytes, count, ?_⟩
  exact Nat.le_trans (by simpa [Nat.toDigits] using work) (Nat.mul_le_mul_right _ count)

private theorem box_name_bytes (t : UInt32) : (Box.typeName t).utf8ByteSize = 4 := by
  have letter (n : Nat) : (if 32 ≤ n ∧ n < 127 then Char.ofNat n else '.').utf8Size = 1 := by
    split
    · rename_i good
      exact (show ∀ i : Fin 127, (Char.ofNat i.val).utf8Size = 1 by decide) ⟨n,good.2⟩
    · rfl
  simp only [Box.typeName,cons_bytes,letter]
  rfl

/-- The expression tree of a diagnostic. Numerals represent `Nat.toDigits` in the
specified base. In particular a hex marker has a separate literal `0x` prefix. -/
inductive Text where
  /-- Existing UTF-8 bytes (literal text or an already constructed field). -/
  | fixed (s : String)
  /-- Decimal natural, as used by interpolation of unsigned wire fields. -/
  | dec (n : Nat)
  /-- Hexadecimal digit sequence, before the marker helper's prefix. -/
  | hexDigits (n : Nat)
  /-- Four printable bytes decoded from a 32-bit JP2 box type. -/
  | boxName (t : UInt32)
  /-- A particular append in the production expression. -/
  | cat (left right : Text)

namespace Text

/-- The represented string, with the same grouping as the production interpolation. -/
def render : Text → String
  | .fixed s => s
  | .dec n => toString n
  | .hexDigits n => String.ofList (Nat.toDigits 16 n)
  | .boxName t => Box.typeName t
  | .cat l r => l.render ++ r.render

/-- UTF-8 payload plus digit conversions and copying at each append. A fixed literal
can be shared; the charge conservatively includes its full payload. -/
def work : Text → Nat
  | .fixed s => 1 + s.utf8ByteSize
  | .dec n => 1 + digitWork 10 (n + 1) n + (toString n).utf8ByteSize
  | .hexDigits n => 1 + digitWork 16 (n + 1) n + (String.ofList (Nat.toDigits 16 n)).utf8ByteSize
  | .boxName t => 32 + (Box.typeName t).utf8ByteSize
  | .cat l r => l.work + r.work + 1 + l.render.utf8ByteSize + r.render.utf8ByteSize

/-- Temporary logical allocation. Count each digit-list entry and each numeric
temporary in the converter, the UTF-8 result buffer, and the entire output buffer
of every append. Summing allocations bounds peak live payload under arbitrary sharing. -/
def storage : Text → Nat
  | .fixed s => s.utf8ByteSize
  | .dec n => digitStorage 10 (n+1) n + (toString n).utf8ByteSize
  | .hexDigits n => digitStorage 16 (n+1) n + (String.ofList (Nat.toDigits 16 n)).utf8ByteSize
  | .boxName t => 20 + (Box.typeName t).utf8ByteSize
  | .cat l r => l.storage + r.storage + 1 + (l.render ++ r.render).utf8ByteSize

/-- Cumulative intermediate logical allocations fit the same interpolation budget. -/
theorem storage_le_work (t : Text) : t.storage ≤ t.work := by
  induction t with
  | fixed => simp [storage,work]
  | dec n => have := digit_storage_le 10 (n+1) n; simp only [storage,work]; omega
  | hexDigits n => have := digit_storage_le 16 (n+1) n; simp only [storage,work]; omega
  | boxName => simp [storage,work]
  | cat l r hl hr => simp only [storage,work,String.utf8ByteSize_append]; omega

/-- Maximum permitted scalar, total literal bytes and number of expression nodes.
The indices are additive so the rule for an append also covers interpolated messages
embedded in another message. -/
inductive Within (cap : Nat) : Text → Nat → Nat → Prop where
  /-- Existing literal. -/
  | fixed (s : String) : Within cap (.fixed s) s.utf8ByteSize 1
  /-- Bounded decimal value. -/
  | dec {n : Nat} (h : n ≤ cap) : Within cap (.dec n) 0 1
  /-- Bounded hexadecimal value. -/
  | hex {n : Nat} (h : n ≤ cap) : Within cap (.hexDigits n) 0 1
  /-- Four fixed-width extractions, printable checks and single-byte characters. -/
  | boxName (t : UInt32) : Within cap (.boxName t) 4 1
  /-- Ordered append. -/
  | cat {l r : Text} {a b i j : Nat} (left : Within cap l a i) (right : Within cap r b j) :
      Within cap (.cat l r) (a + b) (i + j + 1)

/-- Budget in UTF-8 bytes for a message of bounded literal size and shape. -/
def byteBound (cap literal nodes : Nat) := literal + nodes * bits cap

/-- Cumulative logical byte, digit and append charge for a bounded message, also
covering its newly allocated temporary payload. -/
def workBound (cap literal nodes : Nat) :=
  nodes * (1 + byteBound cap literal nodes + bits cap * (32 + 16 * bits (cap + 1)))

/-- A certified expression bounds UTF-8 storage and all digit and append work. -/
theorem bounds {cap literal nodes : Nat} {t : Text} (h : Within cap t literal nodes) :
    t.render.utf8ByteSize ≤ byteBound cap literal nodes ∧ t.work ≤ workBound cap literal nodes := by
  induction h with
  | fixed s =>
    simp [workBound, byteBound, render, work]
    omega
  | dec hn =>
    have ⟨b, d, w⟩ := radix_cost (base := 10) (by decide) hn
    simp only [Nat.toString_eq_ofList_toDigits, render, work, b, workBound, byteBound,
      Nat.one_mul, Nat.zero_add]
    constructor <;> omega
  | hex hn =>
    have ⟨b, d, w⟩ := radix_cost (base := 16) (by decide) hn
    simp only [render, work, b, workBound, byteBound, Nat.one_mul, Nat.zero_add]
    constructor <;> omega
  | boxName t =>
    have p : 1 ≤ bits cap := Nat.succ_pos _
    have w := Nat.mul_le_mul p (show 32 ≤ 32 + 16 * bits (cap+1) by omega)
    simp only [render,work,box_name_bytes,workBound,byteBound,Nat.one_mul]
    omega
  | @cat l r a b i j _ _ hl hr =>
    have hbl : byteBound cap a i ≤ byteBound cap (a+b) (i+j+1) := by
      simp only [byteBound, Nat.add_mul, Nat.one_mul]; omega
    have hbr : byteBound cap b j ≤ byteBound cap (a+b) (i+j+1) := by
      simp only [byteBound, Nat.add_mul, Nat.one_mul]; omega
    have sum : l.render.utf8ByteSize + r.render.utf8ByteSize ≤ byteBound cap (a+b) (i+j+1) := by
      simp only [byteBound, Nat.add_mul, Nat.one_mul] at *; omega
    let D := bits cap * (32 + 16 * bits (cap + 1))
    have wl := Nat.le_trans hl.2 (Nat.mul_le_mul_left i (Nat.add_le_add_right (Nat.add_le_add_left hbl 1) D))
    have wr := Nat.le_trans hr.2 (Nat.mul_le_mul_left j (Nat.add_le_add_right (Nat.add_le_add_left hbr 1) D))
    refine ⟨by simpa only [render, String.utf8ByteSize_append] using sum, ?_⟩
    simp only [work, workBound]
    rw [Nat.add_one_mul, Nat.add_mul]
    dsimp only [D] at wl wr
    omega

end Text

/-! ## Stored and rendered error payloads -/

/-- Only the three textual constructors hold message bytes inside the decoder. -/
def retainedBytes : Error → Nat
  | .truncated _ s | .malformed _ s | .unsupported _ s => s.utf8ByteSize
  | .limitExceeded .. => 0

/-- Oversized public reduction and input arguments produce typed errors. The reduction
is retained by reference with the caller's limit; neither is decimalized here. -/
theorem public_admission {L : Limits} {data : ByteArray} {opts : DecodeOptions}
    (over : L.maxDecompLevels < opts.reduce ∨ L.maxInputBytes < data.size) :
    let e := if L.maxDecompLevels < opts.reduce then
        Error.limitExceeded JPEG2000.Decode.loc .decompLevels opts.reduce L.maxDecompLevels
      else Error.limitExceeded (.atOffset .box 0) .inputBytes data.size L.maxInputBytes
    decodeCodestream L data opts.reduce = .error e ∧ JPEG2000.decode L data opts = .error e ∧
      retainedBytes e = 0 := by
  obtain ⟨_, raw, img⟩ := PublicPacketWork.admission_error (PublicPacketWork.admission_excess over)
  exact ⟨raw, img, by split <;> rfl⟩

/-- A bounded derivation for the interpolation that constructs a particular string. -/
structure Built (cap : Nat) (msg : String) where
  /-- Append tree, including the digits formatted by this call. -/
  tree : Text
  /-- Erasing all charges gives exactly the production message. -/
  erase : tree.render = msg
  /-- Total UTF-8 size of the fixed fragments. -/
  literal : Nat
  /-- Count of fixed fragments, numbers and binary appends. -/
  nodes : Nat
  /-- Provenance of the leaves and the append structure. -/
  shape : tree.Within cap literal nodes
  /-- Maximum fixed UTF-8 payload in the supported calls. -/
  fixedBound : literal ≤ 128
  /-- Maximum expression size in the supported calls. -/
  nodeBound : nodes ≤ 24

/-- Uniform bounds on the string and on its construction, for every certified site. -/
theorem built_cost {cap : Nat} {msg : String} (b : Built cap msg) :
    msg.utf8ByteSize ≤ Text.byteBound cap 128 24 ∧ b.tree.work ≤ Text.workBound cap 128 24 := by
  obtain ⟨bytes, work⟩ := Text.bounds b.shape
  have h := Nat.add_le_add b.fixedBound (Nat.mul_le_mul_right (bits cap) b.nodeBound)
  refine ⟨b.erase ▸ Nat.le_trans bytes h, Nat.le_trans work ?_⟩
  exact Nat.mul_le_mul b.nodeBound (Nat.add_le_add_right (Nat.add_le_add_left h 1) _)

/-- A diagnostic consisting of a single bounded UTF-8 literal. -/
def oneFixed {cap : Nat} (s : String) (hs : s.utf8ByteSize ≤ 128) : Built cap s :=
  ⟨.fixed s,rfl,_,_,.fixed s,hs,by decide⟩

open JPEG2000.Bytes

/-- A diagnostic expression for a particular string with its literal bytes and node count. -/
structure ExprFor (cap : Nat) (s : String) (literal nodes : Nat) where
  /-- The sequence of digit conversions and appends. -/
  tree : Text
  /-- Evaluating the expression produces the original diagnostic text. -/
  erase : tree.render = s
  /-- Numeric operands, literal bytes and nodes meet their declared bounds. -/
  shape : tree.Within cap literal nodes

/-- The expression for a literal fragment. -/
def litExpr (cap : Nat) (s : String) : ExprFor cap s s.utf8ByteSize 1 :=
  ⟨_, rfl, .fixed s⟩

/-- The decimal expression for a natural number within the given bound. -/
def decExpr {cap n : Nat} (h : n ≤ cap) : ExprFor cap (toString n) 0 1 :=
  ⟨_, rfl, .dec h⟩

/-- Join two fragments and charge their intermediate string construction. -/
def catExpr {cap a b i j : Nat} {s t : String}
    (x : ExprFor cap s a i) (y : ExprFor cap t b j) : ExprFor cap (s ++ t) (a+b) (i+j+1) :=
  ⟨_, by simp only [Text.render, x.erase, y.erase], .cat x.shape y.shape⟩

/-- Certify a complete diagnostic from its fragment and node bounds. -/
def closeExpr {cap a i : Nat} {s : String} (x : ExprFor cap s a i)
    (ha : a ≤ 128) (hi : i ≤ 24) : Built cap s :=
  ⟨x.tree,x.erase,a,i,x.shape,ha,hi⟩

/-- All transient messages at a measured site, including messages superseded by
another error. The result index connects the trace to the production code. -/
structure Trace {α : Type} (cap : Nat) (run : Except Error α) (count : Nat) where
  /-- Every charged construction has its own certified tree. -/
  messages : List (Σ s, Built cap s)
  /-- Simulation of the rejecting or successful prefix bounds the event count. -/
  countBound : messages.length ≤ count
  /-- A returned textual payload occurs in the trace. A limit error retains the
  computed value and the original bound. -/
  origin : ∀ e, run = .error e →
    e.offset?.getD 0 ≤ cap ∧ (match e with
    | .truncated _ s | .malformed _ s | .unsupported _ s => ∃ m ∈ messages, m.1 = s
    | .limitExceeded _ _ v _ => v ≤ cap)

/-- Cumulative conversion, copying and storage charge across the entire observed
prefix, plus the retained bytes in its eventual error. -/
theorem trace_cost {α : Type} {cap count : Nat} {run : Except Error α} (t : Trace cap run count) :
    (t.messages.map (fun m => m.2.tree.work)).sum ≤ count * Text.workBound cap 128 24 ∧
      ∀ e, run = .error e → retainedBytes e ≤ Text.byteBound cap 128 24 := by
  have aux (xs : List (Σ s, Built cap s)) :
      (xs.map (fun m => m.2.tree.work)).sum ≤ xs.length * Text.workBound cap 128 24 := by
    induction xs with
    | nil => simp
    | cons m ms ih =>
      rw [List.map_cons, List.sum_cons, List.length_cons, Nat.add_one_mul, Nat.add_comm (_ * _)]
      exact Nat.add_le_add (built_cost m.2).2 ih
  refine ⟨Nat.le_trans (aux _) (Nat.mul_le_mul_right _ t.countBound), ?_⟩
  intro e he
  have ret := (t.origin e he).2
  cases e with
  | limitExceeded => exact Nat.zero_le _
  | _ => obtain ⟨m,_,rfl⟩ := ret; exact (built_cost m.2).1

/-- Cumulative logical storage of the actual events, including temporary converted
digits and copied prefixes even when a parent later discards the whole error. -/
theorem trace_storage {α : Type} {cap count : Nat} {run : Except Error α} (t : Trace cap run count) :
    (t.messages.map (fun m => m.2.tree.storage)).sum ≤ count * Text.workBound cap 128 24 := by
  refine Nat.le_trans ?_ (trace_cost t).1
  generalize t.messages = xs
  induction xs with
  | nil => simp
  | cons m ms ih => exact Nat.add_le_add m.2.tree.storage_le_work ih

/-- Logical payload of a stored error, counting a fixed record, UTF-8 bytes and
the binary width of its offset and its computed value. A typed ceiling is an
existing reference to the caller's field of `Limits`. For the first reduction
error, `borrowValue` also treats the supplied natural as an existing reference.
The six slots overcount the location, tags and references in any constructor. -/
def storedPayload (borrowValue : Bool) (e : Error) : Nat :=
  6 + retainedBytes e + bits (e.offset?.getD 0) +
    match e with
    | .limitExceeded _ _ v _ => if borrowValue then 0 else bits v
    | _ => 0

/-- Every trace bounds the stored record and all internally owned fields,
including the binary width of a computed limit value before admission. -/
theorem trace_retained {α : Type} {cap count : Nat} {run : Except Error α} (t : Trace cap run count)
    {e : Error} (bad : run = .error e) :
    storedPayload false e ≤ 6 + Text.byteBound cap 128 24 + 2*bits cap := by
  obtain ⟨off,value⟩ := t.origin e bad
  have b := bits_mono off
  have h := (trace_cost t).2 e bad
  cases e with
  | limitExceeded loc k v bound =>
    have n := bits_mono value
    simp only [storedPayload,Bool.false_eq_true,↓reduceIte]
    omega
  | _ => simp only [storedPayload,Nat.add_zero]; omega

/-- The first reduction rejection stores references to both external naturals.
Its decoder-owned payload is constant for arbitrary reduction and limit values. -/
theorem reduction_storage {L : Limits} {d : ByteArray} {opts : DecodeOptions}
    (over : L.maxDecompLevels < opts.reduce) :
    let e := Error.limitExceeded Decode.loc .decompLevels opts.reduce L.maxDecompLevels
    decodeCodestream L d opts.reduce = .error e ∧ JPEG2000.decode L d opts = .error e ∧
      storedPayload true e = 7 := by
  obtain ⟨raw,img,_⟩ := public_admission (data := d) (opts := opts) (.inl over)
  exact ⟨by simpa [over] using raw,by simpa [over] using img,rfl⟩

/-- The exact expression evaluated only if a caller requests a rendering of a
typed limit error. Stage and limit-kind names are static. The two numeric fields
and the optional numeric offset incur their own decimal conversion and append costs. -/
def renderLimit (l : Location) (k : LimitKind) (v b : Nat) : Text :=
  let where_ := match l.offset with
    | none => Text.fixed (toString l.stage)
    | some n => .cat (.cat (.fixed (toString l.stage)) (.fixed "@")) (.dec n)
  .cat (.cat (.cat (.cat (.cat (.cat (.cat (.fixed "limit exceeded at ") where_)
    (.fixed ": ")) (.fixed (toString k))) (.fixed " = ")) (.dec v)) (.fixed " > ")) (.dec b)

/-- Rendering on demand has a field-dependent charge. The bound on the external
reduction is required only here, once the caller actually asks for its digits. -/
theorem render_limit_cost (l : Location) (k : LimitKind) (v b : Nat) :
    let cap := max (l.offset.getD 0) (max v b)
    let t := renderLimit l k v b
    t.render = (Error.limitExceeded l k v b).toString ∧
    t.render.utf8ByteSize ≤ Text.byteBound cap 128 24 ∧ t.work ≤ Text.workBound cap 128 24 := by
  let cap := max (l.offset.getD 0) (max v b)
  have hv : v ≤ cap := Nat.le_trans (Nat.le_max_left ..) (Nat.le_max_right ..)
  have hb : b ≤ cap := Nat.le_trans (Nat.le_max_right ..) (Nat.le_max_right ..)
  have stage : (toString l.stage).utf8ByteSize ≤ 8 := by cases l.stage <;> decide
  have kind : (toString k).utf8ByteSize ≤ 18 := by cases k <;> decide
  cases h : l.offset with
  | none =>
    let cert : Built cap (Error.limitExceeded l k v b).toString :=
      ⟨renderLimit l k v b,by simp [renderLimit,Text.render,Error.toString,Location.toString,h,toString],
        _,_,by simp only [renderLimit,h]; exact .cat (.cat (.cat (.cat (.cat (.cat (.cat
          (.fixed _) (.fixed _)) (.fixed _)) (.fixed _)) (.fixed _)) (.dec hv)) (.fixed _)) (.dec hb),
        by change 18+_+2+_+3+0+3+0 ≤ 128; omega,by decide⟩
    rw [← h]
    exact ⟨cert.erase,cert.erase ▸ (built_cost cert).1,(built_cost cert).2⟩
  | some n =>
    have hn : n ≤ cap := by simpa only [cap,h,Option.getD] using Nat.le_max_left n (max v b)
    let cert : Built cap (Error.limitExceeded l k v b).toString :=
      ⟨renderLimit l k v b,by simp [renderLimit,Text.render,Error.toString,Location.toString,h,toString],
        _,_,by simp only [renderLimit,h]; exact .cat (.cat (.cat (.cat (.cat (.cat (.cat
          (.fixed _) (.cat (.cat (.fixed _) (.fixed _)) (.dec hn))) (.fixed _)) (.fixed _))
          (.fixed _)) (.dec hv)) (.fixed _)) (.dec hb),
        by change 18+(_+1+0)+2+_+3+0+3+0 ≤ 128; omega,by decide⟩
    rw [← h]
    exact ⟨cert.erase,cert.erase ▸ (built_cost cert).1,(built_cost cert).2⟩

/-- With fixed limits and a fixed byte string, caller rendering of the first typed
error can produce arbitrarily many bytes. The decoder retains the supplied natural
without constructing any of those decimal digits. -/
theorem caller_render_unbounded (L : Limits) (d : ByteArray) (n : Nat) :
    ∃ red, let e := Error.limitExceeded Decode.loc .decompLevels red L.maxDecompLevels
      decodeCodestream L d red = .error e ∧ JPEG2000.decode L d {reduce := red} = .error e ∧
      retainedBytes e = 0 ∧ n < e.toString.utf8ByteSize := by
  let red := max (L.maxDecompLevels+1) (10^(n+1))
  have over : L.maxDecompLevels < red := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left ..)
  obtain ⟨raw,img,_⟩ := public_admission (L := L) (data := d) (opts := {reduce := red}) (.inl over)
  have digits : n+1 < (Nat.toDigits 10 red).length := by
    apply Nat.lt_of_not_ge
    intro h
    have := (Nat.length_toDigits_le_iff (by decide : 2 ≤ 10) (Nat.succ_pos n)).1 h
    exact (Nat.not_lt_of_ge (Nat.le_max_right ..)) this
  obtain ⟨bytes,_,_⟩ := radix_cost (base := 10) (by decide) (Nat.le_refl red)
  refine ⟨red,by simpa [over] using raw,by simpa [over] using img,rfl,?_⟩
  simp only [Error.toString,String.utf8ByteSize_append,Nat.toString_eq_ofList_toDigits,bytes]
  omega

/-! ## Composing actual diagnostic events -/

/-- A successful operation that constructs no diagnostics. -/
def doneTrace {α : Type} {cap k : Nat} (x : α) : Trace cap (.ok x) k :=
  ⟨[],Nat.zero_le _,by intros; contradiction⟩

/-- Reuse the same events under a larger event-count allowance. -/
def widen {α : Type} {cap j k : Nat} {r : Except Error α} (x : Trace cap r j)
    (h : j ≤ k) : Trace cap r k := ⟨x.messages,Nat.le_trans x.countBound h,x.origin⟩

/-- Compose traces in execution order and stop at the first error. -/
def bindTrace {α β : Type} {cap i j : Nat} {r : Except Error α}
    {f : α → Except Error β} (x : Trace cap r i) (y : ∀ a, r = .ok a → Trace cap (f a) j) :
    Trace cap (r >>= f) (j+i) := by
  cases r with
  | error e =>
    exact ⟨x.messages, Nat.le_trans x.countBound (Nat.le_add_left ..), by intro e' he; cases he; exact x.origin _ rfl⟩
  | ok a =>
    let t := y a rfl
    refine ⟨x.messages ++ t.messages, ?_, ?_⟩
    · rw [List.length_append, Nat.add_comm j i]; exact Nat.add_le_add x.countBound t.countBound
    · intro e he
      obtain ⟨off, why⟩ := t.origin e he
      refine ⟨off, ?_⟩
      cases e with
      | limitExceeded => exact why
      | _ => obtain ⟨m, hm, eq⟩ := why; exact ⟨m,List.mem_append_right _ hm,eq⟩

private def malformed {α : Type} {cap : Nat} {s : String} (l : Location)
    (loc : l.offset.getD 0 ≤ cap) (b : Built cap s) : Trace cap (Except.error (.malformed l s) : Except Error α) 1 :=
  ⟨[⟨s,b⟩], by simp, by intro e he; cases he; exact ⟨loc,⟨s,b⟩,by simp,rfl⟩⟩

private def truncated {α : Type} {cap : Nat} {s : String} (l : Location)
    (loc : l.offset.getD 0 ≤ cap) (b : Built cap s) : Trace cap (Except.error (.truncated l s) : Except Error α) 1 :=
  ⟨[⟨s,b⟩], by simp, by intro e he; cases he; exact ⟨loc,⟨s,b⟩,by simp,rfl⟩⟩

/-- Charge the supplied diagnostic even when the marker requirement succeeds. -/
def requireTrace {cap : Nat} (r : Reader) (hr : r.pos ≤ cap)
    (c : Bool) (s : String) (b : Built cap s) : Trace cap (Marker.require r c s) 1 := by
  cases c
  · exact malformed _ hr b
  · exact ⟨[⟨s,b⟩],by simp,by intros; contradiction⟩

/-- Trace a trailing-byte check and its decimal count. -/
def endTrace {cap : Nat} (r : Reader) (hr : r.data.size ≤ cap) (s : String)
    (hs : s.utf8ByteSize ≤ 96) : Trace cap (Marker.expectEnd r s) 1 := by
  unfold Marker.expectEnd
  split
  · exact doneTrace ()
  · apply malformed _ (Nat.le_trans r.pos_le_size hr)
    apply closeExpr (catExpr (catExpr (catExpr (litExpr _ s) (litExpr _ ": "))
      (decExpr (Nat.le_trans (Nat.sub_le r.stop r.pos) (Nat.le_trans r.stop_le hr)))) (litExpr _ " trailing bytes"))
    · change s.utf8ByteSize + 2 + 0 + 15 ≤ 128; omega
    · decide

/-- Trace a typed limit check, including its computed value on rejection. -/
def checkedTrace {cap : Nat} (L : Limits) (loc : Location) (kind : LimitKind) (n : Nat)
    (hl : loc.offset.getD 0 ≤ cap) (hv : n ≤ cap) : Trace cap (L.check loc kind n) 0 := by
  unfold Limits.check Limits.checkLe
  split
  · exact doneTrace ()
  · exact ⟨[],by simp,by intro e he; cases he; exact ⟨hl,hv⟩⟩

/-- Trace a byte read, including its truncation diagnostic. -/
def u8Trace {cap : Nat} (r : Reader) (hr : r.pos ≤ cap) :
    Trace cap r.u8 1 := by
  unfold Reader.u8
  split
  · exact doneTrace _
  · exact truncated _ hr (oneFixed "u8" (by decide))

/-- Trace an unsigned 16-bit read and its truncation diagnostic. -/
def u16beTrace {cap : Nat} (r : Reader) (hr : r.pos ≤ cap) :
    Trace cap r.u16be 1 := by
  unfold Reader.u16be
  split
  · exact doneTrace _
  · exact truncated _ hr (oneFixed "u16" (by decide))

/-- Trace an unsigned 32-bit read and its truncation diagnostic. -/
def u32beTrace {cap : Nat} (r : Reader) (hr : r.pos ≤ cap) :
    Trace cap r.u32be 1 := by
  unfold Reader.u32be
  split
  · exact doneTrace _
  · exact truncated _ hr (oneFixed "u32" (by decide))

/-- Trace an unsigned 64-bit read and its truncation diagnostic. -/
def u64beTrace {cap : Nat} (r : Reader) (hr : r.pos ≤ cap) :
    Trace cap r.u64be 1 := by
  unfold Reader.u64be
  split
  · exact doneTrace _
  · exact truncated _ hr (oneFixed "u64" (by decide))

/-- Trace a byte-range read and the requested length on truncation. -/
def takeTrace {cap : Nat} (r : Reader) (hr : r.pos ≤ cap) (n : Nat) (hn : n ≤ cap) :
    Trace cap (r.take n) 1 := by
  unfold Reader.take
  split
  · exact doneTrace _
  · exact truncated _ hr (closeExpr (catExpr (litExpr _ "take ") (decExpr hn)) (by decide) (by decide))

private theorem reader_pos {cap : Nat} {r : Reader} (h : r.data.size ≤ cap) : r.pos ≤ cap :=
  Nat.le_trans r.pos_le_size h

private theorem remaining_le {cap : Nat} {r : Reader} (h : r.data.size ≤ cap) : r.remaining ≤ cap :=
  Nat.le_trans (Nat.sub_le ..) (Nat.le_trans r.stop_le h)

private theorem next_data {cap : Nat} {r t : Reader} (h : r.data.size ≤ cap)
    (e : t.data = r.data) : t.data.size ≤ cap := e ▸ h

/-! ## SOC, SIZ and SOT field readers -/

/-- All diagnostics of an Annex A length-bearing segment reader. The raw length and
the computed `length − 2` fit in 16 bits even when the requested body exceeds the input. -/
def segmentTrace {cap : Nat} (r : Reader) (hr : r.data.size ≤ cap) (wire : 65535 ≤ cap) :
    Trace cap (Marker.readSegment r) 3 := by
  unfold Marker.readSegment
  apply bindTrace (u16beTrace r (reader_pos hr))
  rintro ⟨len,t⟩ ht
  have hn : len.toNat ≤ cap := by have := len.toNat_lt; omega
  have mid := next_data hr (Reader.u16be_pos ht).2.2.1
  apply bindTrace (requireTrace r (reader_pos hr) _ _ (closeExpr
    (catExpr (catExpr (litExpr _ "segment length ") (decExpr hn)) (litExpr _ " < 2")) (by decide) (by decide)))
  intro _ _
  apply bindTrace (takeTrace t (reader_pos mid) _ (by omega))
  rintro ⟨_,_⟩ _
  exact doneTrace _

/-- The SOT header prefix charges all four byte readers, including `expectEnd` and
every interpolated `require` argument reached on success or rejection. The declared
32-bit length is priced before its validity test and the initial length uses
`remaining + 2` even on malformed segment bodies. -/
def sotTrace {cap : Nat} (r : Reader) (hr : r.data.size + 2 ≤ cap) (wire : 2^32 ≤ cap) :
    Trace cap (TilePart.parseSOT r) 10 := by
  have source : r.data.size ≤ cap := by omega
  have pos := reader_pos source
  have len : r.remaining + 2 ≤ cap := by have := remaining_le (Nat.le_refl r.data.size); omega
  unfold TilePart.parseSOT
  apply bindTrace (requireTrace r pos _ _ (closeExpr
    (catExpr (catExpr (litExpr _ "Lsot = ") (decExpr len)) (litExpr _ ", expected 10")) (by decide) (by decide)))
  intro _ _
  apply bindTrace (u16beTrace r pos)
  rintro ⟨isot,r1⟩ h1
  have b1 := next_data source (Reader.u16be_pos h1).2.2.1
  apply bindTrace (u32beTrace r1 (reader_pos b1))
  rintro ⟨psot,r2⟩ h2
  have b2 := next_data b1 (Reader.u32be_pos h2).2.2.1
  apply bindTrace (u8Trace r2 (reader_pos b2))
  rintro ⟨tpsot,r3⟩ h3
  have b3 := next_data b2 (Reader.u8_pos h3).2.2.1
  apply bindTrace (u8Trace r3 (reader_pos b3))
  rintro ⟨tnsot,r4⟩ h4
  have b4 := next_data b3 (Reader.u8_pos h4).2.2.1
  apply bindTrace (endTrace r4 b4 "SOT" (by decide))
  intro _ _
  apply bindTrace (requireTrace r pos _ _ (oneFixed _ (by decide)))
  intro _ _
  have hp : psot.toNat ≤ cap := by have := psot.toNat_lt; omega
  apply bindTrace (requireTrace r pos _ _ (closeExpr
    (catExpr (catExpr (litExpr _ "Psot = ") (decExpr hp)) (litExpr _ " (0 or ≥ 14)")) (by decide) (by decide)))
  intro _ _
  apply bindTrace (requireTrace r pos _ _ (oneFixed _ (by decide)))
  intro _ _
  have ha : tpsot.toNat ≤ cap := by have := tpsot.toNat_lt; omega
  have hb : tnsot.toNat ≤ cap := by have := tnsot.toNat_lt; omega
  apply bindTrace (requireTrace r pos _ _ (closeExpr
    (catExpr (catExpr (catExpr (litExpr _ "TPsot = ") (decExpr ha)) (litExpr _ " > TNsot = ")) (decExpr hb))
    (by decide) (by decide)))
  intro _ _
  exact doneTrace _

private def u8Bind {α : Type} {cap j : Nat} {r : Reader} (h : r.data.size ≤ cap)
    {f : UInt8 × Reader → Except Error α}
    (tail : ∀ x t, t.data.size ≤ cap → Trace cap (f (x,t)) j) :
    Trace cap (r.u8 >>= f) (j+1) :=
  bindTrace (u8Trace _ (reader_pos h)) fun (x,t) hr =>
    tail x t (next_data h (Reader.u8_pos hr).2.2.1)

private def u16beBind {α : Type} {cap j : Nat} {r : Reader} (h : r.data.size ≤ cap)
    {f : UInt16 × Reader → Except Error α}
    (tail : ∀ x t, t.data.size ≤ cap → Trace cap (f (x,t)) j) :
    Trace cap (r.u16be >>= f) (j+1) :=
  bindTrace (u16beTrace _ (reader_pos h)) fun (x,t) hr =>
    tail x t (next_data h (Reader.u16be_pos hr).2.2.1)

private def u32beBind {α : Type} {cap j : Nat} {r : Reader} (h : r.data.size ≤ cap)
    {f : UInt32 × Reader → Except Error α}
    (tail : ∀ x t, t.data.size ≤ cap → Trace cap (f (x,t)) j) :
    Trace cap (r.u32be >>= f) (j+1) :=
  bindTrace (u32beTrace _ (reader_pos h)) fun (x,t) hr =>
    tail x t (next_data h (Reader.u32be_pos hr).2.2.1)

/-- Trace an array of reads through the first rejection, preserving their common backing buffer. -/
def arrayTrace {α : Type} {cap k : Nat} {f : Reader → Except Error (α × Reader)}
    (one : ∀ r : Reader, r.data.size ≤ cap → Trace cap (f r) k)
    (same : ∀ r t a, f r = .ok (a,t) → t.data = r.data)
    (a : Array α) (n : Nat) (r : Reader) (hr : r.data.size ≤ cap) :
    Trace cap (Marker.readArray f a n r) (n*k) := by
  induction n generalizing a r with
  | zero => exact doneTrace _
  | succ n ih =>
    rw [show Marker.readArray f a (n+1) r = (f r >>= fun (x,t) =>
        Marker.readArray f (a.push x) n t) by
      rw [Marker.readArray]; cases f r with
      | error => rfl
      | ok p => cases p; rfl, Nat.succ_mul]
    exact bindTrace (one r hr) fun (x,t) hx => ih _ t (next_data hr (same r t x hx))

private theorem array_data {α : Type} {f : Reader → Except Error (α × Reader)}
    (same : ∀ r t a, f r = .ok (a,t) → t.data = r.data)
    {n : Nat} {a z : Array α} {r t : Reader} (ok : Marker.readArray f a n r = .ok (z,t)) :
    t.data = r.data := by
  induction n generalizing a r with
  | zero => cases ok; rfl
  | succ n ih =>
    rw [Marker.readArray] at ok
    split at ok
    · contradiction
    · rename_i x s hs
      exact (ih ok).trans (same r s x hs)

private theorem siz_component_data (r t : Reader) (a : Marker.Component)
    (ok : Marker.readSizComponent r = .ok (a,t)) : t.data = r.data := by
  unfold Marker.readSizComponent at ok
  obtain ⟨⟨_,r1⟩,h1,ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨_,_,ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨⟨_,r2⟩,h2,ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨_,_,ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨⟨_,r3⟩,h3,ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨_,_,ok⟩ := Tier2Equiv.bind_ok ok
  cases ok
  exact (Reader.u8_pos h3).2.2.1.trans ((Reader.u8_pos h2).2.2.1.trans (Reader.u8_pos h1).2.2.1)

private def sizComponent {cap : Nat} (wire : 65535 ≤ cap) (r : Reader) (hr : r.data.size ≤ cap) :
    Trace cap (Marker.readSizComponent r) 6 := by
  unfold Marker.readSizComponent
  apply u8Bind hr
  intro s r1 b1
  have hd : (s &&& 0x7F).toNat + 1 ≤ cap := by have := (s &&& 0x7F).toNat_lt; omega
  apply bindTrace (requireTrace r (reader_pos hr) _ _ (closeExpr
    (catExpr (catExpr (litExpr _ "Ssiz bit depth ") (decExpr hd)) (litExpr _ " > 38")) (by decide) (by decide)))
  intro _ _
  apply u8Bind b1
  intro _ r2 b2
  apply bindTrace (requireTrace r1 (reader_pos b1) _ _ (oneFixed _ (by decide)))
  intro _ _
  apply u8Bind b2
  intro _ _ _
  apply bindTrace (requireTrace r2 (reader_pos b2) _ _ (oneFixed _ (by decide)))
  intro _ _
  exact doneTrace _

/-- Entire SIZ parser, including payloads constructed for successful checks before
an eventual component error. The ten fixed-field reads precede component admission.
The actual 16-bit `Csiz` bounds the first message even if the limits reject it. -/
def sizTrace {cap : Nat} (L : Limits) (r : Reader) (hr : r.data.size ≤ cap) (wire : 65535 ≤ cap) :
    Trace cap (Marker.parseSIZ L r) (L.maxComponents * 6 + 17) := by
  unfold Marker.parseSIZ
  apply u16beBind hr
  intro _ _ h
  iterate 8 (apply u32beBind h; intro _ _ h)
  rename_i r0
  apply u16beBind h
  intro csiz r1 h1
  have n : csiz.toNat ≤ cap := by have := csiz.toNat_lt; omega
  have p := reader_pos h
  apply bindTrace (requireTrace r0 p _ _ (closeExpr
    (catExpr (catExpr (litExpr _ "Csiz = ") (decExpr n)) (litExpr _ " not in 1…16384")) (by decide) (by decide)))
  intro _ _
  apply bindTrace (checkedTrace _ _ _ _ p n)
  intro _ hc
  have count : csiz.toNat ≤ L.maxComponents := (Limits.check_eq_ok_iff ..).1 hc
  apply bindTrace (requireTrace r0 p _ _ (closeExpr
    (catExpr (catExpr (litExpr _ "Lsiz ≠ 38 + 3·Csiz (Csiz = ") (decExpr n)) (litExpr _ ")"))
    (by decide) (by decide)))
  intro _ _
  iterate 4 (apply bindTrace (requireTrace r0 p _ _ (oneFixed _ (by decide))); intro _ _)
  let reads := arrayTrace (sizComponent wire) siz_component_data (Array.mkEmpty csiz.toNat) csiz.toNat r1 h1
  apply widen (bindTrace (j := 1) reads ?_) (by have := Nat.mul_le_mul_right 6 count; omega)
  rintro ⟨_,t⟩ ht
  apply bindTrace (endTrace t (next_data h1 (array_data siz_component_data ht)) "SIZ" (by decide))
  intro _ _
  exact doneTrace _

/-- The length-bearing SIZ prefix inside `Marker.parseMainHeader`, starting at SOC. -/
def mainStart (L : Limits) (r : Reader) : Except Error Marker.SIZ := do
  let (soc,r1) ← r.u16be
  Marker.require r (soc == Marker.Code.SOC) "codestream does not start with SOC"
  let (m,r2) ← r1.u16be
  Marker.require r1 (m == Marker.Code.SIZ) "SIZ does not follow SOC"
  let (body,_,_) ← Marker.readSegment r2
  Marker.parseSIZ L body

private def startTrace {cap : Nat} (L : Limits) (r : Reader) (hr : r.data.size ≤ cap) (wire : 65535 ≤ cap) :
    Trace cap (mainStart L r) (L.maxComponents*6+24) := by
  unfold mainStart
  apply u16beBind hr
  intro _ r1 h1
  apply bindTrace (requireTrace r (reader_pos hr) _ _ (oneFixed _ (by decide)))
  intro _ _
  apply u16beBind h1
  intro _ r2 h2
  apply bindTrace (requireTrace r1 (reader_pos h1) _ _ (oneFixed _ (by decide)))
  intro _ _
  apply bindTrace (segmentTrace r2 h2 wire)
  rintro ⟨b,_,_⟩ hb
  exact sizTrace L b (next_data h2 (HeaderWork.readSegment_extent hb).1) wire

private theorem start_failure {L : Limits} {r : Reader} {e : Error} (bad : mainStart L r = .error e) :
    Marker.parseMainHeader L r = .error e := by
  unfold mainStart at bad
  unfold Marker.parseMainHeader
  cases h0 : r.u16be with
  | error => simpa [h0, bind, Except.bind] using bad
  | ok p =>
    obtain ⟨soc,r1⟩ := p
    cases ha : Marker.require r (soc == Marker.Code.SOC) "codestream does not start with SOC" with
    | error => simpa [h0, ha, bind, Except.bind] using bad
    | ok =>
      cases h1 : r1.u16be with
      | error => simpa [h0, ha, h1, bind, Except.bind] using bad
      | ok p =>
        obtain ⟨m,r2⟩ := p
        cases hb : Marker.require r1 (m == Marker.Code.SIZ) "SIZ does not follow SOC" with
        | error => simpa [h0,ha,h1,hb,bind,Except.bind] using bad
        | ok =>
          cases h2 : Marker.readSegment r2 with
          | error => simpa [h0,ha,h1,hb,h2,bind,Except.bind] using bad
          | ok p =>
            obtain ⟨b,n,r3⟩ := p
            simp only [h0,ha,h1,hb,h2,bind,Except.bind] at bad ⊢
            rw [bad]

private theorem range_data {data : ByteArray} {rg : TilePart.ByteRange} {r : Reader}
    (ok : TilePart.rangeReader data rg = .ok r) : r.data = data := by
  unfold TilePart.rangeReader at ok
  obtain ⟨t, skip, ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨⟨s,v⟩, take, ok⟩ := Tier2Equiv.bind_ok ok
  cases ok
  exact (Reader.take_spec take).2.2.1.trans (Reader.skip_pos skip).2.2.1

/-- Reader reached by the public reduction, container and range checks before SOC.
Includes both raw codestreams and JP2. -/
def mainReader (L : Limits) (d : ByteArray) (red : Nat) : Except Error Reader := do
  L.check JPEG2000.Decode.loc .decompLevels red
  let c ← Box.parseFile L d
  TilePart.rangeReader d ⟨c.codestream.start,c.codestream.len⟩

private theorem main_reader_run {L : Limits} {d : ByteArray} {red : Nat} {r : Reader}
    (hr : mainReader L d red = .ok r) :
    r.data = d ∧ ∀ e, Marker.parseMainHeader L r = .error e → decodeCodestream L d red = .error e := by
  unfold mainReader at hr
  obtain ⟨_,hc,hr⟩ := Tier2Equiv.bind_ok hr
  obtain ⟨c,hb,hr⟩ := Tier2Equiv.bind_ok hr
  refine ⟨range_data hr, fun e err => ?_⟩
  simp only [decodeCodestream, hc, Header.parse, hb, Header.parseCodestreamIn, hr, err, bind, Except.bind]

/-- Count all diagnostic work attributable to the SOC/SIZ prefix on arbitrary public
input, including successful checks before later parser, packet or image errors. -/
def publicStartWork (L : Limits) (d : ByteArray) (red : Nat) : Nat :=
  match h : mainReader L d red with
  | .error _ => 0
  | .ok r =>
    let source := (main_reader_run h).1
    let t := startTrace (cap := max 65535 d.size) L r
      (source ▸ Nat.le_max_right ..) (Nat.le_max_left ..)
    (t.messages.map (fun m => m.2.tree.work)).sum

/-- Uniform work and retained-data bounds from the actual public SIZ prefix. If it
rejects, both entry points return its exact error and the location lies in the bound. -/
theorem public_siz (L : Limits) (d : ByteArray) (opts : DecodeOptions) :
    let cap := max 65535 d.size
    publicStartWork L d opts.reduce ≤ (L.maxComponents*6+24)*Text.workBound cap 128 24 ∧
    ∀ r, mainReader L d opts.reduce = .ok r → ∀ e, mainStart L r = .error e →
      decodeCodestream L d opts.reduce = .error e ∧ JPEG2000.decode L d opts = .error e ∧
      e.offset?.getD 0 ≤ cap ∧ retainedBytes e ≤ Text.byteBound cap 128 24 := by
  unfold publicStartWork
  split
  · rename_i h
    exact ⟨Nat.zero_le _,by intro r hr; rw [h] at hr; contradiction⟩
  · rename_i r hr
    obtain ⟨src,fail⟩ := main_reader_run hr
    let t := startTrace (cap := max 65535 d.size) L r (src ▸ Nat.le_max_right ..) (Nat.le_max_left ..)
    refine ⟨(trace_cost t).1, ?_⟩
    intro r' hr' e bad
    rw [hr] at hr'
    cases hr'
    have raw := fail e (start_failure bad)
    exact ⟨raw,by simp only [JPEG2000.decode,raw,bind,Except.bind],(t.origin e bad).1,(trace_cost t).2 e bad⟩

open JPEG2000.Color JPEG2000.Box

private theorem forIn_failure {α β : Type} (xs : List α) (a : β)
    (f : α → β → Except Error (ForInStep β)) {e : Error} (bad : forIn xs a f = .error e) :
    ∃ x ∈ xs, ∃ z, f x z = .error e := by
  induction xs generalizing a with
  | nil => cases bad
  | cons x xs ih =>
    rw [List.forIn_cons] at bad
    cases hx : f x a with
    | error err => rw [hx] at bad; cases bad; exact ⟨x,by simp,a,hx⟩
    | ok v =>
      rw [hx] at bad
      cases v with
      | done => cases bad
      | yield b =>
        obtain ⟨y,hy,z,hz⟩ := ih b bad
        exact ⟨y,by simp [hy],z,hz⟩

private theorem map_failure {α β : Type} (f : α → Except Error β) (xs : Array α)
    {e : Error} (bad : xs.mapM f = .error e) : ∃ x ∈ xs, f x = .error e := by
  have part (l : List α) (h : l.mapM f = .error e) : ∃ x ∈ l, f x = .error e := by
    induction l with
    | nil => cases h
    | cons x l ih =>
      rw [List.mapM_cons] at h
      cases hx : f x with
      | error err => rw [hx] at h; cases h; exact ⟨x,by simp,hx⟩
      | ok v =>
        cases hl : l.mapM f with
        | error err =>
          rw [hx] at h
          simp only [bind,Except.bind,hl] at h
          cases h
          obtain ⟨y,hy,hf⟩ := ih hl
          exact ⟨y,by simp [hy],hf⟩
        | ok a => simp [hx,hl,bind,Except.bind,pure,Except.pure] at h
  rw [Array.mapM_eq_mapM_toList] at bad
  cases hl : xs.toList.mapM f with
  | error err => rw [hl] at bad; cases bad; simpa using part xs.toList hl
  | ok a => rw [hl] at bad; cases bad

/-! ## JP2 header reads and discarded diagnostics -/

/-- Retain the construction events of an earlier operation whose result was discarded. -/
def includeTrace {α β : Type} {cap i j : Nat} {x : Except Error α} {y : Except Error β}
    (earlier : Trace cap x i) (later : Trace cap y j) : Trace cap y (i+j) := by
  refine ⟨earlier.messages ++ later.messages, ?_, ?_⟩
  · rw [List.length_append]; exact Nat.add_le_add earlier.countBound later.countBound
  · intro e he
    obtain ⟨offset,why⟩ := later.origin e he
    refine ⟨offset,?_⟩
    cases e with
    | limitExceeded => exact why
    | _ => obtain ⟨m,hm,h⟩ := why; exact ⟨m,List.mem_append_right _ hm,h⟩

private def boxBodyMessage {cap n : Nat} (t : UInt32) (r : Reader)
    (hl : n ≤ cap) (hr : r.remaining ≤ cap) :
    Built cap s!"box '{Box.typeName t}' body of {n} bytes, {r.remaining} left" :=
  closeExpr (catExpr (catExpr (catExpr (catExpr (catExpr (catExpr (litExpr _ "box '")
    ⟨_,rfl,.boxName t⟩) (litExpr _ "' body of ")) (decExpr hl)) (litExpr _ " bytes, "))
    (decExpr hr)) (litExpr _ " left")) (by decide) (by decide)

/-- All JP2 box-header branches. A rejecting body split first constructs the
`take n` truncation and then the replacement enclosing the four-byte box type,
the same declared size, and the number of actual bytes left. XLBox is bounded by
its 64-bit wire type before admission. -/
def boxTrace {cap : Nat} (r : Reader) (hr : r.data.size ≤ cap) (wire : 2^64 ≤ cap) :
    Trace cap (Box.readBox r) 5 := by
  unfold Box.readBox
  apply u32beBind hr
  intro len r1 h1
  apply u32beBind h1
  intro ty r2 h2
  have finish (a : Reader) (n : Nat) (ha : a.data.size ≤ cap) (hn : n ≤ cap) :
      Trace cap (match a.take n with
        | .ok (sub,t) => Except.ok ((⟨ty,r.pos,sub⟩ : BoxHdr),t)
        | .error _ => Except.error (.truncated (.atOffset .box r.pos)
            s!"box '{Box.typeName ty}' body of {n} bytes, {a.remaining} left")) 2 := by
    cases hx : a.take n with
    | ok pair => cases pair; exact doneTrace _
    | error err =>
      exact includeTrace (takeTrace a (reader_pos ha) n hn) (truncated (.atOffset .box r.pos) (reader_pos hr)
        (boxBodyMessage ty a hn (remaining_le ha)))
  dsimp only
  split
  · exact widen (finish r2 r2.remaining h2 (remaining_le h2)) (by decide)
  · split
    · apply bindTrace (u64beTrace r2 (reader_pos h2))
      rintro ⟨xl,r3⟩ h3
      have b3 := next_data h2 (Reader.u64be_pos h3).2.2.1
      have hx : xl.toNat ≤ cap := by have := xl.toNat_lt; omega
      dsimp only
      split
      · exact widen (malformed _ (reader_pos hr) (closeExpr (catExpr (catExpr (litExpr _ "XLBox ")
          (decExpr hx)) (litExpr _ " < 16")) (by decide) (by decide))) (by decide)
      · exact finish r3 (xl.toNat-16) b3 (by omega)
    · split
      · have hn : len.toNat ≤ cap := by have := len.toNat_lt; omega
        exact widen (malformed _ (reader_pos hr) (closeExpr (catExpr (catExpr (litExpr _ "LBox ")
          (decExpr hn)) (litExpr _ " in 2..7")) (by decide) (by decide))) (by decide)
      · exact widen (finish r2 (len.toNat-8) h2 (by have := len.toNat_lt; omega)) (by decide)

/-- The first JP2 box can fail after constructing a body-length message which the
container replaces with its fixed signature error. Both are charged and the public
APIs return exactly the replacement. -/
theorem public_signature {L : Limits} {d : ByteArray} {opts : DecodeOptions} {discarded : Error}
    (red : opts.reduce ≤ L.maxDecompLevels) (input : d.size ≤ L.maxInputBytes)
    (wrapped : Box.isRawCodestream d = false)
    (first : Box.readBox (Reader.ofByteArray d .box) = .error discarded) :
    let cap := max (2^64) d.size
    let msg := "neither a JP2 signature box nor a raw codestream (FF4F FF51)"
    let e := Box.malformedAt 0 msg
    ∃ t : Trace cap (Except.error e : Except Error Box.Container) 6,
      decodeCodestream L d opts.reduce = .error e ∧ JPEG2000.decode L d opts = .error e ∧
      (t.messages.map (fun m => m.2.tree.work)).sum ≤ 6 * Text.workBound cap 128 24 ∧
      retainedBytes discarded ≤ Text.byteBound cap 128 24 := by
  let cap := max (2^64) d.size
  let discardedTrace := boxTrace (cap := cap) (Reader.ofByteArray d .box)
    (Nat.le_max_right ..) (Nat.le_max_left ..)
  let msg := "neither a JP2 signature box nor a raw codestream (FF4F FF51)"
  let e := Box.malformedAt 0 msg
  let t := includeTrace discardedTrace (malformed (α := Box.Container) (.atOffset .box 0)
    (cap := cap) (Nat.zero_le _) (oneFixed msg (by decide)))
  have cr := (Limits.check_eq_ok_iff L JPEG2000.Decode.loc .decompLevels opts.reduce).2 red
  have ci := (Limits.check_eq_ok_iff L (.atOffset .box 0) .inputBytes d.size).2 input
  have aux : Box.parseFileAux L d = .error e := by
    simp only [Box.parseFileAux,ci,wrapped,Bool.false_eq_true,↓reduceIte,bind,Except.bind,first]
    rfl
  have raw : decodeCodestream L d opts.reduce = .error e := by
    simp only [decodeCodestream,cr,Header.parse,Box.parseFile,aux,bind,Except.bind]
  exact ⟨t,raw,by simp only [JPEG2000.decode,raw,bind,Except.bind]; rfl,(trace_cost t).1,
    (trace_cost discardedTrace).2 discarded first⟩

/-! ## PPM preflight and SOP on the physical packet walk -/

private def ppmText (cap a b : Nat) (ha : a ≤ cap) (hb : b ≤ cap) :
    Built cap s!"PPM: {a} Nppm/Ippm chunks for {b} tile-parts" :=
  ⟨_,rfl,_,_,.cat (.cat (.cat (.cat (.fixed "PPM: ") (.dec ha))
      (.fixed " Nppm/Ippm chunks for ")) (.dec hb)) (.fixed " tile-parts"),by decide,by decide⟩

/-- The PPM preflight mismatch is priced at the actual public call: the first number
comes from parsing the input, and the second from the admitted aggregate tile-part
count. Both APIs propagate the priced message byte-for-byte. -/
theorem public_ppm_mismatch {L : Limits} {d : ByteArray} {opts : DecodeOptions}
    {h : Header.Header} {initial : Array JPEG2000.NativeOutput.OutputComponent}
    (red : opts.reduce ≤ L.maxDecompLevels) (parse : Header.parse L d = .ok h)
    (alloc : JPEG2000.NativeOutput.allocOutput L h.siz opts.reduce = .ok initial)
    (present : h.ppm.segments.isEmpty = false)
    (partLimit : Tier2.Headers.numTileParts h ≤ L.maxTileParts)
    (mismatch : h.ppm.chunks.size ≠ Tier2.Headers.numTileParts h) :
    ∃ t : Text, let msg := s!"PPM: {h.ppm.chunks.size} Nppm/Ippm chunks for {Tier2.Headers.numTileParts h} tile-parts"
      let e := Error.malformed Tier2.Headers.loc msg
      t.render = msg ∧ decodeCodestream L d opts.reduce = .error e ∧
      JPEG2000.decode L d opts = .error e ∧ retainedBytes e ≤ Text.byteBound L.maxTileParts 128 24 ∧
      t.work ≤ Text.workBound L.maxTileParts 128 24 := by
  let b := ppmText _ _ _ (HeaderWork.parse_ppm parse).1 partLimit
  have ck := (Limits.check_eq_ok_iff L JPEG2000.Decode.loc .decompLevels opts.reduce).2 red
  have cp := (Limits.check_eq_ok_iff L Tier2.Headers.loc .tileParts (Tier2.Headers.numTileParts h)).2 partLimit
  refine ⟨b.tree,b.erase,?_,?_,(built_cost b).1,(built_cost b).2⟩
  all_goals simp [JPEG2000.decode, decodeCodestream, JPEG2000.Decode.nativeFromHeader, parse, alloc,
    JPEG2000.Decode.withTiles, Tier2.Headers.ppmChunkIndex, ck, cp, present, mismatch, bind, Except.bind] <;> rfl

/-- SOP consumes bounded wire numbers and formats only the low 16 bits of the packet
sequence. A failed peek is swallowed and the optional marker is absent. -/
def sopTrace {cap : Nat} (seq : Nat) (r : Reader) (hr : r.data.size ≤ cap) (wire : 65535 ≤ cap) :
    Trace cap (Tier2.Packet.readSop seq r) 5 := by
  unfold Tier2.Packet.readSop
  cases peek : r.u16be with
  | error e =>
    let seen := u16beTrace r (reader_pos hr)
    exact ⟨seen.messages,Nat.le_trans seen.countBound (by decide),by intros; contradiction⟩
  | ok p =>
    obtain ⟨m,r1⟩ := p
    dsimp only
    split
    · have hr1 := next_data hr (Reader.u16be_pos peek).2.2.1
      apply u16beBind hr1
      intro len r2 hr2
      have lenBound : len.toNat ≤ cap := by have := len.toNat_lt; omega
      split
      · exact widen (malformed _ (reader_pos hr) (closeExpr
          (catExpr (catExpr (litExpr _ "SOP: Lsop = ") (decExpr lenBound)) (litExpr _ ", expected 4"))
          (by decide) (by decide))) (by decide)
      · apply u16beBind hr2
        intro n _ _
        have seqBound : seq % 65536 ≤ cap := by omega
        have nBound : n.toNat ≤ cap := by have := n.toNat_lt; omega
        split
        · exact widen (malformed _ (reader_pos hr) (closeExpr
            (catExpr (catExpr (catExpr (litExpr _ "SOP: Nsop = ") (decExpr nBound))
            (litExpr _ ", expected ")) (decExpr seqBound)) (by decide) (by decide))) (by decide)
        · exact doneTrace _
    · exact doneTrace _

open PacketTraversal JPEG2000.Tier2.Packet JPEG2000.Tier2.Headers JPEG2000.Progression

/-- SOP subcall reached by a physical packet callback. The precinct lookup precedes
the optional read, and the reader and sequence come from the incoming packet state. -/
def sopAt (c : Header.Coding) (base : Array (Array Nat)) (s : LoopState) (p : PacketId) :
    Except Error Unit :=
  match s.precs[((base.getD p.comp #[]).getD p.res 0) + p.prec]? with
  | none => pure ()
  | some _ => if c.sop then readSop s.seq s.body >>= fun _ => pure () else pure ()

private def sopAtTrace {cap : Nat} (c : Header.Coding) (base : Array (Array Nat)) (s : LoopState)
    (p : PacketId) (hr : s.body.data.size ≤ cap) (wire : 65535 ≤ cap) : Trace cap (sopAt c base s p) 5 := by
  unfold sopAt
  split
  · exact doneTrace _
  · split
    · exact bindTrace (sopTrace _ _ hr wire) (j := 0) (fun _ _ => doneTrace _)
    · exact doneTrace _

private theorem sopAt_failure {L : Limits} {c : Header.Coding} {base : Array (Array Nat)}
    {s : LoopState} {p : PacketId} {e : Error} {pb : Nat} {same : Bool}
    (bad : sopAt c base s p = .error e) : packetStep L c base same pb s p = .error e := by
  unfold sopAt at bad
  unfold packetStep
  split at bad
  · cases bad
  · rename_i st get
    split at bad
    · rename_i useSop
      cases hs : readSop s.seq s.body with
      | error err =>
        rw [hs] at bad
        cases bad
        simp only [get,decodePacket,useSop,↓reduceIte,hs,bind,Except.bind]
      | ok v => rw [hs] at bad; cases bad
    · cases bad

/-- The actual state reached before an attempted packet has a bounded SOP diagnostic.
Layout, tile input gathering and the fold over the physical prefix identify that state.
An SOP error is the exact callback error. -/
theorem public_sop {L : Limits} {d : ByteArray} {red : Nat} {v : TileVisit} {p : Position}
    {a : PacketAction} (tile : v ∈ (PublicPacketWork.measure L d red).1)
    (member : (p,a) ∈ v.packets) (called : a.attempted = true) :
    let cap := max 65535 (L.maxTilePartsPerTile * d.size)
    ∃ h tp hs g c precs base spans buf parts pre tail s,
      Header.parse L d = .ok h ∧ presentAt h v.tile v.cursor = some tp ∧
      Layout.ofHeader h tp.index = .ok (g,c) ∧ initPrecincts L g = .ok (precs,base,spans) ∧
      tileData d tp.tile = .ok (buf,parts) ∧
      schedule g [] (volumes g c.progression c.poc) = pre ++ p :: tail ∧
      let f := packetStep L c base (hs.map HeaderStream.bytes).isNone v.passesBefore
      pre.foldlM (dispatch f) (firstState precs buf hs) = .ok s ∧
      ∃ t : Trace cap (sopAt c base s p.packet) 5,
        (t.messages.map (fun m => m.2.tree.work)).sum ≤ 5 * Text.workBound cap 128 24 ∧
        ∀ e, sopAt c base s p.packet = .error e → f s p.packet = .error e ∧
          retainedBytes e ≤ Text.byteBound cap 128 24 := by
  obtain ⟨h,tp,hs,parsed,selected,np,_,seen⟩ :=
    (PacketLocalWork.decode_attempts L d red).2.2 v tile p a member called
  obtain ⟨g,c,precs,base,spans,buf,parts,pre,tail,s,layout,init,input,nb,sched,reach,_,_,_,body,_⟩ := seen
  have rb : s.body.data.size ≤ max 65535 (L.maxTilePartsPerTile * d.size) := by
    rw [body]; exact Nat.le_trans nb (Nat.le_trans (Nat.mul_le_mul_right _ np) (Nat.le_max_right ..))
  let t := sopAtTrace c base s p.packet rb (Nat.le_max_left ..)
  exact ⟨h,tp,hs,g,c,precs,base,spans,buf,parts,pre,tail,s,parsed,selected,layout,init,input,sched,
    reach,t,(trace_cost t).1,fun e bad => ⟨sopAt_failure bad,(trace_cost t).2 e bad⟩⟩

/-! ## Tile-part traversal -/

open JPEG2000.Marker JPEG2000.TilePart

/-- The byte reads and field checks preceding the first tile-part index admission. -/
def sotStart (r : Reader) : Except Error SOT := do
  let (_,r1) ← r.u16be
  let (body,_,_) ← readSegment r1
  parseSOT body

private def sotStartTrace {cap : Nat} (r : Reader) (hr : r.data.size + 2 ≤ cap) (wire : 2^32 ≤ cap) :
    Trace cap (sotStart r) 14 := by
  unfold sotStart
  apply bindTrace (u16beTrace r (Nat.le_trans r.pos_le_size (by omega)))
  rintro ⟨_,r1⟩ h1
  have d1 := (Reader.u16be_pos h1).2.2.1
  apply bindTrace (segmentTrace r1 (d1 ▸ (by omega)) (by omega))
  rintro ⟨body,_,_⟩ h2
  exact sotTrace _ ((HeaderWork.readSegment_extent h2).1 ▸ d1 ▸ hr) wire

private theorem sotStart_bad {c : Ctx} {st : State} {r : Reader} {e : Error}
    (bad : sotStart r = .error e) : readTilePart c st r = .error e := by
  unfold sotStart at bad
  unfold readTilePart
  cases h1 : r.u16be with
  | error => simpa [h1,bind,Except.bind] using bad
  | ok p =>
    obtain ⟨_,r1⟩ := p
    cases h2 : readSegment r1 with
    | error => simpa [h1,h2,bind,Except.bind] using bad
    | ok p =>
      obtain ⟨body,_,_⟩ := p
      simp only [h1,h2,bind,Except.bind] at bad ⊢
      rw [bad]

/-- Readers at actual SOT callbacks of the public tile-part loop. The first failing
tile-part is included. EOC, non-SOT markers and exhaustion cause no SOT callback. -/
def sotReaders (c : Ctx) : Nat → State → Reader → List Reader
  | 0, _, _ => []
  | f+1, st, r =>
    match r.u16be with
    | .error _ => []
    | .ok (m,_) =>
      if m == Code.EOC || m != Code.SOT then []
      else r :: match readTilePart c st r with
        | .error _ => []
        | .ok (st',r') => sotReaders c f st' r'

private theorem sotReaders_spec (c : Ctx) (f : Nat) (st : State) (r : Reader) :
    (sotReaders c f st r).length ≤ f ∧ ∀ t ∈ sotReaders c f st r, t.data = r.data ∧
      ∀ e, sotStart t = .error e → tilePartLoop c f st r = .error e := by
  induction f generalizing st r with
  | zero => exact ⟨Nat.le_refl _,by intro t h; cases h⟩
  | succ f ih =>
    simp only [sotReaders,tilePartLoop]
    cases hm : r.u16be with
    | error => simp
    | ok p =>
      obtain ⟨m,mr⟩ := p
      by_cases end_ : (m == Code.EOC) = true
      · simp [end_]
      by_cases other : (m != Code.SOT) = true
      · simp [end_,other]
      simp only [Bool.not_eq_true] at end_ other
      simp only [end_,other,Bool.false_or,Bool.false_eq_true,↓reduceIte]
      cases part : readTilePart c st r with
      | error err =>
        simp only [List.length_cons,List.length_nil,Nat.zero_add,List.mem_singleton]
        refine ⟨by omega,?_⟩
        rintro t rfl
        refine ⟨rfl,fun e bad => ?_⟩
        have hf := sotStart_bad (c := c) (st := st) bad
        rw [part] at hf
        cases hf
        rfl
      | ok p =>
        obtain ⟨st',r'⟩ := p
        obtain ⟨length,later⟩ := ih st' r'
        simp only [List.length_cons,List.mem_cons]
        refine ⟨by omega,?_⟩
        intro t mem
        rcases mem with rfl | mem
        · refine ⟨rfl,fun e bad => ?_⟩
          have hf := sotStart_bad (c := c) (st := st) bad
          rw [part] at hf
          contradiction
        · obtain ⟨ds,hf⟩ := later t mem
          exact ⟨ds.trans (HeaderWork.readTilePart_step part).2.2.2.1,hf⟩

private theorem main_data {L : Limits} {r t : Reader} {mh : MainHeader}
    (ok : parseMainHeader L r = .ok (mh,t)) : t.data = r.data := by
  unfold parseMainHeader at ok
  obtain ⟨⟨_,r1⟩,h1,ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨_,_,ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨⟨_,r2⟩,h2,ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨_,_,ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨⟨_,_,r3⟩,hs,ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨_,_,ok⟩ := Tier2Equiv.bind_ok ok
  obtain ⟨⟨a,last⟩,loop,ok⟩ := Tier2Equiv.bind_ok ok
  cases hc : a.cod <;> simp only [hc] at ok
  · cases ok
  cases hq : a.qcd <;> simp only [hq] at ok
  · cases ok
  cases ok
  exact (HeaderWork.segmentLoop_storage loop).2.1.trans ((HeaderWork.readSegment_extent hs).2.1.trans
    ((Reader.u16be_pos h2).2.2.1.trans (Reader.u16be_pos h1).2.2.1))

private def tileCtx (L : Limits) (mh : MainHeader) : Ctx :=
  ⟨L,mh.siz.csiz,numTiles mh.siz,mh.pointers.any (·.code == Code.PPM)⟩

private def initialParts (mh : MainHeader) : State :=
  { parts := Array.replicate (numTiles mh.siz) #[], total := 0,
    pocEntries := mh.poc.foldl (fun a p => a+p.entries.size) 0 }

/-- The initial tile-part context and reader reached after the public main-header,
geometry, coding defaults and pointer checks. -/
def tileStart (L : Limits) (d : ByteArray) (red : Nat) : Except Error (Ctx × State × Reader) := do
  let r ← mainReader L d red
  let (mh,t) ← parseMainHeader L r
  Header.checkGeometry L mh
  let _ ← Header.mainCoding mh
  let _ ← parsePointers L mh d
  L.check (.atOffset t.stage t.pos) .tiles (numTiles mh.siz)
  return (tileCtx L mh,initialParts mh,t)

private theorem tile_run {L : Limits} {d : ByteArray} {red : Nat} {c : Ctx} {st : State} {r : Reader}
    (start : tileStart L d red = .ok (c,st,r)) :
    r.data = d ∧ ∀ e, tilePartLoop c r.remaining st r = .error e → decodeCodestream L d red = .error e := by
  unfold tileStart at start
  obtain ⟨t,reader,start⟩ := Tier2Equiv.bind_ok start
  obtain ⟨⟨mh,r'⟩,main,start⟩ := Tier2Equiv.bind_ok start
  obtain ⟨_,geom,start⟩ := Tier2Equiv.bind_ok start
  obtain ⟨_,coding,start⟩ := Tier2Equiv.bind_ok start
  obtain ⟨⟨_,_⟩,ptr,start⟩ := Tier2Equiv.bind_ok start
  obtain ⟨_,check,ret⟩ := Tier2Equiv.bind_ok start
  cases ret
  refine ⟨(main_data main).trans (main_reader_run reader).1,?_⟩
  intro e bad
  unfold mainReader at reader
  obtain ⟨_,redOK,reader⟩ := Tier2Equiv.bind_ok reader
  obtain ⟨_,box,range⟩ := Tier2Equiv.bind_ok reader
  unfold tileCtx initialParts at bad
  simp only [decodeCodestream,redOK,Header.parse,box,Header.parseCodestreamIn,range,main,geom,coding,
    ptr,parseTileParts,check,bad,bind,Except.bind]

/-- All SOT rejecting prefixes on the public path. There are at most input-length
many callbacks. Each formats at most fourteen messages, including those used in prior
successful checks. A failure in any SOT prefix reaches both byte-input APIs. -/
theorem public_sot {L : Limits} {d : ByteArray} {opts : DecodeOptions} {c : Ctx} {st : State} {r : Reader}
    (start : tileStart L d opts.reduce = .ok (c,st,r)) :
    let rs := sotReaders c r.remaining st r
    let cap := max (2^32) (d.size+2)
    rs.length ≤ d.size ∧ ∀ t ∈ rs, ∃ tr : Trace cap (sotStart t) 14,
      (tr.messages.map (fun m => m.2.tree.work)).sum ≤ 14*Text.workBound cap 128 24 ∧
      ∀ e, sotStart t = .error e → decodeCodestream L d opts.reduce = .error e ∧
        JPEG2000.decode L d opts = .error e ∧ retainedBytes e ≤ Text.byteBound cap 128 24 := by
  obtain ⟨data,fail⟩ := tile_run start
  obtain ⟨count,each⟩ := sotReaders_spec c r.remaining st r
  refine ⟨Nat.le_trans count (remaining_le (data ▸ Nat.le_refl _)),?_⟩
  intro t mem
  obtain ⟨dt,failed⟩ := each t mem
  let tr := sotStartTrace (cap := max (2^32) (d.size+2)) t (dt.trans data ▸ Nat.le_max_right ..)
    (Nat.le_max_left ..)
  refine ⟨tr,(trace_cost tr).1,?_⟩
  intro e bad
  have raw := fail e (failed e bad)
  exact ⟨raw,by simp only [JPEG2000.decode,raw,bind,Except.bind],(trace_cost tr).2 e bad⟩

/-- A framing error reached by following successful tile-part reads up to the
first marker which is neither SOT nor EOC. -/
def badTileMarker (c : Ctx) : Nat → State → Reader → Option (Reader × UInt16)
  | 0, _, _ => none
  | f+1, st, r => do
    let (m,_) ← r.u16be.toOption
    if m == Code.EOC then none
    else if m != Code.SOT then some (r,m)
    else
      let (st',r') ← (readTilePart c st r).toOption
      badTileMarker c f st' r'

private theorem badTileMarker_run (c : Ctx) (f : Nat) (st : State) (r : Reader)
    {t : Reader} {m : UInt16} (seen : badTileMarker c f st r = some (t,m)) :
    t.data = r.data ∧ tilePartLoop c f st r =
      .error (malformedAt t s!"expected SOT or EOC, found {hex m.toNat}") := by
  induction f generalizing st r with
  | zero => cases seen
  | succ f ih =>
    simp only [badTileMarker] at seen
    simp only [tilePartLoop]
    cases hm : r.u16be with
    | error => rw [hm] at seen; cases seen
    | ok p =>
      obtain ⟨mark,next⟩ := p
      simp only [hm,Except.toOption,bind,Option.bind] at seen
      by_cases end_ : (mark == Code.EOC) = true
      · simp [end_] at seen
      by_cases other : (mark != Code.SOT) = true
      · simp only [end_,other,↓reduceIte] at seen
        obtain ⟨rfl,rfl⟩ := seen
        simp [end_,other]
      · simp only [end_,other] at seen ⊢
        cases hp : readTilePart c st r with
        | error => rw [hp] at seen; cases seen
        | ok p =>
          obtain ⟨st',r'⟩ := p
          simp only [hp] at seen
          obtain ⟨ds,err⟩ := ih st' r' seen
          exact ⟨ds.trans (HeaderWork.readTilePart_step hp).2.2.2.1,err⟩

/-- A misplaced tile marker reached from either byte-input API formats the actual
16-bit marker in hexadecimal. Its stored location refers to the original input. -/
theorem public_tile_marker {L : Limits} {d : ByteArray} {opts : DecodeOptions}
    {c : Ctx} {st : State} {r t : Reader} {m : UInt16}
    (start : tileStart L d opts.reduce = .ok (c,st,r))
    (seen : badTileMarker c r.remaining st r = some (t,m)) :
    let s := s!"expected SOT or EOC, found {hex m.toNat}"
    let e := malformedAt t s
    ∃ b : Built 65535 s, decodeCodestream L d opts.reduce = .error e ∧
      JPEG2000.decode L d opts = .error e ∧ t.pos ≤ d.size ∧
      retainedBytes e ≤ Text.byteBound 65535 128 24 ∧ b.tree.work ≤ Text.workBound 65535 128 24 := by
  obtain ⟨ds,fail⟩ := tile_run start
  obtain ⟨dt,err⟩ := badTileMarker_run c r.remaining st r seen
  have hm : m.toNat ≤ 65535 := by have := m.toNat_lt; omega
  let digits : ExprFor 65535 (String.ofList (Nat.toDigits 16 m.toNat)) 0 1 := ⟨_,rfl,.hex hm⟩
  let b := closeExpr (catExpr (litExpr _ "expected SOT or EOC, found ")
    (catExpr (litExpr _ "0x") digits)) (by decide) (by decide)
  have raw := fail _ err
  exact ⟨b,raw,by simp only [JPEG2000.decode,raw,bind,Except.bind],
    dt.trans ds ▸ t.pos_le_size,(built_cost b).1,(built_cost b).2⟩

/-! ## JP2 colour resolution -/

/-- Diagnostic provenance for JP2 channel layout: this stage formats only the first
failing check and its single result is a malformed colour error at a fixed location. -/
def LayoutError (e : Error) : Prop :=
  ∃ s, e = Color.malformed s ∧ Nonempty (Built 65535 s)

private def validateDef (n : Nat) (d : ChannelDef) (_ : Unit) : Except Error (ForInStep Unit) := do
  if d.cn.toNat ≥ n then throw (Color.malformed s!"cdef: channel {d.cn} ≥ {n} channels")
  if d.asoc != 0 && d.asoc != 65535 && d.asoc.toNat - 1 ≥ n then
    throw (Color.malformed s!"cdef: association {d.asoc} > {n} channels")
  return .yield ()

private theorem validateDef_failure {n : Nat} {d : ChannelDef} {e : Error}
    (bad : validateDef n d () = .error e) : LayoutError e := by
  have hc : d.cn.toNat ≤ 65535 := by have := d.cn.toNat_lt; omega
  have ha : d.asoc.toNat ≤ 65535 := by have := d.asoc.toNat_lt; omega
  by_cases high : d.cn.toNat ≥ n
  · simp only [validateDef, high, ↓reduceIte] at bad
    cases bad
    have hn : n ≤ 65535 := by omega
    exact ⟨_,rfl,⟨closeExpr (catExpr (catExpr (catExpr (catExpr (litExpr _ "cdef: channel ")
      (decExpr hc)) (litExpr _ " ≥ ")) (decExpr hn)) (litExpr _ " channels")) (by decide) (by decide)⟩⟩
  · simp only [validateDef, high, ↓reduceIte] at bad
    by_cases test : (d.asoc != 0 && d.asoc != 65535 && (d.asoc.toNat - 1 ≥ n)) = true
    · simp only [test, ↓reduceIte] at bad
      simp only [Bool.and_eq_true, decide_eq_true_eq] at test
      cases bad
      have hn : n ≤ 65535 := by omega
      exact ⟨_,rfl,⟨closeExpr (catExpr (catExpr (catExpr (catExpr (litExpr _ "cdef: association ")
        (decExpr ha)) (litExpr _ " > ")) (decExpr hn)) (litExpr _ " channels")) (by decide) (by decide)⟩⟩
    · simp only [test] at bad; cases bad

private theorem checkCdef_failure {n : Nat} {ds : Array ChannelDef} {e : Error}
    (bad : Color.checkCdef n ds = .error e) : LayoutError e := by
  unfold Color.checkCdef at bad
  cases run : forIn ds () (validateDef n) with
  | error err =>
    change (forIn ds () (validateDef n) >>= _) = .error e at bad
    rw [run] at bad
    cases bad
    rw [← Array.forIn_toList] at run
    obtain ⟨_,_,⟨⟩,one⟩ := forIn_failure _ _ _ run
    exact validateDef_failure one
  | ok u =>
    change (forIn ds () (validateDef n) >>= _) = .error e at bad
    rw [run] at bad
    dsimp only [bind,Except.bind] at bad
    split at bad
    · cases bad; exact ⟨_,rfl,⟨oneFixed _ (by decide)⟩⟩
    · cases bad

private theorem channel_failure {ds : Array ChannelDef} {k : Nat} {e : Error} (hk : k ≤ 65535)
    (bad : colourChannel ds k = .error e) : LayoutError e := by
  unfold colourChannel at bad
  split at bad
  · cases bad
  · cases bad; exact ⟨_,rfl,⟨closeExpr (catExpr (litExpr _ "cdef: no channel for colour ") (decExpr hk))
      (by decide) (by decide)⟩⟩
  · cases bad; exact ⟨_,rfl,⟨closeExpr (catExpr (litExpr _ "cdef: several channels for colour ") (decExpr hk))
      (by decide) (by decide)⟩⟩

private theorem request_count (s : ColourSpace) (data : ByteArray) (d : Nat) (h : d ≤ 65535) :
    (s.numColours data).getD d ≤ 65535 := by
  cases s <;> simp only [ColourSpace.numColours]
  case enumerated cs params =>
    unfold enumColours
    split <;> simp only [Option.getD] <;> omega
  case icc r =>
    unfold iccColours
    dsimp only
    repeat' split
    all_goals simp only [Option.getD] at * <;> omega
  all_goals simp only [Option.getD] <;> omega

private theorem layout_failure {n : Nat} {s : ColourSpace} {d : ByteArray}
    {defs : Option (Array ChannelDef)} {e : Error} (count : (defs.getD #[]).size ≤ 65535)
    (bad : channelLayout (s.numColours d) n defs = .error e) : LayoutError e := by
  cases defs with
  | none => cases bad
  | some ds =>
    dsimp only [channelLayout] at bad
    cases hc : checkCdef n ds with
    | error err => rw [hc] at bad; cases bad; exact checkCdef_failure hc
    | ok u =>
      rw [hc] at bad
      dsimp only [bind, Except.bind] at bad
      let m := match s.numColours d with
        | some k => k
        | none => (ds.filter fun (a : ChannelDef) => a.typ == 0 && a.asoc != 0 && a.asoc != 65535).size
      have hm : m ≤ 65535 := by
        have hh := request_count s d _ (Nat.le_trans (@Array.size_filter_le _
          (fun a : ChannelDef => a.typ == 0 && a.asoc != 0 && a.asoc != 65535) ds) count)
        cases hh' : s.numColours d <;> simpa only [m,hh',Option.getD] using hh
      split at bad
      · rename_i err calls
        cases bad
        obtain ⟨k,mem,one⟩ := map_failure _ _ calls
        have lt : k < m := by
          cases he : s.numColours d <;> simpa [m,he] using mem
        exact channel_failure (by omega) one
      · cases bad

private def rawSelection (L : Limits) (hdr : Option Jp2Header) (n : Nat) :
    Except Error (ColourSpace × Mapping × Option (Array ChannelDef)) :=
  match hdr with
  | none => do
    L.check (.at .color) .components n
    pure (.unknown, identityMapping n, none)
  | some h => do
    let m ← resolveMapping L h n
    pure (resolveColourSpace h, m, h.cdef)

/-- The channel-layout call actually reached by public image decode, once the raw
codestream and palette selection have succeeded. A missing request costs no layout
diagnostic construction. -/
def publicLayout (L : Limits) (d : ByteArray) (opts : DecodeOptions) :
    Option (Except Error ChannelLayout) := do
  let raw ← (decodeCodestream L d opts.reduce).toOption
  let (s,m,ds) ← (rawSelection L (raw.header.container.bind (·.header)) raw.header.siz.components.size).toOption
  return channelLayout (s.numColours d) m.sources.size ds

/-- Every rejecting layout reached by the byte-input API constructs one bounded
message. Validation of a reference only formats the channel count when that count
is dominated by the offending 16-bit field. Missing and ambiguous association
messages use the actual parsed CDEF count or the colour-space request. -/
theorem public_layout {L : Limits} {d : ByteArray} {opts : DecodeOptions} {e : Error}
    (bad : publicLayout L d opts = some (.error e)) :
    JPEG2000.decode L d opts = .error e ∧ LayoutError e := by
  cases raw : decodeCodestream L d opts.reduce with
  | error => simp [publicLayout,raw,Except.toOption] at bad
  | ok img =>
    let hdr := img.header.container.bind (·.header)
    cases select : rawSelection L hdr img.header.siz.components.size with
    | error => dsimp only [hdr] at select; simp [publicLayout,raw,select,Except.toOption] at bad
    | ok p =>
      obtain ⟨s,m,ds⟩ := p
      have reached : channelLayout (s.numColours d) m.sources.size ds = .error e := by
        dsimp only [hdr] at select
        simpa [publicLayout,raw,select,Except.toOption] using bad
      have defs : ds = hdr.bind (·.cdef) := by
        generalize hdr = o at select ⊢
        cases o <;> (obtain ⟨_,_,eq⟩ := Tier2Equiv.bind_ok select; cases eq; rfl)
      have resolve_eq : resolve L d hdr img.header.siz.components = (do
          let (s,m,ds) ← rawSelection L hdr img.header.siz.components.size
          let layout ← channelLayout (s.numColours d) m.sources.size ds
          pure ⟨s,m,m.formats (componentFormats img.header.siz.components),layout⟩) := by
        cases hdr <;> simp [resolve, rawSelection]
      have er : resolve L d hdr img.header.siz.components = .error e := by
        rw [resolve_eq,select]
        simp only [bind,Except.bind,reached]
      dsimp only [hdr] at er
      exact ⟨by simp only [JPEG2000.decode,raw,bind,Except.bind,er],
        layout_failure (defs ▸ ColorResources.retained_cdef raw) reached⟩

/-- Resolution either retains a component count unchanged, or constructs exactly
one colour-stage message. The count can be the source CMAP length before admission. -/
def ResolveError (L : Limits) (n m : Nat) (e : Error) : Prop :=
  (∃ v, (v = n ∨ v = m) ∧ e = .limitExceeded (.at .color) .components v L.maxComponents) ∨
    ∃ s, (e = Color.malformed s ∨ e = Color.unsupported s) ∧ Nonempty (Built 65535 s)

private theorem paletteFailure {p : Palette} {e : Error} (bad : checkPalette p = .error e) :
    ∃ s, (e = Color.malformed s ∨ e = Color.unsupported s) ∧ Nonempty (Built 65535 s) := by
  unfold checkPalette at bad
  dsimp only at bad
  split at bad
  · cases bad; exact ⟨_,.inl rfl,⟨oneFixed _ (by decide)⟩⟩
  · dsimp only [bind,Except.bind,pure,Except.pure] at bad
    split at bad
    · cases bad; exact ⟨_,.inl rfl,⟨oneFixed _ (by decide)⟩⟩
    · rw [← Array.forIn_toList] at bad
      split at bad
      · rename_i err run
        cases bad
        obtain ⟨_,_,⟨⟩,h⟩ := forIn_failure _ _ _ run
        split at h
        · cases h; exact ⟨_,.inr rfl,⟨oneFixed _ (by decide)⟩⟩
        · cases h
      · cases bad

private theorem entryFailure (n : Nat) (p : Palette) (v : CmapEntry) {e : Error}
    (bad : entrySource n p v = .error e) : LayoutError e := by
  have hc : v.cmp.toNat ≤ 65535 := by have := v.cmp.toNat_lt; omega
  have hp : v.pcol.toNat ≤ 65535 := by have := v.pcol.toNat_lt; omega
  have hm : v.mtyp.toNat ≤ 65535 := by have := v.mtyp.toNat_lt; omega
  unfold entrySource at bad
  by_cases large : v.cmp.toNat ≥ n
  · simp only [large,↓reduceIte] at bad
    cases bad
    exact ⟨_,rfl,⟨closeExpr (catExpr (catExpr (catExpr (litExpr _ "cmap: component ") (decExpr hc))
      (litExpr _ " ≥ Csiz ")) (decExpr (show n ≤ 65535 by omega))) (by decide) (by decide)⟩⟩
  · simp only [large,↓reduceIte] at bad
    split at bad
    · split at bad
      · cases bad
        exact ⟨_,rfl,⟨closeExpr (catExpr (catExpr (litExpr _ "cmap: direct use with PCOL ")
          (decExpr hp)) (litExpr _ " ≠ 0")) (by decide) (by decide)⟩⟩
      · cases bad
    · split at bad
      · rename_i high
        cases bad
        exact ⟨_,rfl,⟨closeExpr (catExpr (catExpr (catExpr (litExpr _ "cmap: palette column ")
          (decExpr hp)) (litExpr _ " ≥ NPC ")) (decExpr (show p.npc ≤ 65535 by omega))) (by decide) (by decide)⟩⟩
      · cases bad
    · cases bad
      exact ⟨_,rfl,⟨closeExpr (catExpr (catExpr (litExpr _ "cmap: MTYP ") (decExpr hm))
        (litExpr _ " not 0 or 1")) (by decide) (by decide)⟩⟩

private theorem cmapFailure {L : Limits} {p : Palette} {cm : ComponentMapping} {n : Nat} {e : Error}
    (bad : mappingOf L p cm n = .error e) : ResolveError L n cm.size e := by
  unfold mappingOf at bad
  cases hc : L.check (.at .color) .components cm.size with
  | error err => rw [hc] at bad; cases bad; exact .inl ⟨_,.inr rfl,(Limits.checkLe_eq_error hc).1⟩
  | ok u =>
    simp only [hc,bind,Except.bind] at bad
    split at bad
    · cases bad; exact .inr ⟨_,.inl rfl,⟨oneFixed _ (by decide)⟩⟩
    · dsimp only [pure,Except.pure] at bad
      cases hp : checkPalette p with
      | error err => rw [hp] at bad; cases bad; exact .inr (paletteFailure hp)
      | ok u =>
        simp only [hp] at bad
        split at bad
        · rename_i err run
          cases bad
          obtain ⟨x,_,badEntry⟩ := map_failure _ _ run
          obtain ⟨s,he,b⟩ := entryFailure _ _ x badEntry
          exact .inr ⟨s,.inl he,b⟩
        · cases bad

private theorem resolveFailure {L : Limits} {d : ByteArray} {hdr : Option Jp2Header}
    {comps : Array Marker.Component} {e : Error}
    (count : ((hdr.bind (·.cdef)).getD #[]).size ≤ 65535)
    (bad : resolve L d hdr comps = .error e) :
    ResolveError L comps.size ((hdr.bind (·.cmap)).getD #[]).size e := by
  let n := comps.size
  have eq : resolve L d hdr comps = (do
      let (s,m,ds) ← rawSelection L hdr n
      let layout ← channelLayout (s.numColours d) m.sources.size ds
      pure ⟨s,m,m.formats (componentFormats comps),layout⟩) := by
    cases hdr <;> simp [resolve,rawSelection,n]
  rw [eq] at bad
  cases sel : rawSelection L hdr n with
  | ok triple =>
    obtain ⟨s,m,ds⟩ := triple
    have he : ds = hdr.bind (·.cdef) := by
      cases hdr <;> (obtain ⟨_,_,ret⟩ := Tier2Equiv.bind_ok sel; cases ret; rfl)
    simp only [sel,bind,Except.bind] at bad
    split at bad
    · rename_i err layout
      cases bad
      obtain ⟨msg,why,b⟩ := layout_failure (he ▸ count) layout
      exact .inr ⟨msg,.inl why,b⟩
    · cases bad
  | error err =>
    rw [sel] at bad; cases bad
    have fromCheck (bad : L.check (.at .color) .components n = .error e) :
        ResolveError L comps.size ((hdr.bind (·.cmap)).getD #[]).size e :=
      .inl ⟨_,.inl rfl,(Limits.checkLe_eq_error bad).1⟩
    cases hdr with
    | none =>
      simp only [rawSelection] at sel
      cases ck : L.check (.at .color) .components n <;> rw [ck] at sel <;> cases sel
      exact fromCheck ck
    | some h =>
      simp only [rawSelection] at sel
      cases rm : resolveMapping L h n with
      | ok m => rw [rm] at sel; cases sel
      | error err' =>
        rw [rm] at sel; cases sel
        unfold resolveMapping at rm
        cases hp : h.pclr <;> cases hc : h.cmap <;> simp only [hp,hc] at rm
        all_goals first
          | (cases ck : L.check (.at .color) .components n <;> rw [ck] at rm <;> cases rm; exact fromCheck ck)
          | (simpa [hc,Option.bind] using cmapFailure rm)

/-- Every failure of colour resolution reached after native decoding. This covers
both raw and JP2 selection, palette validation, all repaired or original CMAP
entries, and CDEF. Successful checks in this stage never format failure text. -/
theorem public_resolve {L : Limits} {d : ByteArray} {opts : DecodeOptions} {img : CodestreamImage}
    {e : Error} (raw : decodeCodestream L d opts.reduce = .ok img)
    (bad : Color.resolve L d (img.header.container.bind (·.header)) img.header.siz.components = .error e) :
    JPEG2000.decode L d opts = .error e ∧
    ResolveError L img.header.siz.components.size
      (((img.header.container.bind (·.header)).bind (·.cmap)).getD #[]).size e := by
  exact ⟨by simp only [JPEG2000.decode,raw,bad,bind,Except.bind],
    resolveFailure (ColorResources.retained_cdef raw) bad⟩

/-- At colour resolution every typed failure retains a count bounded even before
admission. The CMAP value is at most a quarter of the original input length;
the native component count already passed the SIZ limit. -/
theorem public_resolve_limit {L : Limits} {d : ByteArray} {opts : DecodeOptions}
    {img : CodestreamImage} {e : Error} (raw : decodeCodestream L d opts.reduce = .ok img)
    (bad : Color.resolve L d (img.header.container.bind (·.header)) img.header.siz.components = .error e)
    (typed : e.isLimit = true) :
    JPEG2000.decode L d opts = .error e ∧ ∃ v, e = .limitExceeded (.at .color) .components v L.maxComponents ∧
      v ≤ max L.maxComponents (d.size/4) ∧ retainedBytes e = 0 := by
  obtain ⟨pub,h⟩ := public_resolve raw bad
  refine ⟨pub,?_⟩
  rcases h with ⟨v,src,rfl⟩ | ⟨_,(rfl|rfl),_⟩
  · refine ⟨v,rfl,?_,rfl⟩
    obtain ⟨cm,n,_⟩ := ColorResources.MappingPrefix.retained_counts raw
    rcases src with rfl | rfl
    · exact Nat.le_trans n (Nat.le_max_left ..)
    · exact Nat.le_trans cm.2 (Nat.le_max_right ..)
  all_goals contradiction

/-! ## Public interleavers -/

private def channelSize (w h : Nat) (c : JPEG2000.Channel) (_ : Unit) :
    Except Error (ForInStep Unit) := do
  if c.plane.width != w || c.plane.height != h then
    throw (.malformed Image.loc "channel size differs from the image size")
  return .yield ()

/-- Complete error classification even for a caller-constructed interleaver input.
Its dimensions and channel count are external arguments. A rejecting size check stores
their computed product and the caller's display bound. For a decoded image,
`public_interleavers` bounds the product by the original decode limits. -/
theorem interleave_error {L w h chs wide mode e} (bad : interleave L w h chs wide mode = .error e) :
    e = .malformed Image.loc "channel size differs from the image size" ∨
      e = .limitExceeded Image.loc .decodedBytes (w*h*chs.size*(if wide then 2 else 1)) L.maxDecodedBytes := by
  unfold interleave at bad
  change (forIn chs () (channelSize w h) >>= _) = (Except.error e : Except Error ByteArray) at bad
  cases scan : forIn chs () (channelSize w h) with
  | error err =>
    rw [scan] at bad
    cases bad
    rw [← Array.forIn_toList] at scan
    obtain ⟨c,_,⟨⟩,fail⟩ := forIn_failure _ _ _ scan
    dsimp only [channelSize] at fail
    split at fail <;> cases fail
    exact Or.inl rfl
  | ok u =>
    rw [scan] at bad
    let size := w*h*chs.size*(if wide then 2 else 1)
    cases ck : L.check Image.loc .decodedBytes size with
    | error err =>
      dsimp only [size] at ck
      simp only [bind,Except.bind,ck,Except.error.injEq] at bad
      subst e
      exact Or.inr (Limits.checkLe_eq_error ck).1
    | ok u =>
      dsimp only [size] at ck
      simp only [bind,Except.bind,ck] at bad
      cases wide <;> simp only [Bool.false_eq_true,↓reduceIte] at bad <;> split at bad <;> cases bad

private theorem display_error {n : Nat} {L : Limits} {r : Except Error ByteArray} {e : Error}
    (d : ColorResources.DisplayWithin L n r) (bad : r = .error e) :
    e = .limitExceeded Image.loc .decodedBytes n L.maxDecodedBytes := by
  by_cases small : n ≤ L.maxDecodedBytes
  · obtain ⟨_,ok,_⟩ := d.1 small
    rw [bad] at ok
    contradiction
  · rw [d.2 (by omega)] at bad
    cases bad
    rfl

/-- For every publicly decoded image, either interleaver's only error retains the
exact computed count and a reference to the caller's display limit. The count before
display admission is bounded by the *decode* limits. No decimal string is built. -/
theorem public_interleavers {L : Limits} {d : ByteArray} {opts : DecodeOptions} {img : Image}
    (ok : JPEG2000.decode L d opts = .ok img) (budget : Limits) (alpha : Bool) (mode : Scaling)
    (wide : Bool) {e : Error}
    (bad : (if wide then img.interleaved16 budget alpha mode else img.interleaved8 budget alpha mode)
      = .error e) :
    let count := img.width * img.height * (img.outChannels alpha).size * (if wide then 2 else 1)
    e = .limitExceeded Image.loc .decodedBytes count budget.maxDecodedBytes ∧
      count ≤ L.maxImageArea * (L.maxComponents + 2) * (if wide then 2 else 1) ∧
      retainedBytes e = 0 := by
  let c := ColorResources.decode_resources ok
  obtain ⟨ch,eight,sixteen⟩ := c.display budget alpha mode
  have count := Nat.mul_le_mul c.image.1 ch
  cases wide
  · simp only [Bool.false_eq_true, ↓reduceIte, Nat.mul_one] at bad ⊢
    have h := display_error eight bad
    exact ⟨h,count,h ▸ rfl⟩
  · simp only [↓reduceIte] at bad ⊢
    have h := display_error sixteen bad
    exact ⟨h,Nat.mul_le_mul_right _ count,h ▸ rfl⟩

/-- For caller-constructed images, the interleavers' computed count has no uniform
bound in the display limits or the retained native image. A single lazy channel
suffices for either interleaver to reject a count above any prescribed ceiling. -/
theorem external_interleavers_unbounded (L : Limits) (template : Image) (n : Nat) :
    ∃ img : Image, img.decoded = template.decoded ∧ ∃ w, n < w ∧
      img.interleaved8 L = .error (.limitExceeded Image.loc .decodedBytes w L.maxDecodedBytes) ∧
      img.interleaved16 L = .error (.limitExceeded Image.loc .decodedBytes (2*w) L.maxDecodedBytes) := by
  let w := max n L.maxDecodedBytes + 1
  let c : JPEG2000.Channel := ⟨8,false,.view w 1 (fun _ => 0)⟩
  let img := {template with width := w, height := 1, channels := #[c], alpha := none}
  have dims : ∀ x ∈ #[c], x.plane.width = w ∧ x.plane.height = 1 := by
    intro x h
    have : x = c := by simpa using h
    cases this
    exact ⟨rfl,rfl⟩
  have over : L.maxDecodedBytes < w := by dsimp [w]; omega
  have eight := (ColorResources.interleave_resources dims L false .linear).2
  have wide := (ColorResources.interleave_resources dims L true .linear).2
  simp only [List.size_toArray,List.length_cons,List.length_nil,Nat.zero_add,Nat.mul_one,
    Bool.false_eq_true,↓reduceIte] at eight wide
  exact ⟨img,rfl,w,by dsimp [w]; omega,eight over,by rw [Nat.mul_comm 2 w]; exact wide (by omega)⟩

/-! ## Channel selection after upsampling -/

private def IndicesFit (cap : Nat) (layout : ChannelLayout) := ∀ i,
  i ∈ layout.colours ∨ layout.alpha = some i ∨ i ∈ layout.other → i ≤ cap

private theorem indicesFit {n cap : Nat} {nc : Option Nat} {ds : Option (Array ChannelDef)}
    {layout : ChannelLayout} (wire : 65535 ≤ cap) (hn : n ≤ cap)
    (ok : channelLayout nc n ds = .ok layout) : IndicesFit cap layout := by
  cases ds with
  | none =>
    cases ok
    intro i h
    rcases h with hc | h | rest
    · have lt : i < min (nc.getD n) n := by simpa using hc
      omega
    · cases h
    · have lt := List.mem_range.mp (List.mem_of_mem_drop (by simpa only [List.mem_toArray] using rest))
      omega
  | some ds =>
    unfold channelLayout at ok
    obtain ⟨_,_,ok⟩ := Tier2Equiv.bind_ok ok
    obtain ⟨cs,got,ret⟩ := Tier2Equiv.bind_ok ok
    cases ret
    intro i h
    rcases h with hc | ha | ho
    · apply Tier2Equiv.arrayMapM_inv (· ≤ cap) _ _ _ _ got i (Array.mem_def.mp hc)
      intro a b hit
      unfold colourChannel at hit
      split at hit <;> cases hit
      rename_i v _
      have := v.cn.toNat_lt
      omega
    · obtain ⟨v,_,eq⟩ := Option.map_eq_some_iff.mp ha
      change v.cn.toNat = i at eq
      have := v.cn.toNat_lt
      omega
    · have mem := (Array.mem_filter.mp ho).1
      have lt : i < n := by simpa using mem
      omega

private theorem resolvedIndices {L d hdr cs info cap} (wire : 65535 ≤ cap)
    (hn : info.mapping.sources.size ≤ cap) (ok : Color.resolve L d hdr cs = .ok info) :
    IndicesFit cap info.layout := by
  unfold Color.resolve at ok
  cases hdr <;> simp only at ok
  all_goals
    obtain ⟨_,_,ok⟩ := Tier2Equiv.bind_ok ok
    obtain ⟨_,ret,ok⟩ := Tier2Equiv.bind_ok ok
    cases ret
    obtain ⟨_,h,ret⟩ := Tier2Equiv.bind_ok ok
    cases ret
    exact indicesFit wire hn h

open JPEG2000.Header

private def pickConversion (L : Limits) (opts : DecodeOptions) (raw : CodestreamImage) (info : Info)
    (r : Rect) (colours : Array Nat) (cs : Array Color.Channel) : Except Error (ColourSpace × Array Color.Channel) :=
  let sp := if info.space == .unknown && opts.inferSycc && Image.looksSycc raw.comps then .sYCC else info.space
  if sp == .sYCC && opts.convertSycc then Image.convertSycc L r.x0 r.y0 colours cs else pure (sp,cs)

/-- Arguments to the final three channel selections from their actual byte-input
prefix, including the checked upsampling pass and optional sYCC conversion. -/
def pickInputs (L : Limits) (d : ByteArray) (opts : DecodeOptions) :
    Except Error (ChannelLayout × Array JPEG2000.Channel) := do
  let raw ← decodeCodestream L d opts.reduce
  let info ← resolve L d (raw.header.container.bind Container.header) raw.header.siz.components
  let choice := ColorResources.MappingPrefix.choice opts info raw
  let cs ← applyMapping L choice.1 (ColorResources.rawChannels raw)
  let r := Assemble.reduceRect (imageRect raw.header.siz) opts.reduce
  L.check Image.loc .imageArea (r.width*r.height)
  let q ← pickConversion L opts raw info r choice.2.colours cs
  L.check Image.loc .workSamples (q.2.foldl (fun a c => if Image.atFullRes r.width r.height c then a else a+r.width*r.height) 0)
  L.check Image.loc .decodedBytes (q.2.foldl (fun a c => a+r.width*r.height*bytesPerSample c.format.depth) 0)
  let full ← q.2.mapM fun c => do
    let plane ← Image.upsample r.x0 r.y0 r.width r.height c
    pure ({ depth := c.format.depth, signed := c.format.signed, plane } : JPEG2000.Channel)
  pure (choice.2,full)

/-- Run the colour, alpha and other selections in decoder order. -/
def pickChannels (layout : ChannelLayout) (full : Array JPEG2000.Channel) :
    Except Error (Array JPEG2000.Channel × Option JPEG2000.Channel × Array JPEG2000.Channel) := do
  let cols ← layout.colours.mapM (Image.pick full)
  let alpha ← match layout.alpha with
    | some i => some <$> Image.pick full i
    | none => pure none
  let other ← layout.other.mapM (Image.pick full)
  pure (cols,alpha,other)

private theorem pickFailure {l : ChannelLayout} {full : Array JPEG2000.Channel} {e : Error}
    (bad : pickChannels l full = .error e) :
    ∃ i, (i ∈ l.colours ∨ l.alpha = some i ∨ i ∈ l.other) ∧ e = .malformed Image.loc s!"channel {i} missing" := by
  have report {i : Nat} (p : Image.pick full i = .error e) : e = .malformed Image.loc s!"channel {i} missing" := by
    unfold Image.pick at p; split at p <;> cases p; rfl
  unfold pickChannels at bad
  cases hc : l.colours.mapM (Image.pick full) with
  | error err =>
    rw [hc] at bad; cases bad
    obtain ⟨i,mem,p⟩ := map_failure _ _ hc
    exact ⟨i,.inl mem,report p⟩
  | ok cols =>
    simp only [hc,bind,Except.bind] at bad
    have tail (h : l.other.mapM (Image.pick full) = .error e) :
        ∃ i, (i ∈ l.colours ∨ l.alpha = some i ∨ i ∈ l.other) ∧ e = .malformed Image.loc s!"channel {i} missing" := by
      obtain ⟨i,mem,p⟩ := map_failure _ _ h
      exact Exists.intro i (And.intro (Or.inr (Or.inr mem) :
        i ∈ l.colours ∨ l.alpha = some i ∨ i ∈ l.other) (report p))
    cases ha : l.alpha with
    | none => simp only [ha,pure,Except.pure] at bad; split at bad <;> cases bad; simpa only [ha] using tail (by assumption)
    | some i =>
      cases hp : Image.pick full i <;> simp only [ha,hp,Functor.map,Except.map] at bad
      · cases bad; exact ⟨i,.inr (.inl rfl),report hp⟩
      · split at bad <;> cases bad; simpa only [ha] using tail (by assumption)

private theorem pick_propagates {lay : ChannelLayout} {full : Array JPEG2000.Channel} {e : Error}
    (bad : pickChannels lay full = .error e) {α : Type}
    (f : Array JPEG2000.Channel → Option JPEG2000.Channel → Array JPEG2000.Channel → Except Error α) :
    (do let cs ← lay.colours.mapM (Image.pick full)
        let a ← match lay.alpha with
          | some i => some <$> Image.pick full i
          | none => pure none
        let os ← lay.other.mapM (Image.pick full)
        f cs a os) = .error e := by
  unfold pickChannels at bad
  cases hc : lay.colours.mapM (Image.pick full) <;> rw [hc] at bad
  · cases bad; rfl
  dsimp only [bind,Except.bind] at bad ⊢
  cases ha : lay.alpha <;> simp only [ha] at bad ⊢
  case none =>
    simp only [pure,Except.pure] at bad ⊢
    cases ho : lay.other.mapM (Image.pick full) <;> rw [ho] at bad <;> cases bad; rfl
  case some i =>
    cases hp : Image.pick full i <;> simp only [hp,Functor.map,Except.map] at bad ⊢
    · cases bad; rfl
    · split at bad <;> cases bad; simp [*]

private theorem plain_pick {indices : Array Nat} {full : Array JPEG2000.Channel} {e : Error}
    (bad : pickChannels {colours := indices} full = .error e) : indices.mapM (Image.pick full) = .error e := by
  have empty : (#[] : Array Nat).mapM (Image.pick full) = .ok #[] := by
    rw [Array.mapM_eq_mapM_toList]; rfl
  cases hc : indices.mapM (Image.pick full) <;>
    simp only [pickChannels,hc,empty,bind,Except.bind,pure,Except.pure] at bad <;> cases bad; rfl

/-- The final channel index is bounded by the public mapping admission or by
the 16-bit channel named by CDEF. All earlier selections can succeed without
formatting any message; the first failing pick materializes a single decimal. -/
theorem public_pick {L : Limits} {d : ByteArray} {opts : DecodeOptions} {lay : ChannelLayout}
    {full : Array JPEG2000.Channel} {e : Error} (reached : pickInputs L d opts = .ok (lay,full))
    (bad : pickChannels lay full = .error e) :
    JPEG2000.decode L d opts = .error e ∧ ∃ i, i ≤ max 65535 L.maxComponents ∧
      e = .malformed Image.loc s!"channel {i} missing" ∧
      Nonempty (Built (max 65535 L.maxComponents) s!"channel {i} missing") := by
  unfold pickInputs at reached
  obtain ⟨raw,hn,reached⟩ := Tier2Equiv.bind_ok reached
  obtain ⟨info,hi,reached⟩ := Tier2Equiv.bind_ok reached
  obtain ⟨cs,hm,reached⟩ := Tier2Equiv.bind_ok reached
  obtain ⟨_,area,reached⟩ := Tier2Equiv.bind_ok reached
  obtain ⟨q,conv,reached⟩ := Tier2Equiv.bind_ok reached
  obtain ⟨_,work,reached⟩ := Tier2Equiv.bind_ok reached
  obtain ⟨_,bytes,reached⟩ := Tier2Equiv.bind_ok reached
  obtain ⟨fs,up,ret⟩ := Tier2Equiv.bind_ok reached
  cases ret
  have fit : IndicesFit (max 65535 L.maxComponents) (ColorResources.MappingPrefix.choice opts info raw).2 := by
    have count := (ColorResources.applyMapping_resources hm).count
    unfold ColorResources.MappingPrefix.choice at *
    split at count <;> rename_i flag
    · simp only [flag,↓reduceIte]
      exact resolvedIndices (Nat.le_max_left ..) (Nat.le_trans count (Nat.le_max_right ..)) hi
    · simp only [flag,Bool.false_eq_true,↓reduceIte]
      intro i mem
      have lt : i < (ColorResources.rawChannels raw).size := by simpa using mem
      simp only [identityMapping,Array.size_map,List.size_toArray,List.length_range] at count
      omega
  obtain ⟨i,mem,eq⟩ := pickFailure bad
  have cap := fit i mem
  refine ⟨?_,i,cap,eq,⟨closeExpr (catExpr (catExpr (litExpr _ "channel ") (decExpr cap))
    (litExpr _ " missing")) (by decide) (by decide)⟩⟩
  unfold JPEG2000.decode
  simp only [hn,hi,bind,Except.bind]
  unfold ColorResources.MappingPrefix.choice at hm bad conv
  unfold pickConversion at conv
  split at hm <;> rename_i sel
  all_goals
    simp only [sel,Bool.false_eq_true,↓reduceIte] at bad conv ⊢
    change applyMapping L _ _ = .ok cs at hm
    simp only [ColorResources.rawChannels,Array.size_map] at hm bad conv ⊢
    simp only [hm,area]
    generalize hsp : (if info.space == .unknown && opts.inferSycc && Image.looksSycc raw.comps
      then ColourSpace.sYCC else info.space) = sp at conv ⊢
    by_cases active : (sp == .sYCC && opts.convertSycc) = true
    · simp only [active,↓reduceIte] at conv ⊢; rw [conv]
      simp only [work,bytes]
      simp only [pure,Except.pure,bind,Except.bind] at up
      simp only [pure,Except.pure,up]
      first | apply pick_propagates bad | rw [plain_pick bad]
    · simp only [active,Bool.false_eq_true,↓reduceIte] at conv ⊢
      cases conv
      simp only [pure,Except.pure,work,bytes]
      simp only [pure,Except.pure,bind,Except.bind] at up
      simp only [up]
      first | apply pick_propagates bad | rw [plain_pick bad]

end JPEG2000.Spec.Resources.DiagnosticCost

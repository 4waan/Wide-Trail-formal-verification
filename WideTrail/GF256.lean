/-
Copyright (c) 2026 Awaan Siddiqui. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Awaan Siddiqui
-/
import Mathlib.Algebra.Field.Defs
import Mathlib.Data.BitVec

/-!
# `GF(2⁸)`, built and verified from scratch

The AES `MixColumns` step is linear over `GF(2⁸)` = `GF(2)[X] / (X⁸+X⁴+X³+X+1)`. Mathlib has
no concrete instance of this field: `GaloisField p n` is defined as a `SplittingField` inside
a `noncomputable section`, so `decide` can never reduce it, and there is no usable finite-field
API to fall back on. This file builds `GF(2⁸)` directly as `BitVec 8` under xor (addition) and
the standard shift-and-reduce carry-less multiplication (`xtime`, doubling by the primitive
element `X`), and proves it is a field with **no** `sorry`, no `native_decide`, and no
`bv_decide` fallback axiom: every proof here is checked by the kernel alone.

That constraint dictated the proof strategy. A back-of-envelope check shows why:
`Mul` on `BitVec 8` has `256³ ≈ 16.7` million triples, and a literal `decide` over that many
cases hits the kernel's recursion-depth limit and does not finish in any reasonable time (this
was measured directly, not assumed — even the `256²` commutativity-shaped check timed out).
So associativity and commutativity are **not** brute-forced. Instead:

* `rawMul` is additive in each argument separately (`rawMul_add_left`, `rawMul_add_right`),
  proved by induction on the shift-and-reduce recursion using the fact that `xtime` itself is
  additive (`xtime_xor`) — this needs no case enumeration at all, just algebra.
* Additivity makes `rawMul` **bilinear** over `GF(2)`. A bilinear (respectively trilinear) map
  on an 8-dimensional space is determined by its values on the `8×8` (respectively `8×8×8`)
  basis pairs/triples, via `bitDecomp`, the fact that every byte is the xor of the basis
  vectors `2⁰, …, 2⁷` selected by its own bits. Commutativity and associativity are checked on
  those small, closed, concrete bases — `64` and `512` cases respectively — where `decide`
  finishes in seconds, and lifted to all of `GF(2⁸)` by that bilinearity.
* Multiplicative inverses use Fermat: every nonzero byte satisfies `a²⁵⁴ · a = 1`, since the
  nonzero elements form a group of order `255`. `a²⁵⁴` is computed by an *unrolled*
  repeated-squaring chain (`rawInv`) rather than a recursive power function — a first attempt
  using general recursion on `n` either overflowed the elaborator's recursion depth (linear
  recursion to depth `254`, checked across all `256` test values) or got the kernel stuck
  entirely (well-founded recursion on `n / 2` does not reduce by `decide`, for the same reason
  `GaloisField` doesn't: `Acc.rec` is not kernel-computable in general). The fix sidesteps
  both: a fixed, finite, non-recursive chain of `13` multiplications has nothing for the
  elaborator or the kernel to get stuck on.

The `GF256` type itself is a one-field wrapper `structure` around `BitVec 8`, not a bare
`def GF256 := BitVec 8`: `BitVec 8` already has its own (unrelated, mod-`2⁸`) `Add`/`Mul`
instances, and a reducible alias risks instance-resolution picking the wrong one. The wrapper
gets fresh instances with no diamond, at the cost of routing every field access through
`.val`.
-/

set_option autoImplicit false

namespace GF256

/-! ### The xor toolkit

`BitVec 8` under xor is an abelian group where every element is its own inverse
(`xor_self`), a fact core's `BitVec` library already proves structurally (`xor_assoc`,
`xor_comm`, `xor_self`, `xor_zero`), not by enumeration. The four lemmas below are the small
extra closure of that toolkit — cancellation shapes that come up repeatedly once accumulators
start getting shuffled around a recursive multiplier — proved the same structural way. -/

@[simp] theorem zero_xor {w : Nat} (x : BitVec w) : (0#w) ^^^ x = x := by
  rw [BitVec.xor_comm]; exact BitVec.xor_zero

@[simp] theorem xor_cancel_left {w : Nat} (x y : BitVec w) : x ^^^ (x ^^^ y) = y := by
  rw [← BitVec.xor_assoc, BitVec.xor_self, zero_xor]

@[simp] theorem xor_cancel_left' {w : Nat} (x y : BitVec w) : x ^^^ (y ^^^ x) = y := by
  rw [BitVec.xor_comm x, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- The one shape the three lemmas above don't reach directly: two independent atoms with a
repeated one sandwiched between them. Bit-blast to `Bool`, where a full case split on the
(finitely many) truth values is unconditionally robust. -/
@[simp] theorem xor_cancel_middle {w : Nat} (p q r : BitVec w) :
    (p ^^^ q) ^^^ (r ^^^ q) = p ^^^ r := by
  ext i
  rcases hp : p[i] <;> rcases hq : q[i] <;> rcases hr : r[i] <;> simp_all

/-! ### Multiplication by the primitive element `X`

`xtime a` is "multiply by `X`": shift left one bit, and if that overflowed the top bit,
cancel it by xor-ing in the reduction polynomial `X⁸+X⁴+X³+X+1` (mod `X⁸`, i.e. `0x1B`). -/

def xtime (a : BitVec 8) : BitVec 8 :=
  if a.getLsbD 7 then (a <<< 1) ^^^ (0x1B#8 : BitVec 8) else a <<< 1

@[simp] theorem xtime_zero : xtime 0#8 = 0#8 := by simp [xtime]

/-- `xtime` is `GF(2)`-linear: it commutes with addition (xor). This is the fact that powers
everything downstream — it is what lets the shift-and-reduce multiplier be proved additive in
its first argument by a clean induction, with no case enumeration over field elements. -/
theorem xtime_xor (a b : BitVec 8) : xtime (a ^^^ b) = xtime a ^^^ xtime b := by
  simp only [xtime, BitVec.getLsbD_xor, BitVec.shiftLeft_xor_distrib]
  by_cases ha : a[7] <;> by_cases hb : b[7] <;> simp [ha, hb] <;> ac_rfl

/-! ### The shift-and-add multiplier

Standard carry-less multiplication: walk the 8 bits of `b` from the low end, doubling `a`
(via `xtime`) at each step and adding it into the accumulator whenever the current bit of `b`
is set. -/

def mulAux : Nat → BitVec 8 → BitVec 8 → BitVec 8 → BitVec 8
  | 0, _, _, acc => acc
  | n + 1, a, b, acc => mulAux n (xtime a) (b >>> 1) (if b.getLsbD 0 then acc ^^^ a else acc)

def rawMul (a b : BitVec 8) : BitVec 8 := mulAux 8 a b 0#8

/-- Sanity check against the textbook Rijndael example: `0x53 · 0xCA = 0x01` in `GF(2⁸)`. -/
example : rawMul 0x53#8 0xCA#8 = 0x01#8 := by decide

/-- The accumulator is just carried along additively: computing with a nonzero starting
accumulator is the same as computing from `0` and xor-ing the accumulator in afterward. This
is the decoupling lemma that lets every proof below hoist accumulators out on demand. -/
theorem mulAux_acc (n : Nat) (a b acc : BitVec 8) :
    mulAux n a b acc = mulAux n a b 0#8 ^^^ acc := by
  induction n generalizing a b acc with
  | zero => simp [mulAux]
  | succ n ih =>
    by_cases hb : b.getLsbD 0
    · simp only [mulAux, hb, if_true, zero_xor]
      rw [ih (xtime a) (b >>> 1) (acc ^^^ a), ih (xtime a) (b >>> 1) a]
      ac_rfl
    · simp only [mulAux, hb]
      exact ih (xtime a) (b >>> 1) acc

theorem mulAux_zero_left (n : Nat) (b acc : BitVec 8) : mulAux n 0#8 b acc = acc := by
  induction n generalizing b acc with
  | zero => simp [mulAux]
  | succ n ih =>
    simp only [mulAux, xtime_zero, BitVec.xor_zero]
    split <;> exact ih (b >>> 1) acc

theorem rawMul_zero_left (b : BitVec 8) : rawMul 0#8 b = 0#8 := mulAux_zero_left 8 b 0#8

/-- **Left distributivity.** Proved by induction on the recursion depth using `xtime`'s
additivity — no enumeration over `BitVec 8` values anywhere. -/
theorem mulAux_add_left (n : Nat) (a1 a2 b : BitVec 8) :
    mulAux n (a1 ^^^ a2) b 0#8 = mulAux n a1 b 0#8 ^^^ mulAux n a2 b 0#8 := by
  induction n generalizing a1 a2 b with
  | zero => simp [mulAux]
  | succ n ih =>
    by_cases hb : b.getLsbD 0
    · simp only [mulAux, xtime_xor, hb, if_true, zero_xor]
      rw [mulAux_acc n (xtime a1 ^^^ xtime a2) (b >>> 1) (a1 ^^^ a2),
          mulAux_acc n (xtime a1) (b >>> 1) a1, mulAux_acc n (xtime a2) (b >>> 1) a2, ih]
      ac_rfl
    · simp only [mulAux, xtime_xor, hb]
      exact ih (xtime a1) (xtime a2) (b >>> 1)

theorem rawMul_add_left (a1 a2 b : BitVec 8) :
    rawMul (a1 ^^^ a2) b = rawMul a1 b ^^^ rawMul a2 b :=
  mulAux_add_left 8 a1 a2 b

set_option linter.flexible false in
/-- **Right distributivity.** The mirror argument: the recursion reads `b`'s bits directly
(rather than doubling it), so this uses `BitVec.ushiftRight_xor_distrib` in place of
`xtime_xor`, but is otherwise the same shape as the left case.

(The `flexible` linter suggests replacing the `simp [...]` below with a specific
`simp only [...]`; that replacement is not actually safe here — it does not fully close all
four `hb1`/`hb2` branches the way plain `simp` does, checked directly.) -/
theorem mulAux_add_right (n : Nat) (a b1 b2 : BitVec 8) :
    mulAux n a (b1 ^^^ b2) 0#8 = mulAux n a b1 0#8 ^^^ mulAux n a b2 0#8 := by
  induction n generalizing a b1 b2 with
  | zero => simp [mulAux]
  | succ n ih =>
    by_cases hb1 : b1[0] <;> by_cases hb2 : b2[0] <;>
      simp only [mulAux] <;>
      simp [BitVec.ushiftRight_xor_distrib, hb1, hb2]
    · rw [ih (xtime a) (b1 >>> 1) (b2 >>> 1), mulAux_acc n (xtime a) (b1 >>> 1) a,
          mulAux_acc n (xtime a) (b2 >>> 1) a]
      simp
    · rw [mulAux_acc n (xtime a) (b1 >>> 1 ^^^ b2 >>> 1) a, ih (xtime a) (b1 >>> 1) (b2 >>> 1),
          mulAux_acc n (xtime a) (b1 >>> 1) a]
      ac_rfl
    · rw [mulAux_acc n (xtime a) (b1 >>> 1 ^^^ b2 >>> 1) a, ih (xtime a) (b1 >>> 1) (b2 >>> 1),
          mulAux_acc n (xtime a) (b2 >>> 1) a]
      ac_rfl
    · exact ih (xtime a) (b1 >>> 1) (b2 >>> 1)

theorem rawMul_add_right (a b1 b2 : BitVec 8) :
    rawMul a (b1 ^^^ b2) = rawMul a b1 ^^^ rawMul a b2 :=
  mulAux_add_right 8 a b1 b2

theorem rawMul_zero_right (a : BitVec 8) : rawMul a 0#8 = 0#8 := by
  have h := rawMul_add_right a 0#8 0#8
  simpa using h

/-! ### Commutativity and associativity, by bilinear extension from a small basis

`rawMul` is now known to be additive in each argument. An additive (`GF(2)`-linear) map in
each of several arguments is determined by its values on basis elements, so commutativity and
associativity only need checking on the `8` (respectively `8`) basis bytes `pow2 i = 2ⁱ`, not
on all of `GF(2⁸)`: `64` and `512` cases, both small enough for the kernel. `bitDecomp` is the
basis-expansion fact; `rawMul_ite2` is what turns two independently-masked expansions into
flat, directly-comparable atoms so `ac_rfl` can finish the job once the small basis facts have
aligned the content. -/

/-- Basis vector `i` (i.e. `2ⁱ`), in the shape the basis lemmas below are stated in, so they
line up as simp lemmas against `bitDecomp` without a separate numeral-bridging step. -/
def pow2 (i : Fin 8) : BitVec 8 := 1#8 <<< i.val

/-- Every byte is the xor of the basis vectors selected by its own bits: a closed, `256`-case
fact, well inside what `decide` can check directly. -/
theorem bitDecomp (a : BitVec 8) :
    a = (if a[0] then pow2 0 else 0#8) ^^^ (if a[1] then pow2 1 else 0#8) ^^^
        (if a[2] then pow2 2 else 0#8) ^^^ (if a[3] then pow2 3 else 0#8) ^^^
        (if a[4] then pow2 4 else 0#8) ^^^ (if a[5] then pow2 5 else 0#8) ^^^
        (if a[6] then pow2 6 else 0#8) ^^^ (if a[7] then pow2 7 else 0#8) := by
  revert a; decide

theorem rawMul_ite2 (p q : Bool) (x y : BitVec 8) :
    rawMul (if p then x else 0#8) (if q then y else 0#8) = if p && q then rawMul x y else 0#8 := by
  cases p <;> cases q <;> simp [rawMul_zero_left, rawMul_zero_right]

theorem rawMul_pow2_comm : ∀ i j : Fin 8, rawMul (pow2 i) (pow2 j) = rawMul (pow2 j) (pow2 i) := by
  decide

theorem rawMul_comm (a b : BitVec 8) : rawMul a b = rawMul b a := by
  rw [bitDecomp a, bitDecomp b]
  simp only [rawMul_add_left, rawMul_add_right, rawMul_ite2, Bool.and_comm, rawMul_pow2_comm]
  ac_rfl

theorem rawMul_pow2_assoc :
    ∀ i j k : Fin 8, rawMul (rawMul (pow2 i) (pow2 j)) (pow2 k)
      = rawMul (pow2 i) (rawMul (pow2 j) (pow2 k)) := by
  decide

theorem rawMul_assoc (a b c : BitVec 8) : rawMul (rawMul a b) c = rawMul a (rawMul b c) := by
  rw [bitDecomp a, bitDecomp b, bitDecomp c]
  simp only [rawMul_add_left, rawMul_add_right, rawMul_ite2, Bool.and_assoc, rawMul_pow2_assoc]

theorem rawMul_one : ∀ a : BitVec 8, rawMul a 1#8 = a := by decide

theorem rawMul_one_left (a : BitVec 8) : rawMul 1#8 a = a := by
  rw [rawMul_comm]; exact rawMul_one a

/-! ### Multiplicative inverses -/

/-- `a⁻¹ = a²⁵⁴` (Fermat: the `255` nonzero bytes form a group of order `255`), computed by an
*unrolled* repeated-squaring chain rather than a recursive power function — see the module
docstring for why the two natural recursive definitions each broke `decide` in a different
way. `254 = 128+64+32+16+8+4+2` (binary `11111110`). -/
def rawInv (a : BitVec 8) : BitVec 8 :=
  let a2 := rawMul a a
  let a4 := rawMul a2 a2
  let a8 := rawMul a4 a4
  let a16 := rawMul a8 a8
  let a32 := rawMul a16 a16
  let a64 := rawMul a32 a32
  let a128 := rawMul a64 a64
  rawMul a128 (rawMul a64 (rawMul a32 (rawMul a16 (rawMul a8 (rawMul a4 a2)))))

set_option maxRecDepth 4000 in
theorem rawInv_zero : rawInv 0#8 = 0#8 := by decide

set_option maxRecDepth 4000 in
theorem rawMul_inv_cancel : ∀ a : BitVec 8, a ≠ 0#8 → rawMul a (rawInv a) = 1#8 := by decide

end GF256

/-! ### Packaging as a `Field`

`GF256` is a one-field wrapper around `BitVec 8`, not a reducible alias: `BitVec 8` already
carries its own (unrelated) `Add`/`Mul` from ordinary mod-`2⁸` arithmetic, and letting instance
search see through an alias risks silently picking those instead of the ones defined here. -/

structure GF256 where
  val : BitVec 8
deriving DecidableEq

namespace GF256

instance : Fintype (BitVec 8) :=
  Fintype.ofEquiv (Fin (2 ^ 8)) ⟨BitVec.ofFin, BitVec.toFin, fun _ => rfl, fun _ => rfl⟩

/-- The obvious bijection with the underlying representation, used only to transport the
`Fintype` instance below (a `4×4` state over `GF256` needs `Fintype`/`DecidableEq` for the
column/branch-number machinery in `WideTrail.Columns`). -/
def equivBitVec : GF256 ≃ BitVec 8 where
  toFun := GF256.val
  invFun := GF256.mk
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype GF256 := Fintype.ofEquiv (BitVec 8) equivBitVec.symm

instance : Add GF256 := ⟨fun a b => ⟨a.val ^^^ b.val⟩⟩
instance : Mul GF256 := ⟨fun a b => ⟨rawMul a.val b.val⟩⟩
instance : Zero GF256 := ⟨⟨0#8⟩⟩
instance : One GF256 := ⟨⟨1#8⟩⟩
instance : Neg GF256 := ⟨id⟩
instance : Sub GF256 := ⟨fun a b => ⟨a.val ^^^ b.val⟩⟩
instance : Inv GF256 := ⟨fun a => ⟨rawInv a.val⟩⟩

theorem ext {a b : GF256} (h : a.val = b.val) : a = b := by
  cases a; cases b; simpa using h

set_option maxRecDepth 4000 in
instance : Field GF256 where
  add_assoc a b c := ext (BitVec.xor_assoc a.val b.val c.val)
  zero_add a := ext (zero_xor a.val)
  add_zero _ := ext BitVec.xor_zero
  add_comm a b := ext (BitVec.xor_comm a.val b.val)
  neg_add_cancel _ := ext BitVec.xor_self
  mul_assoc a b c := ext (rawMul_assoc a.val b.val c.val)
  mul_comm a b := ext (rawMul_comm a.val b.val)
  one_mul a := ext ((rawMul_comm 1#8 a.val).trans (rawMul_one a.val))
  mul_one a := ext (rawMul_one a.val)
  left_distrib a b c := ext (rawMul_add_right a.val b.val c.val)
  right_distrib a b c := ext (rawMul_add_left a.val b.val c.val)
  zero_mul a := ext (rawMul_zero_left a.val)
  mul_zero a := ext ((rawMul_comm a.val 0#8).trans (rawMul_zero_left a.val))
  exists_pair_ne := ⟨0, 1, fun h => absurd (congrArg GF256.val h) (by decide)⟩
  mul_inv_cancel a ha := ext (rawMul_inv_cancel a.val (fun h => ha (ext h)))
  inv_zero := ext rawInv_zero
  nsmul := nsmulRec
  zsmul := zsmulRec
  nnqsmul := _
  qsmul := _

end GF256

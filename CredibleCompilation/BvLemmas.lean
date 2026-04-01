import Std.Tactic.BVDecide

/-!
# BitVec reassembly lemmas for loadImm64

These lemmas prove that decomposing a 64-bit value into 16-bit chunks
and reassembling via mask/shift/or recovers the original value.
Separated into their own file because `bv_decide` on 64-bit bitvectors
is expensive and these rarely change.
-/

set_option maxHeartbeats 102400000

/-- The full 16-bit chunk reassembly identity on BitVec 64:
    decomposing into 4 chunks and reassembling via insertBits gives back the original. -/
theorem bv_reassemble (bits : BitVec 64) :
    let w0 : BitVec 64 := bits &&& 0xFFFF#64
    let w1 : BitVec 64 := (bits >>> 16) &&& 0xFFFF#64
    let w2 : BitVec 64 := (bits >>> 32) &&& 0xFFFF#64
    let w3 : BitVec 64 := (bits >>> 48) &&& 0xFFFF#64
    ((((w0 &&& ~~~(0xFFFF#64 <<< 16)) ||| (w1 <<< 16)) &&&
      ~~~(0xFFFF#64 <<< 32)) ||| (w2 <<< 32)) &&&
      ~~~(0xFFFF#64 <<< 48) ||| (w3 <<< 48) = bits := by
  bv_decide

-- Partial reassembly variants (when some chunks are zero, the insertBits is skipped)
theorem bv_reassemble_110 (bits : BitVec 64) (hw3 : (bits >>> 48) &&& 0xFFFF#64 = 0) :
    (((bits &&& 0xFFFF#64) &&& ~~~(0xFFFF#64 <<< 16) ||| ((bits >>> 16) &&& 0xFFFF#64) <<< 16) &&&
      ~~~(0xFFFF#64 <<< 32)) ||| ((bits >>> 32) &&& 0xFFFF#64) <<< 32 = bits := by bv_decide
theorem bv_reassemble_101 (bits : BitVec 64) (hw2 : (bits >>> 32) &&& 0xFFFF#64 = 0) :
    ((bits &&& 0xFFFF#64) &&& ~~~(0xFFFF#64 <<< 16) ||| ((bits >>> 16) &&& 0xFFFF#64) <<< 16) &&&
      ~~~(0xFFFF#64 <<< 48) ||| ((bits >>> 48) &&& 0xFFFF#64) <<< 48 = bits := by bv_decide
theorem bv_reassemble_100 (bits : BitVec 64) (hw2 : (bits >>> 32) &&& 0xFFFF#64 = 0)
    (hw3 : (bits >>> 48) &&& 0xFFFF#64 = 0) :
    (bits &&& 0xFFFF#64) &&& ~~~(0xFFFF#64 <<< 16) ||| ((bits >>> 16) &&& 0xFFFF#64) <<< 16 = bits := by bv_decide
theorem bv_reassemble_011 (bits : BitVec 64) (hw1 : (bits >>> 16) &&& 0xFFFF#64 = 0) :
    ((bits &&& 0xFFFF#64) &&& ~~~(0xFFFF#64 <<< 32) ||| ((bits >>> 32) &&& 0xFFFF#64) <<< 32) &&&
      ~~~(0xFFFF#64 <<< 48) ||| ((bits >>> 48) &&& 0xFFFF#64) <<< 48 = bits := by bv_decide
theorem bv_reassemble_010 (bits : BitVec 64) (hw1 : (bits >>> 16) &&& 0xFFFF#64 = 0)
    (hw3 : (bits >>> 48) &&& 0xFFFF#64 = 0) :
    (bits &&& 0xFFFF#64) &&& ~~~(0xFFFF#64 <<< 32) ||| ((bits >>> 32) &&& 0xFFFF#64) <<< 32 = bits := by bv_decide
theorem bv_reassemble_001 (bits : BitVec 64) (hw1 : (bits >>> 16) &&& 0xFFFF#64 = 0)
    (hw2 : (bits >>> 32) &&& 0xFFFF#64 = 0) :
    (bits &&& 0xFFFF#64) &&& ~~~(0xFFFF#64 <<< 48) ||| ((bits >>> 48) &&& 0xFFFF#64) <<< 48 = bits := by bv_decide
theorem bv_reassemble_000 (bits : BitVec 64) (hw1 : (bits >>> 16) &&& 0xFFFF#64 = 0)
    (hw2 : (bits >>> 32) &&& 0xFFFF#64 = 0) (hw3 : (bits >>> 48) &&& 0xFFFF#64 = 0) :
    bits &&& 0xFFFF#64 = bits := by bv_decide

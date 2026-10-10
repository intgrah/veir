module

public import Veir.Rewriter.Basic
public import Veir.Rewriter.EraseContainers
public import Veir.GlobalOpInfo

meta import Veir.IR.Buffed.Basic
import Veir.IR.Buffed.Meta

/-!
# IR construction primitives for the parser

The parser builds IR directly in the buffered representation (`Buffed.IRBufContext`). Each
primitive is a `buffed` definition over the `Sim` view of the context, exactly like the
benchmarks, so that `buffed` generates its executable `*Impl` version and the compiler checks
that no erased (`GHOST_`) specification data survives in it. The proof obligations of the
underlying rewriter operations are discharged with `sorry`, as in the benchmarks.

The generated implementations still take the erased specification arguments and the proofs in
their signatures; the plain wrappers at the end of this file pass `default` and `sorry` for
them. They are never inspected.
-/

public section

namespace Veir.Parser.IR

open Veir
open Veir.Buffed

set_option warn.sorry false

/-- A raw operation address. -/
abbrev Op := OperationMPtr
/-- A raw block address. -/
abbrev Block := BlockMPtr
/-- A raw region address. -/
abbrev Region := RegionMPtr
/-- A raw value address (an operation result or a block argument). -/
abbrev Value := ValueImplMPtr

/-! ## Specialization warm-up

The library's rewriter implementations are generic in the opcode type. When they are first used at
`OpCode` in this module, the compiler creates specialized copies of them. If that happens in the
same compilation batch as one of the `buffed` primitives below, the ghost-elimination check of
`ReduceArity` runs before the follow-up simplification removes the erased arguments from the
call sites, and compilation fails. These plain definitions trigger (and cache) the
specializations first; they are otherwise unused. -/

/- Innermost layer: the non-inlined use-list removal is nested inside the specializations of
`eraseOp` and `replaceValue?`, so it must be specialized in an earlier batch than those. -/
private def warmRemoveFromCurrent (ctx : Sim.IRContext OpCode) (operand : Sim.OpOperandPtr) :
    Sim.IRContext OpCode :=
  operand.removeFromCurrent ctx sorry sorry

private def warmAllocOp (ctx : Sim.IRContext OpCode) (opType : OpCode) (properties : propertiesOf opType)
    (nr no nb ng : UInt64) : Option (Sim.OperationPtr × Sim.IRContext OpCode) :=
  Sim.OperationPtr.allocRecycled ctx opType properties nr no nb ng sorry sorry sorry sorry

private def warmDetachOperands (ctx : Sim.IRContext OpCode) (op : Sim.OperationPtr) : Sim.IRContext OpCode :=
  Rewriter.detachOperands ctx op sorry sorry sorry

private def warmDetachBlockOperands (ctx : Sim.IRContext OpCode) (op : Sim.OperationPtr) : Sim.IRContext OpCode :=
  Rewriter.detachBlockOperands ctx op sorry sorry sorry

private def warmDetachOpIfAttached (ctx : Sim.IRContext OpCode) (op : Sim.OperationPtr) : Sim.IRContext OpCode :=
  Rewriter.detachOpIfAttached ctx op sorry sorry

private def warmDealloc (ctx : Sim.IRContext OpCode) (op : Sim.OperationPtr) : Sim.IRContext OpCode :=
  Sim.OperationPtr.dealloc ctx op sorry sorry

private def warmCreateOp (ctx : Sim.IRContext OpCode) (opType : OpCode) (resultTypes : Array TypeAttr)
    (operands : Sim.ArrayValuePtr) (blockOperands : Sim.ArrayBlockPtr)
    (regions : Sim.ArrayRegionPtr) (properties : propertiesOf opType)
    (ip : Option InsertPoint) : Option (Sim.IRContext OpCode × Sim.OperationPtr) :=
  Rewriter.createOp ctx opType resultTypes operands blockOperands regions properties ip
    sorry sorry sorry sorry sorry sorry sorry

private def warmCreateBlock (ctx : Sim.IRContext OpCode) (argTypes : Array TypeAttr)
    (ip : Option BlockInsertPoint) : Option (Sim.IRContext OpCode × Sim.BlockPtr) :=
  Rewriter.createBlock ctx argTypes ip sorry sorry

private def warmInsertBlock (ctx : Sim.IRContext OpCode) (block : Sim.BlockPtr) (ip : BlockInsertPoint) :
    Option (Sim.IRContext OpCode) :=
  Rewriter.insertBlock? ctx block ip sorry sorry sorry sorry

private def warmCreateRegion (ctx : Sim.IRContext OpCode) : Option (Sim.IRContext OpCode × Sim.RegionPtr) :=
  Rewriter.createRegion ctx

private def warmSetAttributes (ctx : Sim.IRContext OpCode) (op : Sim.OperationPtr) (attrs : DictionaryAttr) :
    Option (Sim.IRContext OpCode) :=
  Sim.OperationPtr.setAttributes ctx op attrs sorry

private def warmReplaceValue (ctx : Sim.IRContext OpCode) (oldValue newValue : Sim.ValuePtr) :
    Option (Sim.IRContext OpCode) :=
  Rewriter.replaceValue? ctx oldValue newValue sorry sorry sorry

private def warmEraseOp (ctx : Sim.IRContext OpCode) (op : Sim.OperationPtr) : Sim.IRContext OpCode :=
  Rewriter.eraseOp ctx op sorry sorry sorry sorry sorry

private def warmEraseBlock (ctx : Sim.IRContext OpCode) (block : Sim.BlockPtr) : Sim.IRContext OpCode :=
  Rewriter.eraseBlock ctx block sorry sorry sorry

private def warmRedirectFirstBlockUse (ctx : Sim.IRContext OpCode) (oldBlock newBlock : Sim.BlockPtr) :
    Option (Sim.IRContext OpCode) :=
  match (oldBlock.getFirstUse ctx sorry).toOption with
  | none => none
  | some use =>
    let ctx := use.removeFromCurrent ctx sorry sorry
    let ctx := use.setValue ctx newBlock sorry sorry
    some (use.insertIntoCurrent ctx sorry sorry)

/-! ## `Sim`-level primitives -/

buffed (inline := false) (def_lemma := false)
def newOpSim (ctx : Sim.IRContext OpCode) (opType : OpCode) (resultTypes : Array TypeAttr)
    (operands : Sim.ArrayValuePtr) (blockOperands : Sim.ArrayBlockPtr)
    (regions : Sim.ArrayRegionPtr) (properties : propertiesOf opType)
    (ip : Option InsertPoint) : Option (Sim.IRContext OpCode × Sim.OperationPtr) :=
  Rewriter.createOp ctx opType resultTypes operands blockOperands regions properties ip
    sorry sorry sorry sorry sorry sorry sorry

buffed (inline := false) (def_lemma := false)
def newBlockSim (ctx : Sim.IRContext OpCode) (argTypes : Array TypeAttr)
    (ip : Option BlockInsertPoint) : Option (Sim.IRContext OpCode × Sim.BlockPtr) :=
  Rewriter.createBlock ctx argTypes ip sorry sorry

buffed (inline := false) (def_lemma := false)
def attachBlockSim (ctx : Sim.IRContext OpCode) (block : Sim.BlockPtr) (ip : BlockInsertPoint) :
    Option (Sim.IRContext OpCode) :=
  Rewriter.insertBlock? ctx block ip sorry sorry sorry sorry

buffed (inline := false) (def_lemma := false)
def newRegionSim (ctx : Sim.IRContext OpCode) : Option (Sim.IRContext OpCode × Sim.RegionPtr) :=
  Rewriter.createRegion ctx

buffed (inline := false) (def_lemma := false)
def setOpAttrsSim (ctx : Sim.IRContext OpCode) (op : Sim.OperationPtr) (attrs : DictionaryAttr) :
    Option (Sim.IRContext OpCode) :=
  Sim.OperationPtr.setAttributes ctx op attrs sorry

buffed (inline := false) (def_lemma := false)
def replaceAllUsesSim (ctx : Sim.IRContext OpCode) (oldValue newValue : Sim.ValuePtr) :
    Option (Sim.IRContext OpCode) :=
  Rewriter.replaceValue? ctx oldValue newValue sorry sorry sorry

buffed (inline := false) (def_lemma := false)
def removeOpSim (ctx : Sim.IRContext OpCode) (op : Sim.OperationPtr) : Sim.IRContext OpCode :=
  Rewriter.eraseOp ctx op sorry sorry sorry sorry sorry

buffed (inline := false) (def_lemma := false)
def removeBlockSim (ctx : Sim.IRContext OpCode) (block : Sim.BlockPtr) : Sim.IRContext OpCode :=
  Rewriter.eraseBlock ctx block sorry sorry sorry

/-- Redirect the first use of `oldBlock` to `newBlock`; `none` when `oldBlock` has no use left. -/
buffed (inline := false) (def_lemma := false)
def redirectFirstBlockUseSim (ctx : Sim.IRContext OpCode) (oldBlock newBlock : Sim.BlockPtr) :
    Option (Sim.IRContext OpCode) :=
  match (oldBlock.getFirstUse ctx sorry).toOption with
  | none => none
  | some use =>
    let ctx := use.removeFromCurrent ctx sorry sorry
    let ctx := use.setValue ctx newBlock sorry sorry
    some (use.insertIntoCurrent ctx sorry sorry)

/-! ## Raw wrappers -/

/-- A fresh, empty buffered context. -/
@[inline]
def empty : IRBufContext := Sim.IRContext.emptyImpl (OpInfo := OpCode)

/-- The erased specification context passed to the generated implementations. -/
@[inline]
private def ghostCtx : Veir.IRContext OpCode := default

/-- Create an operation, optionally inserting it at `ip`. -/
@[inline]
def createOp (ctx : IRBufContext) (opType : OpCode) (resultTypes : Array TypeAttr)
    (operands : Array Value) (blockOperands : Array Block) (regions : Array Region)
    (properties : propertiesOf opType) (ip : Option InsertPoint) :
    Option (IRBufContext × Op) :=
  newOpImpl ctx ghostCtx sorry opType resultTypes
    operands default sorry sorry
    blockOperands default sorry sorry
    regions default sorry sorry
    properties ip

/-- Create a block with the given argument types, optionally inserting it at `ip`. -/
@[inline]
def createBlock (ctx : IRBufContext) (argTypes : Array TypeAttr) (ip : Option BlockInsertPoint) :
    Option (IRBufContext × Block) :=
  newBlockImpl ctx ghostCtx sorry argTypes ip

/-- Insert a detached block at `ip`. -/
@[inline]
def insertBlock (ctx : IRBufContext) (block : Block) (ip : BlockInsertPoint) :
    Option IRBufContext :=
  attachBlockImpl ctx ghostCtx sorry block default ip

/-- Create a detached region. -/
@[inline]
def createRegion (ctx : IRBufContext) : Option (IRBufContext × Region) :=
  newRegionImpl ctx ghostCtx sorry

/-- Set the attribute dictionary of an operation. -/
@[inline]
def setAttributes (ctx : IRBufContext) (op : Op) (attrs : DictionaryAttr) : Option IRBufContext :=
  setOpAttrsImpl ctx ghostCtx sorry op default attrs

/-- Replace every use of `oldValue` by `newValue`. -/
@[inline]
def replaceValue (ctx : IRBufContext) (oldValue newValue : Value) : Option IRBufContext :=
  replaceAllUsesImpl ctx ghostCtx sorry oldValue default newValue default

/-- Erase an operation that has no regions and whose results have no uses. -/
@[inline]
def eraseOp (ctx : IRBufContext) (op : Op) : IRBufContext :=
  removeOpImpl ctx ghostCtx sorry op default

/-- Erase a detached block that has no operations and no uses. -/
@[inline]
def eraseBlock (ctx : IRBufContext) (block : Block) : IRBufContext :=
  removeBlockImpl ctx ghostCtx sorry block default

/-- Redirect every use of `oldBlock` to `newBlock`. -/
partial def replaceBlockUses (ctx : IRBufContext) (oldBlock newBlock : Block) : IRBufContext :=
  match redirectFirstBlockUseImpl ctx ghostCtx sorry oldBlock default newBlock default with
  | none => ctx
  | some ctx => replaceBlockUses ctx oldBlock newBlock

/-- The `index`-th result of `op`, as a value. -/
@[inline]
def opResult (ctx : IRBufContext) (op : Op) (index : UInt64) : Value :=
  op + Buffed.OperationMPtr.computeResultOffset! ctx op index

/-- The `index`-th argument of `block`, as a value. -/
@[inline]
def blockArgument (block : Block) (index : UInt64) : Value :=
  block + BlockMPtr.computeArgumentOffset! index

/-- The type of a value. -/
@[inline]
def valueType (ctx : IRBufContext) (value : Value) : Attribute :=
  ctx.attributes[(Buffed.ValueImplMPtr.readType! ctx value).toNat]!

/-- The `Sim` view of a context, for the printer. -/
@[inline]
def toSim (ctx : IRBufContext) : Sim.IRContext OpCode := ⟨ctx, ghostCtx, sorry⟩

/-- The `Sim` view of an operation pointer, for the printer. -/
@[inline]
def toSimOp (op : Op) : Sim.OperationPtr := ⟨op, ⟨op.toNat⟩⟩

end Veir.Parser.IR

end

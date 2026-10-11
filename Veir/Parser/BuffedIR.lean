module

public import Veir.Rewriter.Basic
public import Veir.Rewriter.EraseContainers
public import Veir.Rewriter.WellFormed
public import Veir.GlobalOpInfo
public import Veir.IR.Buffed.InBounds
public import Veir.IR.DeallocLemmas
public import Veir.IR.GetSet
public import Veir.IR.InBounds

meta import Veir.IR.Buffed.Basic
import Veir.IR.Buffed.Meta

/-!
# Verified IR construction primitives for the parser

The parser builds IR in the buffered representation through the primitives of this file. Each
primitive is a `buffed` definition over the `Sim` view of the context (`Sim.IRContext OpCode`),
taking as hypotheses the well-formedness of the context and the bounds of the pointers it is
handed, and discharging every other obligation of the underlying rewriter operation itself.
Conditions that are not implied by those hypotheses (such as "this operation has no uses")
are checked at run time against the buffer, and the primitive fails (`none`) if they do not
hold. Each primitive comes with theorems stating that it preserves well-formedness and the
bounds of existing pointers, and that the pointers it returns are in bounds.

Pointers are exchanged with the parser at the specification level (`Veir.OperationPtr`,
`Veir.ValuePtr`, ...): a specification pointer is cheap data (an address and an index), and
the corresponding buffer address is recomputed from the buffer when needed, so that the bounds
invariants maintained by the parser are properties of the specification only.

## Erasure

The parser is an ordinary (monadic, partial) program, so it cannot itself be a `buffed`
definition. It therefore calls the primitives through the runtime wrappers at the end of this
file. Logically, each wrapper *is* the `buffed` base function, which computes both the buffer and
the specification; at run time it is implemented (`implemented_by`) by a call to the generated
`*Impl` function, which the compiler has checked to be independent of the erased specification
(see `ReduceArity`'s ghost check), and the specification field of the context is carried along
unchanged. The specification is thus never computed after the initial empty context, and the
only trust is the usual `implemented_by` trust together with the ghost check.
-/

@[expose] public section

namespace Veir.Parser.IR

open Veir
open Veir.Buffed

/-- The parser's IR context. -/
abbrev Ctx := Sim.IRContext OpCode
/-- An operation, at the specification level. -/
abbrev Op := Veir.OperationPtr
/-- A block, at the specification level. -/
abbrev Block := Veir.BlockPtr
/-- A region, at the specification level. -/
abbrev Region := Veir.RegionPtr
/-- A value (an operation result or a block argument), at the specification level. -/
abbrev Value := Veir.ValuePtr

/-! ## Specification pointers and their buffer addresses -/

/-- The buffer address of a value, computed from the owner's header. -/
@[inline]
def Value.address (buf : IRBufContext) : Value → ValueImplMPtr
  | .opResult r => r.op.toM + OperationMPtr.computeResultOffset! buf r.op.toM r.index.toUInt64
  | .blockArgument a => a.block.toM + BlockMPtr.computeArgumentOffset! a.index.toUInt64

/-- The `Sim` view of a value. -/
@[inline]
def Value.toSim (ctx : Ctx) (v : Value) : Sim.ValuePtr :=
  ⟨Value.address ctx.buf v, v⟩

@[simp]
theorem Value.toSim_spec (ctx : Ctx) (v : Value) : (Value.toSim ctx v).spec = v := rfl

theorem GenericPtr.toSim_inBounds {ctx : Ctx} {p : Veir.GenericPtr} (hp : p.InBounds ctx.spec) :
    (⟨p.toM ctx.spec, p⟩ : Sim.GenericPtr).InBounds ctx :=
  ⟨(Sim.GenericPtr.Sim_def _ _).mpr rfl, hp⟩

theorem numResults_lt_size {ctx : Ctx} (wf : ctx.spec.WellFormed) {op : Op}
    (hop : op.InBounds ctx.spec) : op.getNumResults! ctx.spec < UInt64.size := by
  have opWf := wf.operations op hop
  have henc := ctx.sim.encoding_op op hop
  rw [← opWf.capResults_eq_numResults, henc.numResults]
  exact UInt64.toNat_lt _

theorem numRegions_lt_size {ctx : Ctx} (wf : ctx.spec.WellFormed) {op : Op}
    (hop : op.InBounds ctx.spec) : op.getNumRegions! ctx.spec < UInt64.size := by
  have opWf := wf.operations op hop
  have henc := ctx.sim.encoding_op op hop
  rw [← opWf.capRegions_eq_numRegions, henc.numRegions]
  exact UInt64.toNat_lt _

theorem numArguments_lt_size {ctx : Ctx} (wf : ctx.spec.WellFormed) {block : Block}
    (hb : block.InBounds ctx.spec) : block.getNumArguments! ctx.spec < UInt64.size := by
  have bWf := wf.blocks block hb
  have henc := ctx.sim.encoding_block block hb
  rw [← bWf.capBlockArguments_eq_numBlockArguments, henc.numArguments]
  exact UInt64.toNat_lt _

theorem lt_size_of_lt_2_32 {n : Nat} (h : n < 2^32) : n < UInt64.size :=
  Nat.lt_of_lt_of_le h (by decide)

theorem mod_numBits_eq {i : Nat} (h : i < 2^32) : i % 2 ^ System.Platform.numBits = i := by
  apply Nat.mod_eq_of_lt
  rcases System.Platform.numBits_eq with h' | h' <;> rw [h'] <;> omega

theorem Value.toSim_inBounds {ctx : Ctx} (wf : ctx.spec.WellFormed) {v : Value}
    (hv : v.InBounds ctx.spec) : (Value.toSim ctx v).InBounds ctx := by
  refine ⟨?_, hv⟩
  cases v with
  | opResult r =>
    have hr : r.InBounds ctx.spec := by simpa using hv
    obtain ⟨hop, hlt⟩ := hr
    have hidx : r.index < r.op.getNumResults! ctx.spec := by
      simp only [Veir.OperationPtr.getNumResults!, Veir.OperationPtr.get!_eq_get hop]
      exact hlt
    have hsmall : r.index < UInt64.size := by
      have := numResults_lt_size wf hop
      omega
    have hidx' : r.index.toUInt64.toNat = r.index := UInt64.toNat_ofNat_of_lt' hsmall
    have := Sim.OperationPtr.getResult_toM (ctx := ctx) r.op.toSim
      ((Veir.OperationPtr.toSim_inBounds_iff_inBounds r.op).mpr hop) r.index.toUInt64
      (by rw [hidx']; exact hidx)
    rw [hidx'] at this
    rw [Sim.ValuePtr.Sim_def]
    exact this
  | blockArgument a =>
    have ha : a.InBounds ctx.spec := by simpa using hv
    obtain ⟨hb, hlt⟩ := ha
    have hidx : a.index < a.block.getNumArguments ctx.spec hb := by
      simpa [Veir.BlockPtr.getNumArguments] using hlt
    have hsmall : a.index < UInt64.size := by
      have h1 := numArguments_lt_size wf hb
      have h2 : a.block.getNumArguments! ctx.spec = a.block.getNumArguments ctx.spec hb := by
        simp [Veir.BlockPtr.getNumArguments!, Veir.BlockPtr.getNumArguments,
          Veir.BlockPtr.get!_eq_get hb]
      omega
    have hidx' : a.index.toUInt64.toNat = a.index := UInt64.toNat_ofNat_of_lt' hsmall
    have := Sim.BlockPtr.getArgument_toM (ctx := ctx) a.block.toSim
      ((Veir.BlockPtr.toSim_inBounds_iff_inBounds a.block).mpr hb) a.index.toUInt64
      (by rw [hidx']; exact hidx)
    rw [hidx'] at this
    rw [Sim.ValuePtr.Sim_def]
    exact this

/-- The `Sim` view of an array of values. -/
@[inline]
def valuesToSim (ctx : Ctx) (vs : Array Value) (h : vs.size < 2^32) : Sim.ArrayValuePtr :=
  ⟨vs.map (Value.address ctx.buf), vs, by simp, by simpa using h⟩

theorem valuesToSim_inBounds {ctx : Ctx} (wf : ctx.spec.WellFormed) {vs : Array Value}
    (h : vs.size < 2^32) (hvs : ∀ v ∈ vs, v.InBounds ctx.spec) :
    (valuesToSim ctx vs h).InBounds ctx := by
  intro i hi
  have hi : i < vs.size := by simpa [valuesToSim, Sim.ArrayValuePtr.size] using hi
  have hi' : i.toUInt64.toNat = i := UInt64.toNat_ofNat_of_lt' (lt_size_of_lt_2_32 (by omega))
  have hiN := mod_numBits_eq (i := i) (by omega)
  have : (valuesToSim ctx vs h).uget i.toUInt64 = Value.toSim ctx vs[i] := by
    simp [valuesToSim, Sim.ArrayValuePtr.uget, Array.uget, Value.toSim, hi', hiN]
  rw [this]
  exact Value.toSim_inBounds wf (hvs _ (Array.getElem_mem hi))

/-- The `Sim` view of an array of blocks. -/
@[inline]
def blocksToSim (bs : Array Block) (h : bs.size < 2^32) : Sim.ArrayBlockPtr :=
  ⟨bs.map Veir.BlockPtr.toM, bs, by simp, by simpa using h⟩

theorem blocksToSim_inBounds {ctx : Ctx} {bs : Array Block}
    (h : bs.size < 2^32) (hbs : ∀ b ∈ bs, b.InBounds ctx.spec) :
    (blocksToSim bs h).InBounds ctx := by
  intro i hi
  have hi : i < bs.size := by simpa [blocksToSim, Sim.ArrayBlockPtr.size] using hi
  have hi' : i.toUInt64.toNat = i := UInt64.toNat_ofNat_of_lt' (lt_size_of_lt_2_32 (by omega))
  have hiN := mod_numBits_eq (i := i) (by omega)
  have : (blocksToSim bs h).uget i.toUInt64 = bs[i].toSim := by
    simp [blocksToSim, Sim.ArrayBlockPtr.uget, Array.uget, Veir.BlockPtr.toSim, hi', hiN]
  rw [this, Veir.BlockPtr.toSim_inBounds_iff_inBounds]
  exact hbs _ (Array.getElem_mem hi)

/-- The `Sim` view of an array of regions. -/
@[inline]
def regionsToSim (rs : Array Region) (h : rs.size < 2^32) : Sim.ArrayRegionPtr :=
  ⟨rs.map Veir.RegionPtr.toM, rs, by simp, by simpa using h⟩

theorem regionsToSim_inBounds {ctx : Ctx} {rs : Array Region}
    (h : rs.size < 2^32) (hrs : ∀ r ∈ rs, r.InBounds ctx.spec) :
    (regionsToSim rs h).InBounds ctx := by
  intro i hi
  have hi : i < rs.size := by simpa [regionsToSim, Sim.ArrayRegionPtr.size] using hi
  have hi' : i.toUInt64.toNat = i := UInt64.toNat_ofNat_of_lt' (lt_size_of_lt_2_32 (by omega))
  have hiN := mod_numBits_eq (i := i) (by omega)
  have : (regionsToSim rs h).uget i.toUInt64 = rs[i].toSim := by
    simp [regionsToSim, Sim.ArrayRegionPtr.uget, Array.uget, Veir.RegionPtr.toSim, hi', hiN]
  rw [this, Veir.RegionPtr.toSim_inBounds_iff_inBounds]
  exact hrs _ (Array.getElem_mem hi)

/-- An in-bounds insertion point is representable. -/
theorem InsertPoint.isRepr_of_inBounds {ctx : Ctx} {ip : InsertPoint}
    (h : ip.InBounds ctx.spec) : ip.IsRepr := by
  cases ip with
  | before op => exact ctx.sim.repr.operations op h
  | atEnd bl => exact ctx.sim.repr.blocks bl h

theorem InsertPoint.maybe_isRepr_of_inBounds {ctx : Ctx} {ip : Option InsertPoint}
    (h : ip.maybe InsertPoint.InBounds ctx.spec) : ip.maybe₁ InsertPoint.IsRepr := by
  rw [Option.maybe₁_def]
  intro z hz
  exact InsertPoint.isRepr_of_inBounds ((Option.maybe_def _ _ _).mp h z hz)

theorem BlockInsertPoint.isRepr_of_inBounds {ctx : Ctx} {ip : BlockInsertPoint}
    (h : ip.InBounds ctx.spec) : ip.IsRepr := by
  cases ip with
  | before bl => exact ctx.sim.repr.blocks bl h
  | atEnd rg => exact ctx.sim.repr.regions rg h

theorem BlockInsertPoint.maybe_isRepr_of_inBounds {ctx : Ctx} {ip : Option BlockInsertPoint}
    (h : ip.maybe BlockInsertPoint.InBounds ctx.spec) : ip.maybe₁ BlockInsertPoint.IsRepr := by
  rw [Option.maybe₁_def]
  intro z hz
  exact BlockInsertPoint.isRepr_of_inBounds ((Option.maybe_def _ _ _).mp h z hz)

/-! ## Reading the buffer -/

/-- The number of results of an operation. -/
@[inline]
def numResults (ctx : Ctx) (op : Op) : UInt64 :=
  Sim.OperationPtr.getNumResults! ctx op.toSim

theorem numResults_spec {ctx : Ctx} (wf : ctx.spec.WellFormed) {op : Op}
    (hop : op.InBounds ctx.spec) : (numResults ctx op).toNat = op.getNumResults! ctx.spec := by
  have hib := (Veir.OperationPtr.toSim_inBounds_iff_inBounds (ctx := ctx) op).mpr hop
  have h1 := Sim.OperationPtr.getNumResults!_spec_of_wf ctx op.toSim (ib := hib) wf
  unfold numResults
  rw [h1]
  exact UInt64.toNat_ofNat_of_lt' (numResults_lt_size wf hop)

/-- The number of arguments of a block. -/
@[inline]
def numArguments (ctx : Ctx) (block : Block) : UInt64 :=
  Sim.BlockPtr.getNumArguments! ctx block.toSim

theorem numArguments_spec {ctx : Ctx} (wf : ctx.spec.WellFormed) {block : Block}
    (hb : block.InBounds ctx.spec) :
    (numArguments ctx block).toNat = block.getNumArguments! ctx.spec := by
  have hib := (Veir.BlockPtr.toSim_inBounds_iff_inBounds (ctx := ctx) block).mpr hb
  have h1 := Sim.BlockPtr.getNumArguments_spec ctx block.toSim hib
  rw [Sim.BlockPtr.getNumArguments_eq_getNumArguments!] at h1
  unfold numArguments
  rw [h1]
  exact (wf.blocks block hb).capBlockArguments_eq_numBlockArguments

/-- The type of a value. -/
@[inline]
def valueType (ctx : Ctx) (v : Value) : Attribute :=
  ctx.buf.attributes[(ValueImplMPtr.readType! ctx.buf (Value.address ctx.buf v)).toNat]!

theorem opResult_inBounds {ctx : Ctx} (wf : ctx.spec.WellFormed) {op : Op}
    (hop : op.InBounds ctx.spec) {i : Nat} (hi : i < (numResults ctx op).toNat) :
    (Veir.ValuePtr.opResult ⟨op, i⟩).InBounds ctx.spec := by
  rw [numResults_spec wf hop] at hi
  simp only [Veir.ValuePtr.inBounds_opResult, Veir.OpResultPtr.InBounds]
  refine ⟨hop, ?_⟩
  rw [← Veir.OperationPtr.get!_eq_get hop]
  exact hi

theorem blockArgument_inBounds {ctx : Ctx} (wf : ctx.spec.WellFormed) {block : Block}
    (hb : block.InBounds ctx.spec) {i : Nat} (hi : i < (numArguments ctx block).toNat) :
    (Veir.ValuePtr.blockArgument ⟨block, i⟩).InBounds ctx.spec := by
  rw [numArguments_spec wf hb] at hi
  simp only [Veir.ValuePtr.inBounds_blockArg, Veir.BlockArgumentPtr.InBounds]
  refine ⟨hb, ?_⟩
  rw [← Veir.BlockPtr.get!_eq_get hb]
  exact hi

/-! ## Specialization warm-up

The library's rewriter implementations are generic in the opcode type. When they are first used
at `OpCode` in this module, the compiler creates specialized copies of them. If that happens in
the same compilation batch as one of the `buffed` primitives below, the ghost-elimination check
of `ReduceArity` runs before the follow-up simplification removes the erased arguments from the
call sites, and compilation fails. These plain definitions trigger (and cache) the
specializations first; they are otherwise unused. -/

private def warmRemoveFromCurrent (ctx : Ctx) (operand : Sim.OpOperandPtr)
    (h₁ : operand.InBounds ctx) (h₂ : ctx.spec.FieldsInBounds) : Ctx :=
  operand.removeFromCurrent ctx h₁ h₂

private def warmAllocOp (ctx : Ctx) (opType : OpCode) (properties : propertiesOf opType)
    (nr no nb ng : UInt64) (h₁ : nr.toNat ≤ countCard) (h₂ : no.toNat ≤ countCard)
    (h₃ : nb.toNat ≤ countCard) (h₄ : ng.toNat ≤ countCard) :
    Option (Sim.OperationPtr × Ctx) :=
  Sim.OperationPtr.allocRecycled ctx opType properties nr no nb ng h₁ h₂ h₃ h₄

private def warmDetachOperands (ctx : Ctx) (op : Sim.OperationPtr) (h₁ : ctx.spec.FieldsInBounds)
    (h₂ : op.InBounds ctx) (h₃ : (op.spec.get! ctx.spec).capOperands = op.spec.getNumOperands! ctx.spec) : Ctx :=
  Rewriter.detachOperands ctx op h₁ h₂ h₃

private def warmDetachBlockOperands (ctx : Ctx) (op : Sim.OperationPtr) (h₁ : ctx.spec.FieldsInBounds)
    (h₂ : op.InBounds ctx) (h₃ : (op.spec.get! ctx.spec).capBlockOperands = op.spec.getNumSuccessors! ctx.spec) : Ctx :=
  Rewriter.detachBlockOperands ctx op h₁ h₂ h₃

private def warmDetachOpIfAttached (ctx : Ctx) (op : Sim.OperationPtr) (h₁ : ctx.spec.FieldsInBounds)
    (h₂ : op.InBounds ctx) : Ctx :=
  Rewriter.detachOpIfAttached ctx op h₁ h₂

private def warmDealloc (ctx : Ctx) (op : Sim.OperationPtr) (h₁ : op.InBounds ctx)
    (h₂ : (op.spec.dealloc ctx.spec h₁.ib).FieldsInBounds) : Ctx :=
  Sim.OperationPtr.dealloc ctx op h₁ h₂

private def warmCreateOp (ctx : Ctx) (opType : OpCode) (resultTypes : Array TypeAttr)
    (operands : Sim.ArrayValuePtr) (blockOperands : Sim.ArrayBlockPtr)
    (regions : Sim.ArrayRegionPtr) (properties : propertiesOf opType)
    (ip : Option InsertPoint) (h₁ : operands.InBounds ctx) (h₂ : blockOperands.InBounds ctx)
    (h₃ : regions.InBounds ctx) (h₄ : ip.maybe InsertPoint.InBounds ctx.spec)
    (h₅ : ip.maybe₁ InsertPoint.IsRepr) (h₆ : resultTypes.size < 2^32)
    (h₇ : ctx.spec.FieldsInBounds) : Option (Ctx × Sim.OperationPtr) :=
  Rewriter.createOp ctx opType resultTypes operands blockOperands regions properties ip
    h₁ h₂ h₃ h₄ h₅ h₆ h₇

private def warmCreateBlock (ctx : Ctx) (argTypes : Array TypeAttr)
    (ip : Option BlockInsertPoint) (h₁ : ip.maybe BlockInsertPoint.InBounds ctx.spec)
    (h₂ : ip.maybe₁ BlockInsertPoint.IsRepr) : Option (Ctx × Sim.BlockPtr) :=
  Rewriter.createBlock ctx argTypes ip h₁ h₂

private def warmInsertBlock (ctx : Ctx) (block : Sim.BlockPtr) (ip : BlockInsertPoint)
    (h₁ : block.InBounds ctx) (h₂ : ip.InBounds ctx.spec) (h₃ : ip.IsRepr)
    (h₄ : ctx.spec.FieldsInBounds) : Option Ctx :=
  Rewriter.insertBlock? ctx block ip h₁ h₂ h₃ h₄

private def warmCreateRegion (ctx : Ctx) : Option (Ctx × Sim.RegionPtr) :=
  Rewriter.createRegion ctx

private def warmSetAttributes (ctx : Ctx) (op : Sim.OperationPtr) (attrs : DictionaryAttr)
    (h₁ : op.InBounds ctx) : Option Ctx :=
  Sim.OperationPtr.setAttributes ctx op attrs h₁

private def warmReplaceValue (ctx : Ctx) (oldValue newValue : Sim.ValuePtr) (h₁ : oldValue.InBounds ctx)
    (h₂ : newValue.InBounds ctx) (h₃ : ctx.spec.FieldsInBounds) :
    Option Ctx :=
  Rewriter.replaceValue? ctx oldValue newValue h₁ h₂ h₃

private def warmEraseOp (ctx : Ctx) (op : Sim.OperationPtr) (h₁ : ctx.spec.FieldsInBounds)
    (h₂ : op.InBounds ctx) (h₃ : (op.spec.get! ctx.spec).capOperands = op.spec.getNumOperands! ctx.spec)
    (h₄ : (op.spec.get! ctx.spec).capBlockOperands = op.spec.getNumSuccessors! ctx.spec)
    (h₅ : Rewriter.EraseOpDeallocFieldsInBounds ctx op) : Ctx :=
  Rewriter.eraseOp ctx op h₁ h₂ h₃ h₄ h₅

/-! ## `Sim`-level primitives -/

/-- Create an operation, optionally inserting it at `ip`. Fails if any of the arrays is too
large for the buffer encoding. -/
buffed (inline := false)
def newOpSim (ctx : Ctx) (opType : OpCode) (resultTypes : Array TypeAttr)
    (operands : Array Value) (blockOperands : Array Block) (regions : Array Region)
    (properties : propertiesOf opType) (ip : Option InsertPoint)
    (wf : ctx.spec.WellFormed)
    (hoper : ∀ v ∈ operands, v.InBounds ctx.spec)
    (hblocks : ∀ b ∈ blockOperands, b.InBounds ctx.spec)
    (hregions : ∀ r ∈ regions, r.InBounds ctx.spec)
    (hins : ip.maybe InsertPoint.InBounds ctx.spec) :
    Option (Ctx × Sim.OperationPtr) :=
  if h : resultTypes.size < 2^32 ∧ operands.size < 2^32 ∧ blockOperands.size < 2^32 ∧
      regions.size < 2^32 then
    Rewriter.createOp ctx opType resultTypes (valuesToSim ctx operands h.2.1)
      (blocksToSim blockOperands h.2.2.1) (regionsToSim regions h.2.2.2) properties ip
      (valuesToSim_inBounds wf h.2.1 hoper) (blocksToSim_inBounds h.2.2.1 hblocks)
      (regionsToSim_inBounds h.2.2.2 hregions) hins (InsertPoint.maybe_isRepr_of_inBounds hins)
      h.1 wf.inBounds
  else
    none

theorem newOp_wellFormed {ctx ctx' : Ctx} {opType resultTypes operands blockOperands regions
    properties ip wf hoper hblocks hregions hins} {op : Sim.OperationPtr}
    (h : newOp ctx opType resultTypes operands blockOperands regions properties ip wf hoper
      hblocks hregions hins = some (ctx', op)) :
    ctx'.spec.WellFormed := by
  simp only [newOp_def, newOpSim] at h
  split at h
  · exact Rewriter.createOp_preserves_wellFormed wf h
  · contradiction

theorem newOp_inBounds_mono {ctx ctx' : Ctx} {opType resultTypes operands blockOperands regions
    properties ip wf hoper hblocks hregions hins} {op : Sim.OperationPtr}
    (h : newOp ctx opType resultTypes operands blockOperands regions properties ip wf hoper
      hblocks hregions hins = some (ctx', op))
    (p : Veir.GenericPtr) : p.InBounds ctx.spec → p.InBounds ctx'.spec := by
  simp only [newOp_def, newOpSim] at h
  split at h
  · exact Rewriter.createOp_inBounds_mono p h
  · contradiction

theorem newOp_new_inBounds {ctx ctx' : Ctx} {opType resultTypes operands blockOperands regions
    properties ip wf hoper hblocks hregions hins} {op : Sim.OperationPtr}
    (h : newOp ctx opType resultTypes operands blockOperands regions properties ip wf hoper
      hblocks hregions hins = some (ctx', op)) :
    op.spec.InBounds ctx'.spec := by
  simp only [newOp_def, newOpSim] at h
  split at h
  · exact (Rewriter.createOp_new_inBounds op h).ib
  · contradiction

theorem newOp_new_not_inBounds {ctx ctx' : Ctx} {opType resultTypes operands blockOperands
    regions properties ip wf hoper hblocks hregions hins} {op : Sim.OperationPtr}
    (h : newOp ctx opType resultTypes operands blockOperands regions properties ip wf hoper
      hblocks hregions hins = some (ctx', op)) :
    ¬ op.spec.InBounds ctx.spec := by
  simp only [newOp_def, newOpSim] at h
  split at h
  · exact Rewriter.createOp_new_not_inBounds op h
  · contradiction

/-- Create a block with the given argument types, optionally inserting it at `ip`. -/
buffed (inline := false)
def newBlockSim (ctx : Ctx) (argTypes : Array TypeAttr) (ip : Option BlockInsertPoint)
    (_wf : ctx.spec.WellFormed) (hip : ip.maybe BlockInsertPoint.InBounds ctx.spec) :
    Option (Ctx × Sim.BlockPtr) :=
  Rewriter.createBlock ctx argTypes ip hip (BlockInsertPoint.maybe_isRepr_of_inBounds hip)

theorem newBlock_wellFormed {ctx ctx' : Ctx} {argTypes ip wf hip} {block : Sim.BlockPtr}
    (h : newBlock ctx argTypes ip wf hip = some (ctx', block)) : ctx'.spec.WellFormed := by
  simp only [newBlock_def, newBlockSim] at h
  exact Rewriter.createBlock_preserves_wellFormed wf h

theorem newBlock_inBounds_mono {ctx ctx' : Ctx} {argTypes ip wf hip} {block : Sim.BlockPtr}
    (h : newBlock ctx argTypes ip wf hip = some (ctx', block))
    (p : Veir.GenericPtr) : p.InBounds ctx.spec → p.InBounds ctx'.spec := by
  simp only [newBlock_def, newBlockSim] at h
  intro hp
  exact (Rewriter.createBlock_inBounds_mono _ h (GenericPtr.toSim_inBounds hp)).ib

theorem newBlock_new_inBounds {ctx ctx' : Ctx} {argTypes ip wf hip} {block : Sim.BlockPtr}
    (h : newBlock ctx argTypes ip wf hip = some (ctx', block)) : block.spec.InBounds ctx'.spec := by
  simp only [newBlock_def, newBlockSim, Rewriter.createBlock_def, Rewriter.createBlockSim] at h
  split at h
  case isFalse => contradiction
  case isTrue =>
    split at h
    · contradiction
    · rename_i bl ctx₁ halloc
      have hb₁ : bl.InBounds ctx₁ := by grind
      split at h
      · contradiction
      · rename_i ctx₂ hinit
        have hb₂ : bl.InBounds ctx₂ := (Sim.GenericPtr.iff_block bl).mp
          (Rewriter.initBlockArguments_inBounds_mono _ hinit ((Sim.GenericPtr.iff_block bl).mpr hb₁))
        split at h
        · simp only [Option.bind_eq_bind, Option.bind] at h
          split at h
          · contradiction
          · rename_i ctx₃ hins
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ((Rewriter.insertBlock?_inBounds (Sim.GenericPtr.fromBlock bl) hins).mp
              ((Sim.GenericPtr.iff_block bl).mpr hb₂)).ib
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact hb₂.ib

/-- Insert a detached block at `ip`. -/
buffed (inline := false)
def attachBlockSim (ctx : Ctx) (block : Block) (ip : BlockInsertPoint)
    (wf : ctx.spec.WellFormed) (hb : block.InBounds ctx.spec) (hip : ip.InBounds ctx.spec) :
    Option Ctx :=
  Rewriter.insertBlock? ctx block.toSim ip
    ((Veir.BlockPtr.toSim_inBounds_iff_inBounds block).mpr hb) hip
    (BlockInsertPoint.isRepr_of_inBounds hip) wf.inBounds

theorem attachBlock_wellFormed {ctx ctx' : Ctx} {block ip wf hb hip}
    (h : attachBlock ctx block ip wf hb hip = some ctx') : ctx'.spec.WellFormed := by
  simp only [attachBlock_def, attachBlockSim] at h
  exact Rewriter.insertBlock?_WellFormed ctx _ ip _ hip _ _ wf h

theorem attachBlock_inBounds_mono {ctx ctx' : Ctx} {block ip wf hb hip}
    (h : attachBlock ctx block ip wf hb hip = some ctx')
    (p : Veir.GenericPtr) : p.InBounds ctx.spec → p.InBounds ctx'.spec := by
  simp only [attachBlock_def, attachBlockSim] at h
  intro hp
  exact ((Rewriter.insertBlock?_inBounds _ h).mp (GenericPtr.toSim_inBounds hp)).ib

/-- Create a detached region. -/
buffed (inline := false)
def newRegionSim (ctx : Ctx) : Option (Ctx × Sim.RegionPtr) :=
  Rewriter.createRegion ctx

theorem newRegion_wellFormed {ctx ctx' : Ctx} {region : Sim.RegionPtr}
    (wf : ctx.spec.WellFormed) (h : newRegion ctx = some (ctx', region)) :
    ctx'.spec.WellFormed := by
  simp only [newRegion_def, newRegionSim] at h
  exact Rewriter.createRegion_wellFormed wf h

theorem newRegion_inBounds_mono {ctx ctx' : Ctx} {region : Sim.RegionPtr}
    (h : newRegion ctx = some (ctx', region))
    (p : Veir.GenericPtr) : p.InBounds ctx.spec → p.InBounds ctx'.spec := by
  simp only [newRegion_def, newRegionSim] at h
  intro hp
  exact (Rewriter.createRegion_genericPtr_mono p h).mpr (Or.inl hp)

theorem newRegion_new_inBounds {ctx ctx' : Ctx} {region : Sim.RegionPtr}
    (h : newRegion ctx = some (ctx', region)) : region.spec.InBounds ctx'.spec := by
  simp only [newRegion_def, newRegionSim] at h
  exact (Rewriter.createRegion_new_inBounds h).ib

/-- Set the attribute dictionary of an operation. -/
buffed (inline := false)
def setOpAttrsSim (ctx : Ctx) (op : Op) (attrs : DictionaryAttr)
    (_wf : ctx.spec.WellFormed) (hop : op.InBounds ctx.spec) : Option Ctx :=
  Sim.OperationPtr.setAttributes ctx op.toSim attrs
    ((Veir.OperationPtr.toSim_inBounds_iff_inBounds op).mpr hop)

theorem setOpAttrs_spec {ctx ctx' : Ctx} {op attrs wf hop}
    (h : setOpAttrs ctx op attrs wf hop = some ctx') :
    ctx'.spec = op.setAttributes ctx.spec attrs hop := by
  simp only [setOpAttrs_def, setOpAttrsSim, Sim.OperationPtr.setAttributes_def,
    Sim.OperationPtr.setAttributesSim] at h
  split at h
  · contradiction
  · simp only [Option.some.injEq] at h
    subst h
    rfl

/-- Setting attributes preserves well-formedness (copied from the library's
`Veir.Rewriter.WellFormed.Operation`, whose module does not currently build). -/
private theorem setAttributes_wellFormed' (ctx : Veir.IRContext OpCode) (op : Op)
    (hctx : ctx.WellFormed) (hop : op.InBounds ctx) (newAttrs : DictionaryAttr) :
    (op.setAttributes ctx newAttrs hop).WellFormed := by
  have ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ := hctx
  constructor
  · grind
  · intro val hval
    have ⟨array, harray⟩ := h₂ val (by grind)
    exists array
    simp only [Std.ExtHashSet.filter_empty] at harray ⊢
    apply ValuePtr.DefUse.unchanged harray (ctx' := op.setAttributes ctx newAttrs hop) <;> grind
  · intro blk hblk
    have ⟨array, harray⟩ := h₃ blk (by grind)
    exists array
    simp only [Std.ExtHashSet.filter_empty] at harray ⊢
    apply BlockPtr.DefUse.unchanged harray (ctx' := op.setAttributes ctx newAttrs hop) <;> grind
  · intro blk hblk
    have ⟨array, harray⟩ := h₄ blk (by grind)
    exists array
    apply BlockPtr.OpChain_unchanged harray (ctx' := op.setAttributes ctx newAttrs hop) <;> grind
  · intro reg hreg
    have ⟨array, harray⟩ := h₅ reg (by grind)
    exists array
    apply RegionPtr.blockChain_unchanged harray (ctx' := op.setAttributes ctx newAttrs hop) <;> grind
  · intro op' hop'
    have h_wf := h₆ op' (by grind)
    apply OperationPtr.WellFormed_unchanged h_wf (ctx' := op.setAttributes ctx newAttrs hop) <;> grind
  · intro blk hblk
    have h_wf := h₇ blk (by grind)
    apply BlockPtr.WellFormed_unchanged h_wf (ctx' := op.setAttributes ctx newAttrs hop) <;> grind
  · intro reg hreg
    have h_wf := h₈ reg (by grind)
    apply RegionPtr.WellFormed_unchanged h_wf (ctx' := op.setAttributes ctx newAttrs hop) <;> grind

theorem setOpAttrs_wellFormed {ctx ctx' : Ctx} {op attrs wf hop}
    (h : setOpAttrs ctx op attrs wf hop = some ctx') : ctx'.spec.WellFormed := by
  rw [setOpAttrs_spec h]
  exact setAttributes_wellFormed' ctx.spec op wf hop attrs

theorem setOpAttrs_inBounds_mono {ctx ctx' : Ctx} {op attrs wf hop}
    (h : setOpAttrs ctx op attrs wf hop = some ctx')
    (p : Veir.GenericPtr) : p.InBounds ctx.spec → p.InBounds ctx'.spec := by
  rw [setOpAttrs_spec h]
  exact (Veir.OperationPtr.setAttributes_genericPtr_mono hop p).mpr

/-- Replace every use of `oldValue` by `newValue`. -/
buffed (inline := false)
def replaceAllUsesSim (ctx : Ctx) (oldValue newValue : Value)
    (wf : ctx.spec.WellFormed) (hold : oldValue.InBounds ctx.spec)
    (hnew : newValue.InBounds ctx.spec) : Option Ctx :=
  Rewriter.replaceValue? ctx (Value.toSim ctx oldValue) (Value.toSim ctx newValue)
    (Value.toSim_inBounds wf hold) (Value.toSim_inBounds wf hnew) wf.inBounds

theorem replaceAllUses_wellFormed {ctx ctx' : Ctx} {oldValue newValue wf hold hnew}
    (h : replaceAllUses ctx oldValue newValue wf hold hnew = some ctx') :
    ctx'.spec.WellFormed := by
  simp only [replaceAllUses_def, replaceAllUsesSim] at h
  exact Rewriter.replaceValue?_WellFormed _ _ _ _ _ wf h

theorem replaceAllUses_inBounds_mono {ctx ctx' : Ctx} {oldValue newValue wf hold hnew}
    (h : replaceAllUses ctx oldValue newValue wf hold hnew = some ctx')
    (p : Veir.GenericPtr) : p.InBounds ctx.spec → p.InBounds ctx'.spec := by
  simp only [replaceAllUses_def, replaceAllUsesSim] at h
  exact (Rewriter.replaceValue?_veir_inBounds p h).mp

theorem replaceAllUses_noUses {ctx ctx' : Ctx} {oldValue newValue wf hold hnew}
    (h : replaceAllUses ctx oldValue newValue wf hold hnew = some ctx') :
    oldValue.hasUses! ctx'.spec = false := by
  simp only [replaceAllUses_def, replaceAllUsesSim] at h
  exact ValuePtr.hasUses!_replaceValue?_oldValue _ _ _ _ _ h

/-! ### Checking that an operation is unused -/

/-- Whether every result of the operation at `op` from index `i` on has no use, reading the
buffer only (`n` is the number of results). -/
def resultsUnusedRaw (buf : IRBufContext) (op : OperationMPtr) (n : Nat) (i : Nat) : Bool :=
  if i < n then
    if OpResultMPtr.readFirstUse! buf (op + OperationMPtr.computeResultOffset! buf op i.toUInt64)
        = OpOperandOPtr.none then
      resultsUnusedRaw buf op n (i + 1)
    else
      false
  else
    true
termination_by n - i

theorem getResultPtr_inBounds {ctx : Ctx} (op : Sim.OperationPtr) (hop : op.InBounds ctx)
    (i : UInt64) (h₂ : i.toNat < op.spec.getNumResults! ctx.spec) :
    (op.getResultPtr ctx i hop).InBounds ctx := by
  rw [Sim.OperationPtr.getResultPtr_eq_getResultPtr!]
  exact ⟨(Sim.OpResultPtr.Sim_def _ _).mpr (Sim.OperationPtr.getResult_toM op hop i h₂),
    Sim.OperationPtr.getResult_veir_inBounds op hop i h₂⟩

theorem resultsUnusedRaw_spec {ctx : Ctx} (wf : ctx.spec.WellFormed) {op : Sim.OperationPtr}
    (hop : op.InBounds ctx) {n : Nat} (hn : n = op.spec.getNumResults! ctx.spec) {i : Nat}
    (h : resultsUnusedRaw ctx.buf op.impl n i = true) :
    ∀ j, i ≤ j → j < n →
      (Veir.ValuePtr.opResult (op.spec.getResult j)).hasUses! ctx.spec = false := by
  fun_induction resultsUnusedRaw ctx.buf op.impl n i with
  | case1 i hi hnone ih =>
    intro j hij hj
    rcases Nat.eq_or_lt_of_le hij with heq | hlt
    · subst heq
      have hsmall : i < UInt64.size := by
        have := numResults_lt_size wf hop.ib
        omega
      have hi' : i.toUInt64.toNat = i := UInt64.toNat_ofNat_of_lt' hsmall
      have hiN : i.toUInt64.toNat < op.spec.getNumResults! ctx.spec := by rw [hi']; omega
      have hres := getResultPtr_inBounds op hop i.toUInt64 hiN
      have hres_spec : (op.getResultPtr ctx i.toUInt64 hop).spec = op.spec.getResult i := by
        rw [Sim.OperationPtr.getResultPtr_eq_getResultPtr!, Sim.OperationPtr.getResultPtr!_def,
          Sim.OperationPtr.getResultPtr!Sim, hi']
      have hsim := Sim.OpResultPtr.getFirstUse_sim ctx _ hres
      have hib : (Sim.OpResultPtr.getFirstUse ctx _ hres).InBounds ctx := by
        refine ⟨hsim, ?_⟩
        rw [Sim.OpResultPtr.getFirstUse_spec]
        have := (wf.inBounds.operations_inBounds op.spec hop.ib).results_inBounds _
          hres.ib (by rw [hres_spec]; rfl)
        rw [Veir.OpResultPtr.get!_eq_get hres.ib] at this
        exact this.firstUse_inBounds
      have himpl : (Sim.OpResultPtr.getFirstUse ctx _ hres).impl = OpOperandOPtr.none := by
        rw [Sim.OpResultPtr.getFirstUse_eq_getFirstUse!, Sim.OpResultPtr.getFirstUse!_def,
          Sim.OpResultPtr.getFirstUse!Sim, Sim.OperationPtr.getResultPtr_eq_getResultPtr!,
          Sim.OperationPtr.getResultPtr!_def, Sim.OperationPtr.getResultPtr!Sim]
        exact hnone
      have hnone' : (Sim.OpResultPtr.getFirstUse ctx _ hres).toOption = none := by
        simp [Sim.OptionOpOperandPtr.toOption, himpl]
      have hspec := (Sim.OptionOpOperandPtr.toOption_none_iff_spec_none hib).mp hnone'
      rw [Sim.OpResultPtr.getFirstUse_spec, ← Veir.OpResultPtr.get!_eq_get hres.ib,
        hres_spec] at hspec
      simp only [Veir.ValuePtr.hasUses!_def, Veir.ValuePtr.getFirstUse!]
      rw [hspec]
      rfl
    · exact ih h j hlt hj
  | case2 i hi hsome => simp at h
  | case3 i hi =>
    intro j hij hj
    omega

/-- The number of regions of an operation. -/
@[inline]
def numRegions (ctx : Ctx) (op : Op) : UInt64 :=
  Sim.OperationPtr.getNumRegions! ctx op.toSim

theorem numRegions_spec {ctx : Ctx} (wf : ctx.spec.WellFormed) {op : Op}
    (hop : op.InBounds ctx.spec) : (numRegions ctx op).toNat = op.getNumRegions! ctx.spec := by
  have hib := (Veir.OperationPtr.toSim_inBounds_iff_inBounds (ctx := ctx) op).mpr hop
  have h1 := Sim.OperationPtr.getNumRegions!_spec_of_wf ctx op.toSim (ib := hib) wf
  unfold numRegions
  rw [h1]
  exact UInt64.toNat_ofNat_of_lt' (numRegions_lt_size wf hop)

theorem noRegions_of_check {ctx : Ctx} (wf : ctx.spec.WellFormed) {op : Op}
    (hop : op.InBounds ctx.spec) (h : numRegions ctx op = 0) : op.getNumRegions! ctx.spec = 0 := by
  rw [← numRegions_spec wf hop, h]
  rfl

theorem noUses_of_check {ctx : Ctx} (wf : ctx.spec.WellFormed) {op : Op}
    (hop : op.InBounds ctx.spec)
    (h : resultsUnusedRaw ctx.buf op.toM (numResults ctx op).toNat 0 = true) :
    op.hasUses! ctx.spec = false := by
  rw [Veir.OperationPtr.hasUses!_eq_false_iff_hasUses!_getResult_eq_false]
  intro j hj
  have hib := (Veir.OperationPtr.toSim_inBounds_iff_inBounds (ctx := ctx) op).mpr hop
  have hn : (numResults ctx op).toNat = op.toSim.spec.getNumResults! ctx.spec :=
    numResults_spec wf hop
  exact resultsUnusedRaw_spec wf hib hn h j (Nat.zero_le _) (by rw [hn]; exact hj)

/-- Erase an operation. Fails if the operation has regions or if one of its results is used. -/
buffed (inline := false)
def removeOpSim (ctx : Ctx) (op : Op) (wf : ctx.spec.WellFormed) (hop : op.InBounds ctx.spec) :
    Option Ctx :=
  if hreg : numRegions ctx op = 0 then
    if huses : resultsUnusedRaw ctx.buf op.toM (numResults ctx op).toNat 0 = true then
      some (Rewriter.eraseOp ctx op.toSim wf.inBounds
        ((Veir.OperationPtr.toSim_inBounds_iff_inBounds op).mpr hop)
        (wf.operations op hop).capOperands_eq_numOperands
        (wf.operations op hop).capBlockOperands_eq_numSuccessors
        (Rewriter.eraseOp_deallocFieldsInBounds ctx op.toSim wf (noRegions_of_check wf hop hreg)
          (noUses_of_check wf hop huses)))
    else
      none
  else
    none

theorem removeOp_wellFormed {ctx ctx' : Ctx} {op wf hop}
    (h : removeOp ctx op wf hop = some ctx') : ctx'.spec.WellFormed := by
  simp only [removeOp_def, removeOpSim] at h
  split at h
  · rename_i hreg
    split at h
    · rename_i huses
      simp only [Option.some.injEq] at h
      subst h
      exact Rewriter.eraseOp_WellFormed ctx op.toSim wf _ _ _ _
        (noRegions_of_check wf hop hreg) (noUses_of_check wf hop huses) _
    · contradiction
  · contradiction

theorem dealloc_spec (ctx : Ctx) (ptr : Sim.OperationPtr) (ib : ptr.InBounds ctx)
    (fib : (ptr.spec.dealloc ctx.spec ib.ib).FieldsInBounds) :
    (Sim.OperationPtr.dealloc ctx ptr ib fib).spec = ptr.spec.dealloc ctx.spec ib.ib := rfl

/-- Erasing an operation keeps every other operation in bounds. -/
theorem eraseOp_inBounds_of_ne {ctx : Ctx} {op : Sim.OperationPtr}
    {hCtx hOp hOpers hBlOpers hDealloc}
    (q : Op) (hq : q.InBounds ctx.spec) (hne : q ≠ op.spec) :
    q.InBounds (Rewriter.eraseOp ctx op hCtx hOp hOpers hBlOpers hDealloc).spec := by
  simp only [Rewriter.eraseOp_def, Rewriter.eraseOpSim]
  rw [dealloc_spec]
  exact OpOperandPtr.dealloc.inBounds_dealloc_genericPtr (ptr := .operation q) ((Rewriter.detachBlockOperands_inBounds (Sim.GenericPtr.fromOperation q.toSim)).mpr
    ((Rewriter.detachOperands_inBounds _).mpr
      ((Rewriter.detachOpIfAttached_inBounds _).mpr
        ((Sim.GenericPtr.iff_operation q.toSim).mpr
          ((Veir.OperationPtr.toSim_inBounds_iff_inBounds q).mpr hq))))).ib hne

theorem removeOp_inBounds_mono {ctx ctx' : Ctx} {op wf hop}
    (h : removeOp ctx op wf hop = some ctx')
    (q : Op) (hq : q.InBounds ctx.spec) (hne : q ≠ op) : q.InBounds ctx'.spec := by
  simp only [removeOp_def, removeOpSim] at h
  split at h
  · split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact eraseOp_inBounds_of_ne q hq hne
    · contradiction
  · contradiction

/-! ## The initial context -/

/-- A fresh, empty context. -/
def empty : Ctx := Sim.IRContext.empty

theorem empty_wellFormed : empty.spec.WellFormed := Sim.IRContext.empty_wellFormed

/-! ## Runtime wrappers

Each wrapper is, logically, the base function generated by `buffed` above; at run time it is
implemented by the generated `*Impl` function, with the (erased) specification carried along
unchanged. See the module documentation. -/

unsafe def createOpErased (ctx : Ctx) (opType : OpCode) (resultTypes : Array TypeAttr)
    (operands : Array Value) (blockOperands : Array Block) (regions : Array Region)
    (properties : propertiesOf opType) (ip : Option InsertPoint)
    (wf : ctx.spec.WellFormed)
    (hoper : ∀ v ∈ operands, v.InBounds ctx.spec)
    (hblocks : ∀ b ∈ blockOperands, b.InBounds ctx.spec)
    (hregions : ∀ r ∈ regions, r.InBounds ctx.spec)
    (hins : ip.maybe InsertPoint.InBounds ctx.spec) : Option (Ctx × Sim.OperationPtr) :=
  match newOpImpl ctx.buf ctx.spec ctx.sim opType resultTypes operands blockOperands regions
      properties ip wf hoper hblocks hregions hins with
  | none => none
  | some (buf, op) => some (⟨buf, ctx.spec, lcProof⟩, ⟨op, ⟨op.toNat⟩⟩)

/-- Create an operation, optionally inserting it at `ip`. -/
@[implemented_by createOpErased]
def createOp (ctx : Ctx) (opType : OpCode) (resultTypes : Array TypeAttr)
    (operands : Array Value) (blockOperands : Array Block) (regions : Array Region)
    (properties : propertiesOf opType) (ip : Option InsertPoint)
    (wf : ctx.spec.WellFormed)
    (hoper : ∀ v ∈ operands, v.InBounds ctx.spec)
    (hblocks : ∀ b ∈ blockOperands, b.InBounds ctx.spec)
    (hregions : ∀ r ∈ regions, r.InBounds ctx.spec)
    (hins : ip.maybe InsertPoint.InBounds ctx.spec) : Option (Ctx × Sim.OperationPtr) :=
  newOp ctx opType resultTypes operands blockOperands regions properties ip wf hoper hblocks
    hregions hins

unsafe def createBlockErased (ctx : Ctx) (argTypes : Array TypeAttr) (ip : Option BlockInsertPoint)
    (wf : ctx.spec.WellFormed) (hip : ip.maybe BlockInsertPoint.InBounds ctx.spec) :
    Option (Ctx × Sim.BlockPtr) :=
  match newBlockImpl ctx.buf ctx.spec ctx.sim argTypes ip wf hip with
  | none => none
  | some (buf, block) => some (⟨buf, ctx.spec, lcProof⟩, ⟨block, ⟨block.toNat⟩⟩)

/-- Create a block with the given argument types, optionally inserting it at `ip`. -/
@[implemented_by createBlockErased]
def createBlock (ctx : Ctx) (argTypes : Array TypeAttr) (ip : Option BlockInsertPoint)
    (wf : ctx.spec.WellFormed) (hip : ip.maybe BlockInsertPoint.InBounds ctx.spec) :
    Option (Ctx × Sim.BlockPtr) :=
  newBlock ctx argTypes ip wf hip

unsafe def insertBlockErased (ctx : Ctx) (block : Block) (ip : BlockInsertPoint)
    (wf : ctx.spec.WellFormed) (hb : block.InBounds ctx.spec) (hip : ip.InBounds ctx.spec) :
    Option Ctx :=
  match attachBlockImpl ctx.buf ctx.spec ctx.sim block ip wf hb hip with
  | none => none
  | some buf => some ⟨buf, ctx.spec, lcProof⟩

/-- Insert a detached block at `ip`. -/
@[implemented_by insertBlockErased]
def insertBlock (ctx : Ctx) (block : Block) (ip : BlockInsertPoint)
    (wf : ctx.spec.WellFormed) (hb : block.InBounds ctx.spec) (hip : ip.InBounds ctx.spec) :
    Option Ctx :=
  attachBlock ctx block ip wf hb hip

unsafe def createRegionErased (ctx : Ctx) : Option (Ctx × Sim.RegionPtr) :=
  match newRegionImpl ctx.buf ctx.spec ctx.sim with
  | none => none
  | some (buf, region) => some (⟨buf, ctx.spec, lcProof⟩, ⟨region, ⟨region.toNat⟩⟩)

/-- Create a detached region. -/
@[implemented_by createRegionErased]
def createRegion (ctx : Ctx) : Option (Ctx × Sim.RegionPtr) :=
  newRegion ctx

unsafe def setAttributesErased (ctx : Ctx) (op : Op) (attrs : DictionaryAttr)
    (wf : ctx.spec.WellFormed) (hop : op.InBounds ctx.spec) : Option Ctx :=
  match setOpAttrsImpl ctx.buf ctx.spec ctx.sim op attrs wf hop with
  | none => none
  | some buf => some ⟨buf, ctx.spec, lcProof⟩

/-- Set the attribute dictionary of an operation. -/
@[implemented_by setAttributesErased]
def setAttributes (ctx : Ctx) (op : Op) (attrs : DictionaryAttr)
    (wf : ctx.spec.WellFormed) (hop : op.InBounds ctx.spec) : Option Ctx :=
  setOpAttrs ctx op attrs wf hop

unsafe def replaceValueErased (ctx : Ctx) (oldValue newValue : Value)
    (wf : ctx.spec.WellFormed) (hold : oldValue.InBounds ctx.spec)
    (hnew : newValue.InBounds ctx.spec) : Option Ctx :=
  match replaceAllUsesImpl ctx.buf ctx.spec ctx.sim oldValue newValue wf hold hnew with
  | none => none
  | some buf => some ⟨buf, ctx.spec, lcProof⟩

/-- Replace every use of `oldValue` by `newValue`. -/
@[implemented_by replaceValueErased]
def replaceValue (ctx : Ctx) (oldValue newValue : Value)
    (wf : ctx.spec.WellFormed) (hold : oldValue.InBounds ctx.spec)
    (hnew : newValue.InBounds ctx.spec) : Option Ctx :=
  replaceAllUses ctx oldValue newValue wf hold hnew

unsafe def eraseOpErased (ctx : Ctx) (op : Op) (wf : ctx.spec.WellFormed)
    (hop : op.InBounds ctx.spec) : Option Ctx :=
  match removeOpImpl ctx.buf ctx.spec ctx.sim op wf hop with
  | none => none
  | some buf => some ⟨buf, ctx.spec, lcProof⟩

/-- Erase an operation without regions whose results have no uses. -/
@[implemented_by eraseOpErased]
def eraseOp (ctx : Ctx) (op : Op) (wf : ctx.spec.WellFormed) (hop : op.InBounds ctx.spec) :
    Option Ctx :=
  removeOp ctx op wf hop

/-! ### Properties of the runtime wrappers (by unfolding) -/

theorem createOp_wellFormed {ctx ctx' : Ctx} {opType resultTypes operands blockOperands regions
    properties ip wf hoper hblocks hregions hins} {op : Sim.OperationPtr}
    (h : createOp ctx opType resultTypes operands blockOperands regions properties ip wf hoper
      hblocks hregions hins = some (ctx', op)) : ctx'.spec.WellFormed :=
  newOp_wellFormed h

theorem createOp_inBounds_mono {ctx ctx' : Ctx} {opType resultTypes operands blockOperands
    regions properties ip wf hoper hblocks hregions hins} {op : Sim.OperationPtr}
    (h : createOp ctx opType resultTypes operands blockOperands regions properties ip wf hoper
      hblocks hregions hins = some (ctx', op))
    (p : Veir.GenericPtr) : p.InBounds ctx.spec → p.InBounds ctx'.spec :=
  newOp_inBounds_mono h p

theorem createOp_new_inBounds {ctx ctx' : Ctx} {opType resultTypes operands blockOperands
    regions properties ip wf hoper hblocks hregions hins} {op : Sim.OperationPtr}
    (h : createOp ctx opType resultTypes operands blockOperands regions properties ip wf hoper
      hblocks hregions hins = some (ctx', op)) : op.spec.InBounds ctx'.spec :=
  newOp_new_inBounds h

theorem createOp_new_not_inBounds {ctx ctx' : Ctx} {opType resultTypes operands blockOperands
    regions properties ip wf hoper hblocks hregions hins} {op : Sim.OperationPtr}
    (h : createOp ctx opType resultTypes operands blockOperands regions properties ip wf hoper
      hblocks hregions hins = some (ctx', op)) : ¬ op.spec.InBounds ctx.spec :=
  newOp_new_not_inBounds h

theorem createBlock_wellFormed {ctx ctx' : Ctx} {argTypes ip wf hip} {block : Sim.BlockPtr}
    (h : createBlock ctx argTypes ip wf hip = some (ctx', block)) : ctx'.spec.WellFormed :=
  newBlock_wellFormed h

theorem createBlock_inBounds_mono {ctx ctx' : Ctx} {argTypes ip wf hip} {block : Sim.BlockPtr}
    (h : createBlock ctx argTypes ip wf hip = some (ctx', block))
    (p : Veir.GenericPtr) : p.InBounds ctx.spec → p.InBounds ctx'.spec :=
  newBlock_inBounds_mono h p

theorem createBlock_new_inBounds {ctx ctx' : Ctx} {argTypes ip wf hip} {block : Sim.BlockPtr}
    (h : createBlock ctx argTypes ip wf hip = some (ctx', block)) : block.spec.InBounds ctx'.spec :=
  newBlock_new_inBounds h

theorem insertBlock_wellFormed {ctx ctx' : Ctx} {block ip wf hb hip}
    (h : insertBlock ctx block ip wf hb hip = some ctx') : ctx'.spec.WellFormed :=
  attachBlock_wellFormed h

theorem insertBlock_inBounds_mono {ctx ctx' : Ctx} {block ip wf hb hip}
    (h : insertBlock ctx block ip wf hb hip = some ctx')
    (p : Veir.GenericPtr) : p.InBounds ctx.spec → p.InBounds ctx'.spec :=
  attachBlock_inBounds_mono h p

theorem createRegion_wellFormed {ctx ctx' : Ctx} {region : Sim.RegionPtr}
    (wf : ctx.spec.WellFormed) (h : createRegion ctx = some (ctx', region)) :
    ctx'.spec.WellFormed :=
  newRegion_wellFormed wf h

theorem createRegion_inBounds_mono {ctx ctx' : Ctx} {region : Sim.RegionPtr}
    (h : createRegion ctx = some (ctx', region))
    (p : Veir.GenericPtr) : p.InBounds ctx.spec → p.InBounds ctx'.spec :=
  newRegion_inBounds_mono h p

theorem createRegion_new_inBounds {ctx ctx' : Ctx} {region : Sim.RegionPtr}
    (h : createRegion ctx = some (ctx', region)) : region.spec.InBounds ctx'.spec :=
  newRegion_new_inBounds h

theorem setAttributes_wellFormed {ctx ctx' : Ctx} {op attrs wf hop}
    (h : setAttributes ctx op attrs wf hop = some ctx') : ctx'.spec.WellFormed :=
  setOpAttrs_wellFormed h

theorem setAttributes_inBounds_mono {ctx ctx' : Ctx} {op attrs wf hop}
    (h : setAttributes ctx op attrs wf hop = some ctx')
    (p : Veir.GenericPtr) : p.InBounds ctx.spec → p.InBounds ctx'.spec :=
  setOpAttrs_inBounds_mono h p

theorem replaceValue_wellFormed {ctx ctx' : Ctx} {oldValue newValue wf hold hnew}
    (h : replaceValue ctx oldValue newValue wf hold hnew = some ctx') : ctx'.spec.WellFormed :=
  replaceAllUses_wellFormed h

theorem replaceValue_inBounds_mono {ctx ctx' : Ctx} {oldValue newValue wf hold hnew}
    (h : replaceValue ctx oldValue newValue wf hold hnew = some ctx')
    (p : Veir.GenericPtr) : p.InBounds ctx.spec → p.InBounds ctx'.spec :=
  replaceAllUses_inBounds_mono h p

theorem eraseOp_wellFormed {ctx ctx' : Ctx} {op wf hop}
    (h : eraseOp ctx op wf hop = some ctx') : ctx'.spec.WellFormed :=
  removeOp_wellFormed h

theorem eraseOp_inBounds_mono {ctx ctx' : Ctx} {op wf hop}
    (h : eraseOp ctx op wf hop = some ctx')
    (q : Op) (hq : q.InBounds ctx.spec) (hne : q ≠ op) : q.InBounds ctx'.spec :=
  removeOp_inBounds_mono h q hq hne

end Veir.Parser.IR

end

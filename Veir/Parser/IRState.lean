module

public import Veir.Parser.BuffedIR
public import Veir.Parser.ParserError
public import Veir.Parser.Location

/-!
# The parser's IR state and its invariant

The parser keeps, besides the IR context, several tables of pointers: the values defined so far,
the blocks of the regions being parsed, the placeholder operations standing in for
forward-referenced values, and stacks of the containers currently being filled. This file bundles
all of them into `IRState` together with an invariant (`IRStateData.Inv`) stating that the
context is well-formed and that every pointer stored in a table is in bounds.

Every modification of the state goes through one of the operations below, which re-establishes
the invariant. The parser proper (`Veir.Parser.MlirParser`) only calls these operations and
never handles proofs. All pointers are specification-level pointers (see
`Veir.Parser.BuffedIR`).

Placeholder operations are not erased when they are resolved: they are collected in `garbage`
and erased at the very end (`IRState.finish`), once no table refers to any operation anymore.
This keeps the invariant simple: no pointer ever leaves the context while a table may hold it.
-/

@[expose] public section

namespace Veir.Parser

open Veir
open Veir.Parser.IR

instance : LawfulBEq ByteArray where
  eq_of_beq {a b} h := by
    apply ByteArray.ext
    exact eq_of_beq (α := Array UInt8) h
  rfl {a} := beq_self_eq_true (α := Array UInt8) a.data

/-- A value or block name, without its sigil. -/
abbrev Name := ByteArray

/--
  The state of a block encountered during parsing.
  A block is either `Defined` (its label has been parsed) or `ForwardDeclared`
  (it has only been referenced, e.g., as a block operand, but not yet defined; its argument
  types were found by looking ahead for its label).
-/
inductive BlockEntry where
  | Defined (block : IR.Block) (loc : Location)
  | ForwardDeclared (block : IR.Block) (argTypes : Array TypeAttr) (loc : Location)
  deriving Inhabited

/-- Get the block pointer of a `BlockEntry`, regardless of its state. -/
def BlockEntry.block : BlockEntry → IR.Block
  | .Defined block _ => block
  | .ForwardDeclared block _ _ => block

/--
  Bookkeeping for an SSA value referenced before it is defined (a "forward reference").

  Following MLIR's generic-form parser, the name table is flat across all regions: a forward
  reference is resolved by the first textual definition of the name, wherever it appears. Each
  referenced result index holds a detached single-result placeholder operation standing in for
  the value; when the definition is parsed, all uses of each placeholder are replaced by the
  real value. The placeholder itself is erased at the end of parsing.
-/
structure ForwardValue where
  /-- Placeholder operation per referenced result index, with that index's first-use location. -/
  placeholders : Std.HashMap Nat (IR.Op × Location)
  /-- Location of the first use, used for error reporting if the value is never defined. -/
  loc : Location
  deriving Inhabited

/-- The data of the parser's IR state. -/
structure IRStateData where
  /-- The IR context. -/
  ctx : IR.Ctx
  /-- The values defined for a given name, with the location of the definition. -/
  values : Std.HashMap Name (Array IR.Value × Location) := {}
  /-- The block tables of the regions being parsed, innermost first. -/
  blockScopes : List (Std.HashMap Name BlockEntry) := []
  /-- Values referenced but not yet defined, keyed by name. -/
  forwardValues : Std.HashMap Name ForwardValue := {}
  /-- Placeholder operations, to be erased at the end of parsing. -/
  garbage : Std.HashSet IR.Op := {}
  /-- The regions being parsed, innermost first. -/
  openRegions : List IR.Region := []
  /-- The blocks being parsed, innermost first. -/
  openBlocks : List IR.Block := []
  /-- The regions already parsed for operations not yet created, last parsed first. -/
  pendingRegions : List IR.Region := []
  /-- The operands already resolved for the operation being parsed, last resolved first. -/
  pendingOperands : List IR.Value := []
  /-- The block operands already resolved for the operation being parsed, last resolved first. -/
  pendingBlockOperands : List IR.Block := []
  /-- The operation created last. -/
  lastOp : Option IR.Op := none

/-- The invariant of the parser's IR state: the context is well-formed, and every pointer stored
in the state is in bounds. -/
structure IRStateData.Inv (s : IRStateData) : Prop where
  wf : s.ctx.spec.WellFormed
  values : ∀ (name : Name) (vs : Array IR.Value) (loc : Location),
    s.values[name]? = some (vs, loc) → ∀ v ∈ vs, Veir.ValuePtr.InBounds v s.ctx.spec
  blocks : ∀ scope ∈ s.blockScopes, ∀ (name : Name) (e : BlockEntry), scope[name]? = some e →
    Veir.BlockPtr.InBounds e.block s.ctx.spec
  forwards : ∀ (name : Name) (fwd : ForwardValue), s.forwardValues[name]? = some fwd →
    ∀ (i : Nat) (op : IR.Op) (loc : Location), fwd.placeholders[i]? = some (op, loc) →
      Veir.OperationPtr.InBounds op s.ctx.spec
  garbage : ∀ op ∈ s.garbage, Veir.OperationPtr.InBounds op s.ctx.spec
  openRegions : ∀ r ∈ s.openRegions, Veir.RegionPtr.InBounds r s.ctx.spec
  openBlocks : ∀ b ∈ s.openBlocks, Veir.BlockPtr.InBounds b s.ctx.spec
  pendingRegions : ∀ r ∈ s.pendingRegions, Veir.RegionPtr.InBounds r s.ctx.spec
  pendingOperands : ∀ v ∈ s.pendingOperands, Veir.ValuePtr.InBounds v s.ctx.spec
  pendingBlockOperands : ∀ b ∈ s.pendingBlockOperands, Veir.BlockPtr.InBounds b s.ctx.spec
  lastOp : ∀ (op : IR.Op), s.lastOp = some op →
    Veir.OperationPtr.InBounds op s.ctx.spec ∧ op ∉ s.garbage

/-- The parser's IR state: its data together with the invariant. -/
structure IRState where
  data : IRStateData
  inv : data.Inv

/-! ## Monotonicity -/

/-- Bounds monotonicity between two contexts. -/
abbrev Mono (ctx ctx' : IR.Ctx) : Prop :=
  ∀ p : Veir.GenericPtr, p.InBounds ctx.spec → p.InBounds ctx'.spec

theorem Mono.refl (ctx : IR.Ctx) : Mono ctx ctx := fun _ h => h

theorem Mono.trans {c₁ c₂ c₃ : IR.Ctx} (h₁ : Mono c₁ c₂) (h₂ : Mono c₂ c₃) : Mono c₁ c₃ :=
  fun p hp => h₂ p (h₁ p hp)

theorem Mono.value {c c' : IR.Ctx} (m : Mono c c') {v : IR.Value} (h : v.InBounds c.spec) :
    v.InBounds c'.spec :=
  (Veir.GenericPtr.iff_value v).mp (m _ ((Veir.GenericPtr.iff_value v).mpr h))

theorem Mono.op {c c' : IR.Ctx} (m : Mono c c') {op : IR.Op} (h : op.InBounds c.spec) :
    op.InBounds c'.spec :=
  (Veir.GenericPtr.iff_operation op).mp (m _ ((Veir.GenericPtr.iff_operation op).mpr h))

theorem Mono.block {c c' : IR.Ctx} (m : Mono c c') {b : IR.Block} (h : b.InBounds c.spec) :
    b.InBounds c'.spec :=
  (Veir.GenericPtr.iff_block b).mp (m _ ((Veir.GenericPtr.iff_block b).mpr h))

theorem Mono.region {c c' : IR.Ctx} (m : Mono c c') {r : IR.Region} (h : r.InBounds c.spec) :
    r.InBounds c'.spec :=
  (Veir.GenericPtr.iff_region r).mp (m _ ((Veir.GenericPtr.iff_region r).mpr h))

/-- A step from `ctx` to a new well-formed context in which every pointer stays in bounds. -/
structure CtxStep (ctx : IR.Ctx) where
  next : IR.Ctx
  wf : next.spec.WellFormed
  mono : Mono ctx next

/-- A `CtxStep` that also yields a block in bounds in the new context. -/
structure BlockStep (ctx : IR.Ctx) extends CtxStep ctx where
  block : IR.Block
  hb : block.InBounds next.spec

/-- Moving to a new well-formed context in which every pointer stays in bounds preserves the
invariant. -/
theorem IRStateData.Inv.setCtx {s : IRStateData} (h : s.Inv) {ctx' : IR.Ctx}
    (wf' : ctx'.spec.WellFormed) (m : Mono s.ctx ctx') :
    ({ s with ctx := ctx' } : IRStateData).Inv where
  wf := wf'
  values := fun name vs loc hget v hv => m.value (h.values name vs loc hget v hv)
  blocks := fun scope hs name e hget => m.block (h.blocks scope hs name e hget)
  forwards := fun name fwd hget i op loc hp => m.op (h.forwards name fwd hget i op loc hp)
  garbage := fun op hop => m.op (h.garbage op hop)
  openRegions := fun r hr => m.region (h.openRegions r hr)
  openBlocks := fun b hb => m.block (h.openBlocks b hb)
  pendingRegions := fun r hr => m.region (h.pendingRegions r hr)
  pendingOperands := fun v hv => m.value (h.pendingOperands v hv)
  pendingBlockOperands := fun b hb => m.block (h.pendingBlockOperands b hb)
  lastOp := fun op hop => ⟨m.op (h.lastOp op hop).1, (h.lastOp op hop).2⟩

/-! ## The initial state -/

theorem default_spec_eq : (default : IR.Ctx).spec = Veir.IRContext.empty OpCode := rfl

theorem IRContext.default_wellFormed : (default : IR.Ctx).spec.WellFormed := by
  rw [default_spec_eq]
  exact Veir.IRContext.empty_wellFormed

/-- The state at the start of parsing. -/
def IRState.initial : IRState :=
  ⟨{ ctx := IR.empty }, {
    wf := IR.empty_wellFormed
    values := by simp
    blocks := by simp
    forwards := by simp
    garbage := by simp
    openRegions := by simp
    openBlocks := by simp
    pendingRegions := by simp
    pendingOperands := by simp
    pendingBlockOperands := by simp
    lastOp := by simp }⟩

/-- A placeholder state, used to keep the real state uniquely referenced while it is being
modified (see `Veir.Parser.MlirParserM`). -/
def IRState.dummy : IRState :=
  ⟨{ ctx := default }, {
    wf := IRContext.default_wellFormed
    values := by simp
    blocks := by simp
    forwards := by simp
    garbage := by simp
    openRegions := by simp
    openBlocks := by simp
    pendingRegions := by simp
    pendingOperands := by simp
    pendingBlockOperands := by simp
    lastOp := by simp }⟩

instance : Inhabited IRState := ⟨IRState.dummy⟩

/-! ## Read-only queries -/

namespace IRState

/-- The context. -/
@[inline] def ctx (s : IRState) : IR.Ctx := s.data.ctx

/-- The type of a value. -/
@[inline] def valueType (s : IRState) (v : IR.Value) : Attribute := IR.valueType s.data.ctx v

/-- The entry of a block name in the innermost region. -/
def lookupBlock (s : IRState) (name : Name) : Option BlockEntry :=
  match s.data.blockScopes with
  | [] => none
  | scope :: _ => scope[name]?

/-- The names and first-use locations of the values referenced but never defined. -/
def unresolvedForwardValues (s : IRState) : List (Name × Location) :=
  s.data.forwardValues.toList.map fun (name, fwd) => (name, fwd.loc)

/-- The names and first-use locations of the blocks of the innermost region that were referenced
but never defined. -/
def undefinedBlocks (s : IRState) : List (Name × Location) :=
  match s.data.blockScopes with
  | [] => []
  | scope :: _ => scope.toList.filterMap fun (name, entry) =>
    match entry with
    | .ForwardDeclared _ _ loc => some (name, loc)
    | .Defined _ _ => none

/-- Whether the value name is defined (in scope). -/
def isValueDefined (s : IRState) (name : Name) : Bool :=
  s.data.values.contains name

/-! ## Values -/

/-- Forget a value name (when leaving its scope). -/
def eraseValueName (s : IRState) (name : Name) : IRState :=
  ⟨{ s.data with values := s.data.values.erase name },
    { s.inv with
      values := by
        intro k vs loc hget v hv
        rw [Std.HashMap.getElem?_erase] at hget
        split at hget
        · contradiction
        · exact s.inv.values k vs loc hget v hv }⟩

/-- Replace the uses of each placeholder result by the corresponding defined value. -/
def rewire (name : String) (pos : Location) (values : Array IR.Value) :
    (ctx : IR.Ctx) → (ps : List (Nat × (IR.Op × Location))) → (wf : ctx.spec.WellFormed) →
    (hps : ∀ x ∈ ps, x.2.1.InBounds ctx.spec) → (hvs : ∀ v ∈ values, v.InBounds ctx.spec) →
    Except ParserError (CtxStep ctx)
  | ctx, [], wf, _, _ => .ok ⟨ctx, wf, Mono.refl ctx⟩
  | ctx, (index, (p, useLoc)) :: rest, wf, hps, hvs =>
    if hidx : index < values.size then
      let realValue := values[index]
      let placeholderValue : IR.Value := .opResult ⟨p, 0⟩
      have hp : p.InBounds ctx.spec := hps _ (List.mem_cons_self ..)
      if h0 : 0 < (IR.numResults ctx p).toNat then
        let usedType := IR.valueType ctx placeholderValue
        let definedType := IR.valueType ctx realValue
        if usedType ≠ definedType then
          .error (({ msg := s!"definition of value %{name}#{index} has type {definedType} but was used with type {usedType}",
                     pos := some pos } : ParserError).addNote useLoc "value used here")
        else
          match hrep : IR.replaceValue ctx placeholderValue realValue wf
              (IR.opResult_inBounds wf hp h0) (hvs _ (Array.getElem_mem hidx)) with
          | none => .error { msg := "internal error: failed to replace the uses of a forward-reference placeholder", pos := some pos }
          | some ctx' =>
            have wf' := IR.replaceValue_wellFormed hrep
            have m : Mono ctx ctx' := IR.replaceValue_inBounds_mono hrep
            match rewire name pos values ctx' rest wf'
                (fun x hx => m.op (hps x (List.mem_cons_of_mem _ hx)))
                (fun v hv => m.value (hvs v hv)) with
            | .error e => .error e
            | .ok step => .ok ⟨step.next, step.wf, m.trans step.mono⟩
      else
        .error { msg := "internal error: forward-reference placeholder has no result", pos := some pos }
    else
      .error (({ msg := s!"definition of value %{name} provides {values.size} results, but result #{index} was used",
                 pos := some pos } : ParserError).addNote useLoc "value used here")

/--
  Register an array of values with the given name.
  If the name was forward-referenced earlier, the uses of the placeholders created for it are
  replaced by the newly-defined values (following MLIR: the first definition of a name resolves
  it).
-/
def defineValues (s : IRState) (name : Name) (pos : Location) (values : Array IR.Value)
    (hvals : ∀ v ∈ values, v.InBounds s.data.ctx.spec) : Except ParserError IRState := do
  let d := s.data
  let step ←
    match hfwd : d.forwardValues[name]? with
    | none => pure (⟨d.ctx, s.inv.wf, Mono.refl _⟩ : CtxStep d.ctx)
    | some fwd =>
      rewire (String.fromUTF8! name) pos values d.ctx fwd.placeholders.toList s.inv.wf
        (fun x hx => s.inv.forwards name fwd hfwd x.1 x.2.1 x.2.2
          (Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hx))
        hvals
  let ctx' := step.next
  have wf' := step.wf
  have m := step.mono
  if let some (_, existingPos) := d.values[name]? then
    let error := ParserError.mk s!"value %{String.fromUTF8! name} has already been defined" pos []
    throw (error.addNote existingPos "previously defined here")
  let inv' := s.inv.setCtx wf' m
  return ⟨{ d with
      ctx := ctx'
      values := d.values.insert name (values, pos)
      forwardValues := d.forwardValues.erase name },
    { inv' with
      values := by
        intro k vs loc hget v hv
        rw [Std.HashMap.getElem?_insert] at hget
        split at hget
        · simp only [Option.some.injEq, Prod.mk.injEq] at hget
          obtain ⟨rfl, rfl⟩ := hget
          exact m.value (hvals v hv)
        · exact inv'.values k vs loc hget v hv
      forwards := by
        intro k fwd hget
        rw [Std.HashMap.getElem?_erase] at hget
        split at hget
        · contradiction
        · exact inv'.forwards k fwd hget }⟩

/-- Register the results `startIndex, ..., startIndex + count - 1` of the operation created last
under the given name. -/
def defineResults (s : IRState) (name : Name) (pos : Location) (startIndex count : Nat) :
    Except ParserError IRState := do
  match hlast : s.data.lastOp with
  | none => throw { msg := "internal error: no operation to define the results of", pos := some pos }
  | some op =>
  have hop := (s.inv.lastOp op hlast).1
  if hcount : startIndex + count ≤ (IR.numResults s.data.ctx op).toNat then
    let values : Array IR.Value :=
      Array.ofFn fun (i : Fin count) => .opResult ⟨op, startIndex + i.val⟩
    s.defineValues name pos values (by
      intro v hv
      obtain ⟨i, rfl⟩ := Array.mem_ofFn.mp hv
      exact IR.opResult_inBounds s.inv.wf hop (by have := i.isLt; omega))
  else
    throw { msg := "internal error: result index out of range", pos := some pos }

/-- Register the argument `index` of the block being parsed under the given name. -/
def defineBlockArgument (s : IRState) (name : Name) (pos : Location) (index : Nat) :
    Except ParserError IRState := do
  match hb : s.data.openBlocks with
  | [] => throw { msg := "internal error: no block to define the arguments of", pos := some pos }
  | block :: _ =>
    have hblock : block.InBounds s.data.ctx.spec := s.inv.openBlocks block (hb ▸ List.mem_cons_self ..)
    if hidx : index < (IR.numArguments s.data.ctx block).toNat then
      s.defineValues name pos #[.blockArgument ⟨block, index⟩] (by
        intro v hv
        simp only [Array.mem_singleton] at hv
        subst hv
        exact IR.blockArgument_inBounds s.inv.wf hblock hidx)
    else
      throw { msg := "internal error: block argument index out of range", pos := some pos }

/-! ## Operands -/

/-- Push a resolved operand. -/
def pushOperand (s : IRState) (v : IR.Value) (hv : v.InBounds s.data.ctx.spec) : IRState :=
  ⟨{ s.data with pendingOperands := v :: s.data.pendingOperands },
    { s.inv with
      pendingOperands := by
        intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · exact hv
        · exact s.inv.pendingOperands w hw }⟩

/-- Create a detached single-result placeholder operation standing in for the result `index` of
the not-yet-defined value `name`, record it, and push its result as an operand. -/
def pushNewPlaceholder (s : IRState) (name : Name) (index : Nat) (ty : TypeAttr)
    (pos : Location) : Except ParserError IRState := do
  let d := s.data
  match hcreate : IR.createOp d.ctx (.builtin .unrealized_conversion_cast) #[ty] #[] #[] #[] ()
      none s.inv.wf (by simp) (by simp) (by simp) Option.maybe_none with
  | none => throw { msg := "internal error: failed to create forward-reference placeholder", pos := some pos }
  | some (ctx', sop) =>
    let op := sop.spec
    have wf' := IR.createOp_wellFormed hcreate
    have m : Mono d.ctx ctx' := IR.createOp_inBounds_mono hcreate
    have hop : op.InBounds ctx'.spec := IR.createOp_new_inBounds hcreate
    have hfresh : ¬ op.InBounds d.ctx.spec := IR.createOp_new_not_inBounds hcreate
    if h0 : 0 < (IR.numResults ctx' op).toNat then
      let fwd : ForwardValue := match d.forwardValues[name]? with
        | some fwd => { fwd with placeholders := fwd.placeholders.insert index (op, pos) }
        | none => { placeholders := (Std.HashMap.emptyWithCapacity 1).insert index (op, pos), loc := pos }
      let inv' := s.inv.setCtx wf' m
      have hfwd : ∀ (i : Nat) (op' : IR.Op) (loc : Location), fwd.placeholders[i]? = some (op', loc) →
          op'.InBounds ctx'.spec := by
        intro i op' loc hp
        simp only [fwd] at hp
        split at hp
        · rename_i fwd₀ hfwd₀
          simp only [Std.HashMap.getElem?_insert] at hp
          split at hp
          · simp only [Option.some.injEq, Prod.mk.injEq] at hp
            obtain ⟨rfl, rfl⟩ := hp
            exact hop
          · exact inv'.forwards name fwd₀ hfwd₀ i op' loc hp
        · simp only [Std.HashMap.getElem?_insert, Std.HashMap.getElem?_emptyWithCapacity] at hp
          split at hp
          · simp only [Option.some.injEq, Prod.mk.injEq] at hp
            obtain ⟨rfl, rfl⟩ := hp
            exact hop
          · contradiction
      return ⟨{ d with
          ctx := ctx'
          forwardValues := d.forwardValues.insert name fwd
          garbage := d.garbage.insert op
          pendingOperands := (.opResult ⟨op, 0⟩) :: d.pendingOperands },
        { inv' with
          forwards := by
            intro k fwd' hget i op' loc hp
            rw [Std.HashMap.getElem?_insert] at hget
            split at hget
            · simp only [Option.some.injEq] at hget
              subst hget
              exact hfwd i op' loc hp
            · exact inv'.forwards k fwd' hget i op' loc hp
          garbage := by
            intro q hq
            rcases Std.HashSet.mem_insert.mp hq with heq | hq
            · rw [← eq_of_beq heq]; exact hop
            · exact inv'.garbage q hq
          pendingOperands := by
            intro w hw
            rcases List.mem_cons.mp hw with rfl | hw
            · exact IR.opResult_inBounds wf' hop h0
            · exact inv'.pendingOperands w hw
          lastOp := by
            intro l hl
            obtain ⟨hl₁, hl₂⟩ := inv'.lastOp l hl
            refine ⟨hl₁, ?_⟩
            intro hmem
            rcases Std.HashSet.mem_insert.mp hmem with heq | hmem
            · have hol : op = l := eq_of_beq heq
              subst hol
              exact hfresh (s.inv.lastOp op hl).1
            · exact hl₂ hmem }⟩
    else
      throw { msg := "internal error: forward-reference placeholder has no result", pos := some pos }

/--
  Resolve an operand `%name` or `%name#index` of the expected type and push it as an operand of
  the operation being parsed. If the value has not yet been defined, a forward-reference
  placeholder is created (or reused); it is resolved when the definition is parsed, or reported
  as an error once top-level parsing finishes if the value is never defined.
-/
def resolveOperand (s : IRState) (name : Name) (index : Nat) (expectedType : TypeAttr)
    (pos : Location) (display : String) : Except ParserError IRState := do
  let d := s.data
  match hval : d.values[name]? with
  | some (values, defPos) =>
    if hidx : index < values.size then
      let value := values[index]
      let parsedType := IR.valueType d.ctx value
      if parsedType ≠ expectedType.val then
        throw (({ msg := s!"type mismatch for value {display}: expected {expectedType}, got {parsedType}",
                  pos := some pos } : ParserError).addNote defPos "value defined here")
      return s.pushOperand value (s.inv.values name values defPos hval value (Array.getElem_mem hidx))
    else
      throw (({ msg := s!"invalid result index {index} for %{String.fromUTF8! name}",
                pos := some pos } : ParserError).addNote defPos "value defined here")
  | none =>
    match hfwd : d.forwardValues[name]? with
    | some fwd =>
      match hp : fwd.placeholders[index]? with
      | some (placeholderOp, useLoc) =>
        /- The same result index was referenced before: reuse its placeholder and
           check the type is consistent with the previous use. -/
        have hop := s.inv.forwards name fwd hfwd index placeholderOp useLoc hp
        if h0 : 0 < (IR.numResults d.ctx placeholderOp).toNat then
          let placeholderValue : IR.Value := .opResult ⟨placeholderOp, 0⟩
          let parsedType := IR.valueType d.ctx placeholderValue
          if parsedType ≠ expectedType.val then
            throw (({ msg := s!"type mismatch for value {display}: expected {expectedType}, got {parsedType}",
                      pos := some pos } : ParserError).addNote useLoc "value first used here")
          return s.pushOperand placeholderValue (IR.opResult_inBounds s.inv.wf hop h0)
        else
          throw { msg := "internal error: forward-reference placeholder has no result", pos := some pos }
      | none =>
        /- A new result index of an already forward-referenced value. -/
        s.pushNewPlaceholder name index expectedType pos
    | none =>
      /- First reference of a not-yet-defined value. -/
      s.pushNewPlaceholder name index expectedType pos

/-! ## Block operands -/

/-- Push a resolved block operand. -/
def pushBlockOperand (s : IRState) (b : IR.Block) (hb : b.InBounds s.data.ctx.spec) :
    IRState :=
  ⟨{ s.data with pendingBlockOperands := b :: s.data.pendingBlockOperands },
    { s.inv with
      pendingBlockOperands := by
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact hb
        · exact s.inv.pendingBlockOperands c hc }⟩

/-- Push a block operand referring to a block already known in the innermost region. -/
def pushKnownBlockOperand (s : IRState) (name : Name) (pos : Location) :
    Except ParserError IRState := do
  match hscopes : s.data.blockScopes with
  | [] => throw { msg := "internal error: no block scope", pos := some pos }
  | scope :: _ =>
    match hget : scope[name]? with
    | none => throw { msg := "internal error: unknown block", pos := some pos }
    | some entry =>
      return s.pushBlockOperand entry.block
        (s.inv.blocks scope (hscopes ▸ List.mem_cons_self ..) name entry hget)

/-- Forward-declare the block `name` of the innermost region with the given argument types
(found by looking ahead for its label), and push it as a block operand. -/
def declareBlockUse (s : IRState) (name : Name) (argTypes : Array TypeAttr) (pos : Location) :
    Except ParserError IRState := do
  let d := s.data
  match hscopes : d.blockScopes with
  | [] => throw { msg := "internal error: no block scope", pos := some pos }
  | scope :: rest =>
    match hcreate : IR.createBlock d.ctx argTypes none s.inv.wf Option.maybe_none with
    | none => throw { msg := "internal error: failed to create block", pos := some pos }
    | some (ctx', sb) =>
      let block := sb.spec
      have wf' := IR.createBlock_wellFormed hcreate
      have m : Mono d.ctx ctx' := IR.createBlock_inBounds_mono hcreate
      have hb : block.InBounds ctx'.spec := IR.createBlock_new_inBounds hcreate
      let inv' := s.inv.setCtx wf' m
      return ⟨{ d with
          ctx := ctx'
          blockScopes := scope.insert name (.ForwardDeclared block argTypes pos) :: rest
          pendingBlockOperands := block :: d.pendingBlockOperands },
        { inv' with
          blocks := by
            intro sc hsc k e hget
            rcases List.mem_cons.mp hsc with rfl | hsc
            · rw [Std.HashMap.getElem?_insert] at hget
              split at hget
              · simp only [Option.some.injEq] at hget
                subst hget
                exact hb
              · exact inv'.blocks scope (hscopes ▸ List.mem_cons_self ..) k e hget
            · exact inv'.blocks sc (hscopes ▸ List.mem_cons_of_mem _ hsc) k e hget
          pendingBlockOperands := by
            intro c hc
            rcases List.mem_cons.mp hc with rfl | hc
            · exact hb
            · exact inv'.pendingBlockOperands c hc }⟩

/-! ## Operations -/

theorem mem_of_mem_take_reverse_toArray {α} {l : List α} {n : Nat} {a : α}
    (h : a ∈ (l.take n).reverse.toArray) : a ∈ l := by
  rw [List.mem_toArray, List.mem_reverse] at h
  exact List.mem_of_mem_take h

/--
  Create the operation being parsed, with the `nOperands` operands, `nBlockOperands` block
  operands and `nRegions` regions most recently pushed, inserting it at the end of the block being
  parsed (or leaving it detached at top level), and set its attributes. Returns the operation and
  its number of results.
-/
def createOp (s : IRState) (opType : OpCode) (resultTypes : Array TypeAttr)
    (properties : propertiesOf opType) (attrs : DictionaryAttr)
    (nOperands nBlockOperands nRegions : Nat) (pos : Location) :
    Except ParserError (IRState × IR.Op × Nat) := do
  let d := s.data
  let operands := (d.pendingOperands.take nOperands).reverse.toArray
  let blockOperands := (d.pendingBlockOperands.take nBlockOperands).reverse.toArray
  let regions := (d.pendingRegions.take nRegions).reverse.toArray
  let ip : Option InsertPoint := d.openBlocks.head?.map InsertPoint.atEnd
  have hins : ip.maybe InsertPoint.InBounds d.ctx.spec := by
    rw [Option.maybe_def]
    intro z hz
    match hb : d.openBlocks with
    | [] => simp [ip, hb] at hz
    | b :: _ =>
      simp only [ip, hb, List.head?_cons, Option.map_some, Option.some.injEq] at hz
      subst hz
      exact s.inv.openBlocks b (hb ▸ List.mem_cons_self ..)
  match hcreate : IR.createOp d.ctx opType resultTypes operands blockOperands regions properties
      ip s.inv.wf
      (fun v hv => s.inv.pendingOperands v (mem_of_mem_take_reverse_toArray hv))
      (fun b hb => s.inv.pendingBlockOperands b (mem_of_mem_take_reverse_toArray hb))
      (fun r hr => s.inv.pendingRegions r (mem_of_mem_take_reverse_toArray hr))
      hins with
  | none => throw { msg := "internal error: failed to create operation", pos := some pos }
  | some (ctx₁, sop) =>
    let op := sop.spec
    have wf₁ := IR.createOp_wellFormed hcreate
    have m₁ : Mono d.ctx ctx₁ := IR.createOp_inBounds_mono hcreate
    have hop₁ : op.InBounds ctx₁.spec := IR.createOp_new_inBounds hcreate
    have hfresh : ¬ op.InBounds d.ctx.spec := IR.createOp_new_not_inBounds hcreate
    let step ←
      if attrs.entries.isEmpty then
        pure (⟨ctx₁, wf₁, Mono.refl _⟩ : CtxStep ctx₁)
      else
        match hset : IR.setAttributes ctx₁ op attrs wf₁ hop₁ with
        | none => throw { msg := "internal error: failed to set the operation attributes", pos := some pos }
        | some ctx₂ => pure ⟨ctx₂, IR.setAttributes_wellFormed hset, IR.setAttributes_inBounds_mono hset⟩
    let ctx₂ := step.next
    have wf₂ := step.wf
    have m₂ := step.mono
    have m : Mono d.ctx ctx₂ := m₁.trans m₂
    have hop : op.InBounds ctx₂.spec := m₂.op hop₁
    let inv' := s.inv.setCtx wf₂ m
    let numResults := (IR.numResults ctx₂ op).toNat
    return (⟨{ d with
        ctx := ctx₂
        pendingOperands := d.pendingOperands.drop nOperands
        pendingBlockOperands := d.pendingBlockOperands.drop nBlockOperands
        pendingRegions := d.pendingRegions.drop nRegions
        lastOp := some op },
      { inv' with
        pendingRegions := fun r hr => inv'.pendingRegions r (List.mem_of_mem_drop hr)
        pendingOperands := fun v hv => inv'.pendingOperands v (List.mem_of_mem_drop hv)
        pendingBlockOperands := fun b hb => inv'.pendingBlockOperands b (List.mem_of_mem_drop hb)
        lastOp := by
          intro l hl
          simp only [Option.some.injEq] at hl
          subst hl
          exact ⟨hop, fun hmem => hfresh (s.inv.garbage op hmem)⟩ }⟩, op, numResults)

/-! ## Blocks -/

/--
  Define the block `name` of the innermost region with the given argument types, inserting it at
  the end of that region, and make it the block being parsed. If the block was forward-declared,
  it is inserted instead (its argument types must match the ones found when it was declared).
  Returns the number of arguments of the block.
-/
def defineBlock (s : IRState) (name : Name) (argTypes : Array TypeAttr) (loc : Location) :
    Except ParserError (IRState × Nat) := do
  let d := s.data
  match hscopes : d.blockScopes with
  | [] => throw { msg := "internal error: no block scope", pos := some loc }
  | scope :: rest =>
    match hregions : d.openRegions with
    | [] => throw { msg := "internal error: no region to insert the block into", pos := some loc }
    | region :: _ =>
      have hregion : region.InBounds d.ctx.spec :=
        s.inv.openRegions region (hregions ▸ List.mem_cons_self ..)
      let ip := BlockInsertPoint.atEnd region
      have hip : ip.InBounds d.ctx.spec := hregion
      let step : BlockStep d.ctx ←
        match hentry : scope[name]? with
        | some (.Defined _ prevLoc) =>
          throw (({ msg := s!"block %{String.fromUTF8! name} has already been defined",
                    pos := some loc } : ParserError).addNote prevLoc "block previously defined here")
        | some (.ForwardDeclared placeholder fwdArgTypes _) =>
          if fwdArgTypes ≠ argTypes then
            throw { msg := "internal error: block argument types differ from the forward declaration", pos := some loc }
          else
            have hplaceholder : placeholder.InBounds d.ctx.spec :=
              s.inv.blocks scope (hscopes ▸ List.mem_cons_self ..) name _ hentry
            match hins : IR.insertBlock d.ctx placeholder ip s.inv.wf hplaceholder hip with
            | none => throw { msg := "internal error: failed to insert block", pos := some loc }
            | some ctx' =>
              have m : Mono d.ctx ctx' := IR.insertBlock_inBounds_mono hins
              pure ({ next := ctx', wf := IR.insertBlock_wellFormed hins, mono := m,
                      block := placeholder, hb := m.block hplaceholder } : BlockStep d.ctx)
        | none =>
          match hcreate : IR.createBlock d.ctx argTypes (some ip) s.inv.wf
              ((Option.maybe_def _ _ _).mpr fun z hz => by cases hz; exact hip) with
          | none => throw { msg := "internal error: failed to create block", pos := some loc }
          | some (ctx', sb) =>
            pure ({ next := ctx', wf := IR.createBlock_wellFormed hcreate,
                    mono := IR.createBlock_inBounds_mono hcreate, block := sb.spec,
                    hb := IR.createBlock_new_inBounds hcreate } : BlockStep d.ctx)
      let ctx' := step.next
      let block := step.block
      have wf' := step.wf
      have m := step.mono
      have hb := step.hb
      let inv' := s.inv.setCtx wf' m
      let numArgs := (IR.numArguments ctx' block).toNat
      return (⟨{ d with
          ctx := ctx'
          blockScopes := scope.insert name (.Defined block loc) :: rest
          openBlocks := block :: d.openBlocks },
        { inv' with
          blocks := by
            intro sc hsc k e hget
            rcases List.mem_cons.mp hsc with rfl | hsc
            · rw [Std.HashMap.getElem?_insert] at hget
              split at hget
              · simp only [Option.some.injEq] at hget
                subst hget
                exact hb
              · exact inv'.blocks scope (hscopes ▸ List.mem_cons_self ..) k e hget
            · exact inv'.blocks sc (hscopes ▸ List.mem_cons_of_mem _ hsc) k e hget
          openBlocks := by
            intro c hc
            rcases List.mem_cons.mp hc with rfl | hc
            · exact hb
            · exact inv'.openBlocks c hc }⟩, numArgs)

/-- Leave the block being parsed. -/
def closeBlock (s : IRState) : IRState :=
  ⟨{ s.data with openBlocks := s.data.openBlocks.tail },
    { s.inv with openBlocks := fun b hb => s.inv.openBlocks b (List.mem_of_mem_tail hb) }⟩

/-! ## Regions -/

/-- Create a region, make it the region being parsed, and open a fresh block scope for it. -/
def openRegion (s : IRState) (pos : Location) : Except ParserError IRState := do
  let d := s.data
  match hcreate : IR.createRegion d.ctx with
  | none => throw { msg := "internal error: failed to create region", pos := some pos }
  | some (ctx', sr) =>
    let region := sr.spec
    have wf' := IR.createRegion_wellFormed s.inv.wf hcreate
    have m : Mono d.ctx ctx' := IR.createRegion_inBounds_mono hcreate
    have hr : region.InBounds ctx'.spec := IR.createRegion_new_inBounds hcreate
    let inv' := s.inv.setCtx wf' m
    return ⟨{ d with
        ctx := ctx'
        openRegions := region :: d.openRegions
        blockScopes := Std.HashMap.emptyWithCapacity 1 :: d.blockScopes },
      { inv' with
        openRegions := by
          intro r hr'
          rcases List.mem_cons.mp hr' with rfl | hr'
          · exact hr
          · exact inv'.openRegions r hr'
        blocks := by
          intro sc hsc k e hget
          rcases List.mem_cons.mp hsc with rfl | hsc
          · simp at hget
          · exact inv'.blocks sc hsc k e hget }⟩

/-- Leave the region being parsed: close its block scope and make the region available to the
operation being parsed. -/
def closeRegion (s : IRState) (pos : Location) : Except ParserError IRState := do
  let d := s.data
  match hregions : d.openRegions with
  | [] => throw { msg := "internal error: no region to close", pos := some pos }
  | region :: rest =>
    have hr : region.InBounds d.ctx.spec := s.inv.openRegions region (hregions ▸ List.mem_cons_self ..)
    return ⟨{ d with
        openRegions := rest
        pendingRegions := region :: d.pendingRegions
        blockScopes := d.blockScopes.tail },
      { s.inv with
        openRegions := fun r hr' => s.inv.openRegions r (hregions ▸ List.mem_cons_of_mem _ hr')
        pendingRegions := by
          intro r hr'
          rcases List.mem_cons.mp hr' with rfl | hr'
          · exact hr
          · exact s.inv.pendingRegions r hr'
        blocks := fun sc hsc => s.inv.blocks sc (List.mem_of_mem_tail hsc) }⟩

/-! ## Finishing -/

/-- The result of parsing: a well-formed context and an in-bounds top-level operation. -/
structure Result where
  ctx : IR.Ctx
  op : IR.Op
  wf : ctx.spec.WellFormed
  opInBounds : op.InBounds ctx.spec

/-- Erase the given (distinct) operations, keeping `top` in bounds. -/
def eraseAll (top : IR.Op) :
    (ctx : IR.Ctx) → (l : List IR.Op) → (wf : ctx.spec.WellFormed) →
    (hl : ∀ p ∈ l, p.InBounds ctx.spec) → (nd : l.Pairwise (· ≠ ·)) →
    (htop : top.InBounds ctx.spec) → (hnot : top ∉ l) → Except ParserError Result
  | ctx, [], wf, _, _, htop, _ => .ok ⟨ctx, top, wf, htop⟩
  | ctx, p :: rest, wf, hl, nd, htop, hnot =>
    match herase : IR.eraseOp ctx p wf (hl p (List.mem_cons_self ..)) with
    | none => .error { msg := "internal error: failed to erase a forward-reference placeholder" }
    | some ctx' =>
      have wf' := IR.eraseOp_wellFormed herase
      have hrest : ∀ q ∈ rest, q.InBounds ctx'.spec := fun q hq =>
        IR.eraseOp_inBounds_mono herase q (hl q (List.mem_cons_of_mem _ hq))
          (List.rel_of_pairwise_cons nd hq).symm
      have htop' : top.InBounds ctx'.spec :=
        IR.eraseOp_inBounds_mono herase top htop (fun h => hnot (h ▸ List.mem_cons_self ..))
      eraseAll top ctx' rest wf' hrest (List.Pairwise.of_cons nd) htop'
        (fun h => hnot (List.mem_cons_of_mem _ h))

/-- Finish parsing: erase the placeholder operations and return the operation created last (the
top-level operation) with the final context. -/
def finish (s : IRState) : Except ParserError Result := do
  let d := s.data
  match hlast : d.lastOp with
  | none => throw { msg := "internal error: no top-level operation" }
  | some top =>
    have hl := s.inv.lastOp top hlast
    have htop := hl.1
    have hnot := hl.2
    let l := d.garbage.toList
    have hl : ∀ p ∈ l, p.InBounds d.ctx.spec := fun p hp =>
      s.inv.garbage p (Std.HashSet.mem_toList.mp hp)
    have nd : l.Pairwise (· ≠ ·) :=
      Std.HashSet.distinct_toList.imp fun h => beq_eq_false_iff_ne.mp h
    eraseAll top d.ctx l s.inv.wf hl nd htop (fun h => hnot (Std.HashSet.mem_toList.mp h))

end IRState

end Veir.Parser

end

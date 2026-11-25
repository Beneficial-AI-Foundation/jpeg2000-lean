/-
Axiom audit, run by `scripts/check-hygiene.sh` via `lake env lean scripts/axioms.lean`
(Plan.md section 3 rule 1, task 0.3).

Every top-level theorem of the project must depend only on `propext`, `Classical.choice` and
`Quot.sound` (CLAUDE.md, Plan.md section 3).  The guard parses the output of this file and
fails on any other axiom (including `sorryAx`, `Lean.ofReduceBool`, `Lean.trustCompiler` and
the auxiliary axioms `native_decide` creates), and on any `#print axioms` line that produced
no result.  `scripts/hygiene.py` also fails if a non-private `theorem` in `JPEG2000/` or
`Spec/` is not listed here.

To add a check: make sure the module is reachable from the imports below (the umbrellas
import every module), then add one line
    #print axioms Namespace.theorem_name
under a comment naming the task.  This file is a shared registry (CLAUDE.md): subagents report
the lines to add; the orchestrator adds them.  It is outside the libraries and never imported.
-/
import JPEG2000
import Spec
import Encode

/-! ## Guard self-check

Two theorems defined here so that the check exercises a real `#print axioms` result even
before the project has theorems: one with no axioms, one that uses all three allowed ones. -/

namespace AxiomsSelfCheck

/-- No axioms at all. -/
theorem noAxioms (a b : Nat) : a + b = b + a := Nat.add_comm a b

/-- Excluded middle: depends on `propext`, `Classical.choice`, `Quot.sound`. -/
theorem allowedAxioms (p : Prop) : p ∨ ¬p := Classical.em p

end AxiomsSelfCheck

#print axioms AxiomsSelfCheck.noAxioms
#print axioms AxiomsSelfCheck.allowedAxioms

/-! ## Project theorems (one line per top-level theorem, grouped by task) -/

-- Phase 0, task 0.2: limits (JPEG2000/Limits.lean)
#print axioms JPEG2000.Limits.checkLe_eq_ok_iff
#print axioms JPEG2000.Limits.check_eq_ok_iff
#print axioms JPEG2000.Limits.checkLe_eq_error
#print axioms JPEG2000.Limits.strict_le_default

-- Phase 1, task 1.1: bytes (JPEG2000/Bytes.lean)
#print axioms JPEG2000.Bytes.Reader.pos_le_size
#print axioms JPEG2000.Bytes.Reader.u8_pos
#print axioms JPEG2000.Bytes.Reader.u16be_pos
#print axioms JPEG2000.Bytes.Reader.u32be_pos
#print axioms JPEG2000.Bytes.Reader.u64be_pos
#print axioms JPEG2000.Bytes.Reader.skip_pos
#print axioms JPEG2000.Bytes.Reader.take_spec
#print axioms JPEG2000.Bytes.Reader.u8_error
#print axioms JPEG2000.Bytes.BitReader.load_pos
#print axioms JPEG2000.Bytes.BitReader.bit_pos
#print axioms JPEG2000.Bytes.BitReader.bitsAux_pos
#print axioms JPEG2000.Bytes.BitReader.bits_pos
#print axioms JPEG2000.Bytes.BitReader.align_pos
#print axioms JPEG2000.Bytes.size_pushZeros
#print axioms JPEG2000.Bytes.get_pushZeros
#print axioms JPEG2000.Bytes.Plane.zero_dims
#print axioms JPEG2000.Bytes.Plane.set_dims
#print axioms JPEG2000.Bytes.Plane.get_set_self
#print axioms JPEG2000.Bytes.Plane.get_set_ne
#print axioms JPEG2000.Bytes.Plane.get_zero

-- Phase 1, task 1.2: boxes (JPEG2000/Box.lean)
#print axioms JPEG2000.Box.parseFile_range

-- Phase 2, task 2.1: MQ spec (Spec/MQ.lean)
#print axioms JPEG2000.Spec.MQ.qe_bounds
#print axioms JPEG2000.Spec.MQ.qeAt_qe_bounds
#print axioms JPEG2000.Spec.MQ.bit15_iff
#print axioms JPEG2000.Spec.MQ.bytein_A
#print axioms JPEG2000.Spec.MQ.bytein_C_lt
#print axioms JPEG2000.Spec.MQ.bytein_CT_le
#print axioms JPEG2000.Spec.MQ.bytein_pos_le
#print axioms JPEG2000.Spec.MQ.bytein_data
#print axioms JPEG2000.Spec.MQ.renormStep_A
#print axioms JPEG2000.Spec.MQ.renormLoop_bit15
#print axioms JPEG2000.Spec.MQ.renormd_fuel_suffices
#print axioms JPEG2000.Spec.MQ.lpsExchange_A
#print axioms JPEG2000.Spec.MQ.decode_A_range

-- Phase 1, task 1.6: marker round trip (Spec/MarkerRoundTrip.lean)
#print axioms JPEG2000.Spec.MarkerRoundTrip.be16_val
#print axioms JPEG2000.Spec.MarkerRoundTrip.be32_val
#print axioms JPEG2000.Spec.MarkerRoundTrip.rd_ofByteArray
#print axioms JPEG2000.Spec.MarkerRoundTrip.rd_get
#print axioms JPEG2000.Spec.MarkerRoundTrip.rd_adv
#print axioms JPEG2000.Spec.MarkerRoundTrip.rd_len
#print axioms JPEG2000.Spec.MarkerRoundTrip.rd_u8
#print axioms JPEG2000.Spec.MarkerRoundTrip.rd_u16
#print axioms JPEG2000.Spec.MarkerRoundTrip.rd_u32
#print axioms JPEG2000.Spec.MarkerRoundTrip.rd_readArray
#print axioms JPEG2000.Spec.MarkerRoundTrip.rd_readArray'
#print axioms JPEG2000.Spec.MarkerRoundTrip.rd_expectEnd
#print axioms JPEG2000.Spec.MarkerRoundTrip.parseSIZ_rd
#print axioms JPEG2000.Spec.MarkerRoundTrip.parseSIZ_roundTrip
#print axioms JPEG2000.Spec.MarkerRoundTrip.readCodingStyle_rd
#print axioms JPEG2000.Spec.MarkerRoundTrip.progression_roundTrip
#print axioms JPEG2000.Spec.MarkerRoundTrip.parseCOD_rd
#print axioms JPEG2000.Spec.MarkerRoundTrip.readCompIndex_rd
#print axioms JPEG2000.Spec.MarkerRoundTrip.readComponent_rd
#print axioms JPEG2000.Spec.MarkerRoundTrip.parseCOC_rd
#print axioms JPEG2000.Spec.MarkerRoundTrip.parseCOD_roundTrip
#print axioms JPEG2000.Spec.MarkerRoundTrip.parseCOC_roundTrip
#print axioms JPEG2000.Spec.MarkerRoundTrip.readQuant_rd
#print axioms JPEG2000.Spec.MarkerRoundTrip.parseQCD_rd
#print axioms JPEG2000.Spec.MarkerRoundTrip.parseQCD_roundTrip
#print axioms JPEG2000.Spec.MarkerRoundTrip.parseQCC_rd
#print axioms JPEG2000.Spec.MarkerRoundTrip.parseQCC_roundTrip
#print axioms JPEG2000.Spec.MarkerRoundTrip.parseRGN_rd
#print axioms JPEG2000.Spec.MarkerRoundTrip.parsePOC_rd
#print axioms JPEG2000.Spec.MarkerRoundTrip.rd_rest
#print axioms JPEG2000.Spec.MarkerRoundTrip.parseCOM_rd
#print axioms JPEG2000.Spec.MarkerRoundTrip.parseCRG_rd
#print axioms JPEG2000.Spec.MarkerRoundTrip.parseRGN_roundTrip
#print axioms JPEG2000.Spec.MarkerRoundTrip.parsePOC_roundTrip
#print axioms JPEG2000.Spec.MarkerRoundTrip.parseCOM_roundTrip
#print axioms JPEG2000.Spec.MarkerRoundTrip.parseCRG_roundTrip
#print axioms JPEG2000.Spec.MarkerRoundTrip.rd_take
#print axioms JPEG2000.Spec.MarkerRoundTrip.segment_rd
#print axioms JPEG2000.Spec.MarkerRoundTrip.pack_append
#print axioms JPEG2000.Spec.MarkerRoundTrip.segment_roundTrip
#print axioms JPEG2000.Spec.MarkerRoundTrip.parseCOD_segment

-- Phase 2, task 2.2: MQ encoder (Encode/MQ.lean)
#print axioms JPEG2000.Encode.MQ.renormeStep_A
#print axioms JPEG2000.Encode.MQ.renormeLoop_bit15
#print axioms JPEG2000.Encode.MQ.renorme_fuel_suffices
#print axioms JPEG2000.Encode.MQ.encode_A_range

-- Phase 2, task 2.3: fast MQ decoder (JPEG2000/MQ.lean, Spec/MQTable.lean)
#print axioms JPEG2000.MQ.qeTab_size
#print axioms JPEG2000.Spec.MQTable.mkEntry_agree
#print axioms JPEG2000.Spec.MQTable.entry_eq
#print axioms JPEG2000.Spec.MQTable.qeTab_agree
#print axioms JPEG2000.Spec.MQTable.stateOf_packCx

-- Phase 2, task 2.4: C1 MQ round trip (Spec/MQRoundTrip.lean)
#print axioms JPEG2000.Spec.MQRoundTrip.roundTrip
#print axioms JPEG2000.Spec.MQRoundTrip.run_Q
#print axioms JPEG2000.Spec.MQRoundTrip.dec_many

-- Phase 2, task 2.5: C2 fast MQ = spec (Spec/MQEquiv.lean)
#print axioms JPEG2000.Spec.MQEquiv.byteAt_lt
#print axioms JPEG2000.Spec.MQEquiv.bytein_sim
#print axioms JPEG2000.Spec.MQEquiv.bit_fast
#print axioms JPEG2000.Spec.MQEquiv.bytein_cx
#print axioms JPEG2000.Spec.MQEquiv.spec_bytein_CT
#print axioms JPEG2000.Spec.MQEquiv.renormStep_sim
#print axioms JPEG2000.Spec.MQEquiv.renormLoop_sim
#print axioms JPEG2000.Spec.MQEquiv.renormd_sim
#print axioms JPEG2000.Spec.MQEquiv.ctxSet_size
#print axioms JPEG2000.Spec.MQEquiv.ctxGet_ctxSet
#print axioms JPEG2000.Spec.MQEquiv.contexts_get_put
#print axioms JPEG2000.Spec.MQEquiv.cxRel_set
#print axioms JPEG2000.Spec.MQEquiv.mps_fast
#print axioms JPEG2000.Spec.MQEquiv.decode_sim
#print axioms JPEG2000.Spec.MQEquiv.decodeList_sim
#print axioms JPEG2000.Spec.MQEquiv.segment_byteAt
#print axioms JPEG2000.Spec.MQEquiv.toList_eq_data_toList
#print axioms JPEG2000.Spec.MQEquiv.segment_full
#print axioms JPEG2000.Spec.MQEquiv.init_sim
#print axioms JPEG2000.Spec.MQEquiv.initContexts_size
#print axioms JPEG2000.Spec.MQEquiv.initContexts_rel
#print axioms JPEG2000.Spec.MQEquiv.decode_init_eq
#print axioms JPEG2000.Spec.MQEquiv.decodeAll_eq
#print axioms JPEG2000.Spec.MQEquiv.renormStep_a
#print axioms JPEG2000.Spec.MQEquiv.renormLoop_a_range
#print axioms JPEG2000.Spec.MQEquiv.renormd_fuel_suffices_fast
#print axioms JPEG2000.Spec.MQEquiv.decode_a_range

-- Phase 3, task 3.1: Tier-1 context tables (Spec/Tier1/Context.lean)
#print axioms JPEG2000.Spec.Tier1.initialStates_eq
#print axioms JPEG2000.Spec.Tier1.initialStates_length
#print axioms JPEG2000.Spec.Tier1.zcContext_LL_eq_LH
#print axioms JPEG2000.Spec.Tier1.zcContext_HL_swap
#print axioms JPEG2000.Spec.Tier1.zcContext_HH_symm
#print axioms JPEG2000.Spec.Tier1.zcContext_clamp
#print axioms JPEG2000.Spec.Tier1.zcContext_le
#print axioms JPEG2000.Spec.Tier1.zcContext_eq_zero_iff
#print axioms JPEG2000.Spec.Tier1.zcContext_mono_h
#print axioms JPEG2000.Spec.Tier1.zcContext_mono_v
#print axioms JPEG2000.Spec.Tier1.zcContext_mono_d
#print axioms JPEG2000.Spec.Tier1.signContribution_comm
#print axioms JPEG2000.Spec.Tier1.signContribution_range
#print axioms JPEG2000.Spec.Tier1.signContribution_eq_clamp
#print axioms JPEG2000.Spec.Tier1.scContext_range
#print axioms JPEG2000.Spec.Tier1.scContext_neg_fst
#print axioms JPEG2000.Spec.Tier1.scContext_neg_snd
#print axioms JPEG2000.Spec.Tier1.scContext_zero
#print axioms JPEG2000.Spec.Tier1.mrContext_range
#print axioms JPEG2000.Spec.Tier1.contexts_partition

-- Phase 1, task 1.10: tile-part segment round trip (Spec/TilePartRoundTrip.lean)
#print axioms JPEG2000.Spec.TilePartRoundTrip.parseSOT_rd
#print axioms JPEG2000.Spec.TilePartRoundTrip.parseSOT_roundTrip
#print axioms JPEG2000.Spec.TilePartRoundTrip.parseTLM_rd
#print axioms JPEG2000.Spec.TilePartRoundTrip.parseTLM_roundTrip
#print axioms JPEG2000.Spec.TilePartRoundTrip.varintHigh_succ
#print axioms JPEG2000.Spec.TilePartRoundTrip.readVarints_high
#print axioms JPEG2000.Spec.TilePartRoundTrip.readVarints_encodeVarint
#print axioms JPEG2000.Spec.TilePartRoundTrip.readVarints_list
#print axioms JPEG2000.Spec.TilePartRoundTrip.parsePLT_rd
#print axioms JPEG2000.Spec.TilePartRoundTrip.parsePLT_roundTrip
#print axioms JPEG2000.Spec.TilePartRoundTrip.rd_range
#print axioms JPEG2000.Spec.TilePartRoundTrip.parsePPM_rd
#print axioms JPEG2000.Spec.TilePartRoundTrip.parsePPT_rd
#print axioms JPEG2000.Spec.TilePartRoundTrip.parsePPM_roundTrip
#print axioms JPEG2000.Spec.TilePartRoundTrip.parsePPT_roundTrip

-- Phase 3, task 3.2: Tier-1 spec decoder (Spec/Tier1/Decode.lean)
#print axioms JPEG2000.Spec.Tier1.passKind_cycle
#print axioms JPEG2000.Spec.Tier1.passPlane_group
#print axioms JPEG2000.Spec.Tier1.stripeColumn_length_le
#print axioms JPEG2000.Spec.Tier1.mem_scanOrder

-- Phase 3, task 3.3: Tier-1 code-block styles (Spec/Tier1/Modes.lean, Spec/Tier1/Decode.lean;
-- passKind_cycle and passPlane_group above moved to Modes.lean)
#print axioms JPEG2000.Spec.Tier1.segmentRuns_sum
#print axioms JPEG2000.Spec.Tier1.segmentPasses_sum
#print axioms JPEG2000.Spec.Tier1.segmentRuns_pos
#print axioms JPEG2000.Spec.Tier1.segmentPasses_pos
#print axioms JPEG2000.Spec.Tier1.segmentRuns_noTerm
#print axioms JPEG2000.Spec.Tier1.segmentPasses_plain
#print axioms JPEG2000.Spec.Tier1.segmentRuns_termAll
#print axioms JPEG2000.Spec.Tier1.segmentPasses_termAll
#print axioms JPEG2000.Spec.Tier1.isRawPass_noBypass
#print axioms JPEG2000.Spec.Tier1.runPassM_plain
#print axioms JPEG2000.Spec.Tier1.decodeState_plain
#print axioms JPEG2000.Spec.Tier1.geom_vertCausal_plain

-- Phase 4, task 4.1: tag trees, C4 (Spec/TagTree.lean)
#print axioms JPEG2000.Spec.TagTree.value_monotone
#print axioms JPEG2000.Spec.TagTree.inv_init
#print axioms JPEG2000.Spec.TagTree.encodeAll_spec
#print axioms JPEG2000.Spec.TagTree.decodeAll_encodeAll
#print axioms JPEG2000.Spec.TagTree.decode_encode
#print axioms JPEG2000.Spec.TagTree.decode_encode_init
#print axioms JPEG2000.Spec.TagTree.idx_inj
#print axioms JPEG2000.Spec.TagTree.walk_corr
#print axioms JPEG2000.Spec.TagTree.create_rel
#print axioms JPEG2000.Spec.TagTree.fast_decode_eq
#print axioms JPEG2000.Spec.TagTree.fast_decodeValue_eq

-- Phase 3, task 3.4a: fast Tier-1 tables (JPEG2000/Tier1/Tables.lean)
#print axioms JPEG2000.Tier1.zcTable_size
#print axioms JPEG2000.Tier1.zcFor_eq
#print axioms JPEG2000.Tier1.zcFor_size
#print axioms JPEG2000.Tier1.scLut_size
#print axioms JPEG2000.Encode.Tier1.lt_two_pow_numBits

-- Phase 4, task 4.3: progression orders, C5 (Spec/Progression.lean)
#print axioms JPEG2000.Spec.Progression.forRange_eq
#print axioms JPEG2000.Spec.Progression.mem_dedup
#print axioms JPEG2000.Spec.Progression.nodup_dedup
#print axioms JPEG2000.Spec.Progression.Axis.cdiv_cdiv
#print axioms JPEG2000.Spec.Progression.Axis.ref_spec
#print axioms JPEG2000.Spec.Progression.Axis.col_spec
#print axioms JPEG2000.Spec.Progression.precAt_some
#print axioms JPEG2000.Spec.Progression.precAt_ref
#print axioms JPEG2000.Spec.Progression.sortedPrecincts_eq
#print axioms JPEG2000.Spec.Progression.c5_volume
#print axioms JPEG2000.Spec.Progression.c5
#print axioms JPEG2000.Spec.Progression.c5_perm
#print axioms JPEG2000.Spec.Progression.c5_poc
#print axioms JPEG2000.Spec.Progression.packets_noPoc
#print axioms JPEG2000.Spec.Progression.forVolume_eq_spec
#print axioms JPEG2000.Spec.Progression.forPackets_eq_spec

-- Phase 5, task 5.2: 5/3 DWT, C6 (Spec/DWT53.lean, JPEG2000/DWT53.lean)
#print axioms JPEG2000.DWT53.idx_lt
#print axioms JPEG2000.DWT53.srcIdx_lt
#print axioms JPEG2000.DWT53.halfN_le
#print axioms JPEG2000.DWT53.upd_exact
#print axioms JPEG2000.DWT53.pred_exact
#print axioms JPEG2000.DWT53.narrow_exact
#print axioms JPEG2000.DWT53.Buf.get_set
#print axioms JPEG2000.DWT53.liftPass_ok
#print axioms JPEG2000.DWT53.liftPass_spec
#print axioms JPEG2000.DWT53.unupdate_sym
#print axioms JPEG2000.DWT53.sym_left
#print axioms JPEG2000.DWT53.sym_right
#print axioms JPEG2000.DWT53.lift1d_eq_sr1d
#print axioms JPEG2000.Spec.DWT53.unpredict_predict
#print axioms JPEG2000.Spec.DWT53.unupdate_update
#print axioms JPEG2000.Spec.DWT53.predict_sym
#print axioms JPEG2000.Spec.DWT53.update_sym
#print axioms JPEG2000.Spec.DWT53.sym_shift
#print axioms JPEG2000.Spec.DWT53.pse_mem
#print axioms JPEG2000.Spec.DWT53.pse_id
#print axioms JPEG2000.Spec.DWT53.sym_pse
#print axioms JPEG2000.Spec.DWT53.ext_sym
#print axioms JPEG2000.Spec.DWT53.sr1d_sd1d
#print axioms JPEG2000.Spec.DWT53.sr1d_local
#print axioms JPEG2000.Spec.DWT53.sd1d_local
#print axioms JPEG2000.Spec.DWT53.ofList_get
#print axioms JPEG2000.Spec.DWT53.sr1dList_sd1dList
#print axioms JPEG2000.Spec.DWT53.memo_eq
#print axioms JPEG2000.Spec.DWT53.sr2d_local
#print axioms JPEG2000.Spec.DWT53.sr2d_sd2d
#print axioms JPEG2000.Spec.DWT53.interleave_deinterleave
#print axioms JPEG2000.Spec.DWT53.srMulti_sdMulti

-- Phase 3, task 3.6: C3 plain mode (Spec/Tier1Equiv*)
-- Phase 3, task 3.6: C3 fast Tier-1 = spec, plain mode (Spec/Tier1Equiv.lean, Spec/Tier1Equiv/*.lean)
#print axioms JPEG2000.Spec.Tier1Equiv.coeffAt_replicate
#print axioms JPEG2000.Spec.Tier1Equiv.fget_replicate
#print axioms JPEG2000.Spec.Tier1Equiv.init_rel
#print axioms JPEG2000.Spec.Tier1Equiv.get?_set
#print axioms JPEG2000.Spec.Tier1Equiv.fillRow_dims
#print axioms JPEG2000.Spec.Tier1Equiv.fillRow_get
#print axioms JPEG2000.Spec.Tier1Equiv.row_iff
#print axioms JPEG2000.Spec.Tier1Equiv.fillRows_dims
#print axioms JPEG2000.Spec.Tier1Equiv.fillRows_get
#print axioms JPEG2000.Spec.Tier1Equiv.toInt_toInt32
#print axioms JPEG2000.Spec.Tier1Equiv.toInt_neg_toInt32
#print axioms JPEG2000.Spec.Tier1Equiv.negTest_rel
#print axioms JPEG2000.Spec.Tier1Equiv.val_toInt
#print axioms JPEG2000.Spec.Tier1Equiv.specBlock_numPasses
#print axioms JPEG2000.Spec.Tier1Equiv.validate_eq
#print axioms JPEG2000.Spec.Tier1Equiv.specBlock_coeffs
#print axioms JPEG2000.Spec.Tier1Equiv.out_ok
#print axioms JPEG2000.Spec.Tier1Equiv.c3_plain
#print axioms JPEG2000.Spec.Tier1Equiv.testBit_lit
#print axioms JPEG2000.Spec.Tier1Equiv.ite_pos'
#print axioms JPEG2000.Spec.Tier1Equiv.ite_neg'
#print axioms JPEG2000.Spec.Tier1Equiv.bt_or
#print axioms JPEG2000.Spec.Tier1Equiv.bt_and
#print axioms JPEG2000.Spec.Tier1Equiv.bt_ge32
#print axioms JPEG2000.Spec.Tier1Equiv.eq_zero_iff_bt
#print axioms JPEG2000.Spec.Tier1Equiv.bt_hi
#print axioms JPEG2000.Spec.Tier1Equiv.and_eq_zero_iff
#print axioms JPEG2000.Spec.Tier1Equiv.bitOf_lt8
#print axioms JPEG2000.Spec.Tier1Equiv.rowcol_inj
#print axioms JPEG2000.Spec.Tier1Equiv.nb_lt_size
#print axioms JPEG2000.Spec.Tier1Equiv.fset_size
#print axioms JPEG2000.Spec.Tier1Equiv.fadd_size
#print axioms JPEG2000.Spec.Tier1Equiv.fget_fset
#print axioms JPEG2000.Spec.Tier1Equiv.fget_fadd
#print axioms JPEG2000.Spec.Tier1Equiv.coeffAt_nat
#print axioms JPEG2000.Spec.Tier1Equiv.idx_lt
#print axioms JPEG2000.Spec.Tier1Equiv.coeffAt_setCoeff
#print axioms JPEG2000.Spec.Tier1Equiv.setCoeff_size
#print axioms JPEG2000.Spec.Tier1Equiv.zcLLLH_eq
#print axioms JPEG2000.Spec.Tier1Equiv.zcHHcol_eq
#print axioms JPEG2000.Spec.Tier1Equiv.zcOf_eq
#print axioms JPEG2000.Spec.Tier1Equiv.zcOf_le
#print axioms JPEG2000.Spec.Tier1Equiv.zcCtx_eq
#print axioms JPEG2000.Spec.Tier1Equiv.scOf_eq_all
#print axioms JPEG2000.Spec.Tier1Equiv.scOf_lt
#print axioms JPEG2000.Spec.Tier1Equiv.scIndex_bit
#print axioms JPEG2000.Spec.Tier1Equiv.bitOf_eq
#print axioms JPEG2000.Spec.Tier1Equiv.scEntry_eq
#print axioms JPEG2000.Spec.Tier1Equiv.mem_stripeColumn
#print axioms JPEG2000.Spec.Tier1Equiv.scanOrder_eq
#print axioms JPEG2000.Spec.Tier1Equiv.scanOrder_nodup
#print axioms JPEG2000.Spec.Tier1Equiv.mem_scanOrder_iff
#print axioms JPEG2000.Spec.Tier1Equiv.allP_set
#print axioms JPEG2000.Spec.Tier1Equiv.decodeBit_split
#print axioms JPEG2000.Spec.Tier1Equiv.becomeSignificant_coeffs
#print axioms JPEG2000.Spec.Tier1Equiv.becomeSignificant_base
#print axioms JPEG2000.Spec.Tier1Equiv.zeroCode_cases
#print axioms JPEG2000.Spec.Tier1Equiv.ISP.base
#print axioms JPEG2000.Spec.Tier1Equiv.sigPropStep_inv
#print axioms JPEG2000.Spec.Tier1Equiv.foldl_allP
#print axioms JPEG2000.Spec.Tier1Equiv.sigPropPass_inv
#print axioms JPEG2000.Spec.Tier1Equiv.foldl_ordered
#print axioms JPEG2000.Spec.Tier1Equiv.add_pow_lt
#print axioms JPEG2000.Spec.Tier1Equiv.magRefPass_inv
#print axioms JPEG2000.Spec.Tier1Equiv.cleanupStep_inv
#print axioms JPEG2000.Spec.Tier1Equiv.cleanupColumn_inv
#print axioms JPEG2000.Spec.Tier1Equiv.mem_stripeColumns
#print axioms JPEG2000.Spec.Tier1Equiv.cleanupPass_inv
#print axioms JPEG2000.Spec.Tier1Equiv.passKind_mul3
#print axioms JPEG2000.Spec.Tier1Equiv.runPass_inv
#print axioms JPEG2000.Spec.Tier1Equiv.decodePasses_inv
#print axioms JPEG2000.Spec.Tier1Equiv.bt_pow
#print axioms JPEG2000.Spec.Tier1Equiv.bt_ite
#print axioms JPEG2000.Spec.Tier1Equiv.bt_zero
#print axioms JPEG2000.Spec.Tier1Equiv.bt_SIG_N
#print axioms JPEG2000.Spec.Tier1Equiv.bt_SIG_W
#print axioms JPEG2000.Spec.Tier1Equiv.bt_SIG_E
#print axioms JPEG2000.Spec.Tier1Equiv.bt_SIG_S
#print axioms JPEG2000.Spec.Tier1Equiv.bt_SIG_NW
#print axioms JPEG2000.Spec.Tier1Equiv.bt_SIG_NE
#print axioms JPEG2000.Spec.Tier1Equiv.bt_SIG_SW
#print axioms JPEG2000.Spec.Tier1Equiv.bt_SIG_SE
#print axioms JPEG2000.Spec.Tier1Equiv.bt_NEG_N
#print axioms JPEG2000.Spec.Tier1Equiv.bt_NEG_W
#print axioms JPEG2000.Spec.Tier1Equiv.bt_NEG_E
#print axioms JPEG2000.Spec.Tier1Equiv.bt_NEG_S
#print axioms JPEG2000.Spec.Tier1Equiv.bt_SIG
#print axioms JPEG2000.Spec.Tier1Equiv.bt_NEG
#print axioms JPEG2000.Spec.Tier1Equiv.bt_VIS
#print axioms JPEG2000.Spec.Tier1Equiv.bt_REF
#print axioms JPEG2000.Spec.Tier1Equiv.nbPos_eq_iff
#print axioms JPEG2000.Spec.Tier1Equiv.bt_nbMask
#print axioms JPEG2000.Spec.Tier1Equiv.bt_nbMask_hi
#print axioms JPEG2000.Spec.Tier1Equiv.nbPos_ne
#print axioms JPEG2000.Spec.Tier1Equiv.bidx_forms
#print axioms JPEG2000.Spec.Tier1Equiv.idx_eq_iff
#print axioms JPEG2000.Spec.Tier1Equiv.flags_after
#print axioms JPEG2000.Spec.Tier1Equiv.bidx_down
#print axioms JPEG2000.Spec.Tier1Equiv.bidx_right
#print axioms JPEG2000.Spec.Tier1Equiv.bidx_zero
#print axioms JPEG2000.Spec.Tier1Equiv.stripeColumn_eq
#print axioms JPEG2000.Spec.Tier1Equiv.foldl_fix
#print axioms JPEG2000.Spec.Tier1Equiv.colRows_succ
#print axioms JPEG2000.Spec.Tier1Equiv.colRows_zero
#print axioms JPEG2000.Spec.Tier1Equiv.colRows_rel
#print axioms JPEG2000.Spec.Tier1Equiv.or_test
#print axioms JPEG2000.Spec.Tier1Equiv.colOr_test
#print axioms JPEG2000.Spec.Tier1Equiv.colOr_test'
#print axioms JPEG2000.Spec.Tier1Equiv.range4
#print axioms JPEG2000.Spec.Tier1Equiv.spCol_rel
#print axioms JPEG2000.Spec.Tier1Equiv.mrCol_rel
#print axioms JPEG2000.Spec.Tier1Equiv.rlTest_rel
#print axioms JPEG2000.Spec.Tier1Equiv.runLength_eq
#print axioms JPEG2000.Spec.Tier1Equiv.cuCol_rel
#print axioms JPEG2000.Spec.Tier1Equiv.bit_nb
#print axioms JPEG2000.Spec.Tier1Equiv.bit_nbneg
#print axioms JPEG2000.Spec.Tier1Equiv.bit_own
#print axioms JPEG2000.Spec.Tier1Equiv.nbAt_sgeom
#print axioms JPEG2000.Spec.Tier1Equiv.anySig_eq
#print axioms JPEG2000.Spec.Tier1Equiv.u8_bne
#print axioms JPEG2000.Spec.Tier1Equiv.ofBits_and
#print axioms JPEG2000.Spec.Tier1Equiv.zc_rel
#print axioms JPEG2000.Spec.Tier1Equiv.sign_rel
#print axioms JPEG2000.Spec.Tier1Equiv.sign_rel'
#print axioms JPEG2000.Spec.Tier1Equiv.sigTest_rel
#print axioms JPEG2000.Spec.Tier1Equiv.nbrTest_rel
#print axioms JPEG2000.Spec.Tier1Equiv.sigVisTest_rel
#print axioms JPEG2000.Spec.Tier1Equiv.visTest_rel
#print axioms JPEG2000.Spec.Tier1Equiv.mr_rel
#print axioms JPEG2000.Spec.Tier1Equiv.scanCols_rel
#print axioms JPEG2000.Spec.Tier1Equiv.scanStripes_rel
#print axioms JPEG2000.Spec.Tier1Equiv.scanBlock_rel
#print axioms JPEG2000.Spec.Tier1Equiv.clearVisFrom_size
#print axioms JPEG2000.Spec.Tier1Equiv.fget_fset'
#print axioms JPEG2000.Spec.Tier1Equiv.clearVisFrom_get
#print axioms JPEG2000.Spec.Tier1Equiv.coeffAt_map
#print axioms JPEG2000.Spec.Tier1Equiv.clearVis_rel
#print axioms JPEG2000.Spec.Tier1Equiv.sigPropPass_rel
#print axioms JPEG2000.Spec.Tier1Equiv.magRefPass_rel
#print axioms JPEG2000.Spec.Tier1Equiv.cleanupPass_rel
#print axioms JPEG2000.Spec.Tier1Equiv.hone_of
#print axioms JPEG2000.Spec.Tier1Equiv.passKind_cases
#print axioms JPEG2000.Spec.Tier1Equiv.runPass_rel
#print axioms JPEG2000.Spec.Tier1Equiv.runPasses_rel
#print axioms JPEG2000.Spec.Tier1Equiv.bidx_eq_iff
#print axioms JPEG2000.Spec.Tier1Equiv.bt_notVIS
#print axioms JPEG2000.Spec.Tier1Equiv.coeffAt_setCoeff_pair
#print axioms JPEG2000.Spec.Tier1Equiv.specBit_hi
#print axioms JPEG2000.Spec.Tier1Equiv.specBit_lo
#print axioms JPEG2000.Spec.Tier1Equiv.sgeom_size
#print axioms JPEG2000.Spec.Tier1Equiv.rel_own
#print axioms JPEG2000.Spec.Tier1Equiv.decodeBit_coeffs
#print axioms JPEG2000.Spec.Tier1Equiv.decode_rel
#print axioms JPEG2000.Spec.Tier1Equiv.becomeSig_rel
#print axioms JPEG2000.Spec.Tier1Equiv.bidx_lt
#print axioms JPEG2000.Spec.Tier1Equiv.zeroCode_rel
#print axioms JPEG2000.Spec.Tier1Equiv.spStep_rel
#print axioms JPEG2000.Spec.Tier1Equiv.mrStep_rel
#print axioms JPEG2000.Spec.Tier1Equiv.cuStep_rel

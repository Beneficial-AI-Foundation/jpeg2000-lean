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
#print axioms JPEG2000.Spec.MQEquiv.renormLoop_bit
#print axioms JPEG2000.Spec.MQEquiv.renormd_bit
#print axioms JPEG2000.Spec.MQEquiv.renormS_eq
#print axioms JPEG2000.Spec.MQEquiv.ctxSet_ctxGet
#print axioms JPEG2000.Spec.MQEquiv.step_eq_ref
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
#print axioms JPEG2000.Spec.Tier1.segmentPasses_congr
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
#print axioms JPEG2000.Spec.Tier1Equiv.c3_plain_exact
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

-- Phase 5, task 5.1: dequantisation, ROI (Spec/Quant.lean, JPEG2000/Quant.lean)
#print axioms JPEG2000.Quant.absU_toNat
#print axioms JPEG2000.Quant.shr_toNat
#print axioms JPEG2000.Quant.shl1_toNat
#print axioms JPEG2000.Quant.unshift_spec
#print axioms JPEG2000.Quant.coeffOf_value
#print axioms JPEG2000.Quant.satSigned_spec
#print axioms JPEG2000.Quant.revCoeff_eq
#print axioms JPEG2000.Quant.sat32_toInt
#print axioms JPEG2000.Quant.half_bound
#print axioms JPEG2000.Quant.mul_div_mul_right'
#print axioms JPEG2000.Quant.scaled_value
#print axioms JPEG2000.Quant.irrevCoeff_bound
#print axioms JPEG2000.Spec.Quant.stepSize_mul_pow
#print axioms JPEG2000.Spec.Quant.stepSize_unit
#print axioms JPEG2000.Spec.Quant.bandSteps_derived_exponent
#print axioms JPEG2000.Spec.Quant.roiUnshift_zero
#print axioms JPEG2000.Spec.Quant.roiUnshift_background
#print axioms JPEG2000.Spec.Quant.roiUnshift_roi
#print axioms JPEG2000.Spec.Quant.reconstructRev_full
#print axioms JPEG2000.Spec.Quant.reconstructRev_eq_irrev
#print axioms JPEG2000.Spec.Quant.reconstructIrrev_eq_E6
#print axioms JPEG2000.Spec.Quant.reconstructRev_congr
#print axioms JPEG2000.Spec.Quant.roiUnshift_congr
#print axioms JPEG2000.Spec.Quant.dequantRev_congr
#print axioms JPEG2000.Spec.Quant.dequantIrrev_congr

-- Phase 5, task 5.3: 9/7 DWT, C8 for the DWT (Spec/DWT97.lean, JPEG2000/DWT97.lean)
#print axioms JPEG2000.Spec.DWT97.K_ne_zero
#print axioms JPEG2000.Spec.DWT97.chain_inv_fwd
#print axioms JPEG2000.Spec.DWT97.sr1d_sd1d
#print axioms JPEG2000.Spec.DWT97.memo_eq
#print axioms JPEG2000.Spec.DWT97.sr2d_sd2d
#print axioms JPEG2000.Spec.DWT97.srMulti_sdMulti
#print axioms JPEG2000.Spec.DWT97.chain_add
#print axioms JPEG2000.Spec.DWT97.chain_smul
#print axioms JPEG2000.Spec.DWT97.chain_eq_wsum
#print axioms JPEG2000.Spec.DWT97.abs_le_iff
#print axioms JPEG2000.Spec.DWT97.abs_add_le
#print axioms JPEG2000.Spec.DWT97.abs_mul_le
#print axioms JPEG2000.Spec.DWT97.chain_bound
#print axioms JPEG2000.Spec.DWT97.gb_mod
#print axioms JPEG2000.Spec.DWT97.pert_eq
#print axioms JPEG2000.Spec.DWT97.pert_zero_bound
#print axioms JPEG2000.Spec.DWT97.injBound_mod
#print axioms JPEG2000.Spec.DWT97.srMulti_smul
#print axioms JPEG2000.DWT97.invQ_toStep
#print axioms JPEG2000.DWT97.qchain_pert
#print axioms JPEG2000.DWT97.rnd_err
#print axioms JPEG2000.DWT97.step_resid
#print axioms JPEG2000.DWT97.resids_bound
#print axioms JPEG2000.DWT97.qsr1d_err
#print axioms JPEG2000.DWT97.qsr2d_err
#print axioms JPEG2000.DWT97.qsrMulti_err
#print axioms JPEG2000.DWT97.castDec_close
#print axioms JPEG2000.DWT97.qsrMulti_err_exact
#print axioms JPEG2000.DWT97.qsrMulti_err_frac
#print axioms JPEG2000.DWT97.liftStep_exact
#print axioms JPEG2000.DWT97.scaleStep_exact
#print axioms JPEG2000.DWT97.liftPass97_spec
#print axioms JPEG2000.DWT97.scalePass97_spec
#print axioms JPEG2000.DWT97.lift1d97_eq

-- Phase 5, task 5.4: RCT/ICT, DC shift, C7, C8 for ICT (Spec/MCT.lean, JPEG2000/MCT.lean)
#print axioms JPEG2000.MCT.shrK
#print axioms JPEG2000.MCT.sat_toInt
#print axioms JPEG2000.MCT.rctSample_eq
#print axioms JPEG2000.MCT.rctSample_exact
#print axioms JPEG2000.MCT.ictSample_eq
#print axioms JPEG2000.MCT.ictRow_err
#print axioms JPEG2000.MCT.ict_c8
#print axioms JPEG2000.MCT.reconIrrev_sat
#print axioms JPEG2000.MCT.DcShift.make_wf
#print axioms JPEG2000.MCT.DcShift.rev_eq
#print axioms JPEG2000.MCT.DcShift.irrev_eq
#print axioms JPEG2000.MCT.map1_get
#print axioms JPEG2000.MCT.map3_get
#print axioms JPEG2000.Spec.MCT.rctInv_rctFwd
#print axioms JPEG2000.Spec.MCT.rctFwd_rctInv
#print axioms JPEG2000.Spec.MCT.ictInv_ictFwd
#print axioms JPEG2000.Spec.MCT.ictInv_ictFwd_ne
#print axioms JPEG2000.Spec.MCT.clamp_mem
#print axioms JPEG2000.Spec.MCT.clamp_of_mem
#print axioms JPEG2000.Spec.MCT.sampleMin_le_max
#print axioms JPEG2000.Spec.MCT.reconRev_mem
#print axioms JPEG2000.Spec.MCT.reconRev_unsigned
#print axioms JPEG2000.Spec.MCT.reconRev_signed
#print axioms JPEG2000.Spec.MCT.roundFix_err

-- Phase 6, task 6.2: consumer image API (JPEG2000/Image.lean)
#print axioms JPEG2000.scaleNat_linear_le

-- Phase 7, task 7.1a: Spec.decode, C9 composition (Spec/Equiv.lean)
#print axioms JPEG2000.Spec.Equiv.ERel.bind
#print axioms JPEG2000.Spec.Equiv.ERel.bind_same
#print axioms JPEG2000.Spec.Equiv.ok_bind
#print axioms JPEG2000.Spec.Equiv.ERel.pure
#print axioms JPEG2000.Spec.Equiv.ERel.and_left
#print axioms JPEG2000.Spec.Equiv.ERel.mono
#print axioms JPEG2000.Spec.Equiv.ERel.forIn_list
#print axioms JPEG2000.Spec.Equiv.ERel.forIn_range
#print axioms JPEG2000.Spec.Equiv.ERel.forIn_range'_idx
#print axioms JPEG2000.Spec.Equiv.ERel.forIn_range_idx
#print axioms JPEG2000.Spec.Equiv.reconstructTileComp_eq_with
#print axioms JPEG2000.Spec.Equiv.decodeTile_eq_with
#print axioms JPEG2000.Spec.Equiv.decodeCodestream_eq_with
#print axioms JPEG2000.Spec.Equiv.fin_rel
#print axioms JPEG2000.Spec.Equiv.tileComp_rel
#print axioms JPEG2000.Spec.Equiv.ArrRel.push
#print axioms JPEG2000.Spec.Equiv.ArrRel.set
#print axioms JPEG2000.Spec.Equiv.ArrRel.mono
#print axioms JPEG2000.Spec.Equiv.CellsRel.mono
#print axioms JPEG2000.Spec.Equiv.CellsRel.zero
#print axioms JPEG2000.Spec.Equiv.pre_post
#print axioms JPEG2000.Spec.Equiv.rct_cell
#print axioms JPEG2000.Spec.Equiv.ict_cell
#print axioms JPEG2000.Spec.Equiv.mct_step
#print axioms JPEG2000.Spec.Equiv.irrev_sample
#print axioms JPEG2000.Spec.Equiv.dc_step
#print axioms JPEG2000.Spec.Equiv.tile_rel
#print axioms JPEG2000.Spec.Equiv.PlaneArr.weaken
#print axioms JPEG2000.Spec.Equiv.SameDims.trans
#print axioms JPEG2000.Spec.Equiv.SameDims.refl
#print axioms JPEG2000.Spec.Equiv.ArrRel.setv
#print axioms JPEG2000.Spec.Equiv.ERel.throw_bind
#print axioms JPEG2000.Spec.Equiv.placeEquiv
#print axioms JPEG2000.Spec.Equiv.tail_rel
#print axioms JPEG2000.Spec.Equiv.final_rel
#print axioms JPEG2000.Spec.Equiv.c9_of_stages

-- Phase 7, task 7.1f: real Tier-2 spec wired into C9 (Spec/Equiv.lean, Spec/Tier2Wire.lean)
#print axioms JPEG2000.Spec.Equiv.segment_append
#print axioms JPEG2000.Spec.Equiv.segment_new
#print axioms JPEG2000.Spec.Equiv.foldl_concat
#print axioms JPEG2000.Spec.Equiv.directSeg_ok
#print axioms JPEG2000.Spec.Equiv.tier1Input_ok
#print axioms JPEG2000.Spec.Equiv.specCodeBlock_eq
#print axioms JPEG2000.Spec.Equiv.decodeBlock_eq_st
#print axioms JPEG2000.Spec.Equiv.imagePrecs_getD
#print axioms JPEG2000.Spec.Equiv.tileComp_image
#print axioms JPEG2000.Spec.Equiv.list_forIn_congr
#print axioms JPEG2000.Spec.Equiv.array_forIn_congr
#print axioms JPEG2000.Spec.Equiv.tileCompWith_congr
#print axioms JPEG2000.Spec.Equiv.image_getD
#print axioms JPEG2000.Spec.Equiv.readSizComponent_dxdy
#print axioms JPEG2000.Spec.Equiv.readArray_dxdy
#print axioms JPEG2000.Spec.Equiv.parseSIZ_dxdy
#print axioms JPEG2000.Spec.Equiv.parseMainHeader_dxdy
#print axioms JPEG2000.Spec.Equiv.parseCodestreamIn_dxdy
#print axioms JPEG2000.Spec.Equiv.parse_dxdy
#print axioms JPEG2000.Spec.Tier2Wire.tier2Equiv
#print axioms JPEG2000.Spec.Tier2Wire.c9_of_open

-- Phase 7, task 7.1b: Tier-2 spec + equivalence (Spec/Tier2*.lean)
#print axioms JPEG2000.Spec.Tier2Equiv.Res.toERel
#print axioms JPEG2000.Spec.Tier2Equiv.tier2_equiv
#print axioms JPEG2000.Spec.Tier2Equiv.tier2_equiv_of_siz
#print axioms JPEG2000.Spec.Tier2Equiv.blockOf_segs
#print axioms JPEG2000.Spec.Tier2Equiv.bytesFrom_of_le
#print axioms JPEG2000.Spec.Tier2Equiv.bytesFrom_cons
#print axioms JPEG2000.Spec.Tier2Equiv.bytesFrom_add
#print axioms JPEG2000.Spec.Tier2Equiv.length_bytesFrom
#print axioms JPEG2000.Spec.Tier2Equiv.bytesFrom_all
#print axioms JPEG2000.Spec.Tier2Equiv.toUInt32_eq_FF
#print axioms JPEG2000.Spec.Tier2Equiv.shift_and_one
#print axioms JPEG2000.Spec.Tier2Equiv.bit_ne
#print axioms JPEG2000.Spec.Tier2Equiv.bit_load
#print axioms JPEG2000.Spec.Tier2Equiv.bit_end
#print axioms JPEG2000.Spec.Tier2Equiv.get_eq_data
#print axioms JPEG2000.Spec.Tier2Equiv.bit_rem
#print axioms JPEG2000.Spec.Tier2Equiv.bitNext_rem
#print axioms JPEG2000.Spec.Tier2Equiv.bitNext_sim
#print axioms JPEG2000.Spec.Tier2Equiv.readBit_sim
#print axioms JPEG2000.Spec.Tier2Equiv.shl_or
#print axioms JPEG2000.Spec.Tier2Equiv.bitsAux_sim
#print axioms JPEG2000.Spec.Tier2Equiv.bits_sim
#print axioms JPEG2000.Spec.Tier2Equiv.length_bitsOf
#print axioms JPEG2000.Spec.Tier2Equiv.wdAt_le
#print axioms JPEG2000.Spec.Tier2Equiv.align_count
#print axioms JPEG2000.Spec.Tier2Equiv.unstuffAux_append
#print axioms JPEG2000.Spec.Tier2Equiv.flagAfter_take
#print axioms JPEG2000.Spec.Tier2Equiv.wdAt_eq
#print axioms JPEG2000.Spec.Tier2Equiv.getD_of_lt
#print axioms JPEG2000.Spec.Tier2Equiv.getElem?_bytesFrom
#print axioms JPEG2000.Spec.Tier2Equiv.bit_hr
#print axioms JPEG2000.Spec.Tier2Equiv.inv_sim
#print axioms JPEG2000.Spec.Tier2Equiv.align_sim
#print axioms JPEG2000.Spec.Tier2Equiv.ofReader_inv
#print axioms JPEG2000.Spec.Tier2Equiv.extract_toList
#print axioms JPEG2000.Spec.Tier2Equiv.rb_eq
#print axioms JPEG2000.Spec.Tier2Equiv.foldl_bytes
#print axioms JPEG2000.Spec.Tier2Equiv.segment_bytes
#print axioms JPEG2000.Spec.Tier2Equiv.back?_toList
#print axioms JPEG2000.Spec.Tier2Equiv.pushRange_bytes
#print axioms JPEG2000.Spec.Tier2Equiv.addPieces_eq
#print axioms JPEG2000.Spec.Tier2Equiv.length_rbytes
#print axioms JPEG2000.Spec.Tier2Equiv.takePieces_sim
#print axioms JPEG2000.Spec.Tier2Equiv.readBody_eq
#print axioms JPEG2000.Spec.Tier2Equiv.BRel.size
#print axioms JPEG2000.Spec.Tier2Equiv.BRel.set
#print axioms JPEG2000.Spec.Tier2Equiv.bodyLoop_sim
#print axioms JPEG2000.Spec.Tier2Equiv.readBody_sim
#print axioms JPEG2000.Spec.Tier2Equiv.Fol.bind
#print axioms JPEG2000.Spec.Tier2Equiv.Fol.pure
#print axioms JPEG2000.Spec.Tier2Equiv.readNumPasses_sim
#print axioms JPEG2000.Spec.Tier2Equiv.Res.bind
#print axioms JPEG2000.Spec.Tier2Equiv.Res.bindR
#print axioms JPEG2000.Spec.Tier2Equiv.Res.bindL
#print axioms JPEG2000.Spec.Tier2Equiv.Res.mono
#print axioms JPEG2000.Spec.Tier2Equiv.Res.pure
#print axioms JPEG2000.Spec.Tier2Equiv.Res.error
#print axioms JPEG2000.Spec.Tier2Equiv.ok_bind
#print axioms JPEG2000.Spec.Tier2Equiv.pure_bind'
#print axioms JPEG2000.Spec.Tier2Equiv.Res.ofFol
#print axioms JPEG2000.Spec.Tier2Equiv.Res.check
#print axioms JPEG2000.Spec.Tier2Equiv.commaCode_sim
#print axioms JPEG2000.Spec.Tier2Equiv.readLengths_sim
#print axioms JPEG2000.Spec.Tier2Equiv.passEndsSegment_eq
#print axioms JPEG2000.Spec.Tier2Equiv.segmentRuns_eq
#print axioms JPEG2000.Spec.Tier2Equiv.segmentPasses_eq
#print axioms JPEG2000.Spec.Tier2Equiv.tail_sim
#print axioms JPEG2000.Spec.Tier2Equiv.headerBlock_sim
#print axioms JPEG2000.Spec.Tier2Equiv.headerBand_eq
#print axioms JPEG2000.Spec.Tier2Equiv.bandLoop_sim
#print axioms JPEG2000.Spec.Tier2Equiv.headerBand_sim
#print axioms JPEG2000.Spec.Tier2Equiv.headerBands_eq
#print axioms JPEG2000.Spec.Tier2Equiv.bandsLoop_sim
#print axioms JPEG2000.Spec.Tier2Equiv.headerBands_sim
#print axioms JPEG2000.Spec.Tier2Equiv.u16_toNat
#print axioms JPEG2000.Spec.Tier2Equiv.u16be_rbytes
#print axioms JPEG2000.Spec.Tier2Equiv.marker_eq
#print axioms JPEG2000.Spec.Tier2Equiv.readSop_sim
#print axioms JPEG2000.Spec.Tier2Equiv.readEph_sim
#print axioms JPEG2000.Spec.Tier2Equiv.ite_bind'
#print axioms JPEG2000.Spec.Tier2Equiv.sop_step
#print axioms JPEG2000.Spec.Tier2Equiv.eph_step
#print axioms JPEG2000.Spec.Tier2Equiv.hdr_step
#print axioms JPEG2000.Spec.Tier2Equiv.decodePacket_sim
#print axioms JPEG2000.Spec.Tier2Equiv.readLoop_sim
#print axioms JPEG2000.Spec.Tier2Equiv.nodeStep_sim
#print axioms JPEG2000.Spec.Tier2Equiv.walk_sim
#print axioms JPEG2000.Spec.Tier2Equiv.decodeWith_sim
#print axioms JPEG2000.Spec.Tier2Equiv.valueLoop_sim
#print axioms JPEG2000.Spec.Tier2Equiv.decodeValueWith_sim
#print axioms JPEG2000.Spec.Tier2Equiv.bitNext_nextSim
#print axioms JPEG2000.Spec.Tier2Equiv.query_out
#print axioms JPEG2000.Spec.Tier2Equiv.exact_out
#print axioms JPEG2000.Spec.Tier2Equiv.decode_spec
#print axioms JPEG2000.Spec.Tier2Equiv.decodeValue_spec
#print axioms JPEG2000.Spec.Tier2Equiv.step_sim
#print axioms JPEG2000.Spec.Tier2Equiv.loop_sim
#print axioms JPEG2000.Spec.Tier2Equiv.bind_ok
#print axioms JPEG2000.Spec.Tier2Equiv.listMapM_inv
#print axioms JPEG2000.Spec.Tier2Equiv.arrayMapM_inv
#print axioms JPEG2000.Spec.Tier2Equiv.forIn_inv
#print axioms JPEG2000.Spec.Tier2Equiv.init_fresh
#print axioms JPEG2000.Spec.Tier2Equiv.initPrecincts_fresh
#print axioms JPEG2000.Spec.Tier2Equiv.fresh_rel
#print axioms JPEG2000.Spec.Tier2Equiv.partsOK_snoc
#print axioms JPEG2000.Spec.Tier2Equiv.tileData_ok
#print axioms JPEG2000.Spec.Tier2Equiv.window
#print axioms JPEG2000.Spec.Tier2Equiv.translate_bytes
#print axioms JPEG2000.Spec.Tier2Equiv.foldl_translate
#print axioms JPEG2000.Spec.Tier2Equiv.outBlock_eq
#print axioms JPEG2000.Spec.Tier2Equiv.out_eq
#print axioms JPEG2000.Spec.Tier2Equiv.outD_eq
#print axioms JPEG2000.Spec.Tier2Equiv.Res.self
#print axioms JPEG2000.Spec.Tier2Equiv.decodeTile_sim
#print axioms JPEG2000.Spec.Tier2Equiv.decodeWithStream_sim
#print axioms JPEG2000.Spec.Tier2Equiv.geomOfHeader_rect
#print axioms JPEG2000.Spec.Tier2Equiv.ofHeader_wf

-- Phase 7, task 7.1d: DWT plane loops, dequantisation loop (Spec/DWTPlane*, Spec/QuantBlock*)
#print axioms JPEG2000.Spec.DWTPlane.fast_core
#print axioms JPEG2000.Spec.DWTPlane.idwt53Fast_spec
#print axioms JPEG2000.Spec.DWTPlane.clamp32_int32
#print axioms JPEG2000.Spec.DWTPlane.idwt53Fast_bandsEq
#print axioms JPEG2000.Spec.DWTPlane.dwt53PlaneEquiv
#print axioms JPEG2000.Spec.DWTPlane.bandsClose_agree
#print axioms JPEG2000.Spec.DWTPlane.idwt97Fast_spec
#print axioms JPEG2000.Spec.DWTPlane.clampR_int
#print axioms JPEG2000.Spec.DWTPlane.clampR_lip
#print axioms JPEG2000.Spec.DWTPlane.clampR_int32
#print axioms JPEG2000.Spec.DWTPlane.roundRat_err
#print axioms JPEG2000.Spec.DWTPlane.idwt97Fast_err
#print axioms JPEG2000.Spec.DWTPlane.dwt97PlaneErr
#print axioms JPEG2000.Spec.DWTPlane.rmax_l
#print axioms JPEG2000.Spec.DWTPlane.rmax_r
#print axioms JPEG2000.Spec.DWTPlane.le_E1'
#print axioms JPEG2000.Spec.DWTPlane.B1_le_E1'
#print axioms JPEG2000.Spec.DWTPlane.le_En'
#print axioms JPEG2000.Spec.DWTPlane.wsum_nonneg
#print axioms JPEG2000.Spec.DWTPlane.gb_nonneg
#print axioms JPEG2000.Spec.DWTPlane.injBound_nonneg
#print axioms JPEG2000.Spec.DWTPlane.qη_nonneg
#print axioms JPEG2000.Spec.DWTPlane.injInv_nonneg
#print axioms JPEG2000.Spec.DWTPlane.sr1d_lip
#print axioms JPEG2000.Spec.DWTPlane.sr2d_lip
#print axioms JPEG2000.Spec.DWTPlane.srMulti_lip
#print axioms JPEG2000.Spec.DWTPlane.qsrMulti_err_loc
#print axioms JPEG2000.Spec.DWTPlane.cdivPow_succ
#print axioms JPEG2000.Spec.DWTPlane.cdivPow_zero
#print axioms JPEG2000.Spec.DWTPlane.cdivPow_add
#print axioms JPEG2000.Spec.DWTPlane.halfN_coords
#print axioms JPEG2000.Spec.DWTPlane.bandCoord_high
#print axioms JPEG2000.Spec.DWTPlane.bandCoord_low
#print axioms JPEG2000.Spec.DWTPlane.bandCoord_zero
#print axioms JPEG2000.Spec.DWTPlane.bandCoord_reduce
#print axioms JPEG2000.Spec.DWTPlane.Band.xob_le
#print axioms JPEG2000.Spec.DWTPlane.Band.yob_le
#print axioms JPEG2000.Spec.DWTPlane.bandRect_reduce
#print axioms JPEG2000.Spec.DWTPlane.rhalf_succ
#print axioms JPEG2000.Spec.DWTPlane.specRect_halfRect
#print axioms JPEG2000.Spec.DWTPlane.specRect_halfN
#print axioms JPEG2000.Spec.DWTPlane.halfN_mono
#print axioms JPEG2000.Spec.DWTPlane.liftPass_frame
#print axioms JPEG2000.Spec.DWTPlane.kspec53
#print axioms JPEG2000.Spec.DWTPlane.sr2d_eq
#print axioms JPEG2000.Spec.DWTPlane.gMulti_sr1d
#print axioms JPEG2000.Spec.DWTPlane.liftPass97_frame
#print axioms JPEG2000.Spec.DWTPlane.scalePass97_frame
#print axioms JPEG2000.Spec.DWTPlane.liftPass97_ok
#print axioms JPEG2000.Spec.DWTPlane.scalePass97_ok
#print axioms JPEG2000.Spec.DWTPlane.qsr1d_local
#print axioms JPEG2000.Spec.DWTPlane.kspec97
#print axioms JPEG2000.Spec.DWTPlane.qsr2d_eq
#print axioms JPEG2000.Spec.DWTPlane.gMulti_qsr1d
#print axioms JPEG2000.Spec.DWTPlane.gOk_okMulti
#print axioms JPEG2000.Spec.DWTPlane.g2d_local
#print axioms JPEG2000.Spec.DWTPlane.level_spec
#print axioms JPEG2000.Spec.DWTPlane.toDec_eq
#print axioms JPEG2000.Spec.DWTPlane.mallat_interleave
#print axioms JPEG2000.Spec.DWTPlane.levelsG_ok
#print axioms JPEG2000.Spec.DWTPlane.levelsG_spec
#print axioms JPEG2000.Spec.DWTPlane.gMulti_local
#print axioms JPEG2000.Spec.DWTPlane.bandsEq_agree
#print axioms JPEG2000.Spec.DWTPlane.if_t
#print axioms JPEG2000.Spec.DWTPlane.if_f
#print axioms JPEG2000.Spec.DWTPlane.rd_set
#print axioms JPEG2000.Spec.DWTPlane.rd_get
#print axioms JPEG2000.Spec.DWTPlane.idx_inj
#print axioms JPEG2000.Spec.DWTPlane.loadRow_spec
#print axioms JPEG2000.Spec.DWTPlane.storeRow_spec
#print axioms JPEG2000.Spec.DWTPlane.loadCols_spec
#print axioms JPEG2000.Spec.DWTPlane.storeCols_spec
#print axioms JPEG2000.Spec.DWTPlane.rowPass53_eq
#print axioms JPEG2000.Spec.DWTPlane.rowPass97_eq
#print axioms JPEG2000.Spec.DWTPlane.liftCols53_eq
#print axioms JPEG2000.Spec.DWTPlane.liftCols97_eq
#print axioms JPEG2000.Spec.DWTPlane.colPass53_eq
#print axioms JPEG2000.Spec.DWTPlane.colPass97_eq
#print axioms JPEG2000.Spec.DWTPlane.levels53_eq
#print axioms JPEG2000.Spec.DWTPlane.levels97_eq
#print axioms JPEG2000.Spec.DWTPlane.row_hit
#print axioms JPEG2000.Spec.DWTPlane.rowPassG_spec
#print axioms JPEG2000.Spec.DWTPlane.liftColsG_spec
#print axioms JPEG2000.Spec.DWTPlane.colPassG_spec
#print axioms JPEG2000.Spec.DWTPlane.gMulti_snoc
#print axioms JPEG2000.Spec.DWTPlane.gOk_snoc
#print axioms JPEG2000.Spec.DWTPlane.storeRow_width
#print axioms JPEG2000.Spec.DWTPlane.storeCols_width
#print axioms JPEG2000.Spec.DWTPlane.rowPassG_width
#print axioms JPEG2000.Spec.DWTPlane.colPassG_width
#print axioms JPEG2000.Spec.DWTPlane.levelsG_width
#print axioms JPEG2000.Spec.DWTPlane.get?_buf
#print axioms JPEG2000.Spec.DWTPlane.get?_rd
#print axioms JPEG2000.Spec.DWTPlane.cellInt_rd
#print axioms JPEG2000.Spec.DWTPlane.sat32_clamp
#print axioms JPEG2000.Spec.DWTPlane.forIn'_range'_inv
#print axioms JPEG2000.Spec.DWTPlane.divmod_idx
#print axioms JPEG2000.Spec.DWTPlane.forIn'_range_inv
#print axioms JPEG2000.Spec.DWTPlane.ofGrid_eq
#print axioms JPEG2000.Spec.DWTPlane.ofGrid_spec
#print axioms JPEG2000.Spec.QuantBlock.dequantBlock_ok
#print axioms JPEG2000.Spec.QuantBlock.band53_dec53
#print axioms JPEG2000.Spec.QuantBlock.band97_dec97
#print axioms JPEG2000.Spec.QuantBlock.entryAt_cons
#print axioms JPEG2000.Spec.QuantBlock.bval_agree
#print axioms JPEG2000.Spec.QuantBlock.step_rel
#print axioms JPEG2000.Spec.QuantBlock.init_rel
#print axioms JPEG2000.Spec.QuantBlock.ERel.forIn_list_mem
#print axioms JPEG2000.Spec.QuantBlock.ERel.forIn_arr_mem
#print axioms JPEG2000.Spec.QuantBlock.ERel.forIn_range_mem
#print axioms JPEG2000.Spec.QuantBlock.dequantLoopEquiv
#print axioms JPEG2000.Spec.QuantBlock.band53_toDec
#print axioms JPEG2000.Spec.QuantBlock.band97_eq
#print axioms JPEG2000.Spec.QuantBlock.Wd_anti
#print axioms JPEG2000.Spec.QuantBlock.mpos_range
#print axioms JPEG2000.Spec.QuantBlock.Band.ob_of_ne
#print axioms JPEG2000.Spec.QuantBlock.Band.eq_of_ob
#print axioms JPEG2000.Spec.QuantBlock.mpos_inj
#print axioms JPEG2000.Spec.QuantBlock.readBand_of
#print axioms JPEG2000.Spec.QuantBlock.mx_origin
#print axioms JPEG2000.Spec.QuantBlock.my_origin
#print axioms JPEG2000.Spec.QuantBlock.cellInt_cv
#print axioms JPEG2000.Spec.QuantBlock.block_pos
#print axioms JPEG2000.Spec.QuantBlock.write_hit
#print axioms JPEG2000.Spec.QuantBlock.blockRow_spec
#print axioms JPEG2000.Spec.QuantBlock.row_hit2
#print axioms JPEG2000.Spec.QuantBlock.blockRows_spec

-- Phase 7, task 7.1c: C3 for all code-block styles (Spec/Tier1Equiv/Modes*)
-- Phase 7, task 7.1c: C3 for every code-block style (Spec/Tier1Equiv/Modes.lean, Spec/Tier1Equiv/Modes/*.lean)
#print axioms JPEG2000.Spec.Tier1EquivM.coeffAt_gV
#print axioms JPEG2000.Spec.Tier1EquivM.setCoeff_gV
#print axioms JPEG2000.Spec.Tier1EquivM.bitV_nb
#print axioms JPEG2000.Spec.Tier1EquivM.bitV_nbneg
#print axioms JPEG2000.Spec.Tier1EquivM.bitV_own
#print axioms JPEG2000.Spec.Tier1EquivM.anySig_eqV
#print axioms JPEG2000.Spec.Tier1EquivM.zc_relM
#print axioms JPEG2000.Spec.Tier1EquivM.sign_relM
#print axioms JPEG2000.Spec.Tier1EquivM.sign_relM'
#print axioms JPEG2000.Spec.Tier1EquivM.sigTest_relM
#print axioms JPEG2000.Spec.Tier1EquivM.nbrTest_relM
#print axioms JPEG2000.Spec.Tier1EquivM.sigVisTest_relM
#print axioms JPEG2000.Spec.Tier1EquivM.visTest_relM
#print axioms JPEG2000.Spec.Tier1EquivM.negTest_relM
#print axioms JPEG2000.Spec.Tier1EquivM.mr_relM
#print axioms JPEG2000.Spec.Tier1EquivM.rlTest_relM
#print axioms JPEG2000.Spec.Tier1EquivM.bt_nbMaskV
#print axioms JPEG2000.Spec.Tier1EquivM.bt_nbMaskV_hi
#print axioms JPEG2000.Spec.Tier1EquivM.flags_afterM
#print axioms JPEG2000.Spec.Tier1EquivM.causalTop_bidx
#print axioms JPEG2000.Spec.Tier1EquivM.hidden_iff
#print axioms JPEG2000.Spec.Tier1EquivM.nbAt_setCoeff
#print axioms JPEG2000.Spec.Tier1EquivM.specBitV_lo
#print axioms JPEG2000.Spec.Tier1EquivM.specBitV_hi
#print axioms JPEG2000.Spec.Tier1EquivM.setSig_rel
#print axioms JPEG2000.Spec.Tier1EquivM.rel_ownM
#print axioms JPEG2000.Spec.Tier1EquivM.decodeBit_eq
#print axioms JPEG2000.Spec.Tier1EquivM.decode_relM
#print axioms JPEG2000.Spec.Tier1EquivM.rawBit_sim
#print axioms JPEG2000.Spec.Tier1EquivM.rawBit_eq
#print axioms JPEG2000.Spec.Tier1EquivM.rawBit_relM
#print axioms JPEG2000.Spec.Tier1EquivM.becomeSigM_rel
#print axioms JPEG2000.Spec.Tier1EquivM.zeroCodeM_rel
#print axioms JPEG2000.Spec.Tier1EquivM.spStepM_rel
#print axioms JPEG2000.Spec.Tier1EquivM.cuStepM_rel
#print axioms JPEG2000.Spec.Tier1EquivM.mrStep_relM
#print axioms JPEG2000.Spec.Tier1EquivM.rawSpStep_rel
#print axioms JPEG2000.Spec.Tier1EquivM.rawMrStep_rel
#print axioms JPEG2000.Spec.Tier1EquivM.colRows_relG
#print axioms JPEG2000.Spec.Tier1EquivM.scanCols_relG
#print axioms JPEG2000.Spec.Tier1EquivM.scanStripes_relG
#print axioms JPEG2000.Spec.Tier1EquivM.scanBlock_relG
#print axioms JPEG2000.Spec.Tier1EquivM.skipCol_rel
#print axioms JPEG2000.Spec.Tier1EquivM.spColM_rel
#print axioms JPEG2000.Spec.Tier1EquivM.rawSpCol_rel
#print axioms JPEG2000.Spec.Tier1EquivM.sig_false_of
#print axioms JPEG2000.Spec.Tier1EquivM.mrCol_relM
#print axioms JPEG2000.Spec.Tier1EquivM.rawMrCol_rel
#print axioms JPEG2000.Spec.Tier1EquivM.runLength_eqM
#print axioms JPEG2000.Spec.Tier1EquivM.cuColM_rel
#print axioms JPEG2000.Spec.Tier1EquivM.clearVis_relM
#print axioms JPEG2000.Spec.Tier1EquivM.sigPropPassM_rel
#print axioms JPEG2000.Spec.Tier1EquivM.magRefPass_relM
#print axioms JPEG2000.Spec.Tier1EquivM.cleanupPassM_rel
#print axioms JPEG2000.Spec.Tier1EquivM.rawSigPropPass_rel
#print axioms JPEG2000.Spec.Tier1EquivM.rawMagRefPass_rel
#print axioms JPEG2000.Spec.Tier1EquivM.styleRel_ofByte
#print axioms JPEG2000.Spec.Tier1EquivM.pk_bne
#print axioms JPEG2000.Spec.Tier1EquivM.isRawPass_eq
#print axioms JPEG2000.Spec.Tier1EquivM.passEndsSegment_eq
#print axioms JPEG2000.Spec.Tier1EquivM.segmentRuns_eq
#print axioms JPEG2000.Spec.Tier1EquivM.segmentPasses_eq
#print axioms JPEG2000.Spec.Tier1EquivM.coder_cx
#print axioms JPEG2000.Spec.Tier1EquivM.coder_setcx
#print axioms JPEG2000.Spec.Tier1EquivM.tier1Contexts_rel
#print axioms JPEG2000.Spec.Tier1EquivM.runPassM_fst
#print axioms JPEG2000.Spec.Tier1EquivM.segSymbol_rel
#print axioms JPEG2000.Spec.Tier1EquivM.reset_rel
#print axioms JPEG2000.Spec.Tier1EquivM.passF_rel
#print axioms JPEG2000.Spec.Tier1EquivM.runPassM_rel
#print axioms JPEG2000.Spec.Tier1EquivM.runPassesM_rel
#print axioms JPEG2000.Spec.Tier1EquivM.rawInit_sim
#print axioms JPEG2000.Spec.Tier1EquivM.startSegment_rel
#print axioms JPEG2000.Spec.Tier1EquivM.isRawPass_succ
#print axioms JPEG2000.Spec.Tier1EquivM.segmentRuns_homog
#print axioms JPEG2000.Spec.Tier1EquivM.segmentPasses_homog
#print axioms JPEG2000.Spec.Tier1EquivM.getD_of_drop
#print axioms JPEG2000.Spec.Tier1EquivM.runSegs_rel
#print axioms JPEG2000.Spec.Tier1EquivM.allP_setV
#print axioms JPEG2000.Spec.Tier1EquivM.becomeSignificant_coeffsV
#print axioms JPEG2000.Spec.Tier1EquivM.becomeSignificant_baseV
#print axioms JPEG2000.Spec.Tier1EquivM.zeroCode_casesV
#print axioms JPEG2000.Spec.Tier1EquivM.sigPropStep_invV
#print axioms JPEG2000.Spec.Tier1EquivM.foldl_allPV
#print axioms JPEG2000.Spec.Tier1EquivM.sigPropPass_invV
#print axioms JPEG2000.Spec.Tier1EquivM.foldl_orderedV
#print axioms JPEG2000.Spec.Tier1EquivM.magRefPass_invV
#print axioms JPEG2000.Spec.Tier1EquivM.cleanupStep_invV
#print axioms JPEG2000.Spec.Tier1EquivM.cleanupColumn_invV
#print axioms JPEG2000.Spec.Tier1EquivM.cleanupPass_invV
#print axioms JPEG2000.Spec.Tier1EquivM.runPass_invV
#print axioms JPEG2000.Spec.Tier1EquivM.rawBit_split
#print axioms JPEG2000.Spec.Tier1EquivM.rawSigPropStep_invV
#print axioms JPEG2000.Spec.Tier1EquivM.rawSigPropPass_invV
#print axioms JPEG2000.Spec.Tier1EquivM.rawMagRefPass_invV
#print axioms JPEG2000.Spec.Tier1EquivM.runRawPass_invV
#print axioms JPEG2000.Spec.Tier1EquivM.segSymbol_coeffs
#print axioms JPEG2000.Spec.Tier1EquivM.runPassM_coeffs
#print axioms JPEG2000.Spec.Tier1EquivM.runPassM_invV
#print axioms JPEG2000.Spec.Tier1EquivM.startSegment_coeffs
#print axioms JPEG2000.Spec.Tier1EquivM.passes_invV
#print axioms JPEG2000.Spec.Tier1EquivM.decodeSegments_inv
#print axioms JPEG2000.Spec.Tier1EquivM.segsPasses_eq
#print axioms JPEG2000.Spec.Tier1EquivM.specBlockM_numPasses
#print axioms JPEG2000.Spec.Tier1EquivM.validate_eqM
#print axioms JPEG2000.Spec.Tier1EquivM.validate_ok_facts
#print axioms JPEG2000.Spec.Tier1EquivM.runPassM_plainLike
#print axioms JPEG2000.Spec.Tier1EquivM.startSegment_plainLike
#print axioms JPEG2000.Spec.Tier1EquivM.decodeCodeBlock_plainLike
#print axioms JPEG2000.Spec.Tier1EquivM.init_relM
#print axioms JPEG2000.Spec.Tier1EquivM.val_toIntM
#print axioms JPEG2000.Spec.Tier1EquivM.out_okM
#print axioms JPEG2000.Spec.Tier1EquivM.decodeCodeBlock_ok
#print axioms JPEG2000.Spec.Tier1EquivM.c3_all_exact
#print axioms JPEG2000.Spec.Tier1EquivM.validate_eq_unsup
#print axioms JPEG2000.Spec.Tier1EquivM.c3_all_unsup_exact
#print axioms JPEG2000.Spec.Tier1EquivM.decodeBit_bad
#print axioms JPEG2000.Spec.Tier1EquivM.becomeSignificant_bad
#print axioms JPEG2000.Spec.Tier1EquivM.zeroCode_bad
#print axioms JPEG2000.Spec.Tier1EquivM.foldl_bad
#print axioms JPEG2000.Spec.Tier1EquivM.sigPropPass_bad
#print axioms JPEG2000.Spec.Tier1EquivM.magRefPass_bad
#print axioms JPEG2000.Spec.Tier1EquivM.rawSigPropPass_bad
#print axioms JPEG2000.Spec.Tier1EquivM.rawMagRefPass_bad
#print axioms JPEG2000.Spec.Tier1EquivM.cleanupPass_bad
#print axioms JPEG2000.Spec.Tier1EquivM.pass_bad
#print axioms JPEG2000.Spec.Tier1EquivM.decodeSegments_bad_noSeg
#print axioms JPEG2000.Spec.Tier1EquivM.runPassM_snd
#print axioms JPEG2000.Spec.Tier1EquivM.segSymbol_bad
#print axioms JPEG2000.Spec.Tier1EquivM.runPassM_bad
#print axioms JPEG2000.Spec.Tier1EquivM.runPassesM_both
#print axioms JPEG2000.Spec.Tier1EquivM.runSegs_both
#print axioms JPEG2000.Spec.Tier1EquivM.core_bad
#print axioms JPEG2000.Spec.Tier1EquivM.c3_all_strict_exact

-- Phase 7, task 7.4: S2/S3 (Spec/Resources.lean); the decoder definitions themselves
#print axioms JPEG2000.decode
#print axioms JPEG2000.decodeCodestream
#print axioms JPEG2000.decodeCodestreamNarrow
#print axioms JPEG2000.Spec.CodestreamDispatch.compact_read
#print axioms JPEG2000.Spec.CodestreamDispatch.native_dispatch
#print axioms JPEG2000.Spec.CodestreamDispatch.native_geometry
#print axioms JPEG2000.Spec.CodestreamDispatch.native_read
#print axioms JPEG2000.Spec.WideAssembly.blockSt_raster
#print axioms JPEG2000.Spec.WideAssembly.decodeBlock_eq
#print axioms JPEG2000.Spec.WideAssembly.tileComp_eq_finish
#print axioms JPEG2000.Spec.WideAssembly.tileComp_equiv
#print axioms JPEG2000.Spec.WideAssembly.tileComp_sound
#print axioms JPEG2000.Spec.WideAssembly.bandGrid53_eq
#print axioms JPEG2000.Spec.WideAssembly.bandGrid97_close
#print axioms JPEG2000.Spec.WideAssembly.parsed_component
#print axioms JPEG2000.Spec.WideAssembly.parsed_component_ok
#print axioms JPEG2000.Spec.Resources.checkGeometry_limitOnly
#print axioms JPEG2000.Spec.Resources.checkGeometry_ok_iff
#print axioms JPEG2000.Spec.Resources.addTile_within
#print axioms JPEG2000.Spec.Resources.checkWork_within
#print axioms JPEG2000.Spec.Resources.parseCodestreamIn_ok
#print axioms JPEG2000.Spec.Resources.parse_ok
#print axioms JPEG2000.Spec.Resources.parse_within
#print axioms JPEG2000.Spec.Resources.decodeCodestream_ok
#print axioms JPEG2000.Spec.Resources.allocOutput_ok
#print axioms JPEG2000.Spec.Resources.decodeCodestream_within
#print axioms JPEG2000.Spec.Resources.upsample_dims
#print axioms JPEG2000.Spec.Resources.decode_within
#print axioms JPEG2000.Spec.Resources.interleave_size
#print axioms JPEG2000.Spec.Resources.interleaved8_size
#print axioms JPEG2000.Spec.Resources.interleaved16_size
#print axioms JPEG2000.Spec.Resources.parse_error_of_geometry
#print axioms JPEG2000.Spec.Resources.decode_limitExceeded_of_geometry
#print axioms JPEG2000.Spec.Resources.decode_limitExceeded_of_area
#print axioms JPEG2000.Spec.Resources.decode_limitExceeded_of_bytes
#print axioms JPEG2000.Spec.Resources.allocOutput_limitOnly
#print axioms JPEG2000.Spec.Resources.allocOutput_ok_iff
#print axioms JPEG2000.Spec.Resources.decodeCodestream_limitExceeded_of_output
#print axioms JPEG2000.Spec.Resources.decode_limitExceeded_of_output
#print axioms JPEG2000.Spec.Resources.blit_dims
#print axioms JPEG2000.Spec.Resources.place_dims
#print axioms JPEG2000.Spec.Resources.decodeCodestream_planes
#print axioms JPEG2000.Spec.Resources.allocOutput_dims
#print axioms JPEG2000.Spec.Resources.decodeCodestream_comp_dims
#print axioms JPEG2000.Spec.Resources.forPackets_inv
#print axioms JPEG2000.Spec.Resources.decodeTilePacketsWith_ok
#print axioms JPEG2000.Spec.Resources.decodeWithStream_ok
#print axioms JPEG2000.Spec.Resources.decodeAllTileCodeBlocks_passes
#print axioms JPEG2000.Spec.Resources.decodeTile_work
#print axioms JPEG2000.Spec.Resources.reconstructTileComp_work
#print axioms JPEG2000.Spec.Resources.decode_total
#print axioms JPEG2000.Spec.Resources.array_foldl_sum
#print axioms JPEG2000.Spec.Resources.decodeCodestream_resources
#print axioms JPEG2000.Spec.NativeResources.decodeCodestream_resources
#print axioms JPEG2000.Spec.Resources.decode_resources
#print axioms JPEG2000.Spec.Resources.decode_size

-- Phase 7, task 7.1h: Tier-1 wired into C9 (Spec/Tier1Wire.lean)
#print axioms JPEG2000.Spec.Tier1Wire.validateSegs_error
#print axioms JPEG2000.Spec.Tier1Wire.fast_error_of_bad
#print axioms JPEG2000.Spec.Tier1Wire.specCodeBlock_ok
#print axioms JPEG2000.Spec.Tier1Wire.agree_blockAgree
#print axioms JPEG2000.Spec.Tier1Wire.tier1Equiv
#print axioms JPEG2000.Spec.Tier1Wire.c9_of_header

-- Phase 7, task 7.1g: Tier2WF (Spec/Tier2WF.lean)
#print axioms JPEG2000.Spec.Tier2WF.foldlM_inv
#print axioms JPEG2000.Spec.Tier2WF.forRange_pres
#print axioms JPEG2000.Spec.Tier2WF.forVolume_pres
#print axioms JPEG2000.Spec.Tier2WF.forVolumes_pres
#print axioms JPEG2000.Spec.Tier2WF.forPackets_pres
#print axioms JPEG2000.Spec.Tier2WF.mem_of_mem_pop
#print axioms JPEG2000.Spec.Tier2WF.pushRange_in
#print axioms JPEG2000.Spec.Tier2WF.partsOK_in
#print axioms JPEG2000.Spec.Tier2WF.translate_in
#print axioms JPEG2000.Spec.Tier2WF.foldl_translate_in
#print axioms JPEG2000.Spec.Tier2WF.out_segsIn
#print axioms JPEG2000.Spec.Tier2WF.mem_getD
#print axioms JPEG2000.Spec.Tier2WF.map_set_eq
#print axioms JPEG2000.Spec.Tier2WF.headerBlock_shape
#print axioms JPEG2000.Spec.Tier2WF.headerBand_shape
#print axioms JPEG2000.Spec.Tier2WF.headerBands_shape
#print axioms JPEG2000.Spec.Tier2WF.addPieces_geom
#print axioms JPEG2000.Spec.Tier2WF.readBody_shape
#print axioms JPEG2000.Spec.Tier2WF.decodePacket_shape
#print axioms JPEG2000.Spec.Tier2WF.lt_cdivPow
#print axioms JPEG2000.Spec.Tier2WF.codeBlocksOf_in
#print axioms JPEG2000.Spec.Tier2WF.clip_in
#print axioms JPEG2000.Spec.Tier2WF.RectIn.trans
#print axioms JPEG2000.Spec.Tier2WF.listMapM_mem
#print axioms JPEG2000.Spec.Tier2WF.arrayMapM_mem
#print axioms JPEG2000.Spec.Tier2WF.gridCount_pos
#print axioms JPEG2000.Spec.Tier2WF.pbr_in
#print axioms JPEG2000.Spec.Tier2WF.resolution_bands
#print axioms JPEG2000.Spec.Tier2WF.precinct_bands
#print axioms JPEG2000.Spec.Tier2WF.init_wf
#print axioms JPEG2000.Spec.Tier2WF.forIn_range'_inv
#print axioms JPEG2000.Spec.Tier2WF.getElem?_push_of_some
#print axioms JPEG2000.Spec.Tier2WF.SpanOK.push
#print axioms JPEG2000.Spec.Tier2WF.initPrecincts_wf
#print axioms JPEG2000.Spec.Tier2WF.map_set2
#print axioms JPEG2000.Spec.Tier2WF.fastStep_pres
#print axioms JPEG2000.Spec.Tier2WF.WFPrec.of_shape
#print axioms JPEG2000.Spec.Tier2WF.getD_map_arr
#print axioms JPEG2000.Spec.Tier2WF.decodeTile_wf
#print axioms JPEG2000.Spec.Tier2WF.tier2WF
#print axioms JPEG2000.Spec.Tier2WF.c9_of_hdr
-- Phase 5, task 5.8: passes below bit-plane 0 dropped; C3 for the clamping decoders
-- (Spec/Tier1Equiv/Clamp.lean)
#print axioms JPEG2000.Spec.Tier1Equiv.specBlock_clamp
#print axioms JPEG2000.Spec.Tier1Equiv.c3_plain
#print axioms JPEG2000.Spec.Tier1EquivM.truncSegments_map
#print axioms JPEG2000.Spec.Tier1EquivM.mem_truncSegs
#print axioms JPEG2000.Spec.Tier1EquivM.truncSegs_sum_le
#print axioms JPEG2000.Spec.Tier1EquivM.specBlockM_clamp
#print axioms JPEG2000.Spec.Tier1EquivM.clampSegs_range
#print axioms JPEG2000.Spec.Tier1EquivM.clampSegs_sum_le
#print axioms JPEG2000.Spec.Tier1EquivM.badRange_false
#print axioms JPEG2000.Spec.Tier1EquivM.decodeCodeBlockSegs_clamp
#print axioms JPEG2000.Spec.Tier1EquivM.decodeCodeBlockSegsStrict_clamp
#print axioms JPEG2000.Spec.Tier1EquivM.c3_all
#print axioms JPEG2000.Spec.Tier1EquivM.c3_all_unsup
#print axioms JPEG2000.Spec.Tier1EquivM.c3_all_strict

-- Phase 7, task 7.1e: HeaderWF, final C9 (Spec/HeaderWF.lean, Spec/C9.lean)
#print axioms JPEG2000.Spec.HeaderWF.headerWF
#print axioms JPEG2000.Spec.HeaderWF.parse_wf
#print axioms JPEG2000.Spec.C9.c9

-- Phase 4, tasks 4.9 + 4.8: plain-mode 109-pass segment cap (Spec/Tier1/Modes.lean,
-- `segmentPasses_congr` above); S3 passes per code-block (Spec/Resources/BlockPasses.lean)
#print axioms JPEG2000.Spec.Resources.BlockPasses.decodePacket_within
#print axioms JPEG2000.Spec.Resources.BlockPasses.decodeTilePacketsWith_blockPasses
#print axioms JPEG2000.Spec.Resources.BlockPasses.decodeWithStream_blockPasses
#print axioms JPEG2000.Spec.Resources.BlockPasses.decodeAllTileCodeBlocks_blockPasses

-- Phase 7, task 7.3a: C10 layers 1–2a (Spec/RoundTrip/*)
#print axioms JPEG2000.Spec.RoundTrip.decodePasses_encode
#print axioms JPEG2000.Spec.RoundTrip.scanOrder_nodup
#print axioms JPEG2000.Spec.RoundTrip.mem_scanOrder_of
#print axioms JPEG2000.Spec.RoundTrip.decodeValues_encodeCodeBlock
#print axioms JPEG2000.Spec.RoundTrip.length_bitsOf
#print axioms JPEG2000.Spec.RoundTrip.bitsOf_double
#print axioms JPEG2000.Spec.RoundTrip.bitsOf_zero
#print axioms JPEG2000.Spec.RoundTrip.unstuffAux_append
#print axioms JPEG2000.Spec.RoundTrip.lastFF_snoc
#print axioms JPEG2000.Spec.RoundTrip.unstuffAux_snoc
#print axioms JPEG2000.Spec.RoundTrip.winv_init
#print axioms JPEG2000.Spec.RoundTrip.winv_bit
#print axioms JPEG2000.Spec.RoundTrip.winv_bits
#print axioms JPEG2000.Spec.RoundTrip.length_unstuffAux_cons
#print axioms JPEG2000.Spec.RoundTrip.lastFF_cons
#print axioms JPEG2000.Spec.RoundTrip.alignedLength_at
#print axioms JPEG2000.Spec.RoundTrip.bitsOf_shift
#print axioms JPEG2000.Spec.RoundTrip.unstuff_append_noFF
#print axioms JPEG2000.Spec.RoundTrip.finish_spec
#print axioms JPEG2000.Spec.RoundTrip.natBits_succ
#print axioms JPEG2000.Spec.RoundTrip.bitsVal_natBits
#print axioms JPEG2000.Spec.RoundTrip.field_natBits
#print axioms JPEG2000.Spec.RoundTrip.numPasses_passBits
#print axioms JPEG2000.Spec.RoundTrip.commaCode_replicate

-- Phase 7, task 7.3b: C10 packet layer (Spec/RoundTrip/Tier2.lean)
#print axioms JPEG2000.Spec.RoundTrip.query_enc
#print axioms JPEG2000.Spec.RoundTrip.exact_enc
#print axioms JPEG2000.Spec.RoundTrip.lt_width
#print axioms JPEG2000.Spec.RoundTrip.width_le
#print axioms JPEG2000.Spec.RoundTrip.blockBits_eq
#print axioms JPEG2000.Spec.RoundTrip.blockHeader_enc
#print axioms JPEG2000.Spec.RoundTrip.blockBits_inv
#print axioms JPEG2000.Spec.RoundTrip.BitWriter.bits_append
#print axioms JPEG2000.Spec.RoundTrip.foldl_blockBits
#print axioms JPEG2000.Spec.RoundTrip.bandBits_eq
#print axioms JPEG2000.Spec.RoundTrip.blocksHeader_enc
#print axioms JPEG2000.Spec.RoundTrip.band_enc
#print axioms JPEG2000.Spec.RoundTrip.bands_enc
#print axioms JPEG2000.Spec.RoundTrip.readBody_append
#print axioms JPEG2000.Spec.RoundTrip.list_set_self_of_some
#print axioms JPEG2000.Spec.RoundTrip.bandBody_enc
#print axioms JPEG2000.Spec.RoundTrip.bandsBody_enc
#print axioms JPEG2000.Spec.RoundTrip.blockAfter_fresh
#print axioms JPEG2000.Spec.RoundTrip.range_map_array_getD
#print axioms JPEG2000.Spec.RoundTrip.foldl_bandBits
#print axioms JPEG2000.Spec.RoundTrip.packetBody_toList
#print axioms JPEG2000.Spec.RoundTrip.newPasses_eq
#print axioms JPEG2000.Spec.RoundTrip.contribs_passes
#print axioms JPEG2000.Spec.RoundTrip.sum_map_eq_zero_of
#print axioms JPEG2000.Spec.RoundTrip.out_fill
#print axioms JPEG2000.Spec.RoundTrip.packet_enc
#print axioms JPEG2000.Spec.RoundTrip.packet_roundtrip
#print axioms JPEG2000.Spec.RoundTrip.fold_enc
#print axioms JPEG2000.Spec.RoundTrip.encodeTileLRCP_eq
#print axioms JPEG2000.Spec.RoundTrip.tile_enc

-- Phase 7, task 7.3c: C10 header layer (Spec/RoundTrip/Header.lean)
#print axioms JPEG2000.Spec.RoundTrip.checkFacts_of_ok
#print axioms JPEG2000.Spec.RoundTrip.ranges_size
#print axioms JPEG2000.Spec.RoundTrip.bandMaxMags_size
#print axioms JPEG2000.Spec.RoundTrip.encodeDetailed_shape
#print axioms JPEG2000.Spec.RoundTrip.encCodestream_eq
#print axioms JPEG2000.Spec.RoundTrip.parseMainHeader_enc
#print axioms JPEG2000.Spec.RoundTrip.tilePartLoop_enc
#print axioms JPEG2000.Spec.RoundTrip.parseTileParts_enc
#print axioms JPEG2000.Spec.RoundTrip.mkComp_enc
#print axioms JPEG2000.Spec.RoundTrip.wfSIZ_enc
#print axioms JPEG2000.Spec.RoundTrip.wfCOD_enc
#print axioms JPEG2000.Spec.RoundTrip.wfQCD_enc
#print axioms JPEG2000.Spec.RoundTrip.mainCoding_enc
#print axioms JPEG2000.Spec.RoundTrip.tileCoding_enc
#print axioms JPEG2000.Spec.RoundTrip.numTiles_enc
#print axioms JPEG2000.Spec.RoundTrip.tileRect_enc
#print axioms JPEG2000.Spec.RoundTrip.checkWork_enc
#print axioms JPEG2000.Spec.RoundTrip.parseFile_raw
#print axioms JPEG2000.Spec.RoundTrip.parse_encCodestream
#print axioms JPEG2000.Spec.RoundTrip.data_bytes
#print axioms JPEG2000.Spec.RoundTrip.parse_encodeDetailed
#print axioms JPEG2000.Spec.RoundTrip.parse_encode

-- Phase 7, task 7.3f1: Layout
#print axioms JPEG2000.Spec.RoundTrip.tileComp_enc
#print axioms JPEG2000.Spec.RoundTrip.encLayout_coding
#print axioms JPEG2000.Spec.RoundTrip.encLayout_comp
#print axioms JPEG2000.Spec.RoundTrip.encLayout_wf
#print axioms JPEG2000.Spec.RoundTrip.layout_ofHeader_enc
#print axioms JPEG2000.Spec.RoundTrip.encLayout_maxLevels
#print axioms JPEG2000.Spec.RoundTrip.encLayout_numPrecincts
#print axioms JPEG2000.Spec.RoundTrip.iterationWork_enc
#print axioms JPEG2000.Spec.RoundTrip.encCounts_precincts
#print axioms JPEG2000.Spec.RoundTrip.iterationWork_check_of_headerFits
#print axioms JPEG2000.Spec.RoundTrip.iterationWork_enc_le
#print axioms JPEG2000.Spec.RoundTrip.iterationWork_check_default

-- Phase 7, task 7.3f2: TileBytes
#print axioms JPEG2000.Spec.RoundTrip.encodeDetailed_tilePackets
#print axioms JPEG2000.Spec.RoundTrip.tileData_encCodestream
#print axioms JPEG2000.Spec.RoundTrip.parse_encodeDetailed_tileData

-- Phase 7, task 7.3f3: BlockBounds
#print axioms JPEG2000.Spec.RoundTrip.encodeCodeBlock_counts
#print axioms JPEG2000.Spec.RoundTrip.blockOK_encodeCodeBlock
#print axioms JPEG2000.Spec.RoundTrip.width_le_iff_length_lt

-- Phase 7, task 7.3f4: encoder and decoder precinct geometry
#print axioms JPEG2000.Spec.RoundTrip.encodeComp_shape
#print axioms JPEG2000.Spec.RoundTrip.ReversibleTilePackets.tileShape
#print axioms JPEG2000.Spec.RoundTrip.encodeComp_precinctGeometry
#print axioms JPEG2000.Spec.RoundTrip.encodeComp_precReady
#print axioms JPEG2000.Spec.RoundTrip.initPrecincts_shape
#print axioms JPEG2000.Spec.RoundTrip.initPrecincts_geometry
#print axioms JPEG2000.Spec.RoundTrip.ReversibleTilePackets.precReady

-- Phase 7, task 7.3f5a: disjoint precinct spans and packet index injectivity
#print axioms JPEG2000.Spec.RoundTrip.initPrecincts_spans_disjoint
#print axioms JPEG2000.Spec.RoundTrip.initPrecincts_precIdx_injective

-- Phase 7, task 7.3f5d: end-to-end Tier-2 wrapper under explicit admissions
#print axioms JPEG2000.Spec.RoundTrip.decodeTile_encodeDetailed

-- Phase 7, task 7.3f5b: PacketBlocks
#print axioms JPEG2000.Spec.RoundTrip.encodeComp_packetBlock
#print axioms JPEG2000.Spec.RoundTrip.encodeComp_blockRecords
#print axioms JPEG2000.Spec.RoundTrip.encodeComp_blockOK
#print axioms JPEG2000.Spec.RoundTrip.ReversibleTilePackets.packetBlock
#print axioms JPEG2000.Spec.RoundTrip.ReversibleTilePackets.blockOK
#print axioms JPEG2000.Spec.RoundTrip.ReversibleTilePackets.componentRecords
#print axioms JPEG2000.Spec.RoundTrip.encodeComp_passes
#print axioms JPEG2000.Spec.RoundTrip.ReversibleTilePackets.packetPasses

-- Phase 7, task 7.3f5c: InitAdmission
#print axioms JPEG2000.Spec.RoundTrip.tagTree_create_of_le
#print axioms JPEG2000.Spec.RoundTrip.initPrecincts_of_encCounts
#print axioms JPEG2000.Spec.RoundTrip.initPrecincts_of_headerFits

-- Phase 7, task 7.3f5e1: CodewordBudget
#print axioms JPEG2000.Spec.RoundTrip.included_size_le_packet
#print axioms JPEG2000.Spec.RoundTrip.ReversibleTilePackets.packet_size_le_tile
#print axioms JPEG2000.Spec.RoundTrip.PacketBlockCall.planes_le_37
#print axioms JPEG2000.Spec.RoundTrip.encodeDetailed_packetBlockOK

-- Phase 7, task 7.3f5e2: ImageBudget
#print axioms JPEG2000.Spec.RoundTrip.imageArea_of_check
#print axioms JPEG2000.Spec.RoundTrip.imageCodeBlocks_eq_encCounts
#print axioms JPEG2000.Spec.RoundTrip.precincts_le_default_of_check
#print axioms JPEG2000.Spec.RoundTrip.headerFits_default_iff
#print axioms JPEG2000.Spec.RoundTrip.ImageBudget.headerFits
#print axioms JPEG2000.Spec.RoundTrip.ImageBudget.packetPasses
#print axioms JPEG2000.Spec.RoundTrip.imageBudget_iff

-- Phase 7, task 7.3f5e3: Link
#print axioms JPEG2000.Spec.RoundTrip.reversible_tile_roundtrip

-- Phase 7, task 7.3d2: DisplayReconstruction
#print axioms JPEG2000.Spec.RoundTrip.check_component_samples
#print axioms JPEG2000.Spec.RoundTrip.reversibleRows_size
#print axioms JPEG2000.Spec.RoundTrip.mctSpec_reversibleRows
#print axioms JPEG2000.Spec.RoundTrip.dcSpec_shifted
#print axioms JPEG2000.Spec.RoundTrip.display_reconstruction

-- Phase 7, task 7.3d1: BlockReconstruction
#print axioms JPEG2000.Spec.RoundTrip.DecodedEncoderBands.reconstructBlock
#print axioms JPEG2000.Spec.RoundTrip.DecodedEncoderTile.reconstructBlock

-- Phase 7, task 7.3d4a: TilePlacement
#print axioms JPEG2000.Spec.RoundTrip.blitRow_samples
#print axioms JPEG2000.Spec.RoundTrip.blitRows_samples
#print axioms JPEG2000.Spec.RoundTrip.blit_fullTile
#print axioms JPEG2000.Spec.RoundTrip.place_fullTile
#print axioms JPEG2000.Spec.RoundTrip.place_encTile
#print axioms JPEG2000.Spec.RoundTrip.outputCells_encSIZ
#print axioms JPEG2000.Spec.RoundTrip.outputBytes_encSIZ
#print axioms JPEG2000.Spec.RoundTrip.place_encTile_of_limits

-- Phase 7, task 7.3d3b: SubbandInverse
#print axioms JPEG2000.Spec.RoundTrip.reversibleBand_eq
#print axioms JPEG2000.Spec.RoundTrip.reversibleBand_sample
#print axioms JPEG2000.Spec.RoundTrip.idwt_reversibleRow

-- Phase 7, task 7.3d3a: BandCoverage
#print axioms JPEG2000.Spec.RoundTrip.sample_raster
#print axioms JPEG2000.Spec.RoundTrip.BandBlockAt.indices
#print axioms JPEG2000.Spec.RoundTrip.BandBlockAt.unique
#print axioms JPEG2000.Spec.RoundTrip.encBandCoverage
#print axioms JPEG2000.Spec.RoundTrip.encBandCoverage_of_headerFits
#print axioms JPEG2000.Spec.RoundTrip.blockCoeffs_sample

-- Phase 7, task 7.3d3c: CollectedBlocks
#print axioms JPEG2000.Spec.RoundTrip.blockCoeffs_at
#print axioms JPEG2000.Spec.RoundTrip.DecodedEncoderTile.packetBlockAt
#print axioms JPEG2000.Spec.RoundTrip.DecodedEncoderTile.blockAtGeometry
#print axioms JPEG2000.Spec.RoundTrip.DecodedEncoderTile.tileComp_collected
#print axioms JPEG2000.Spec.RoundTrip.DecodedEncoderTile.bandGrid53_collected

-- Phase 7, task 7.3d3d: WaveletReconstruction
#print axioms JPEG2000.Spec.RoundTrip.DecodedEncoderTile.tileComp_reversibleRow
#print axioms JPEG2000.Spec.RoundTrip.encodeDetailed_waveletReconstruction

-- Phase 7, task 7.3d4b2: SingleTile
#print axioms JPEG2000.Spec.RoundTrip.decode_encTile
#print axioms JPEG2000.Spec.RoundTrip.spec_roundtrip_of_tile

-- Phase 7, task 7.3d5: reversible display for every component count
#print axioms JPEG2000.Spec.RoundTrip.reversibleRows_size_all_components
#print axioms JPEG2000.Spec.RoundTrip.mctSpec_reversibleRows_all_components
#print axioms JPEG2000.Spec.RoundTrip.display_reconstruction_all_components

-- Phase 7, task 7.1j1: exact wide native sample planes
#print axioms JPEG2000.Bytes.WidePlane.size_eq
#print axioms JPEG2000.Bytes.WidePlane.get_range
#print axioms JPEG2000.Bytes.WidePlane.get_zero
#print axioms JPEG2000.Bytes.WidePlane.get_set
#print axioms JPEG2000.Spec.WidePlane.zeroChecked_spec
#print axioms JPEG2000.Spec.WidePlane.zeroChecked_layout
#print axioms JPEG2000.Spec.WidePlane.get?_eq_none_iff
#print axioms JPEG2000.Spec.WidePlane.set?_layout
#print axioms JPEG2000.Spec.WidePlane.set?_spec

-- Phase 7, task 7.1i1: wide plain Tier-1 equivalence
#print axioms JPEG2000.Spec.Tier1Wide.cellOf_value
#print axioms JPEG2000.Spec.Tier1Wide.runPasses_equiv
#print axioms JPEG2000.Spec.Tier1Wide.decodeCodeBlockSegs_equiv
#print axioms JPEG2000.Spec.Tier1Wide.decodeCodeBlock_equiv
#print axioms JPEG2000.Spec.Tier1Wide.codedPlanes_le_of_header

-- Phase 7, task 7.3d6b: resource limits for reference encodings
#print axioms JPEG2000.Spec.RoundTrip.reversible_tile_roundtrip_with_limits
#print axioms JPEG2000.Spec.RoundTrip.encoderLimits_eq_default_iff
#print axioms JPEG2000.Spec.RoundTrip.headerFits_encoderLimits
#print axioms JPEG2000.Spec.RoundTrip.reversible_tile_roundtrip_encoderLimits
#print axioms JPEG2000.Spec.RoundTrip.output_admitted_encoderLimits
#print axioms JPEG2000.Spec.RoundTrip.spec_roundtrip_with_limits_of_tile

-- Phase 7, task 7.3d4b1: component loops and tile display
#print axioms JPEG2000.Spec.RoundTrip.decodeTile_reconstructedEncoderTile

-- Phase 7, task 7.3d6a: full spec block and row recovery
#print axioms JPEG2000.Spec.RoundTrip.DecodedEncoderTile.reconstructsComponentBlocks
#print axioms JPEG2000.Spec.RoundTrip.ComponentPlanes31.reconstructsComponentBlocks
#print axioms JPEG2000.Spec.RoundTrip.ReconstructsComponentBlocks.tileComp_collected
#print axioms JPEG2000.Spec.RoundTrip.ReconstructsComponentBlocks.bandGrid53_collected
#print axioms JPEG2000.Spec.RoundTrip.DecodedEncoderTile.tileComp_reversibleRow_of_encodeDetailed
#print axioms JPEG2000.Spec.RoundTrip.encodeDetailed_waveletReconstruction_full

-- Phase 7, task 7.1i2a: wide style-aware passes
#print axioms JPEG2000.Spec.Tier1Wide.Modes.mqDecision_equiv
#print axioms JPEG2000.Spec.Tier1Wide.Modes.rawDecision_equiv
#print axioms JPEG2000.Spec.Tier1Wide.Modes.passBody_equiv
#print axioms JPEG2000.Spec.Tier1Wide.Modes.segSymbol_equiv
#print axioms JPEG2000.Spec.Tier1Wide.Modes.runPass_equiv
#print axioms JPEG2000.Spec.Tier1Wide.Segments.decodeCodeBlockSegs_equiv
#print axioms JPEG2000.Spec.Tier1Wide.Segments.decodeRanges_equiv

-- Phase 7, tasks 7.3d4b3 and 7.3d6c: spec-level image round trip
#print axioms JPEG2000.Spec.RoundTrip.assembled_image
#print axioms JPEG2000.Spec.RoundTrip.decodeTile_reconstructedEncoderTile_lossless
#print axioms JPEG2000.Spec.RoundTrip.spec_roundtrip_lossless_with_limits
#print axioms JPEG2000.Spec.RoundTrip.encoderImageOfNative_eq
#print axioms JPEG2000.Spec.RoundTrip.native_roundtrip_of_c9
#print axioms JPEG2000.Spec.RoundTrip.encode_native_roundtrip_of_c9
#print axioms JPEG2000.Spec.RoundTrip.spec_roundtrip_with_limits
#print axioms JPEG2000.Spec.RoundTrip.spec_roundtrip
#print axioms JPEG2000.Spec.RoundTrip.spec_roundtrip_default
#print axioms JPEG2000.Spec.RoundTrip.encode_spec_roundtrip

-- Phase 7, task 7.1j2a: wide sample reconstruction and placement
#print axioms JPEG2000.WideOutput.destIndex_lt
#print axioms JPEG2000.Spec.WideOutput.sample_rev
#print axioms JPEG2000.Spec.WideOutput.sample_irrev
#print axioms JPEG2000.Spec.WideOutput.roundFix_eq_roundHalf
#print axioms JPEG2000.Spec.WideOutput.sample_recovers
#print axioms JPEG2000.Spec.WideOutput.blit_succeeds
#print axioms JPEG2000.Spec.WideOutput.blit_spec
#print axioms JPEG2000.Spec.WideQuant.zeroChecked_eq
#print axioms JPEG2000.Spec.WideQuant.unshift_eq
#print axioms JPEG2000.Spec.WideQuant.prepare_zero
#print axioms JPEG2000.Spec.WideQuant.reversible_eq
#print axioms JPEG2000.Spec.WideQuant.reversible_midpoint
#print axioms JPEG2000.Spec.WideQuant.irreversible_eq
#print axioms JPEG2000.Spec.WideQuant.irreversible_error
#print axioms JPEG2000.Spec.WideQuant.reduced_band
#print axioms JPEG2000.Spec.WideQuant.blockOffset_eq
#print axioms JPEG2000.Spec.WideQuant.dequantBlock_succeeds
#print axioms JPEG2000.Spec.WideQuant.dequantBlock_read
#print axioms JPEG2000.Spec.WideQuant.dequantBlock_sample
#print axioms JPEG2000.Spec.WideReversible.idwt53_spec
#print axioms JPEG2000.Spec.WideReversible.idwt53_of_bandsEq
#print axioms JPEG2000.Spec.WideReversible.rctInverse_spec
#print axioms JPEG2000.Spec.WideReversible.reconstruct_rgb
#print axioms JPEG2000.Spec.WideICT.ictInverse_ok
#print axioms JPEG2000.Spec.WideICT.ictInverse_fixed_error
#print axioms JPEG2000.Spec.WideICT.ictInverse_error
#print axioms JPEG2000.Spec.WideICT.ictInverse_c8
#print axioms JPEG2000.Spec.WideDWT97.product_err
#print axioms JPEG2000.Spec.WideDWT97.idwt97_spec
#print axioms JPEG2000.Spec.WideDWT97.level_work
#print axioms JPEG2000.Spec.WideDWT97.idwt97_of_bandsClose
#print axioms JPEG2000.Spec.NativeOutput.allocOutput_spec
#print axioms JPEG2000.Spec.NativeOutput.writeComponent_badGeometry
#print axioms JPEG2000.Spec.NativeOutput.writeComponent_spec
#print axioms JPEG2000.Spec.NativeOutput.writeComponent_succeeds
#print axioms JPEG2000.Spec.NativeOutput.disjoint_writes
#print axioms JPEG2000.Spec.NativeOutput.writeTile_spec
#print axioms JPEG2000.Spec.NativeOutput.allocOutput_succeeds
#print axioms JPEG2000.Spec.NativeOutput.backing_size
#print axioms JPEG2000.Spec.NativeOutput.allocOutput_bounds
#print axioms JPEG2000.Spec.NativeOutput.writeComponent_roundHalf
#print axioms JPEG2000.Spec.NativeOutput.writeComponent_recovers
#print axioms JPEG2000.Spec.NativeOutput.writeTile_succeeds
#print axioms JPEG2000.Spec.NativeSample.placed_sample
#print axioms JPEG2000.Spec.NativeSample.writeTile_sample

-- Phase 7, task 7.1j3a: exact scaling through 38 bits
#print axioms JPEG2000.Scaler.applyNative_make_eq

#print axioms JPEG2000.Spec.HeaderWF.readArray_inv
#print axioms JPEG2000.Spec.HeaderWF.parseMainHeader_fields
#print axioms JPEG2000.Spec.HeaderWF.parseTileParts_fields
#print axioms JPEG2000.Spec.HeaderWF.mem_extract
#print axioms JPEG2000.Spec.HeaderWF.overrides_inv
#print axioms JPEG2000.Spec.HeaderWF.getD_none
#print axioms JPEG2000.Spec.HeaderWF.getD_getD
#print axioms JPEG2000.Spec.HeaderWF.arrayMapM_mem
#print axioms JPEG2000.Spec.HeaderWF.list_foldl_inv
#print axioms JPEG2000.Spec.HeaderWF.geom_params
#print axioms JPEG2000.Spec.WideHeaderBounds.parsed_component_bounds
#print axioms JPEG2000.Spec.WideHeaderBounds.ComponentBounds.block_planes
#print axioms JPEG2000.Spec.WideHeaderBounds.parsed_component
#print axioms JPEG2000.Spec.WideHeaderBounds.absent_component

#print axioms JPEG2000.CodestreamComponent.samples_get?
#print axioms JPEG2000.Spec.Resources.public_limitExceeded_of_output
#print axioms JPEG2000.Spec.Resources.publicCodestream_resources

#print axioms JPEG2000.Spec.ReversibleDispatch.mallat_read
#print axioms JPEG2000.Spec.ReversibleDispatch.wideBands
#print axioms JPEG2000.Spec.ReversibleDispatch.tileComp_sound
#print axioms JPEG2000.Spec.ReversibleDispatch.tileComp_equiv
#print axioms JPEG2000.Spec.ReversibleDispatch.parsed_component_ok
#print axioms JPEG2000.Spec.ReversibleDispatch.parsed_component
#print axioms JPEG2000.Spec.ReversibleDispatch.colour_spec
#print axioms JPEG2000.Spec.ReversibleDispatch.colour_cells
#print axioms JPEG2000.Spec.ReversibleDispatch.colour_mctSpec
#print axioms JPEG2000.Spec.IrreversibleDispatch.compactBands_ok
#print axioms JPEG2000.Spec.IrreversibleDispatch.source_fixed
#print axioms JPEG2000.Spec.IrreversibleDispatch.component_c8
#print axioms JPEG2000.Spec.IrreversibleDispatch.ict_c8
#print axioms JPEG2000.Spec.IrreversibleDispatch.sources_c8
#print axioms JPEG2000.Spec.IrreversibleDispatch.tile_c8
#print axioms JPEG2000.Spec.IrreversibleDispatch.parsed_tile_c8

#print axioms JPEG2000.Spec.NativeTraversal.decode_of_stages

#print axioms JPEG2000.Spec.NativePlacement.parsed_depth
#print axioms JPEG2000.Spec.NativePlacement.allocation
#print axioms JPEG2000.Spec.NativePlacement.guarded_allocation
#print axioms JPEG2000.Spec.NativePlacement.blit_reads
#print axioms JPEG2000.Spec.NativePlacement.tile_grid
#print axioms JPEG2000.Spec.NativePlacement.tile_reduction
#print axioms JPEG2000.Spec.NativePlacement.place_components
#print axioms JPEG2000.Spec.NativePlacement.source_dcSpec
#print axioms JPEG2000.Spec.NativePlacement.placement
#print axioms JPEG2000.Spec.NativePlacement.placement_sim
#print axioms JPEG2000.Spec.NativePlacement.finalize
#print axioms JPEG2000.Spec.NativeComposition.of_tiles

#print axioms JPEG2000.Spec.IrreversibleDispatch.ict_sources
#print axioms JPEG2000.Spec.TileDispatch.component_equiv
#print axioms JPEG2000.Spec.TileDispatch.ComponentRel.centered
#print axioms JPEG2000.Spec.TileDispatch.parsed_component
#print axioms JPEG2000.Spec.TileDispatch.components_equiv
#print axioms JPEG2000.Spec.TileDispatch.parsed_tile
#print axioms JPEG2000.Spec.C9.c9_narrow
#print axioms JPEG2000.Spec.RoundTrip.native_roundtrip
#print axioms JPEG2000.Spec.RoundTrip.native_roundtrip_default
#print axioms JPEG2000.Spec.RoundTrip.encode_native_roundtrip
#print axioms JPEG2000.Spec.RoundTrip.image_roundtrip
#print axioms JPEG2000.Spec.RoundTrip.encode_image_roundtrip

#print axioms JPEG2000.Spec.ColorResources.interleave_resources
#print axioms JPEG2000.Spec.ColorResources.interleave_loop
#print axioms JPEG2000.Spec.ColorResources.channel_map_size
#print axioms JPEG2000.Spec.ColorResources.resolved_layout_size
#print axioms JPEG2000.Spec.ColorResources.applyMapping_resources
#print axioms JPEG2000.Spec.ColorResources.mapping_backing
#print axioms JPEG2000.Spec.ColorResources.retained_palette
#print axioms JPEG2000.Spec.ColorResources.plane_domain
#print axioms JPEG2000.Spec.ColorResources.upsample_resources
#print axioms JPEG2000.Spec.ColorResources.sycc_indices_size
#print axioms JPEG2000.Spec.ColorResources.sycc_resources
#print axioms JPEG2000.Spec.ColorResources.replication_resources
#print axioms JPEG2000.Spec.ColorResources.decode_resources
#print axioms JPEG2000.Spec.ColorResources.image_native_spec

#print axioms JPEG2000.Spec.NativeResources.centeredTile_limitExceeded
#print axioms JPEG2000.Spec.NativeResources.centeredTile_work

#print axioms JPEG2000.Spec.Resources.PacketTraversal.inspectPrevious_any
#print axioms JPEG2000.Spec.Resources.PacketTraversal.visits_tests_le_charge
#print axioms JPEG2000.Spec.Resources.PacketTraversal.forPackets_schedule
#print axioms JPEG2000.Spec.Resources.PacketTraversal.schedule_charge
#print axioms JPEG2000.Spec.Resources.PacketTraversal.decodePacket_contributions
#print axioms JPEG2000.Spec.Resources.PacketTraversal.packetStep_passes
#print axioms JPEG2000.Spec.Resources.PacketTraversal.walk_prefix
#print axioms JPEG2000.Spec.Resources.PacketTraversal.walk_outcome
#print axioms JPEG2000.Spec.Resources.PacketTraversal.measureStream_erase
#print axioms JPEG2000.Spec.Resources.PacketTraversal.measureStream_bounds
#print axioms JPEG2000.Spec.Resources.PacketTraversal.measureStream_read
#print axioms JPEG2000.Spec.Resources.PacketTraversal.measureTiles_erase
#print axioms JPEG2000.Spec.Resources.PacketTraversal.trace_visit
#print axioms JPEG2000.Spec.Resources.PacketTraversal.trace_bounds
#print axioms JPEG2000.Spec.Resources.PacketTraversal.measureTiles_finish
#print axioms JPEG2000.Spec.Resources.PacketTraversal.measureGrid_trace
#print axioms JPEG2000.Spec.Resources.PacketTraversal.measureTiles_bounds
#print axioms JPEG2000.Spec.Resources.PublicPacketWork.decode_packet_work

#print axioms JPEG2000.Spec.Resources.WideArithmetic.magnitude_bits
#print axioms JPEG2000.Spec.Resources.WideArithmetic.quant_operands
#print axioms JPEG2000.Spec.Resources.WideArithmetic.pass53_operands
#print axioms JPEG2000.Spec.Resources.WideArithmetic.lift53
#print axioms JPEG2000.Spec.Resources.WideArithmetic.synthesis53
#print axioms JPEG2000.Spec.Resources.WideArithmetic.product_operands
#print axioms JPEG2000.Spec.Resources.WideArithmetic.step97_operands
#print axioms JPEG2000.Spec.Resources.WideArithmetic.passes97
#print axioms JPEG2000.Spec.Resources.WideArithmetic.synthesis97
#print axioms JPEG2000.Spec.Resources.WideArithmetic.idwt53_bounds
#print axioms JPEG2000.Spec.Resources.WideArithmetic.idwt97_bounds
#print axioms JPEG2000.Spec.Resources.WideArithmetic.rct_operands
#print axioms JPEG2000.Spec.Resources.WideArithmetic.rct_bounds
#print axioms JPEG2000.Spec.Resources.WideArithmetic.ict_operands
#print axioms JPEG2000.Spec.Resources.WideArithmetic.ict_bounds
#print axioms JPEG2000.Spec.Resources.WideArithmetic.tile_coefficients
#print axioms JPEG2000.Spec.Resources.WideArithmetic.parsed_quant
#print axioms JPEG2000.Spec.Resources.WideArithmetic.coefficient_width
#print axioms JPEG2000.Spec.Resources.WideArithmetic.rct_view
#print axioms JPEG2000.Spec.Resources.WideArithmetic.parsed_spatial
#print axioms JPEG2000.Spec.Resources.WideArithmetic.promoted_ict
#print axioms JPEG2000.Spec.Resources.WideArithmetic.dispatched_rct
#print axioms JPEG2000.Spec.Resources.WideArithmetic.dispatched_ict
#print axioms JPEG2000.Spec.Resources.WideArithmetic.parsed_tile

#print axioms JPEG2000.Spec.Resources.HeaderWork.insertionSort_perm
#print axioms JPEG2000.Spec.Resources.HeaderWork.readSegment_extent
#print axioms JPEG2000.Spec.Resources.HeaderWork.segmentLoop_fuel
#print axioms JPEG2000.Spec.Resources.HeaderWork.tileHeaderLoop_fuel
#print axioms JPEG2000.Spec.Resources.HeaderWork.readTilePart_step
#print axioms JPEG2000.Spec.Resources.HeaderWork.tilePartLoop_fuel
#print axioms JPEG2000.Spec.Resources.HeaderWork.readBox_extent
#print axioms JPEG2000.Spec.Resources.HeaderWork.boxLoops_fuel
#print axioms JPEG2000.Spec.Resources.HeaderWork.parse_input_excess
#print axioms JPEG2000.Spec.Resources.HeaderWork.gatherBytes_size
#print axioms JPEG2000.Spec.Resources.HeaderWork.tier1Input_storage
#print axioms JPEG2000.Spec.Resources.HeaderWork.headerGather_storage
#print axioms JPEG2000.Spec.Resources.HeaderWork.segmentLoop_storage
#print axioms JPEG2000.Spec.Resources.HeaderWork.tileHeaderLoop_storage
#print axioms JPEG2000.Spec.Resources.HeaderWork.precinct_geometry
#print axioms JPEG2000.Spec.Resources.HeaderWork.precinct_storage
#print axioms JPEG2000.Spec.Resources.HeaderWork.takeRanges_account
#print axioms JPEG2000.Spec.Resources.HeaderWork.ppmLength_copy
#print axioms JPEG2000.Spec.Resources.HeaderWork.ppmChunks_account
#print axioms JPEG2000.Spec.Resources.HeaderWork.headerStreamAt_storage
#print axioms JPEG2000.Spec.Resources.HeaderWork.initPrecincts_storage
#print axioms JPEG2000.Spec.Resources.HeaderWork.parse_storage
#print axioms JPEG2000.Spec.Resources.HeaderWork.layout_budget
#print axioms JPEG2000.Spec.Resources.HeaderWork.parse_ppm
#print axioms JPEG2000.Spec.Resources.HeaderWork.parse_tile_storage
#print axioms JPEG2000.Spec.Resources.HeaderWork.parsed_headerStream
#print axioms JPEG2000.Spec.Resources.HeaderWork.gather_copy_charge
#print axioms JPEG2000.Spec.Resources.HeaderWork.tier1Input_copy_charge
#print axioms JPEG2000.Spec.Resources.HeaderWork.tileData_copy_charge
#print axioms JPEG2000.Spec.Resources.HeaderWork.palette_table
#print axioms JPEG2000.Spec.Resources.HeaderWork.jp2h_depth_excess
#print axioms JPEG2000.Spec.Resources.HeaderWork.checkWork_visits
#print axioms JPEG2000.Spec.Resources.HeaderWork.ppmChunks_fuel

#print axioms JPEG2000.Spec.Resources.Tier1Work.wide_value
#print axioms JPEG2000.Spec.Resources.Tier1Work.compact_value
#print axioms JPEG2000.Spec.Resources.Tier1Work.compact_buffers
#print axioms JPEG2000.Spec.Resources.Tier1Work.wide_area
#print axioms JPEG2000.Spec.Resources.Tier1Work.call_work
#print axioms JPEG2000.Spec.Resources.Tier1Work.refusal_work
#print axioms JPEG2000.Spec.Resources.Tier1Work.bad_range_work
#print axioms JPEG2000.Spec.Resources.Tier1Work.compact_preflight
#print axioms JPEG2000.Spec.Resources.Tier1Work.wide_preflight
#print axioms JPEG2000.Spec.Resources.Tier1Work.preflight_work
#print axioms JPEG2000.Spec.Resources.Tier1Work.preflight_ok
#print axioms JPEG2000.Spec.Resources.Tier1Work.preflight_domains
#print axioms JPEG2000.Spec.Resources.Tier1Work.compact_plain_prefix
#print axioms JPEG2000.Spec.Resources.Tier1Work.plain_work
#print axioms JPEG2000.Spec.Resources.Tier1Work.wide_work
#print axioms JPEG2000.Spec.Resources.Tier1Work.compact_work
#print axioms JPEG2000.Spec.Resources.Tier1Work.fast_work
#print axioms JPEG2000.Spec.Resources.Tier1Work.Reads.decisions_le
#print axioms JPEG2000.Spec.Resources.Tier1Work.Reads.work_le
#print axioms JPEG2000.Spec.Resources.Tier1Work.Reads.operations_le
#print axioms JPEG2000.Spec.Resources.Tier1Work.schedule_counts
#print axioms JPEG2000.Spec.Resources.Tier1Work.plain_schedule
#print axioms JPEG2000.Spec.Resources.Tier1Work.wide_schedule
#print axioms JPEG2000.Spec.Resources.Tier1Work.compact_plain_schedule
#print axioms JPEG2000.Spec.Resources.Tier1Work.compact_schedule
#print axioms JPEG2000.Spec.Resources.Tier1Work.clamp_shape
#print axioms JPEG2000.Spec.Resources.Tier1Work.stripe_domains
#print axioms JPEG2000.Spec.Resources.Tier1Work.column_budget
#print axioms JPEG2000.Spec.Resources.Tier1Work.wide_storage
#print axioms JPEG2000.Spec.Resources.Tier1Work.compact_storage
#print axioms JPEG2000.Spec.Resources.Tier1Work.wide_cells
#print axioms JPEG2000.Spec.Resources.Tier1Work.parsed_cells
#print axioms JPEG2000.Spec.Resources.Tier1Work.compact_cells
#print axioms JPEG2000.Spec.Resources.Tier1Work.parsed_compact_cells
#print axioms JPEG2000.Spec.Resources.Tier1Work.parsed_call_work
#print axioms JPEG2000.Spec.Resources.Tier1Work.plainPassReads
#print axioms JPEG2000.Spec.Resources.Tier1Work.widePassReads
#print axioms JPEG2000.Spec.Resources.Tier1Work.compactPlainReads
#print axioms JPEG2000.Spec.Resources.Tier1Work.compactModeReads
#print axioms JPEG2000.Spec.Resources.parsed_tile_signed_width
#print axioms JPEG2000.Spec.Resources.centeredTile_signed_width
#print axioms JPEG2000.Spec.Resources.PublicPacketWork.admission_error
#print axioms JPEG2000.Spec.Resources.PublicPacketWork.admission_excess

#print axioms JPEG2000.Spec.Resources.HeaderWork.measuredSort_work
#print axioms JPEG2000.Spec.Resources.HeaderWork.sortUnique_work

-- Task 7.4c2s1, coefficient assembly and precision fallback.
#print axioms JPEG2000.Spec.Resources.AssemblyCost.walk_value
#print axioms JPEG2000.Spec.Resources.AssemblyCost.walk_bound
#print axioms JPEG2000.Spec.Resources.AssemblyCost.origin_levels
#print axioms JPEG2000.Spec.Resources.AssemblyCost.compact_placement
#print axioms JPEG2000.Spec.Resources.AssemblyCost.wide_place
#print axioms JPEG2000.Spec.Resources.AssemblyCost.reversible_work
#print axioms JPEG2000.Spec.Resources.AssemblyCost.irreversible_work
#print axioms JPEG2000.Spec.Resources.AssemblyCost.parsed_component_work
#print axioms JPEG2000.Spec.Resources.AssemblyCost.native_budget
#print axioms JPEG2000.Spec.Resources.AssemblyCost.block_storage
#print axioms JPEG2000.Spec.Resources.AssemblyCost.mallat_width
#print axioms JPEG2000.Spec.Resources.AssemblyCost.packed_storage
#print axioms JPEG2000.Spec.Resources.AssemblyCost.wide_storage
#print axioms JPEG2000.Spec.Resources.AssemblyCost.native_plane_cells
#print axioms JPEG2000.Spec.Resources.AssemblyCost.block_workspace
#print axioms JPEG2000.Spec.Resources.AssemblyCost.block_ceiling
#print axioms JPEG2000.Spec.Resources.AssemblyCost.topology_split
#print axioms JPEG2000.Spec.Resources.AssemblyCost.topology_budget
#print axioms JPEG2000.Spec.Resources.AssemblyCost.component_budget

-- Task 7.4c2s3, native tile colour and output placement.
#print axioms JPEG2000.Spec.Resources.TileColorPlacement.colourFits_work
#print axioms JPEG2000.Spec.Resources.TileColorPlacement.view_reads
#print axioms JPEG2000.Spec.Resources.TileColorPlacement.packRows_work
#print axioms JPEG2000.Spec.Resources.TileColorPlacement.fill_work
#print axioms JPEG2000.Spec.Resources.TileColorPlacement.map1_work
#print axioms JPEG2000.Spec.Resources.TileColorPlacement.map3_work
#print axioms JPEG2000.Spec.Resources.TileColorPlacement.blitRows_work
#print axioms JPEG2000.Spec.Resources.TileColorPlacement.blitCells_work
#print axioms JPEG2000.Spec.Resources.TileColorPlacement.tabulate_work
#print axioms JPEG2000.Spec.Resources.TileColorPlacement.compactICT_work
#print axioms JPEG2000.Spec.Resources.TileColorPlacement.ict_work
#print axioms JPEG2000.Spec.Resources.TileColorPlacement.rct_work
#print axioms JPEG2000.Spec.Resources.TileColorPlacement.sources_work
#print axioms JPEG2000.Spec.Resources.TileColorPlacement.preColour_work
#print axioms JPEG2000.Spec.Resources.TileColorPlacement.tile_work
#print axioms JPEG2000.Spec.Resources.TileColorPlacement.writeComponent_work
#print axioms JPEG2000.Spec.Resources.TileColorPlacement.writeTile_work
#print axioms JPEG2000.Spec.Resources.TileColorPlacement.centeredTile_placement
#print axioms JPEG2000.Spec.Resources.TileColorPlacement.centeredTile_reads
#print axioms JPEG2000.Spec.Resources.TileColorPlacement.native_tile_work
#print axioms JPEG2000.Spec.Resources.TileColorPlacement.placement_read_domain

-- Signed-magnitude byte payloads of retained native component data.
#print axioms JPEG2000.Spec.Resources.component_signed_width
#print axioms JPEG2000.Spec.Resources.TileColorPlacement.component_backing_bytes
#print axioms JPEG2000.Spec.Resources.TileColorPlacement.centeredTile_backing_bytes

-- Task 7.4c1h, progression setup and packet callback prefixes.
#print axioms JPEG2000.Spec.Resources.PacketSortWork.sort_work
#print axioms JPEG2000.Spec.Resources.ProgressionFields.parsed_limits
#print axioms JPEG2000.Spec.Resources.PacketLocalWork.takePieces_extent
#print axioms JPEG2000.Spec.Resources.PacketLocalWork.addPieces_storage
#print axioms JPEG2000.Spec.Resources.PacketLocalWork.body_range_bytes
#print axioms JPEG2000.Spec.Resources.PacketLocalWork.packet_prefix_storage
#print axioms JPEG2000.Spec.Resources.PacketLocalWork.packet_work
#print axioms JPEG2000.Spec.Resources.PacketLocalWork.stream_attempt
#print axioms JPEG2000.Spec.Resources.PacketLocalWork.decode_attempts
#print axioms JPEG2000.Spec.Resources.PacketLocalWork.positionTable_work
#print axioms JPEG2000.Spec.Resources.PacketLocalWork.progression_work
#print axioms JPEG2000.Spec.Resources.PacketLocalWork.table_limit
#print axioms JPEG2000.Spec.Resources.PacketLocalWork.parsed_setup
#print axioms JPEG2000.Spec.Resources.PacketLocalWork.preflight_work
#print axioms JPEG2000.Spec.Resources.PacketLocalWork.completed_store

-- Native colour and placement charges across the public packet traversal.
#print axioms JPEG2000.Spec.Resources.PacketTraversal.placementFromHeader_work
#print axioms JPEG2000.Spec.Resources.PublicPacketWork.decode_placement_work

-- Task 7.4c2s2, checked inverse-wavelet visits, allocations and operand widths.
#print axioms JPEG2000.Spec.Resources.WaveletCost.compact_work
#print axioms JPEG2000.Spec.Resources.WaveletCost.operands53
#print axioms JPEG2000.Spec.Resources.WaveletCost.operands97
#print axioms JPEG2000.Spec.Resources.WaveletCost.lines_shape
#print axioms JPEG2000.Spec.Resources.WaveletCost.wide53_work
#print axioms JPEG2000.Spec.Resources.WaveletCost.wide97_work
#print axioms JPEG2000.Spec.Resources.WaveletCost.compact_allocation
#print axioms JPEG2000.Spec.Resources.WaveletCost.retry53_work
#print axioms JPEG2000.Spec.Resources.WaveletCost.retry97_work

-- JP2 channel metadata and alpha selection.
#print axioms JPEG2000.Spec.ColorResources.channelSort_work
#print axioms JPEG2000.Spec.ColorResources.alpha_work
#print axioms JPEG2000.Spec.ColorResources.cdef_work
#print axioms JPEG2000.Spec.ColorResources.associations_work
#print axioms JPEG2000.Spec.ColorResources.layout_work
#print axioms JPEG2000.Spec.ColorResources.retained_cdef
#print axioms JPEG2000.Spec.ColorResources.resolve_layout_work
#print axioms JPEG2000.Spec.ColorResources.decode_layout_error
#print axioms JPEG2000.Spec.ColorResources.image_layout_work

-- Header and packet geometry on the actual public decoding prefix.
#print axioms JPEG2000.Spec.Resources.GeometryInit.parsed_init_work
#print axioms JPEG2000.Spec.Resources.GeometryInit.init_index_rows
#print axioms JPEG2000.Spec.Resources.GeometryInit.decoded_store_geometry
#print axioms JPEG2000.Spec.Resources.GeometryInit.parse_geometry_work
#print axioms JPEG2000.Spec.Resources.GeometryInit.decode_geometry_work
#print axioms JPEG2000.Spec.Resources.GeometryInit.image_geometry_work
#print axioms JPEG2000.Spec.Resources.ReconstructionCost.prefix_work
#print axioms JPEG2000.Spec.Resources.ReconstructionCost.packed_entry
#print axioms JPEG2000.Spec.Resources.ReconstructionCost.block_operands
#print axioms JPEG2000.Spec.Resources.ReconstructionCost.wave_operands
#print axioms JPEG2000.Spec.Resources.ReconstructionCost.colour_operands
#print axioms JPEG2000.Spec.Resources.ReconstructionCost.prefix_backing
#print axioms JPEG2000.Spec.Resources.ReconstructionCost.block_workspace
#print axioms JPEG2000.Spec.Resources.ReconstructionCost.tile_work
#print axioms JPEG2000.Spec.Resources.ReconstructionCost.decode_work
#print axioms JPEG2000.Spec.Resources.ReconstructionCost.placement_operands
#print axioms JPEG2000.Spec.Resources.ReconstructionCost.mallat_prefix
#print axioms JPEG2000.Spec.Resources.ReconstructionCost.live_workspace
#print axioms JPEG2000.Spec.Resources.ReconstructionCost.promoted_operands
#print axioms JPEG2000.Spec.Resources.ReconstructionCost.block_payload
#print axioms JPEG2000.Spec.Resources.SegmentHistory.translate_visits
#print axioms JPEG2000.Spec.Resources.SegmentHistory.completed_history
#print axioms JPEG2000.Spec.Resources.SegmentHistory.store_bounds
#print axioms JPEG2000.Spec.Resources.SegmentHistory.selected_store_bounds
#print axioms JPEG2000.Spec.Resources.SegmentHistory.tile_copies
#print axioms JPEG2000.Spec.Resources.SegmentHistory.tile_assembly_work
#print axioms JPEG2000.Spec.Resources.SegmentHistory.packet_body_erase
#print axioms JPEG2000.Spec.Resources.SegmentHistory.packet_prefix_counts
#print axioms JPEG2000.Spec.Resources.SegmentHistory.selected_block_input
#print axioms JPEG2000.Spec.Resources.SegmentHistory.translation_history
#print axioms JPEG2000.Spec.Resources.SegmentHistory.tile_translation_work
#print axioms JPEG2000.Spec.Resources.SegmentHistory.present_mem
#print axioms JPEG2000.Spec.Resources.ReconstructionCost.public_work
#print axioms JPEG2000.Spec.Resources.HeaderPayload.arrayReads_work
#print axioms JPEG2000.Spec.Resources.HeaderPayload.varintReads_work
#print axioms JPEG2000.Spec.Resources.HeaderPayload.rank_work
#print axioms JPEG2000.Spec.Resources.HeaderPayload.pointerSorts_work
#print axioms JPEG2000.Spec.Resources.HeaderPayload.tileSorts_work
#print axioms JPEG2000.Spec.Resources.HeaderPayload.rank_table
#print axioms JPEG2000.Spec.Resources.HeaderPayload.parse_work
#print axioms JPEG2000.Spec.Resources.HeaderPayload.sort_calls
#print axioms JPEG2000.Spec.Resources.HeaderPayload.chunks_work
#print axioms JPEG2000.Spec.Resources.HeaderPayload.selection_work
#print axioms JPEG2000.Spec.Resources.HeaderPayload.decode_header_work
#print axioms JPEG2000.Spec.ColorResources.MappingPrefix.retained_counts
#print axioms JPEG2000.Spec.ColorResources.MappingPrefix.scan_le
#print axioms JPEG2000.Spec.ColorResources.MappingPrefix.resolver_work
#print axioms JPEG2000.Spec.ColorResources.MappingPrefix.resolve_prefix_work
#print axioms JPEG2000.Spec.ColorResources.MappingPrefix.mapping_work
#print axioms JPEG2000.Spec.ColorResources.MappingPrefix.native_mapping_work
#print axioms JPEG2000.Spec.ColorResources.MappingPrefix.native_mapping_success
#print axioms JPEG2000.Spec.ColorResources.MappingPrefix.image_mapping_work
#print axioms JPEG2000.Spec.ColorResources.MappingPrefix.decode_mapping_error
#print axioms JPEG2000.Spec.ColorResources.reduce_sides
#print axioms JPEG2000.Spec.ColorResources.raw_sides
#print axioms JPEG2000.Spec.ColorResources.mapped_sides
#print axioms JPEG2000.Spec.ColorResources.DisplayPrefix.read_value
#print axioms JPEG2000.Spec.ColorResources.DisplayPrefix.channel_reads
#print axioms JPEG2000.Spec.ColorResources.DisplayPrefix.channel_precision
#print axioms JPEG2000.Spec.ColorResources.DisplayPrefix.mapped_precision
#print axioms JPEG2000.Spec.ColorResources.DiagnosticImage.display_refusal
#print axioms JPEG2000.Spec.ColorResources.DiagnosticImage.image_diagnostics
#print axioms JPEG2000.Spec.ColorResources.DiagnosticImage.compose_native
#print axioms JPEG2000.Spec.ColorResources.DiagnosticImage.interleaver_diagnostics
#print axioms JPEG2000.Spec.ColorResources.DisplayPrefix.display_work
#print axioms JPEG2000.Spec.ColorResources.DisplayPrefix.interleaving_work
#print axioms JPEG2000.Spec.ColorResources.DisplayPrefix.public_interleaving_work
#print axioms JPEG2000.Spec.ColorResources.DisplayPrefix.selected_reads
#print axioms JPEG2000.Spec.Resources.HeaderPayload.rank_storage
#print axioms JPEG2000.Spec.Resources.NativeCost.allocation_work
#print axioms JPEG2000.Spec.Resources.NativeCost.entry_storage
#print axioms JPEG2000.Spec.Resources.NativeCost.packetMeter_result
#print axioms JPEG2000.Spec.Resources.NativeCost.visited_storage
#print axioms JPEG2000.Spec.Resources.NativeCost.destination_storage
#print axioms JPEG2000.Spec.Resources.NativeCost.attempted_storage
#print axioms JPEG2000.Spec.Resources.NativeCost.reconstruction_storage
#print axioms JPEG2000.Spec.Resources.NativeCost.decode_work
#print axioms JPEG2000.Spec.Resources.PacketLocalWork.partial_body_store
#print axioms JPEG2000.Spec.Resources.PacketLocalWork.completed_iteration
#print axioms JPEG2000.Spec.Resources.PacketTraversal.prefix_destination
#print axioms JPEG2000.Spec.Resources.SegmentHistory.iteration_translation
#print axioms JPEG2000.Spec.Resources.SegmentHistory.raw_store_slots
#print axioms JPEG2000.Spec.Resources.DiagnosticCost.radix_cost
#print axioms JPEG2000.Spec.Resources.DiagnosticCost.Text.storage_le_work
#print axioms JPEG2000.Spec.Resources.DiagnosticCost.Text.bounds
#print axioms JPEG2000.Spec.Resources.DiagnosticCost.public_admission
#print axioms JPEG2000.Spec.Resources.DiagnosticCost.built_cost
#print axioms JPEG2000.Spec.Resources.DiagnosticCost.Text.Within.raiseCap
#print axioms JPEG2000.Spec.Resources.DiagnosticCost.Trace.raiseCap_events
#print axioms JPEG2000.Spec.Resources.DiagnosticCost.trace_cost
#print axioms JPEG2000.Spec.Resources.DiagnosticCost.trace_storage
#print axioms JPEG2000.Spec.Resources.DiagnosticCost.trace_retained
#print axioms JPEG2000.Spec.Resources.DiagnosticCost.reduction_storage
#print axioms JPEG2000.Spec.Resources.DiagnosticCost.render_limit_cost
#print axioms JPEG2000.Spec.Resources.DiagnosticCost.caller_render_unbounded
#print axioms JPEG2000.Spec.Resources.DiagnosticCost.public_siz
#print axioms JPEG2000.Spec.Resources.DiagnosticCost.public_signature
#print axioms JPEG2000.Spec.Resources.DiagnosticCost.public_ppm_mismatch
#print axioms JPEG2000.Spec.Resources.DiagnosticCost.public_sop
#print axioms JPEG2000.Spec.Resources.DiagnosticCost.public_sot
#print axioms JPEG2000.Spec.Resources.DiagnosticCost.public_tile_marker
#print axioms JPEG2000.Spec.Resources.DiagnosticCost.public_layout
#print axioms JPEG2000.Spec.Resources.DiagnosticCost.public_resolve
#print axioms JPEG2000.Spec.Resources.DiagnosticCost.public_resolve_limit
#print axioms JPEG2000.Spec.Resources.DiagnosticCost.interleave_error
#print axioms JPEG2000.Spec.Resources.DiagnosticCost.public_interleavers
#print axioms JPEG2000.Spec.Resources.DiagnosticCost.external_interleavers_unbounded
#print axioms JPEG2000.Spec.Resources.DiagnosticCost.public_pick
#print axioms JPEG2000.Spec.Resources.DiagnosticMarkerOrigin.main_location
#print axioms JPEG2000.Spec.Resources.DiagnosticMarker.marker_digits
#print axioms JPEG2000.Spec.Resources.DiagnosticMarker.main_source
#print axioms JPEG2000.Spec.Resources.DiagnosticMarker.range_source
#print axioms JPEG2000.Spec.Resources.DiagnosticMarker.inRange_location
#print axioms JPEG2000.Spec.Resources.DiagnosticMarker.public_main
#print axioms JPEG2000.Spec.Resources.DiagnosticMarker.public_cost
#print axioms JPEG2000.Spec.Resources.DiagnosticMarker.public_throughMain
#print axioms JPEG2000.Spec.Resources.DiagnosticMarker.throughMain_events
#print axioms JPEG2000.Spec.Resources.DiagnosticBox.file_bounds
#print axioms JPEG2000.Spec.Resources.DiagnosticBox.raw_eq
#print axioms JPEG2000.Spec.Resources.DiagnosticBox.public_box
#print axioms JPEG2000.Spec.Resources.DiagnosticBox.public_admission_excess
#print axioms JPEG2000.Spec.Resources.DiagnosticBox.public_raw
#print axioms JPEG2000.Spec.Resources.DiagnosticBox.signature_replacement
#print axioms JPEG2000.Spec.Resources.DiagnosticPointers.sort_events
#print axioms JPEG2000.Spec.Resources.DiagnosticPointers.main_ranges
#print axioms JPEG2000.Spec.Resources.DiagnosticPointers.public_cost
#print axioms JPEG2000.Spec.Resources.DiagnosticPointers.public_refusal
#print axioms JPEG2000.Spec.Resources.DiagnosticTileMarkers.plt_bounds
#print axioms JPEG2000.Spec.Resources.DiagnosticTileMarkers.ppt_range
#print axioms JPEG2000.Spec.Resources.DiagnosticTileMarkers.header_continuation
#print axioms JPEG2000.Spec.Resources.DiagnosticTileMarkers.read_count
#print axioms JPEG2000.Spec.Resources.DiagnosticTileMarkers.main_count
#print axioms JPEG2000.Spec.Resources.DiagnosticTileMarkers.prefix_fields
#print axioms JPEG2000.Spec.Resources.DiagnosticTileMarkers.public_header
#print axioms JPEG2000.Spec.Resources.DiagnosticTilePart.tileParts_payload
#print axioms JPEG2000.Spec.Resources.DiagnosticTilePart.public_cost
#print axioms JPEG2000.Spec.Resources.DiagnosticTilePart.public_refusal
#print axioms JPEG2000.Spec.Resources.DiagnosticCoding.tile_positions
#print axioms JPEG2000.Spec.Resources.DiagnosticCoding.merge_refusal
#print axioms JPEG2000.Spec.Resources.DiagnosticCoding.repeated_overrides
#print axioms JPEG2000.Spec.Resources.DiagnosticCoding.public_digits
#print axioms JPEG2000.Spec.Resources.DiagnosticCoding.public_cost
#print axioms JPEG2000.Spec.Resources.DiagnosticCoding.main_refusal
#print axioms JPEG2000.Spec.Resources.DiagnosticCoding.short_quantization_refusal
#print axioms JPEG2000.Spec.Resources.DiagnosticCoding.inherited_quantization_refusal
#print axioms JPEG2000.Spec.Resources.DiagnosticGeometry.component_counts
#print axioms JPEG2000.Spec.Resources.DiagnosticGeometry.reached_totals
#print axioms JPEG2000.Spec.Resources.DiagnosticGeometry.geometry_refusal
#print axioms JPEG2000.Spec.Resources.DiagnosticGeometry.work_refusal
#print axioms JPEG2000.Spec.Resources.DiagnosticGeometry.work_cost
#print axioms JPEG2000.Spec.Resources.DiagnosticPacketRanges.parsed_ranges
#print axioms JPEG2000.Spec.Resources.DiagnosticPacket.public_callback
#print axioms JPEG2000.Spec.Resources.DiagnosticPacket.admission_free
#print axioms JPEG2000.Spec.Resources.DiagnosticPacket.storage_le_charge
#print axioms JPEG2000.Spec.Resources.DiagnosticPacket.decode_work
#print axioms JPEG2000.Spec.Resources.DiagnosticPacket.header_work
#print axioms JPEG2000.Spec.Resources.DiagnosticPacket.public_tile_refusal
#print axioms JPEG2000.Spec.Resources.DiagnosticPacket.visit_records
#print axioms JPEG2000.Spec.Resources.DiagnosticPacket.public_rank_refusal
#print axioms JPEG2000.Spec.Resources.DiagnosticPacket.ppm_mismatch
#print axioms JPEG2000.Spec.Resources.DiagnosticPacket.packed_refusal
#print axioms JPEG2000.Spec.Resources.DiagnosticCodeBlock.reader_messages
#print axioms JPEG2000.Spec.Resources.DiagnosticCodeBlock.reader_calls
#print axioms JPEG2000.Spec.Resources.DiagnosticCodeBlock.public_readers
#print axioms JPEG2000.Spec.Resources.DiagnosticComponent.tile_eq
#print axioms JPEG2000.Spec.Resources.DiagnosticComponent.messages
#print axioms JPEG2000.Spec.Resources.DiagnosticComponent.public_components
#print axioms JPEG2000.Spec.Resources.DiagnosticColour.source_geometry
#print axioms JPEG2000.Spec.Resources.DiagnosticColour.messages
#print axioms JPEG2000.Spec.Resources.DiagnosticColour.public_colour

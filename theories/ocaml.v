From Giskard Require Import structures refinement.
From Coq Require Extraction.
From Coq Require ExtrOcamlBasic.
From Coq Require ExtrOcamlNatInt.

Extract Inlined Constant block => "int".
Extract Inlined Constant node => "int".
Extract Constant block_eqb => "(=)".
Extract Constant node_eqb => "(=)".
Extract Constant has_at_least_two_thirdsb => "fun _ -> true".
Extract Constant GenesisBlock => "0".
Extract Constant b_height => "fun _ -> 0".
Extract Constant parent_ofb => "fun _ _ -> false".
Extract Constant generate_last_block => "fun x -> x + 1".
Extract Constant generate_new_block => "fun x -> x + 1".

Extraction "giskard.ml"
 propose_block_init_set
 process_timeout_set
 discard_view_invalid_set
 process_PrepareBlock_duplicate_set
 process_PrepareBlock_pending_vote_set
 process_PrepareBlock_vote_set
 process_PrepareVote_wait_set
 process_PrepareVote_vote_set
 process_PrepareQC_last_block_new_proposer_set
 process_PrepareQC_last_block_set
 process_PrepareQC_non_last_block_set
 process_ViewChange_quorum_new_proposer_set
 process_ViewChange_pre_quorum_set
 process_ViewChangeQC_single_set
 malicious_ignore_set
 process_PrepareBlock_malicious_vote_set.

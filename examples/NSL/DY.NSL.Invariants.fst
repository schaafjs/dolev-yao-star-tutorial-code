module DY.NSL.Invariants

open Comparse
open DY.Core
open DY.Lib
open DY.Extend

open DY.NSL.Data
open DY.NSL.Protocol

// may or may not be needed
open FStar.List.Tot.Base

// Taken from OnlineS
#set-options "--fuel 0 --ifuel 1 --z3rlimit 25"

(* Crypto invariants *)

%splice [ps_msg1_t_is_well_formed] (gen_is_well_formed_lemma (`msg1_t))
%splice [ps_msg2_t_is_well_formed] (gen_is_well_formed_lemma (`msg2_t))
%splice [ps_msg3_t_is_well_formed] (gen_is_well_formed_lemma (`msg3_t))
%splice [ps_message_t_is_well_formed] (gen_is_well_formed_lemma (`message_t))

// Taken from OnlineS, not sure if needed
instance crypto_usages_nsl : crypto_usages = default_crypto_usages

#push-options "--ifuel 3"
let crypto_predicates_nsl : crypto_predicates = {
  default_crypto_predicates with
  
  pke_pred = {
    pred = (fun tr sk_usage pk msg ->
    (exists prin.
      sk_usage == long_term_key_type_to_usage (LongTermPkeKey key_tag) prin /\
      (match parse message_t msg with
      | Some (Msg1 {alice; n_a}) ->
        let bob = prin in
        get_label tr n_a == nonce_label alice bob /\
        event_triggered tr alice (Initiating {alice; bob; n_a})
      | Some (Msg2 {bob; n_a; n_b}) ->
        let alice = prin in
        get_label tr n_a == nonce_label alice bob /\
        get_label tr n_b == nonce_label alice bob /\
        event_triggered tr bob (Responding1{alice; bob; n_a; n_b})
      | Some (Msg3 {n_b}) ->
        True // Analogous to just accepting a previously sent and verified nonce in the Online protocol
      | _ -> False // fallthrough case, reject all other messages that do not conform to any of the expected types.
      ))
    );
  pred_later = (fun tr1 tr2 sk_usage pk msg ->
    parse_wf_lemma message_t (bytes_well_formed tr1) msg
  );
  };
}
#pop-options

instance crypto_invariants_nsl: crypto_invariants = {
  usages = crypto_usages_nsl;
  preds = crypto_predicates_nsl
}

(* State invariants *)

%splice [ps_sent_msg1_t_is_well_formed](gen_is_well_formed_lemma (`sent_msg1_t))
%splice [ps_sent_msg2_t_is_well_formed](gen_is_well_formed_lemma (`sent_msg2_t))
%splice [ps_sent_msg3_t_is_well_formed](gen_is_well_formed_lemma (`sent_msg3_t))
%splice [ps_rcvd_msg3_t_is_well_formed](gen_is_well_formed_lemma (`rcvd_msg3_t))
%splice [ps_state_t_is_well_formed](gen_is_well_formed_lemma (`state_t))

#push-options "--ifuel 2 --z3cliopt 'smt.qi.eager_threshold=50'"
let state_predicate_nsl: local_state_predicate state_t = {
  pred = (fun tr prin sess_id st ->
    match st with
    | SentMsg1 {bob; n_a} -> (
      let alice = prin in
      is_secret (nonce_label alice bob) tr n_a /\
      //is_knowable_by (nonce_label alice bob) tr n_a /\
      event_triggered tr alice (Initiating{alice; bob; n_a})
    )
    | SentMsg2 {alice; n_a; n_b} -> (
      let bob = prin in
      //is_knowable_by (principal_label bob) tr n_a /\
      is_secret (nonce_label alice bob) tr n_b /\
      //is_knowable_by (nonce_label alice bob) tr n_b /\
      event_triggered tr bob (Responding1{alice; bob; n_a; n_b}) /\
      // Too strong of an assumption as is. If the attacker sends some public n_a, neither hold
      ((is_secret (nonce_label alice bob) tr n_a /\
      //is_knowable_by (nonce_label alice bob) tr n_a /\
      state_was_set_some_id tr alice (SentMsg1 {bob; n_a})) \/
      is_publishable tr n_a)
    )
    | SentMsg3 {bob; n_a; n_b} -> (
      let alice = prin in
      // Not implied by state_was_set_some_id
      is_secret (nonce_label alice bob) tr n_a /\
      //is_knowable_by (nonce_label alice bob) tr n_a /\
      // The next line implies
      event_triggered tr alice (Initiating{alice; bob; n_a}) /\
      //state_was_set_some_id tr alice (SentMsg1 {bob; n_a}) /\
      ((is_secret (nonce_label alice bob) tr n_b /\
      //is_knowable_by (nonce_label alice bob) tr n_b /\
      state_was_set_some_id tr bob (SentMsg2 {alice; n_a; n_b})) \/
      (is_publishable tr n_a /\ is_publishable tr n_b))
    )
    | RcvdMsg3 {alice; n_a; n_b} -> (
      let bob = prin in
      is_secret (nonce_label alice bob) tr n_b /\
      //is_knowable_by (nonce_label alice bob) tr n_b /\
      event_triggered tr bob (Responding1{alice; bob; n_a; n_b}) /\
      // Required for pred_knowable
      is_knowable_by (nonce_label alice bob) tr n_a /\
      ((is_secret (nonce_label alice bob) tr n_a /\
      //is_knowable_by (nonce_label alice bob) tr n_a /\
      state_was_set_some_id tr alice (SentMsg3 {bob; n_a; n_b})) \/
      // is_publishable tr n_a or n_b???
      (is_publishable tr n_b))
    )
    | _ -> False
    );
  pred_later = (fun tr1 tr2 prin sess_id st -> ());
  pred_knowable = (fun tr prin sess_id st -> ());
}
#pop-options

(* Event invariants, taken from NSLP *)
let event_predicate_nsl: event_predicate event_t =
  fun tr prin e ->
    match e with
    | Initiating {alice; bob; n_a} -> (
      prin == alice /\
      is_secret (nonce_label alice bob) tr n_a /\
      rand_just_generated tr n_a
    )
    | Responding1 {alice; bob; n_a; n_b} -> (
      prin == bob /\
      is_secret (nonce_label alice bob) tr n_b /\
      rand_just_generated tr n_b
    )

(* Trace invariants *)

let all_sessions = [
  pki_tag_and_invariant;
  private_keys_tag_and_invariant;
  (|local_state_state_t.tag,
  local_state_predicate_to_local_bytes_state_predicate
  state_predicate_nsl|);
]

/// List of all local event predicates, taken from NSLP

let all_events = [
  (event_event_t.tag, compile_event_pred event_predicate_nsl)
]

let trace_invariants_nsl: trace_invariants = {
  state_pred = mk_state_pred all_sessions;
  event_pred = mk_event_pred all_events;
}

instance protocol_invariants_nsl: protocol_invariants = {
  crypto_invs = crypto_invariants_nsl;
  trace_invs = trace_invariants_nsl;
}

let complies_with_nsl_protocol tr = trace_invariant
#protocol_invariants_nsl tr

val all_sessions_has_all_sessions: unit -> Lemma (norm [delta_only [`%all_sessions; `%for_allP]; iota; zeta] (for_allP (has_local_bytes_state_predicate) all_sessions))
let all_sessions_has_all_sessions () =
  assert_norm(List.Tot.no_repeats_p (List.Tot.map dfst (all_sessions)));
  mk_state_pred_correct all_sessions;
  norm_spec [delta_only [`%all_sessions; `%for_allP]; iota; zeta] (for_allP (has_local_bytes_state_predicate) all_sessions)

val protocol_invariants_p_has_p_session_invariant: squash (has_local_state_predicate state_predicate_nsl)
let protocol_invariants_p_has_p_session_invariant = all_sessions_has_all_sessions ()

val protocol_invariants_p_has_pki_invariant: squash (has_pki_invariant #protocol_invariants_nsl)
let protocol_invariants_p_has_pki_invariant = all_sessions_has_all_sessions ()

val protocol_invariants_p_has_private_keys_invariant: squash (has_private_keys_invariant #protocol_invariants_nsl)
let protocol_invariants_p_has_private_keys_invariant = all_sessions_has_all_sessions ()

/// Lemmas that the global event predicate contains all the local ones, taken from NSLP

val all_events_has_all_events: unit -> Lemma (norm [delta_only [`%all_events; `%for_allP]; iota; zeta] (for_allP (has_compiled_event_pred #protocol_invariants_nsl) all_events))
let all_events_has_all_events () =
  assert_norm(List.Tot.no_repeats_p (List.Tot.map fst (all_events)));
  mk_event_pred_correct #protocol_invariants_nsl all_events;
  norm_spec [delta_only [`%all_events; `%for_allP]; iota; zeta] (for_allP (has_compiled_event_pred #protocol_invariants_nsl) all_events);
  let dumb_lemma (x:prop) (y:prop): Lemma (requires x /\ x == y) (ensures y) = () in
  dumb_lemma (for_allP (has_compiled_event_pred #protocol_invariants_nsl) all_events) (norm [delta_only [`%all_events; `%for_allP]; iota; zeta] (for_allP (has_compiled_event_pred #protocol_invariants_nsl) all_events))

val protocol_invariants_nsl_has_nsl_event_invariant: squash (has_event_pred event_predicate_nsl)
let protocol_invariants_nsl_has_nsl_event_invariant = all_events_has_all_events ()

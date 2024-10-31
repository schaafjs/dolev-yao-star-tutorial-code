module DY.OnlineS.Invariants

open Comparse 
open DY.Core
open DY.Lib
open DY.OnlineS.Protocol

#set-options "--fuel 0 --ifuel 1 --z3rlimit 25"

/// In this module, we define the protocol invariants.
/// They consist of
/// * crypto invariants and
/// * trace invariants which in turn consist of
///   * state invariants and
///   * event invariants
///
/// We then have to show
/// * these invariants imply the secrecy property (see DY.OnlineS.Secrecy) and
/// * every protocol step maintains these invariants (see DY.OnlineS.Invariants.Proofs)
/// With this, we then know that
/// the protocol model satisfies the secrecy property.


(*** Crypto Invariants ***)


(** TODO **)
// needed for `crypto_prediates.pkenc_pred.pred_later`
%splice [ps_ping_t_is_well_formed] (gen_is_well_formed_lemma (`ping_t))
%splice [ps_ack_is_well_formed] (gen_is_well_formed_lemma (`ack))
%splice [ps_message_is_well_formed] (gen_is_well_formed_lemma (`message))


// ignore this for now
instance crypto_usages_p : crypto_usages = default_crypto_usages

#push-options "--ifuel 2"
let crypto_p : crypto_predicates = { 
  default_crypto_predicates with 
  // we restrict when a message is allowed to be encrypted 
  // with some secret key
  pkenc_pred = { 
    pred = (fun tr sk_usage msg ->
    exists prin. // the intended receiver of the message
    (
      // needed for `decode_ping_proof` [Why?]
      (* the key used for the encryption is
         a protocol-level public key for the intended receiver (prin) 
      *)
      sk_usage == long_term_key_type_to_usage (LongTermPkEncKey key_tag) prin /\
      (match parse message msg with
      | Some (Ping ping) ->
          (* a Ping message can only be encrypted if
             the contained nonce n_a
             is labeled for 
             * the name provided in the message (alice)
             * and the intended receiver of the message (bob)
          *)
          let bob = prin in
          let alice = ping.p_alice in
          let n_a = ping.p_n_a in
          get_label tr n_a == nonce_label alice bob
      | Some (Ack ack) ->
         (* an Ack message can only be encrypted if
            the contained nonce n_a
            is readable by the intended receiver (alice)
         *)
          let alice = prin in
          let n_a = ack.a_n_a in
          get_label tr n_a `can_flow tr` principal_label alice
      | _ -> False // other messages can not be encrypted
      ))
      ); 
    (* a lemma guaranteeing:
       if the predicate specified above holds for some trace tr1
       it also holds for any extension tr2 of tr1
    *)
    pred_later = (fun tr1 tr2 pk msg -> 
      parse_wf_lemma message (bytes_well_formed tr1) msg
    ) 
  } 
}
#pop-options

/// Collecting the usages and prediates in the final crypto invariants

instance crypto_invariants_p: crypto_invariants = {
  usages = crypto_usages_p;
  preds =  crypto_p
}


(*** State Invariant ***)

// TODO
// Needed for `state_predicate.pred_knowable`
%splice [ps_sent_ping_is_well_formed] (gen_is_well_formed_lemma (`sent_ping))
%splice [ps_sent_ack_is_well_formed] (gen_is_well_formed_lemma (`sent_ack))
%splice [ps_received_ack_is_well_formed] (gen_is_well_formed_lemma (`received_ack))
%splice [ps_state_is_well_formed] (gen_is_well_formed_lemma (`state))

#push-options "--z3cliopt 'smt.qi.eager_threshold=50'"
(* We restrict what states are allowed to be stored by principals *)
let state_predicate_p: local_state_predicate state = {
  pred = (fun tr prin sess_id st ->
    match st with
    | SentPing ping -> (
        (* a SentPing state may only be stored if
           the stored nonce is labeled for
           * the storing principal (alice)
           * the principal stored in the state 
             (the intended receiver of the Ping: bob)
        *) 
        let alice = prin in
        let bob = ping.sp_bob in
        let n_a = ping.sp_n_a in
        is_secret (nonce_label alice bob) tr n_a
    )
    | SentAck ack -> (
        (* a SentAck state may only be stored if
           the stored nonce is readable by
           * the storing principal (bob)
           * the principal stored in the state 
             (the intended receiver of the Ack: alice)
        *)
        let bob = prin in
        let alice = ack.sa_alice in
        let n_a = ack.sa_n_a in
        is_knowable_by (nonce_label alice bob) tr n_a
    )
    | ReceivedAck rack  -> (
        (* a ReceivedAck state may only be stored if
           the stored nonce is labeled for
           * the storing principal (alice)
           * the principal stored in the state
             (the expected sender of the Ack)
        *)
        let alice = prin in
        let bob = rack.ra_bob in
        let n_a = rack.ra_n_a in
        is_secret (nonce_label alice bob) tr n_a
    )
  );
  (* as for encryption we have a lemma guaranteeing:
     if the state predicate holds on some trace tr1
     it also holds for any extension tr2 of tr2
  *)
  pred_later = (fun tr1 tr2 prin sess_id st -> ());
  (* a lemma guaranteeing that
     the content of the state to be stored
     is readable by the storing principal
  *)
  pred_knowable = (fun tr prin sess_id st -> ());
}
#pop-options

(*** Trace invariants ***)

// TODO: can this (all_sessions and all_events) be hidden somehow?
let all_sessions = [
  pki_tag_and_invariant;
  private_keys_tag_and_invariant;
  (|local_state_state.tag, local_state_predicate_to_local_bytes_state_predicate state_predicate_p|);
]

/// We have no events here,
/// but we need to specify that for the trace invariants
let all_events = []


/// The final trace invariants
/// consisting of
/// * the state invariant and
/// * the event invariant

let trace_invariants_p: trace_invariants = {
  state_pred = mk_state_pred all_sessions;
  event_pred = mk_event_pred all_events;
}


(*** Protocol Invariants ***)

/// The final protocol invariants
/// consisting of
/// * the crypto invariants and
/// * the trace invariants

instance protocol_invariants_p: protocol_invariants = {
  crypto_invs = crypto_invariants_p;
  trace_invs = trace_invariants_p;
}


(*** Helper Lemmas for the Secrecy Proof ***)

// TODO: Can all of this be hidden somehow?

val all_sessions_has_all_sessions: unit -> Lemma (norm [delta_only [`%all_sessions; `%for_allP]; iota; zeta] (for_allP (has_local_bytes_state_predicate) all_sessions))
let all_sessions_has_all_sessions () =
  assert_norm(List.Tot.no_repeats_p (List.Tot.map dfst (all_sessions)));
  mk_state_pred_correct all_sessions;
  norm_spec [delta_only [`%all_sessions; `%for_allP]; iota; zeta] (for_allP (has_local_bytes_state_predicate) all_sessions)

val protocol_invariants_p_has_p_session_invariant: squash (has_local_state_predicate state_predicate_p)
let protocol_invariants_p_has_p_session_invariant = all_sessions_has_all_sessions ()

val protocol_invariants_p_has_pki_invariant: squash (has_pki_invariant #protocol_invariants_p)
let protocol_invariants_p_has_pki_invariant = all_sessions_has_all_sessions ()

val protocol_invariants_p_has_private_keys_invariant: squash (has_private_keys_invariant #protocol_invariants_p)
let protocol_invariants_p_has_private_keys_invariant = all_sessions_has_all_sessions ()

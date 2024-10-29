module DY.OnlineSB.Secrecy

open Comparse
open DY.Core
open DY.Lib

open DY.OnlineSB.Protocol
open DY.OnlineSB.Invariants


/// The nonce n_a is unknown to the attacker,
/// unless the attacker corrupted Alice or Bob.

val n_a_secrecy:
  tr:trace -> alice:principal -> bob:principal -> n_a:bytes ->
  Lemma
  (requires
    attacker_knows tr n_a /\
    trace_invariant tr /\ (
      (exists sess_id. state_was_set tr alice sess_id (SendingPing {sp_bob = bob; sp_n_a = n_a})) \/
      // (exists sess_id. state_was_set tr alice sess_id (SendingAck {sa_alice = alice; sa_n_a = n_a})) \/
      (exists sess_id. state_was_set tr bob sess_id (ReceivedAck {ra_bob = bob; ra_n_a = n_a} ))
    )
  )
  (ensures is_corrupt tr (principal_label alice) \/ is_corrupt tr (principal_label bob))
let n_a_secrecy tr alice bob n_a =
  attacker_only_knows_publishable_values tr n_a

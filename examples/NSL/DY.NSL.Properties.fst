module DY.NSL.Properties

open Comparse
open DY.Core
open DY.Lib
open DY.Simplified
open DY.Extend

open DY.NSL.Data
open DY.NSL.Invariants

// Contains secrecy and authentication properties

// We want both n_a and n_b to stay secret, i.e., be unknown to the attacker
val n_a_secrecy:
  tr:trace -> alice:principal -> bob:principal -> n_a:bytes -> n_b:bytes ->
  Lemma
  (requires
    complies_with_nsl_protocol tr /\ (
      (state_was_set_some_id tr alice (SentMsg1 {bob; n_a})) \/
      (exists n_b. state_was_set_some_id tr bob (SentMsg2 {alice; n_a; n_b})) \/
      (exists n_b. state_was_set_some_id tr alice (SentMsg3 {bob; n_a; n_b})) \/
      (exists n_b. state_was_set_some_id tr bob (RcvdMsg3 {alice; n_a; n_b}))
    )
  )
  (ensures
    attacker_knows tr n_a ==>
    principal_is_corrupt tr alice \/ principal_is_corrupt tr bob
  )

let nonce_label alice bob = join (principal_label alice) (principal_label bob)

val publishable_implies_corruption:
  tr:trace -> alice:principal -> bob:principal -> n:bytes ->
  Lemma
    (requires
      trace_invariant tr /\
      is_secret (nonce_label alice bob) tr n
    )
    (ensures 
      is_publishable tr n ==>
      principal_is_corrupt tr alice \/
      principal_is_corrupt tr bob
    )

let publishable_implies_corruption tr alice bob n_a = ()

let n_a_secrecy tr alice bob n_a n_b =
  introduce attacker_knows tr n_a ==> principal_is_corrupt tr alice \/ principal_is_corrupt tr bob
  with _ .
    attacker_only_knows_publishable_values tr n_a

(*
let n_a_secrecy tr alice bob n_a n_b =
  introduce attacker_knows tr n_a ==> principal_is_corrupt tr alice \/ principal_is_corrupt tr bob
  with _ .
    attacker_only_knows_publishable_values tr n_a*)

val n_b_secrecy:
  tr:trace -> alice:principal -> bob:principal -> n_a:bytes -> n_b:bytes ->
  Lemma
  (requires
    complies_with_nsl_protocol tr /\ (
      (state_was_set_some_id tr bob (SentMsg2 {alice; n_a; n_b})) \/
      (state_was_set_some_id tr alice (SentMsg3 {bob; n_a; n_b}))
    )
  )
  (ensures
    attacker_knows tr n_b ==>
    principal_is_corrupt tr alice \/ principal_is_corrupt tr bob
  )

let n_b_secrecy tr alice bob n_a n_b =
  introduce attacker_knows tr n_b ==> principal_is_corrupt tr alice \/ principal_is_corrupt tr bob
  with _ .
    attacker_only_knows_publishable_values tr n_b

// If Bob at the end of a run believes to be talking with Alice, then this Alice must indeed be involved in the run.
val initiator_authentication:
  alice:principal -> bob:principal -> n_a:bytes -> n_b:bytes -> tr:trace ->
  Lemma
  (requires
    complies_with_nsl_protocol tr /\
    trace_invariant tr /\
    state_was_set_some_id tr bob (RcvdMsg3 {alice; n_a; n_b})
  )
  (ensures
    principal_is_corrupt tr alice \/
    principal_is_corrupt tr bob \/ (
    state_was_set_some_id tr alice (SentMsg1 {bob; n_a}) /\
    state_was_set_some_id tr alice (SentMsg3 {bob; n_a; n_b})
    // TODO: Not sure if the following line is strictly necessary since it is implied by setting the RcvdMsg3 state
    //state_was_set_some_id tr bob (SentMsg2 {alice; n_a; n_b})
    )
  )

let initiator_authentication alice bob n_a n_b tr = ()
  //assert(state_was_set_some_id tr alice (SentMsg3 {bob; n_a; n_b}))

// If Alice at the end of a run believes to be talking with Bob, then this Bob must indeed be involved in the run.
val responder_authentication:
  alice:principal -> bob:principal -> n_a:bytes -> n_b:bytes -> tr:trace ->
  Lemma
  (requires
    complies_with_nsl_protocol tr /\
    trace_invariant tr /\
    state_was_set_some_id tr alice (SentMsg3 {bob; n_a; n_b})
  )
  (ensures
    principal_is_corrupt tr alice \/
    principal_is_corrupt tr bob \/ (
    state_was_set_some_id tr bob (SentMsg2 {alice; n_a; n_b})
    //state_was_set_some_id tr bob (RcvdMsg3 {alice; n_a; n_b})
    // Same as above: almost certainly not needed; bot from a proof perspective and to satisfy the intuitive meaning behind the statement
    //state_was_set_some_id tr alice (SentMsg1 {bob; n_a})
    )
  )

let responder_authentication alice bob n_a n_b tr = ()
